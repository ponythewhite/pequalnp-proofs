import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25173

open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[⟨.and, [1, 3]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.and, [8, 11]⟩, ⟨.not, [12]⟩, ⟨.and, [7, 13]⟩, ⟨.or, [6, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_25173

theorem PEqualNP.Outside.L_meta_25173 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17209 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_25173.witness, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_25173.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
