-- Prove2me | solution 1 for GlobalTheory.Nef.nrm_coeff_prod_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:21:39.783551+00:00
-- url     : https://prove2.me/submissions/a09d6e56-703b-45ec-8918-2df9afaf3a82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NrmCoeffProdLinear
import Theorems.Thm_GlobalTheory_Nef_coeff_max_prod_linear
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef
namespace GlobalTheory.Nef
theorem _root_.solution : ∀ (k F : Type) [Field k] [Field F] [Algebra k F], ∀ (v : Place k F) (m : ℕ) (α β : Fin m → F), nrm v (fun a : Fin (m + 1) => (∏ j, (Polynomial.C (α j) + Polynomial.C (β j) * Polynomial.X)).coeff a) = ∏ j, max (v.1 (α j)) (v.1 (β j)) := by
  intro k F _ _ _ v m α β
  obtain ⟨h1, i, hi⟩ := coeff_max_prod_linear v.1 α β Finset.univ
  have hdeg : (∏ j, (Polynomial.C (α j) + Polynomial.C (β j) * Polynomial.X)).natDegree ≤ m := by
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    calc _ ≤ ∑ _j : Fin m, 1 := Finset.sum_le_sum fun j _ => by
            rw [add_comm]; exact Polynomial.natDegree_linear_le
      _ = m := by simp
  refine le_antisymm (Finset.sup_le fun a _ => h1 a) ?_
  rw [← hi]
  by_cases him : i < m + 1
  · exact Finset.le_sup (f := fun a : Fin (m + 1) =>
      v.1 ((∏ j, (Polynomial.C (α j) + Polynomial.C (β j) * Polynomial.X)).coeff a))
      (Finset.mem_univ (⟨i, him⟩ : Fin (m + 1)))
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
    exact zero_le'
end GlobalTheory.Nef
