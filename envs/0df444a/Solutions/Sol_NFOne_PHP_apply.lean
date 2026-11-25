-- Prove2me | solution 1 for NFOne.PHP_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:29:27.20904+00:00
-- url     : https://prove2.me/submissions/9f300ff7-5468-4c16-865c-084ab7f66c74

import Definitions.Def_Formalism_HermitianCurvature_OperatorsCommuteTranslations
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_PRowWSColW
import Theorems.Thm_NFOne_sg_val
import Theorems.Thm_NFOne_P_rowS
import Theorems.Thm_NFOne_HP_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] NFOne.sg_val

set_option autoImplicit false
open Matrix Finset Formalism.QuantumDeterminants
noncomputable section
open NFOne
namespace NFOne
theorem _root_.solution (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1)) :
    ((Pm k r j V)ᴴ * (Hpk k r * Pm k r j V)) p q = ∑ i, (if r ≤ i.val ∧ i.val ≤ r + k then
      dW k r i * star (Pm k r j V i p) * Pm k r j V i q else 0) := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [HP_apply, Matrix.conjTranspose_apply]
  have hi := i.isLt
  by_cases h : r ≤ i.val ∧ i.val ≤ r + k
  · rw [if_pos h, if_pos h]
    ring
  · rw [if_neg h, if_neg h]
    by_cases h2 : i.val < r
    · rw [P_rowS k r j V (sg k r i) q (by simp only [sg_val]; omega), mul_zero]
    · rw [P_rowS k r j V i p (by omega), star_zero, zero_mul]
end NFOne
