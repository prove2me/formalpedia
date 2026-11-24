-- Prove2me | solution 1 for GlobalTheory.SmoothForms.gelfA_eq_sum_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:06:53.261697+00:00
-- url     : https://prove2.me/submissions/9140029e-305c-4a45-bc4b-05c1d1bb98ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PowEntryCommutator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Theorems.Thm_GlobalTheory_SmoothForms_sum_fin_succ_fun_cons
import Theorems.Thm_GlobalTheory_SmoothForms_pow_of_apply_eq_sum_paths

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
open GlobalTheory GlobalTheory.SmoothForms
variable {A : Type} [Ring A] {n : ℕ}
namespace GlobalTheory.SmoothForms
theorem _root_.solution (E : Fin n → Fin n → A) (k : ℕ) :
    gelfA E k = ∑ c, (Matrix.of E ^ (k + 1)) c c := by
  rw [gelfA, sum_fin_succ_fun_cons]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [pow_of_apply_eq_sum_paths]
  refine Finset.sum_congr rfl fun idx _ => ?_
  congr 2
  funext a
  congr 1
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp
  · rw [Fin.coeSucc_eq_succ]; simp
end GlobalTheory.SmoothForms
