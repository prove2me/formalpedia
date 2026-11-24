-- Prove2me | solution 1 for GlobalTheory.HCA.SolSub.integrable_tr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:12:40.467896+00:00
-- url     : https://prove2.me/submissions/82af25d7-2aa8-41bb-a95d-2aa05f229368

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AestronglyMeasurableExtendByZeroOffSubset
import Theorems.Thm_GlobalTheory_HCA_SolSub_contDiff_dw
import Theorems.Thm_GlobalTheory_HCA_SolSub_hasCompactSupport_dw
import Theorems.Thm_GlobalTheory_HCA_SolSub_contDiff_mul_of_on
import Theorems.Thm_ZetaZeros_D_EllReg_Dec_contDiff_dw
import Theorems.Thm_ZetaZeros_D_EllReg_WF_contDiff_dw


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
noncomputable section
open GlobalTheory GlobalTheory.HCA GlobalTheory.HCA.SolSub
variable {d : ℕ}
namespace GlobalTheory.HCA.SolSub
theorem _root_.solution {ι : Type} (P : Sys d ι) {U : Set (E d)} (hU : IsOpen U)
    (ha : ∀ i n w, ContDiffOn ℝ ∞ (P.a i n w) U) (i : ι) {φ : E d → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) :
    Integrable (P.tr i φ) := by
  unfold Sys.tr trOp
  refine integrable_finset_sum _ (fun n _ => integrable_finset_sum _ (fun w _ => ?_))
  refine Integrable.const_mul ?_ _
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (contDiff_dw (contDiff_mul_of_on hU (ha i n w) hφ hs) _).continuous
  · refine hasCompactSupport_dw ?_ _
    exact hc.mul_left
end GlobalTheory.HCA.SolSub
