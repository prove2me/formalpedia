-- Prove2me | solution 1 for GlobalTheory.HCA.SolSub.contDiff_dw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:54:04.845833+00:00
-- url     : https://prove2.me/submissions/72ef51ff-6c00-4e40-9ab7-c45c4060416d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AestronglyMeasurableExtendByZeroOffSubset

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
theorem _root_.solution {f : E d → ℂ} (hf : ContDiff ℝ ∞ f) : ∀ w : List (Fin d), ContDiff ℝ ∞ (dw w f)
  | [] => hf
  | j :: w => by
      have h := solution hf w
      show ContDiff ℝ ∞ (fun x => fderiv ℝ (dw w f) x (ev j))
      exact (h.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
end GlobalTheory.HCA.SolSub
