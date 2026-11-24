-- Prove2me | solution 1 for GlobalTheory.T.integral_exp_neg_hermitian_form_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:15:00.809717+00:00
-- url     : https://prove2.me/submissions/92bdf489-33e6-4408-b7d7-3778752a9816

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralExpNegHermitianFormPosDef
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralExpNegHermitianFormPosDefStatement
import Theorems.Thm_GlobalTheory_GaussHerm_integral_exp_neg_herm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), H.PosDef → Integrable (fun w : V n => Real.exp (-(∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re)) ∧ ∫ w : V n, Real.exp (-(∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re) = Real.pi ^ n / H.det.re := by
  first | exact @GlobalTheory.GaussHerm.integral_exp_neg_herm | exact GlobalTheory.GaussHerm.integral_exp_neg_herm | (intros; apply GlobalTheory.GaussHerm.integral_exp_neg_herm <;> assumption)
end _root_.GlobalTheory.T
