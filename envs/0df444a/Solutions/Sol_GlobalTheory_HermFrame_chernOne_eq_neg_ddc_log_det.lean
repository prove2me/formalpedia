-- Prove2me | solution 1 for GlobalTheory.HermFrame.chernOne_eq_neg_ddc_log_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:51:16.150144+00:00
-- url     : https://prove2.me/submissions/49b233ad-50d4-43d2-838a-fc59bec12973

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChernOneEqNegDdcLogDet
import Theorems.Thm_GlobalTheory_HermFrame_trace_curv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m n l : Type*}
variable [Fintype n] [DecidableEq n] {H : E → Matrix n n ℂ} {z : E}
namespace GlobalTheory.HermFrame
theorem _root_.solution (h : MContDiffAt 2 H z)
    (hh : ∀ᶠ x in 𝓝 z, (H x).IsHermitian) (hu : IsUnit (H z).det) (ξ η : E) :
    chernOne H z ξ η = -ddc (fun x => Real.log (H x).det.re) z ξ η := by
  rw [chernOne, trace_curv h hh hu, ddc, mul_neg]
end GlobalTheory.HermFrame
