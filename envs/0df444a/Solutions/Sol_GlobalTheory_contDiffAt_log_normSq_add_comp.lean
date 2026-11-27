-- Prove2me | solution 1 for GlobalTheory.contDiffAt_log_normSq_add_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:36:53.593911+00:00
-- url     : https://prove2.me/submissions/e5033b7e-02d2-4dcc-96f9-9aa07cf84713

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology ComplexConjugate
noncomputable section
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G]
  [IsScalarTower ℝ ℂ G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedSpace ℝ H]
  [IsScalarTower ℝ ℂ H]
variable {φ : E → H} {z : E}
namespace GlobalTheory
theorem _root_.solution {δ : ℝ} (hφ : ContDiffAt ℂ 2 φ z)
    (hz : ‖φ z‖ ^ 2 + δ ≠ 0) : ContDiffAt ℝ 2 (fun x => Real.log (‖φ x‖ ^ 2 + δ)) z :=
  (((hφ.restrict_scalars ℝ).norm_sq ℂ).add contDiffAt_const).log hz
end GlobalTheory
