-- Prove2me | solution 1 for GlobalTheory.ZetaHalfPlane.integrableOn_integrand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:36:09.990149+00:00
-- url     : https://prove2.me/submissions/3ad6c089-d2b1-491b-8ddf-8d7e816d7cf7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ZetaEqSubIntegralFract
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableAtFractInt
import Theorems.Thm_GlobalTheory_ZetaHalfPlane_norm_fract_le
import Theorems.Thm_GlobalTheory_ZetaHalfPlane_measurable_fract_ofReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Set Filter Topology
open GlobalTheory GlobalTheory.ZetaHalfPlane
namespace GlobalTheory.ZetaHalfPlane
theorem _root_.solution {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  have h : (-(s + 1)).re < -1 := by simp; linarith
  exact (integrableOn_Ioi_cpow_of_lt h one_pos).bdd_mul (c := 1)
    measurable_fract_ofReal.aestronglyMeasurable (Eventually.of_forall norm_fract_le)
end GlobalTheory.ZetaHalfPlane
