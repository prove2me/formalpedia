-- Prove2me | solution 1 for GroundTheory.LocalField.localFourier_oneAddValBallIndicator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:53:06.572313+00:00
-- url     : https://prove2.me/submissions/6112993e-2c17-49bf-ab84-1df4c826517d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaTate
import Definitions.Def_GroundTheory_LocalFields_PadicLogHom
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
import Theorems.Thm_GroundTheory_LocalField_localFourier_indicator_valBall
import Theorems.Thm_GroundTheory_LocalField_oneAddValBallIndicator_add_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
namespace GroundTheory.LocalField
theorem _root_.solution (μ : Measure K) [μ.IsAddHaarMeasure]
    {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (c : ℤ) (y : K) :
    localFourier μ ψ (oneAddValBallIndicator c) y =
      (ψ y : ℂ) * ((μ.real (valBall K c) : ℂ) *
        (valBall K (addCharConductor ψ - c) : Set K).indicator (fun _ => 1) y) := by
  rw [← localFourier_indicator_valBall μ hψ hψ1 c y]
  unfold localFourier
  rw [← integral_add_left_eq_self (fun x => oneAddValBallIndicator c x * (ψ (x * y) : ℂ)) 1,
    ← integral_const_mul]
  congr 1
  funext h
  rw [oneAddValBallIndicator_add_one, add_mul, one_mul, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring
end GroundTheory.LocalField
