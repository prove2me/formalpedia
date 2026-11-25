-- Prove2me | solution 1 for GroundTheory.LocalField.localFourier_indicator_valBall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:23:49.568016+00:00
-- url     : https://prove2.me/submissions/5d78b84e-5d4e-416b-86ef-73707b15f73f

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaTate
import Definitions.Def_GroundTheory_LocalFields_PadicLogHom
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
import Theorems.Thm_GroundTheory_LocalField_integral_valBall_char
import Theorems.Thm_GroundTheory_LocalField_measurableSet_valBall


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
variable {χ : Kˣ →* ℂˣ}
namespace GroundTheory.LocalField
theorem _root_.solution (μ : Measure K) [μ.IsAddHaarMeasure] {ψ : AddChar K Circle}
    (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (k : ℤ) (y : K) :
    localFourier μ ψ ((valBall K k : Set K).indicator fun _ => 1) y =
      (μ.real (valBall K k) : ℂ) *
        (valBall K (addCharConductor ψ - k) : Set K).indicator (fun _ => 1) y := by
  classical
  have e : (fun x => (valBall K k : Set K).indicator (fun _ => (1 : ℂ)) x * (ψ (x * y) : ℂ)) =
      (valBall K k : Set K).indicator fun x => ((ψ.mulShift y) x : ℂ) := by
    funext x
    by_cases hx : x ∈ (valBall K k : Set K)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul, AddChar.mulShift_apply,
        mul_comm]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  unfold localFourier
  rw [e, integral_indicator (measurableSet_valBall k), integral_valBall_char]
  by_cases hy : y ∈ valBall K (addCharConductor ψ - k)
  · rw [if_pos ((isTrivialOn_mulShift_iff_mem hψ hψ1 y k).mpr hy),
      Set.indicator_of_mem (show y ∈ (valBall K (addCharConductor ψ - k) : Set K) from hy), mul_one]
  · rw [if_neg (mt (isTrivialOn_mulShift_iff_mem hψ hψ1 y k).mp hy),
      Set.indicator_of_notMem (show y ∉ (valBall K (addCharConductor ψ - k) : Set K) from hy),
      mul_zero]
end GroundTheory.LocalField
