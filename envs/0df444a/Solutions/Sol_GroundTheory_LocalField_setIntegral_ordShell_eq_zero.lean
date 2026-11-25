-- Prove2me | solution 1 for GroundTheory.LocalField.setIntegral_ordShell_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:46:26.637216+00:00
-- url     : https://prove2.me/submissions/82600e95-7b49-4d0a-a095-4b0cac7a659a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_GroundTheory_LocalFields_LocalZetaShell
import Theorems.Thm_GroundTheory_LocalField_measurableSet_ordShell
import Theorems.Thm_GroundTheory_LocalField_integral_eq_zero_of_mul_eq

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
theorem _root_.solution (F : Kˣ → ℂ) {v : Kˣ} (hv : ord (v : K) = 0) {a : ℂ}
    (ha : a ≠ 1) (k : ℤ) (hF : ∀ u ∈ ordShell K k, F (v * u) = a * F u) :
    ∫ u in ordShell K k, F u ∂multHaar K = 0 := by
  rw [← integral_indicator (measurableSet_ordShell k)]
  refine integral_eq_zero_of_mul_eq _ _ v ha fun u => ?_
  have hiff : v * u ∈ ordShell K k ↔ u ∈ ordShell K k := by
    have := mul_mem_ordShell_iff (K := K) v (k := k) (u := u)
    rwa [hv, zero_add] at this
  by_cases hu : u ∈ ordShell K k
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (hiff.mpr hu), hF u hu]
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (mt hiff.mp hu), mul_zero]
end GroundTheory.LocalField
