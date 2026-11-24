-- Prove2me | solution 1 for Kyprianou.Ch03.boundedStoppingDensityEventV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T15:45:43.810585+00:00
-- url     : https://prove2.me/submissions/3b963662-6f28-4457-9cba-8a4e39cad116

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_boundedStoppingUpperGridV1
import Theorems.Thm_AvramDividend_Classical_avram_ja18_rightcontinuous_clock_composition
import Theorems.Thm_AvramDividend_Classical_ftap_condExp_ae_eq_of_uniformIntegrable_tendsto
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (Z : NNReal → Omega → ℝ) (hMart : Martingale Z F P)
    (hRight : ∀ᵐ w ∂P, ∀ t : NNReal, ContinuousWithinAt (fun u => Z u w) (Set.Ici t) t)
    (rho : Omega → NNReal)
    (hStop : IsStoppingTime F (fun w => (rho w : WithTop NNReal)))
    (n : NNReal) (hBound : ∀ w, rho w ≤ n)
    (B : Set Omega) (hB : MeasurableSet[hStop.measurableSpace] B)
    : Integrable (B.indicator (fun w => Z (rho w) w)) P ∧
      (∫ w, B.indicator (fun v => Z (rho v) v) w ∂P) =
      (∫ w, B.indicator (Z n) w ∂P) := by 
  obtain ⟨G, hG, hCount, hAbove, hBelow, hConv⟩ :=
    Kyprianou.Ch03.boundedStoppingUpperGridV1 F rho hStop n hBound
  let V : ℕ → Omega → ℝ := fun k w => Z (G k w) w
  let M : Omega → ℝ := fun w => Z (rho w) w
  let H := fun k => (hG k).measurableSpace
  have hH (k : ℕ) : H k ≤ (inferInstance : MeasurableSpace Omega) :=
    (hG k).measurableSpace_le_of_le (fun w => WithTop.coe_le_coe.mpr (hBelow k w))
  have hS := hStop.measurableSpace_le_of_le (fun w => WithTop.coe_le_coe.mpr (hBound w))
  have hMono (k : ℕ) : hStop.measurableSpace ≤ H k :=
    hStop.measurableSpace_mono (hG k) (fun w => WithTop.coe_le_coe.mpr (hAbove k w))
  have hCE (k : ℕ) : V k =ᵐ[P] P[Z n | H k] :=
    hMart.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
      (hG k) (fun w => WithTop.coe_le_coe.mpr (hBelow k w)) (hCount k)
  have hui : UniformIntegrable V 1 P :=
    (uniformIntegrable_congr_ae hCE).2 ((hMart.integrable n).uniformIntegrable_condExp hH)
  have hlim : ∀ᵐ w ∂P, Tendsto (fun k => V k w) atTop (nhds (M w)) :=
    AvramDividend.Classical.avram_ja18_rightcontinuous_clock_composition Z rho G hRight hAbove hConv
  have hi := hui.integrable_of_ae_tendsto hlim
  have hc (k : ℕ) : P[V k | hStop.measurableSpace] =ᵐ[P] P[Z n | hStop.measurableSpace] :=
    (condExp_congr_ae (hCE k)).trans (condExp_condExp_of_le (hMono k) (hH k))
  have he := AvramDividend.Classical.ftap_condExp_ae_eq_of_uniformIntegrable_tendsto
    hS V M hui hlim (P[Z n | hStop.measurableSpace])
    stronglyMeasurable_condExp.aestronglyMeasurable hc
  refine ⟨hi.indicator (hS B hB), ?_⟩
  rw [integral_indicator (hS B hB), integral_indicator (hS B hB),
    ← setIntegral_condExp hS hi hB, ← setIntegral_condExp hS (hMart.integrable n) hB]
  exact integral_congr_ae (ae_mono Measure.restrict_le_self he)
