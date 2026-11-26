-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_alltime_meas_only
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:38:30.960632+00:00
-- url     : https://prove2.me/submissions/abb33908-cd36-4a08-830c-735cb83221c7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_measurable
import Theorems.Thm_Kyprianou_Ch04_pathRunningInfimumLimit
import Theorems.Thm_Kyprianou_Ch04_infimumLimitSupport
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) :
    let B : Set Ω := {w | BddBelow (range (fun t : NNReal => L.X t w))}
    let D : Ω → ℝ := B.indicator (fun w => -sInf (range (fun t => L.X t w)))
    Measurable D := by
  classical
  intro B D
  have hB : MeasurableSet B :=
    (Kyprianou.Ch04.infimumLimitSupport P F L 1 (by norm_num)).1
  let g : ℕ → Ω → ℝ := fun n =>
    B.indicator (fun w => -sInf ((fun t : NNReal => L.X t w) '' Iic (n : NNReal)))
  have hg (n : ℕ) : Measurable (g n) := by
    apply Measurable.indicator _ hB
    convert levy_running_infimum_measurable L (n : NNReal) using 1
    funext w
    congr 2
    ext y
    constructor <;> rintro ⟨t,ht,he⟩ <;> exact ⟨t,ht,he.symm⟩
  have hlim : Tendsto g atTop (𝓝 D) := by
    rw [tendsto_pi_nhds]
    intro w
    by_cases hw : w ∈ B
    · have hh := Kyprianou.Ch04.pathRunningInfimumLimit (fun t => L.X t w) hw
      simpa [g,D,hw] using
        (hh.comp (tendsto_natCast_atTop_atTop (R := NNReal))).neg
    · simpa [g,D,hw] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact measurable_of_tendsto_metrizable hg hlim
