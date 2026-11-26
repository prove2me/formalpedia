-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_zero_atom_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:52:57.006361+00:00
-- url     : https://prove2.me/submissions/6edfbc94-a7fb-4391-a437-3b654abba740

import Mathlib
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch03_exercise35LaplaceExponentRegularity
import Theorems.Thm_Kyprianou_Ch04_cor412_secant_deriv
import Theorems.Thm_Kyprianou_Ch04_cor412_positive_exponent
import Theorems.Thm_Kyprianou_Ch04_cor412_lower_bounded
import Theorems.Thm_Kyprianou_Ch04_cor412_alltime_measurable
import Theorems.Thm_Kyprianou_Ch04_cor412_perpetual_transform
import Theorems.Thm_Kyprianou_Ch04_cor412_frequency_limit
import Theorems.Thm_Kyprianou_Ch04_cor412_zero_atom_path
import Theorems.Thm_Kyprianou_Ch04_cor412_finite_iff_negative
import Theorems.Thm_AvramDividend_Classical_nonnegative_laplace_transform_atom_zero_limit_nat
import Theorems.Thm_Kyprianou_Ch04_cor412_extended_perpetual_transform
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift)
    (hm : 0 < derivWithin L.ψ (Ici (0 : ℝ)) 0) :
    let B : Set Omega := {w | BddBelow (range (fun t : NNReal => L.X t w))}
    let D : Omega → ℝ := B.indicator (fun w => -sInf (range (fun t => L.X t w)))
    (P {w : Omega | D w = 0}).toReal = derivWithin L.ψ (Ici 0) 0 / L.drift := by
  classical
  intro B D
  let : IsProbabilityMeasure P := L.isProbability
  let m := derivWithin L.ψ (Ici 0) 0
  obtain ⟨hD,hD0⟩ := Kyprianou.Ch04.cor412_alltime_measurable P F L
  have hfreq := (Kyprianou.Ch04.cor412_frequency_limit P F L hBV hd m).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlim := nonnegative_laplace_transform_atom_zero_limit_nat P D hD (Eventually.of_forall hD0)
  have hlim2 : Tendsto (fun n : ℕ => ∫ w, Real.exp ((n : ℝ) * (-D w)) ∂P)
      atTop (𝓝 (m / L.drift)) := by
    apply hfreq.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    exact (Kyprianou.Ch04.cor412_extended_perpetual_transform P F L hm n hnR).symm
  have hmass := tendsto_nhds_unique hlim hlim2
  let Z : Set Omega := {w | D w = 0}
  have hZ : MeasurableSet Z := hD (measurableSet_singleton 0)
  have hZmass : (P Z).toReal = m / L.drift := by
    change P.real Z = m / L.drift
    rw [← hmass, ← integral_indicator_one hZ]
    apply integral_congr_ae
    exact Eventually.of_forall fun w => by simp [Z,Set.indicator]
  exact hZmass
