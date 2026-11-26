-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_zero_atom_complement
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:48:14.483193+00:00
-- url     : https://prove2.me/submissions/22f7479b-2753-4574-8512-ca47cf2cf2e1

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
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P F)
    (hm : 0 < derivWithin L.ψ (Ici (0 : ℝ)) 0) :
    let B : Set Omega := {w | BddBelow (range (fun t : NNReal => L.X t w))}
    let D : Omega → ℝ := B.indicator (fun w => -sInf (range (fun t => L.X t w)))
    (P {w : Omega | Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w ≠ ⊤}).toReal =
      1 - (P {w : Omega | D w = 0}).toReal := by
  classical
  intro B D
  let : IsProbabilityMeasure P := L.isProbability
  let tau : Omega → WithTop NNReal := fun w => Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w
  obtain ⟨_,hb⟩ := Kyprianou.Ch04.cor412_lower_bounded P F L hm
  obtain ⟨hD,_⟩ := Kyprianou.Ch04.cor412_alltime_measurable P F L
  let Z : Set Omega := {w | D w = 0}
  have hZ : MeasurableSet Z := hD (measurableSet_singleton 0)
  have heq : {w : Omega | tau w ≠ ⊤} =ᵐ[P] Zᶜ := by
    filter_upwards [hb] with w hw
    have hwB : w ∈ B := hw
    have hzero := Kyprianou.Ch04.cor412_zero_atom_path (fun t => L.X t w) (L.X_zero w) hw
    have hhit := Kyprianou.Ch04.cor412_finite_iff_negative P F L w
    change (tau w ≠ ⊤) = (D w ≠ 0)
    change (Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w ≠ ⊤) = (D w ≠ 0)
    rw [hhit]
    rw [show D w = -sInf (range (fun t => L.X t w)) by simp [D,hwB]]
    rw [ne_eq, hzero]
    simp [not_le]
  rw [measure_congr heq]
  change P.real Zᶜ = 1 - P.real Z
  rw [measureReal_compl hZ]
  simp [Measure.real]
