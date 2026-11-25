-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46OverloadedIdleCDFV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T10:52:17.425272+00:00
-- url     : https://prove2.me/submissions/93b5027b-3550-498c-b0b0-f90df48abba2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_totalIdleTimeTrafficRegimesV2
import Theorems.Thm_Kyprianou_Ch04_totalIdleMeasurableV1
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_Kyprianou_Ch04_exercise46CDFWithoutZeroAtomV1
import Theorems.Thm_Kyprianou_Ch04_exercise46UnitDriftRecordNonnegV1
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : L.drift = 1)
    (hrho : 1 < ∫⁻ y : Real, ENNReal.ofReal (-y) ∂L.ν) :
    ∃ phi : Real, 0 < phi ∧ L.ψ phi = 0 ∧
      (∀ theta : Real, 0 ≤ theta → L.ψ theta = 0 → theta ≤ phi) ∧
      ∀ x : Real, 0 ≤ x →
        (P {omega : Omega |
          (∫⁻ t in Ici (0 : Real),
            if sSup ((fun s : NNReal => L.X s omega) '' Iic t.toNNReal) -
              L.X t.toNNReal omega = 0 then (1 : ENNReal) else 0 ∂volume)
            ≤ ENNReal.ofReal x}).toReal = 1 - Real.exp (-phi * x) := by
  letI : IsProbabilityMeasure P := L.isProbability
  have hdpos : 0 < L.drift := by rw [hd]; norm_num
  let I : Omega → ENNReal := fun omega =>
    ∫⁻ t in Ici (0 : Real),
      if max 0 (sSup ((fun s : NNReal => L.X s omega) '' Iic t.toNNReal)) -
        L.X t.toNNReal omega = 0 then (1 : ENNReal) else 0 ∂volume
  have hm : Measurable I :=
    Kyprianou.Ch04.totalIdleMeasurableV1 P F L hBV hdpos 0 le_rfl
  have h := (Kyprianou.Ch04.totalIdleTimeTrafficRegimesV2
    P F L hBV hdpos 0 le_rfl).1
  obtain ⟨phi, hp, hroot, hmax, hzero, hpos⟩ :=
    h (by simpa [hd] using hrho)
  have hz : (P {omega | I omega = 0}).toReal = 0 := by
    simpa [I] using hzero
  refine ⟨phi, hp, hroot, hmax, ?_⟩
  intro x hx
  have hcdf : (P {omega | I omega ≤ ENNReal.ofReal x}).toReal =
      1 - Real.exp (-phi * x) := by
    rw [Kyprianou.Ch04.exercise46CDFWithoutZeroAtomV1 P I hm hz]
    simpa [I, hd] using hpos x hx
  have hs := Kyprianou.Ch04.exercise46UnitDriftRecordNonnegV1 P F L hBV hd
  have he : {omega | I omega ≤ ENNReal.ofReal x} =ᵐ[P]
      {omega | (∫⁻ t in Ici (0 : Real),
        if sSup ((fun s : NNReal => L.X s omega) '' Iic t.toNNReal) -
          L.X t.toNNReal omega = 0 then (1 : ENNReal) else 0 ∂volume)
          ≤ ENNReal.ofReal x} := by
    filter_upwards [hs] with omega hsup
    have hm0 (t : NNReal) := max_eq_right (hsup t)
    change (I omega ≤ ENNReal.ofReal x) =
      ((∫⁻ t in Ici (0 : Real),
        if sSup ((fun s : NNReal => L.X s omega) '' Iic t.toNNReal) -
          L.X t.toNNReal omega = 0 then (1 : ENNReal) else 0 ∂volume)
          ≤ ENNReal.ofReal x)
    simp only [I, hm0]
  rw [← measure_congr he]
  exact hcdf
