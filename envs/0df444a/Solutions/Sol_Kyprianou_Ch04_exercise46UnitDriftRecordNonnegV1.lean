-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46UnitDriftRecordNonnegV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T10:51:43.64223+00:00
-- url     : https://prove2.me/submissions/a46c614a-469e-41f8-a84e-32cfe06f20e9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : L.drift = 1) :
    ∀ᵐ omega ∂P, ∀ t : NNReal,
      0 ≤ sSup ((fun s : NNReal => L.X s omega) '' Iic t) := by
  filter_upwards [bv_actual_levy_residual_ae_monotone_all_times L hBV]
    with omega hmono
  intro t
  have hbdd : BddAbove ((fun s : NNReal => L.X s omega) '' Iic t) := by
    refine ⟨(t : Real), ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have hle := hmono (zero_le : (0 : NNReal) ≤ s)
    have hst : (s : Real) ≤ (t : Real) := hs
    simp [L.X_zero, hd] at hle
    linarith
  have hmem : L.X 0 omega ∈ ((fun s : NNReal => L.X s omega) '' Iic t) :=
    ⟨0, mem_Iic.mpr zero_le, rfl⟩
  simpa [L.X_zero] using le_csSup hbdd hmem
