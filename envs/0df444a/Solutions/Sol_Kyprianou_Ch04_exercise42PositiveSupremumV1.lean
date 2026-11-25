-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42PositiveSupremumV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T18:00:45.389191+00:00
-- url     : https://prove2.me/submissions/db030bd0-990a-4401-b4bc-850d7aec0437

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_smallTimeDriftLimit
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
open MeasureTheory Filter AvramDividend.Classical Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)

    (hd : 0 < L.drift) :
    ∀ᵐ omega : Omega ∂P, ∀ t : NNReal, 0 < t →
      0 < sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t) := by
  filter_upwards [
    Kyprianou.Ch04.smallTimeDriftLimit P F L hBV,
    bv_drift_deficit_ae_monotone_all_times L hBV] with omega hratio hmono
  intro t ht
  have hNear :
      ∀ᶠ s : NNReal in 𝓝[>] (0 : NNReal),
        0 < L.X s omega / (s : ℝ) :=
    hratio.eventually (Ioi_mem_nhds hd)
  have hRange :
      ∀ᶠ s : NNReal in 𝓝[>] (0 : NNReal), s ∈ Ioo 0 t :=
    Ioo_mem_nhdsGT ht
  obtain ⟨s, hs, hposRatio⟩ := (hRange.and hNear).exists
  have hsReal : 0 < (s : ℝ) := by exact_mod_cast hs.1
  have hXpos : 0 < L.X s omega := by
    have hprod := mul_pos hposRatio hsReal
    simpa [div_mul_cancel₀ _ (ne_of_gt hsReal)] using hprod
  have hBound : BddAbove
      ((fun u : NNReal => L.X u omega) '' Iic t) := by
    refine ⟨L.drift * (t : ℝ), ?_⟩
    rintro x ⟨u, hu, rfl⟩
    have hXu : L.X u omega ≤ L.drift * (u : ℝ) := by
      simpa only [NNReal.coe_zero, mul_zero, L.X_zero,
        sub_self, sub_nonneg] using hmono (show (0 : NNReal) ≤ u from zero_le)
    have hut : (u : ℝ) ≤ (t : ℝ) := by exact_mod_cast hu
    exact hXu.trans (mul_le_mul_of_nonneg_left hut hd.le)
  have hmem : L.X s omega ∈
      ((fun u : NNReal => L.X u omega) '' Iic t) :=
    ⟨s, hs.2.le, rfl⟩
  exact hXpos.trans_le (le_csSup hBound hmem)
