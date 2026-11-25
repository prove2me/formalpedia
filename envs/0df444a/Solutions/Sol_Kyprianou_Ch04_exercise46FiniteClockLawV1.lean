-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46FiniteClockLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:21:45.896288+00:00
-- url     : https://prove2.me/submissions/91cb7706-da36-449c-975e-b39295b9b627

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Push forward the restriction of the original measure to finite clocks. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (B : Omega → WithTop NNReal) (hB : AEMeasurable B P) :
    ∃ nu : Measure Real, IsFiniteMeasure nu ∧ nu (Iio (0 : Real)) = 0 ∧
      nu univ = P {w | B w ≠ ⊤} ∧
      (∀ t : Real, 0 ≤ t → nu (Iic t) =
        P {w | B w ≤ (t.toNNReal : WithTop NNReal)}) ∧
      ∀ beta : Real, (∫ y, Real.exp (-beta * y) ∂nu) =
        ∫ w, if B w = ⊤ then (0 : Real)
          else Real.exp (-beta * (((B w).untopD 0 : NNReal) : Real)) ∂P := by
  classical
  let D : Set Omega := {w | B w ≠ ⊤}
  let T : Omega → Real := fun w => ((B w).untopD 0 : NNReal)
  have hD : NullMeasurableSet D P :=
    hB.nullMeasurableSet_preimage (measurableSet_singleton (⊤ : WithTop NNReal)).compl
  have hT : AEMeasurable T (P.restrict D) :=
    (measurable_coe_nnreal_real.comp_aemeasurable
      ((WithTop.measurable_untopD (0 : NNReal)).comp_aemeasurable hB)).restrict
  refine ⟨(P.restrict D).map T, Measure.isFiniteMeasure_map _ _, ?_, ?_, ?_, ?_⟩
  · rw [Measure.map_apply_of_aemeasurable hT measurableSet_Iio]
    have : T ⁻¹' Iio (0 : Real) = ∅ := by
      ext w
      simp [T, not_lt_of_ge (NNReal.coe_nonneg ((B w).untopD 0))]
    simp [this]
  · rw [Measure.map_apply_of_aemeasurable hT MeasurableSet.univ]
    simp [D]
  · intro t ht
    rw [Measure.map_apply_of_aemeasurable hT measurableSet_Iic, Measure.restrict_apply₀' hD]
    congr 1
    ext w
    cases h : B w with
    | top =>
      simp [D, T, h]
      exact fun hle => WithTop.coe_ne_top (WithTop.top_le_iff.mp hle)
    | coe a =>
      simp [D, T, h]
      change ((WithTop.untopD 0 (WithTop.some a) : NNReal) : Real) ≤ t ∧
        WithTop.some a ≠ ⊤ ↔ WithTop.some a ≤ WithTop.some t.toNNReal
      have he : WithTop.untopD 0 (WithTop.some a) = a := WithTop.untopD_coe 0 a
      rw [he]
      exact ⟨fun h => WithTop.coe_le_coe.mpr ((Real.le_toNNReal_iff_coe_le ht).mpr h.1),
        fun h => ⟨(Real.le_toNNReal_iff_coe_le ht).mp (WithTop.coe_le_coe.mp h),
          WithTop.coe_ne_top⟩⟩
  · intro beta
    rw [integral_map hT (by fun_prop), ← integral_indicator₀ hD]
    apply integral_congr_ae
    filter_upwards with w
    by_cases hw : B w = ⊤ <;> simp [D, T, hw]
