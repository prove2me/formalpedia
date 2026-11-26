-- Prove2me | solution 1 for Kyprianou.Ch04.boundedPrimitiveClockLipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:40:49.943667+00:00
-- url     : https://prove2.me/submissions/adfb6dc2-b9ca-4ea8-985d-ab4353559403

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A locally integrable bounded time density has a Lipschitz Lebesgue primitive. -/
theorem solution (g : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hi : ∀ t : NNReal, IntegrableOn g (Icc (0 : ℝ) (t : ℝ)) volume)
    (hb : ∀ᵐ r ∂volume.restrict (Ici (0 : ℝ)), ‖g r‖ ≤ C)
    (s t : NNReal) (hst : s ≤ t) :
    |(∫ r in Icc (0 : ℝ) (t : ℝ), g r ∂volume) -
      (∫ r in Icc (0 : ℝ) (s : ℝ), g r ∂volume)| ≤ C*((t:ℝ)-(s:ℝ)) := by
  have hst' : (s:ℝ) ≤ (t:ℝ) := hst
  have h0s : (0:ℝ) ≤ s := NNReal.coe_nonneg _
  have he : Icc (0:ℝ) (s:ℝ) ∪ Ioc (s:ℝ) (t:ℝ) = Icc 0 (t:ℝ) :=
    Icc_union_Ioc_eq_Icc h0s hst'
  have hsub : Ioc (s:ℝ) (t:ℝ) ⊆ Icc (0:ℝ) (t:ℝ) :=
    fun r hr => ⟨h0s.trans hr.1.le,hr.2⟩
  have hd : Disjoint (Icc (0:ℝ) (s:ℝ)) (Ioc (s:ℝ) (t:ℝ)) :=
    Set.disjoint_left.mpr fun r hr h' => (not_lt_of_ge hr.2) h'.1
  rw [← he,setIntegral_union hd measurableSet_Ioc (hi s) ((hi t).mono_set hsub)]
  rw [add_sub_cancel_left,← Real.norm_eq_abs]
  have hab := ae_restrict_of_ae_restrict_of_subset
    (show Ioc (s:ℝ) (t:ℝ) ⊆ Ici (0:ℝ) from fun _ hr => h0s.trans hr.1.le) hb
  calc
    _ ≤ ∫ r in Ioc (s:ℝ) (t:ℝ), ‖g r‖ ∂volume := norm_integral_le_integral_norm _
    _ ≤ ∫ r in Ioc (s:ℝ) (t:ℝ), C ∂volume :=
      integral_mono_ae ((hi t).mono_set hsub).norm (by
        haveI : IsFiniteMeasure (volume.restrict (Ioc (s:ℝ) (t:ℝ))) := ⟨by simp [Measure.restrict_apply_univ,Real.volume_Ioc]⟩
        exact integrable_const C) hab
    _ = _ := by simp [Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr hst'),mul_comm]
