-- Prove2me | solution 1 for Kyprianou.compensatedBandIsL2MartingaleCorrected
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:41:06.759212+00:00
-- url     : https://prove2.me/submissions/1514c037-25c1-450e-a39b-ab91ff09b777

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_compensatedGeneralRegionMartingaleCh02V3

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Reduce the finite compensated small-jump band to the general region theorem. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)),
      Kyprianou.Ch02.IsCompletedPoissonFiltration P levyMeasure N ℱ ∧
      MeasureTheory.Martingale
        (Kyprianou.compensatedSmallJumpBand P levyMeasure N ε) ℱ P ∧
      ∀ t : ℝ≥0,
        MemLp (Kyprianou.compensatedSmallJumpBand P levyMeasure N ε t) 2 P := by
  let B : Set ℝ := {x | ε ≤ |x| ∧ |x| < 1}
  have hB : MeasurableSet B := by
    exact (measurableSet_le measurable_const continuous_abs.measurable).inter
      (measurableSet_lt continuous_abs.measurable measurable_const)
  have hfinite : levyMeasure B < ⊤ := by
    let c : ENNReal := ENNReal.ofReal (min 1 (ε ^ 2))
    let f : ℝ → ENNReal := fun x => ENNReal.ofReal (min 1 (x ^ 2))
    have hc_pos : 0 < c :=
      ENNReal.ofReal_pos.mpr (lt_min one_pos (sq_pos_of_pos hε))
    have hf_meas : Measurable f := by
      apply ENNReal.measurable_ofReal.comp
      exact measurable_const.min (measurable_id'.pow_const 2)
    have hsub : B ⊆ {x : ℝ | c ≤ f x} := by
      intro x hx
      simp only [B, Set.mem_setOf_eq] at hx
      simp only [Set.mem_setOf_eq]
      apply ENNReal.ofReal_le_ofReal
      exact min_le_min le_rfl
        ((sq_abs x).symm ▸ pow_le_pow_left₀ hε.le hx.1 2)
    have hMarkov := mul_meas_ge_le_lintegral hf_meas c (μ := levyMeasure)
    have hle : c * levyMeasure B ≤ ∫⁻ x, f x ∂levyMeasure :=
      le_trans (mul_le_mul_right (measure_mono hsub) c) hMarkov
    exact ENNReal.lt_top_of_mul_ne_top_right
      (ne_top_of_le_ne_top hlevyMeasure.2.ne hle) hc_pos.ne'
  haveI : IsFiniteMeasure (levyMeasure.restrict B) :=
    isFiniteMeasure_restrict.mpr hfinite.ne
  have hbound : ∀ᵐ x ∂(levyMeasure.restrict B), ‖x‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem hB] with x hx
    simpa only [Real.norm_eq_abs] using (hx.2.le : |x| ≤ 1)
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x) (levyMeasure.restrict B) :=
    measurable_id.aestronglyMeasurable
  have hfirst : Integrable (fun x : ℝ => x) (levyMeasure.restrict B) :=
    MeasureTheory.Integrable.of_bound hmeas 1 hbound
  have hsecond : MemLp (fun x : ℝ => x) 2 (levyMeasure.restrict B) :=
    MeasureTheory.MemLp.of_bound hmeas 1 hbound
  obtain ⟨ℱ, hfil, hmart, hmem⟩ :=
    Kyprianou.compensatedGeneralRegionMartingaleCh02V3
      P levyMeasure N B hB hfinite hfirst
  refine ⟨ℱ, hfil, ?_, ?_⟩
  · change MeasureTheory.Martingale
      (fun (t : ℝ≥0) ω =>
        (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
          z.2 ∂(N.N ω)) -
        (t : ℝ) * (∫ x in B, x ∂levyMeasure)) ℱ P
    exact hmart
  · intro t
    change MemLp (fun ω =>
      (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
        z.2 ∂(N.N ω)) -
      (t : ℝ) * (∫ x in B, x ∂levyMeasure)) 2 P
    exact hmem hsecond t
