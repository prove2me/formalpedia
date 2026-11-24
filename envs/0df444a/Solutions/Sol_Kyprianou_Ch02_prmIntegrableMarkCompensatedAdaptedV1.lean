-- Prove2me | solution 1 for Kyprianou.Ch02.prmIntegrableMarkCompensatedAdaptedV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:37:28.272304+00:00
-- url     : https://prove2.me/submissions/6d9394e7-29e9-46fa-8731-26dca20d8c76

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Theorems.Thm_Kyprianou_Ch02_prmWindowNonnegativeMarkMomentFiniteIffV1
import Theorems.Thm_Kyprianou_Ch02_measurableRealBochnerIntegralOnMeasuresV1
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (f : ℝ → ℝ) (hf : Measurable f) (hi : Integrable f ν)
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hℱ : Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ), f z.2 ∂(N.N ω)) -
      (t : ℝ) * ∫ x, f x ∂ν
    (∀ t, StronglyMeasurable[ℱ t] (M t)) ∧ (∀ t, Integrable (M t) P) := by
  classical
  let R (t : ℝ≥0) : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ
  let μ (t : ℝ≥0) (ω : Ω) : Measure ℝ := ((N.N ω).restrict (R t)).map Prod.snd
  let I (t : ℝ≥0) (ω : Ω) : ℝ := ∫ z in R t, f z.2 ∂(N.N ω)
  have hμ (t : ℝ≥0) : @Measurable Ω (Measure ℝ) (ℱ t) inferInstance (μ t) := by
    refine Measure.measurable_of_measurable_coe (μ t) (fun A hA => ?_)
    have heq : (fun ω => μ t ω A) =
        (fun ω => N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ A)) := by
      funext ω
      simp only [μ, Measure.map_apply measurable_snd hA,
        Measure.restrict_apply (measurable_snd hA)]
      congr 1
      ext z
      simp [R, and_comm]
    rw [heq]
    exact hℱ.1 t t le_rfl A hA
  have hI (t : ℝ≥0) : @Measurable Ω ℝ (ℱ t) inferInstance (I t) := by
    have hEq : I t = fun ω => ∫ x, f x ∂(μ t ω) := by
      funext ω
      exact (integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable).symm
    rw [hEq]
    exact (Kyprianou.Ch02.measurableRealBochnerIntegralOnMeasuresV1 f hf).comp (hμ t)
  constructor
  · intro t
    exact ((hI t).sub measurable_const).stronglyMeasurable
  · intro t
    have hInt : Integrable (I t) P := by
      refine ⟨((hI t).mono (ℱ.le t) le_rfl).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      by_cases ht : t = 0
      · subst t
        simp [I, R]
      · have hfin := (Kyprianou.Ch02.prmWindowNonnegativeMarkMomentFiniteIffV1
          P ν N (fun x => |f x|) hf.abs (fun x => abs_nonneg (f x))
          t (pos_iff_ne_zero.mpr ht)).2 hi.abs
        refine lt_of_le_of_lt (lintegral_mono (fun ω => ?_)) hfin
        simpa only [I, R, Real.enorm_eq_ofReal_abs] using
          (enorm_integral_le_lintegral_enorm
            (μ := (N.N ω).restrict (R t)) (fun z => f z.2))
    exact hInt.sub (integrable_const _)
