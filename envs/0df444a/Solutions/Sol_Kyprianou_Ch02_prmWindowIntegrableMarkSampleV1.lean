-- Prove2me | solution 1 for Kyprianou.Ch02.prmWindowIntegrableMarkSampleV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:49:14.641292+00:00
-- url     : https://prove2.me/submissions/52ed61ff-9a40-40ae-b4d5-4b25b9d886b1

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch02_prmWindowNonnegativeMarkMomentFiniteIffV1
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (f : ℝ → ℝ) (hf : Measurable f) (hi : Integrable f ν) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, IntegrableOn (fun z : ℝ × ℝ => f z.2)
      (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ) (N.N ω) := by
  by_cases ht : t = 0
  · subst t
    simp
  let R : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ
  let M (ω : Ω) := (N.N ω).restrict R
  let G (z : ℝ × ℝ) := ENNReal.ofReal |f z.2|
  have hR : MeasurableSet R := measurableSet_Ioc.prod MeasurableSet.univ
  have hM : Measurable M := Measure.measurable_of_measurable_coe M (fun A hA => by
    simpa only [M, Measure.restrict_apply hA] using N.measurable_eval (hA.inter hR))
  have hG : Measurable G := ENNReal.measurable_ofReal.comp (hf.abs.comp measurable_snd)
  have hfin := (Kyprianou.Ch02.prmWindowNonnegativeMarkMomentFiniteIffV1
    P ν N (fun x => |f x|) hf.abs (fun x => abs_nonneg (f x))
    t (pos_iff_ne_zero.mpr ht)).2 hi.abs
  have ha : ∀ᵐ ω ∂P, (∫⁻ z, G z ∂(M ω)) < ⊤ :=
    ae_lt_top ((Measure.measurable_lintegral hG).comp hM) hfin.ne
  filter_upwards [ha] with ω h
  refine ⟨(hf.comp measurable_snd).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simpa only [Real.enorm_eq_ofReal_abs] using h
