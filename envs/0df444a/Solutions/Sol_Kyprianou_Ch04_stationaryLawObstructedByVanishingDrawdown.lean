-- Prove2me | solution 1 for Kyprianou.Ch04.stationaryLawObstructedByVanishingDrawdown
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:17:15.419781+00:00
-- url     : https://prove2.me/submissions/7a36fcfa-132f-4d43-bd3c-12b0084a3f44

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
set_option autoImplicit false

/-- A bounded positive test whose mean vanishes rules out a stationary probability. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : NNReal → Ω → ℝ) (W : NNReal → ℝ → Ω → ℝ)
    (hD : ∀ t, Measurable (D t)) (hD0 : ∀ t z, 0 ≤ D t z)
    (hW : ∀ t w z, 0 ≤ w → D t z ≤ W t w z)
    (hlim : Tendsto (fun t => ∫ z, Real.exp (-D t z) ∂P) atTop (nhds 0)) :
    ¬ ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ (Ici 0) = 1 ∧
      ∀ (t : NNReal) (f : BoundedContinuousFunction ℝ ℝ),
        (∫ w in Ici 0, (∫ z, f (W t w z) ∂P) ∂μ) = ∫ w, f w ∂μ := by
  rintro ⟨μ,hμ,hμ0,hstat⟩
  letI : IsProbabilityMeasure μ := hμ
  let f : BoundedContinuousFunction ℝ ℝ :=
    ⟨⟨fun x => Real.exp (-max 0 x), by fun_prop⟩, ⟨1, by
      intro x y
      rw [Real.dist_eq]
      have hx := (Real.exp_pos (-max 0 x)).le
      have hy := (Real.exp_pos (-max 0 y)).le
      have hx' := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (le_max_left 0 x))
      have hy' := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (le_max_left 0 y))
      exact abs_le.mpr ⟨by linarith,by linarith⟩⟩⟩
  have hf0 (x : ℝ) : 0 < f x := Real.exp_pos _
  have hf1 (x : ℝ) : f x ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (le_max_left 0 x))
  have hfi : Integrable (fun x => f x) μ :=
    (integrable_const (1 : ℝ)).mono f.continuous.measurable.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs,abs_of_nonneg (hf0 x).le] using hf1 x)
  have hp : 0 < ∫ w, f w ∂μ := by
    apply (integral_pos_iff_support_of_nonneg (fun x => (hf0 x).le) hfi).mpr
    have hs : Function.support (fun x => f x) = univ := by
      ext x; simp [Function.mem_support, (hf0 x).ne']
    rw [hs,measure_univ]; exact zero_lt_one
  have hbound (t : NNReal) : (∫ w, f w ∂μ) ≤ ∫ z, Real.exp (-D t z) ∂P := by
    let a := ∫ z, Real.exp (-D t z) ∂P
    have ha : Integrable (fun z => Real.exp (-D t z)) P :=
      (integrable_const (1 : ℝ)).mono ((hD t).neg.exp.aestronglyMeasurable)
        (Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs,abs_of_nonneg (Real.exp_pos _).le,Real.norm_eq_abs,abs_one]
          exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hD0 t z)))
    have hle (w : ℝ) (hw : w ∈ Ici (0 : ℝ)) : (∫ z, f (W t w z) ∂P) ≤ a := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun z => (hf0 _).le) ha
      exact Eventually.of_forall fun z => Real.exp_le_exp.mpr (neg_le_neg
        ((hW t w z hw).trans (le_max_right _ _)))
    rw [← hstat t f]
    have hh := setIntegral_mono_of_nonneg (μ := μ)
      (fun (w : ℝ) (_ : w ∈ Ici (0 : ℝ)) => integral_nonneg fun z => (hf0 (W t w z)).le)
      hle (integrable_const a).integrableOn
    simpa [hμ0, Measure.real, a] using hh
  have hn := hlim.eventually_lt_const hp
  obtain ⟨t,ht⟩ := hn.exists
  exact (not_lt_of_ge (hbound t)) ht
