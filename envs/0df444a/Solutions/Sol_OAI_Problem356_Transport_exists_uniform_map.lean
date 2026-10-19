-- Prove2me | solution 1 for OAI.Problem356.Transport.exists_uniform_map
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:41:05.687309+00:00
-- url     : https://prove2.me/submissions/1dd1ccdc-1bd7-434d-a430-4adfce602d8b

import Mathlib
import Definitions.Def_CoulombCounterexample

open OAI OAI.Problem356
universe uX uY
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal unitInterval
theorem pb_cdf_sub (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hc : Continuous (cdf μ)) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    μ.real {x : ℝ | cdf μ x ≤ u} = u := by
  set F := cdf μ with hF
  rcases eq_or_lt_of_le hu1 with h1 | h1
  · subst h1
    have : {x : ℝ | F x ≤ 1} = Set.univ := Set.eq_univ_of_forall fun x => cdf_le_one μ x
    rw [this]; simp
  set S := {x : ℝ | F x ≤ u} with hS
  have hSc : IsClosed S := isClosed_le hc continuous_const
  obtain ⟨x0, hx0⟩ : ∃ x0, u < F x0 :=
    ((tendsto_cdf_atTop μ).eventually (lt_mem_nhds h1)).exists
  have hbdd : BddAbove S := by
    refine ⟨x0, fun x hx => ?_⟩
    by_contra hlt
    push Not at hlt
    have := monotone_cdf μ hlt.le
    exact absurd (lt_of_lt_of_le hx0 this) (not_lt.mpr hx)
  rcases S.eq_empty_or_nonempty with he | hne
  · rw [he]
    have hu0' : u ≤ 0 := by
      by_contra hpos
      push Not at hpos
      obtain ⟨x, hx⟩ := ((tendsto_cdf_atBot μ).eventually (gt_mem_nhds hpos)).exists
      have : x ∈ S := le_of_lt hx
      rw [he] at this; exact this
    simp; linarith
  set a := sSup S with ha
  have haS : a ∈ S := hSc.csSup_mem hne hbdd
  have hSI : S = Set.Iic a := by
    ext x
    constructor
    · intro hx; exact le_csSup hbdd hx
    · intro hx; exact le_trans (monotone_cdf μ hx) haS
  have hFa : F a = u := by
    apply le_antisymm haS
    by_contra hlt
    push Not at hlt
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp ((hc.tendsto a).eventually (gt_mem_nhds hlt))
    have hmem : a + ε / 2 ∈ S := by
      show F (a + ε / 2) ≤ u
      apply le_of_lt
      apply hball
      rw [Real.dist_eq]
      rw [abs_of_pos (by linarith)]
      linarith
    have := le_csSup hbdd hmem
    linarith
  rw [hSI, ← cdf_eq_real, ← hF, hFa]

theorem pb_cdf_cont (ν : Measure ℝ) [IsProbabilityMeasure ν] (h : ∀ x, ν {x} = 0) :
    Continuous (cdf ν) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [(monotone_cdf ν).continuousAt_iff_leftLim_eq_rightLim, StieltjesFunction.rightLim_eq]
  have h1 := (cdf ν).measure_singleton x
  rw [measure_cdf, h x] at h1
  have h2 : cdf ν x - Function.leftLim (cdf ν) x ≤ 0 := ENNReal.ofReal_eq_zero.mp h1.symm
  have h3 := (monotone_cdf ν).leftLim_le (le_refl x)
  linarith

theorem solution {X : Type uX} [MeasurableSpace X]
    [StandardBorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] :
    ∃ f : X → I, Measurable f ∧ Measure.map f μ = volume := by
  obtain ⟨e, he⟩ := exists_measurableEmbedding_real (α := X)
  set ν := Measure.map e μ with hν
  have hνp : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map he.measurable.aemeasurable
  have hatom : ∀ x, ν {x} = 0 := by
    intro x
    rw [hν, Measure.map_apply he.measurable (measurableSet_singleton x)]
    rcases (e ⁻¹' {x}).eq_empty_or_nonempty with h | ⟨y, hy⟩
    · rw [h]; simp
    · have : e ⁻¹' {x} = {y} := by
        ext z
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy ⊢
        constructor
        · intro hz; exact he.injective (hz.trans hy.symm)
        · intro hz; rw [hz, hy]
      rw [this]; exact measure_singleton y
  have hc := pb_cdf_cont ν hatom
  let f : X → I := fun x => ⟨cdf ν (e x), cdf_nonneg ν _, cdf_le_one ν _⟩
  have hf : Measurable f := (hc.measurable.comp he.measurable).subtype_mk
  refine ⟨f, hf, ?_⟩
  have hprob : IsProbabilityMeasure (Measure.map f μ) := Measure.isProbabilityMeasure_map hf.aemeasurable
  apply Measure.ext_of_Iic
  intro a
  rw [unitInterval.volume_Iic, Measure.map_apply hf measurableSet_Iic]
  have hset : f ⁻¹' Set.Iic a = e ⁻¹' {y : ℝ | cdf ν y ≤ (a : ℝ)} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]
    rfl
  rw [hset, ← Measure.map_apply he.measurable (measurableSet_le hc.measurable measurable_const), ← hν]
  have := pb_cdf_sub ν hc a.2.1 a.2.2
  rw [← ofReal_measureReal (measure_ne_top ν _), this]

