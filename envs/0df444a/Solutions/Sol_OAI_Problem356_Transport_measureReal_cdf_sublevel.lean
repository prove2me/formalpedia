-- Prove2me | solution 1 for OAI.Problem356.Transport.measureReal_cdf_sublevel
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:38:32.058702+00:00
-- url     : https://prove2.me/submissions/2a2bed84-2cc5-4e2c-acb1-02fcd94e4cf1

import Mathlib
import Definitions.Def_CoulombCounterexample

open OAI OAI.Problem356
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology unitInterval


theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
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

