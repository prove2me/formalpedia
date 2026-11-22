-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.stopped_eq_sub_sum
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T05:02:59.163956+00:00
-- url     : https://prove2.me/submissions/14a1a172-43cc-4753-855b-d23e3b335273

import Definitions.Def_LevyStochCalc_Brownian_ItoOptionalStopping_F000
open LevyStochCalc.Brownian.Ito
open LevyStochCalc

theorem solution {Ω : Type*} [MeasurableSpace Ω] (τ : Ω → WithTop ℝ)
    (H : Ω → ℝ → ℝ) {t : ℝ} (J : Finset ℝ)
    (hJ0 : ∀ c ∈ J, 0 ≤ c) (hJt : ∀ c ∈ J, c < t)
    (hτJ : ∀ ω, (∃ c ∈ J, τ ω = ((c : ℝ) : WithTop ℝ)) ∨ ((t : ℝ) : WithTop ℝ) ≤ τ ω) :
    indTerm (Probability.stopped τ H) 0 t
      = fun ω s => indTerm H 0 t ω s - ∑ c ∈ J, cutTerm τ H c t ω s := by
  classical
  funext ω s
  have hz (c : ℝ) (hc : τ ω ≠ (c : WithTop ℝ)) : cutTerm τ H c t ω s = 0 := by
    simp [cutTerm, hitInd, Set.indicator, hc]
  rcases hτJ ω with ⟨c, hc, he⟩ | hafter
  · have hsum : ∑ x ∈ J, cutTerm τ H x t ω s = cutTerm τ H c t ω s := by
      apply Finset.sum_eq_single_of_mem c hc
      intro b _ hbc
      apply hz
      simpa [he] using Ne.symm hbc
    rw [hsum]
    simp only [cutTerm, hitInd, Set.indicator, Set.mem_ofPred_eq, he, if_true, one_mul,
      indTerm, indIoc, Set.mem_Ioc, Probability.stopped, WithTop.coe_le_coe]
    have h0 := hJ0 c hc
    split_ifs <;> ring_nf <;> grind
  · have hsum : ∑ c ∈ J, cutTerm τ H c t ω s = 0 := by
      apply Finset.sum_eq_zero
      intro c hc
      apply hz
      exact (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (hJt c hc)) hafter).ne'
    rw [hsum, sub_zero]
    by_cases hs : s ∈ Set.Ioc (0:ℝ) t
    · have hst := (WithTop.coe_le_coe.mpr hs.2).trans hafter
      simp [indTerm, indIoc, hs, Probability.stopped, hst]
    · simp [indTerm, indIoc, hs]
