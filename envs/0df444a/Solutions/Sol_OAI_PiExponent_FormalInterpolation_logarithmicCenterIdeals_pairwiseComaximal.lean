-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeals_pairwiseComaximal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:07:09.696617+00:00
-- url     : https://prove2.me/submissions/4f4d1ce3-9ce3-4d78-8474-6b9b29b9b334

import Mathlib
import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
theorem solution
    {m : Nat} (c₁ c₂ : Fin m → Complex) (T : Fin m → Nat)
    (e : Fin (m + 1) → Nat) (he : ∀ i, 0 < e i) (h : c₁ ≠ c₂) :
    IsCoprime (logarithmicCenterIdeal c₁ T e)
      (logarithmicCenterIdeal c₂ T e) := by
  obtain ⟨i, hi⟩ : ∃ i, c₁ i ≠ c₂ i := by
    by_contra hcon; push Not at hcon; exact h (funext hcon)
  have hne : c₂ i - c₁ i ≠ 0 := sub_ne_zero.mpr (Ne.symm hi)
  have hdiff : logarithmicCoordinate c₁ T i.succ - logarithmicCoordinate c₂ T i.succ =
      MvPolynomial.C (c₂ i - c₁ i) := by
    simp only [logarithmicCoordinate, Fin.cases_succ, map_sub]
    ring
  have hcop : IsCoprime (logarithmicCoordinate c₁ T i.succ) (logarithmicCoordinate c₂ T i.succ) := by
    refine ⟨MvPolynomial.C (c₂ i - c₁ i)⁻¹, -MvPolynomial.C (c₂ i - c₁ i)⁻¹, ?_⟩
    have : MvPolynomial.C (c₂ i - c₁ i)⁻¹ * logarithmicCoordinate c₁ T i.succ +
        -MvPolynomial.C (c₂ i - c₁ i)⁻¹ * logarithmicCoordinate c₂ T i.succ =
        MvPolynomial.C (c₂ i - c₁ i)⁻¹ *
          (logarithmicCoordinate c₁ T i.succ - logarithmicCoordinate c₂ T i.succ) := by ring
    rw [this, hdiff, ← map_mul, inv_mul_cancel₀ hne, map_one]
  obtain ⟨u, v, huv⟩ := hcop.pow (m := e i.succ) (n := e i.succ)
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one, ← huv]
  apply Ideal.add_mem
  · apply Ideal.mem_sup_left
    apply Ideal.mul_mem_left
    exact Ideal.subset_span ⟨i.succ, rfl⟩
  · apply Ideal.mem_sup_right
    apply Ideal.mul_mem_left
    exact Ideal.subset_span ⟨i.succ, rfl⟩
