-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeals_pairwise_comaximal_of_separating_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:50:52.993084+00:00
-- url     : https://prove2.me/submissions/0cf63a0f-3940-42fa-9351-061d68d9706d

import Mathlib
import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.RingTheory.Ideal.Quotient.Operations

open OAI.PiExponent OAI.PiExponent.FormalInterpolation


theorem solution
    {m K : Nat} (T : Fin m → Nat) (S : Fin (m + 1) → Nat)
    (c : Fin K → Fin m → Complex) (i : Fin m)
    (hi : Function.Injective (fun j : Fin K => c j i)) :
    ∀ j k : Fin K, j ≠ k →
      logarithmicCenterIdeal (c j) T S ⊔ logarithmicCenterIdeal (c k) T S = ⊤ := by
  intro j k hjk
  have hne : c j i ≠ c k i := fun h => hjk (hi h)
  set x := logarithmicCoordinate (c j) T i.succ with hx
  set y := logarithmicCoordinate (c k) T i.succ with hy
  have hdiff : x - y = MvPolynomial.C (c k i - c j i) := by
    simp only [hx, hy, logarithmicCoordinate, Fin.cases_succ, map_sub]
    ring
  have hcop : IsCoprime x y := by
    have hd : c k i - c j i ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    refine ⟨MvPolynomial.C (c k i - c j i)⁻¹, -MvPolynomial.C (c k i - c j i)⁻¹, ?_⟩
    have : MvPolynomial.C (c k i - c j i)⁻¹ * x + -MvPolynomial.C (c k i - c j i)⁻¹ * y =
        MvPolynomial.C (c k i - c j i)⁻¹ * (x - y) := by ring
    rw [this, hdiff, ← map_mul, inv_mul_cancel₀ hd, map_one]
  have hcop2 : IsCoprime (x ^ S i.succ) (y ^ S i.succ) := hcop.pow
  have htop : Ideal.span {x ^ S i.succ} ⊔ Ideal.span {y ^ S i.succ} = ⊤ := by
    rw [← Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_span_singleton_iff]
    exact hcop2
  rw [eq_top_iff, ← htop]
  apply sup_le_sup
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span ⟨i.succ, rfl⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span ⟨i.succ, rfl⟩

