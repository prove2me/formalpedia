-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinate_power_has_lower_weight_span
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:01:23.864957+00:00
-- url     : https://prove2.me/submissions/ba6c0c81-7741-40bc-b576-27a52b5a5b74

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_relation_mem_lower_weight_span

open scoped BigOperators

theorem solution {d : Nat} (W : Fin d → Nat) (hW : ∀ i, 0 < W i)
    (delta : Nat) (hdelta : 0 < delta) (m : Nat)
    (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hrelations : ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
      ∃ q : Fin m → MvPolynomial (Fin d) ℂ,
        (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n = ∑ j, q j * p j ∧
        ∀ j, ∀ a : Fin d →₀ Nat, a ∈ (q j).support →
          (∑ k : Fin d, (a k : ℤ) * (W k : ℤ)) =
            (n : ℤ) * (W i : ℤ) - (delta : ℤ)) :
    ∀ i : Fin d, ∃ r : Nat, 0 < r ∧
      (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ r ∈
        Submodule.span (Algebra.adjoin ℂ (Set.range p))
          {f : MvPolynomial (Fin d) ℂ |
            ∃ a : Fin d →₀ Nat,
              (∑ k : Fin d, a k * W k) < r * W i ∧
                f = MvPolynomial.monomial a (1 : ℂ)} := by
  intro i
  obtain ⟨n, hn, q, hrel, hq⟩ := hrelations i
  refine ⟨n, hn, ?_⟩
  rw [hrel]
  exact OAI.PiExponent.FormalInterpolation.weighted_relation_mem_lower_weight_span
    W delta hdelta n i m p q hq