-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.homogeneous_power_relations
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:01:10.528009+00:00
-- url     : https://prove2.me/submissions/e2c101bf-9f18-4aa7-bc9d-10dda88859ba

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_homogeneous_relation_extract

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ) (D : Nat) (hD : 0 < D) (m : Nat)
    (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) (D : ℚ))
    (hpow : ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
      (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n ∈ Ideal.span (Set.range p)) :
    ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
      ∃ q : Fin m → MvPolynomial (Fin d) ℂ,
        (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n = ∑ j, q j * p j ∧
        ∀ j, MvPolynomial.IsWeightedHomogeneous w (q j)
          ((n : ℚ) * w i - (D : ℚ)) := by
  intro i
  obtain ⟨n, hn, hmem⟩ := hpow i
  refine ⟨n, hn, ?_⟩
  classical
  have hX : MvPolynomial.IsWeightedHomogeneous w
      ((MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n) ((n : ℚ) * w i) := by
    simpa [nsmul_eq_mul] using
      (MvPolynomial.IsWeightedHomogeneous.pow
        (MvPolynomial.isWeightedHomogeneous_X ℂ w i) n)
  obtain ⟨q, hq⟩ := (Ideal.mem_span_range_iff_exists_fun.mp hmem)
  obtain ⟨q', hrel, hqhom⟩ :=
    OAI.PiExponent.FormalInterpolation.weighted_homogeneous_relation_extract
      (w := w) (D := (D : ℚ)) (N := (n : ℚ) * w i) (p := p)
      hp (F := (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n) hX
      (q := q) hq.symm
  exact ⟨q', hrel, hqhom⟩