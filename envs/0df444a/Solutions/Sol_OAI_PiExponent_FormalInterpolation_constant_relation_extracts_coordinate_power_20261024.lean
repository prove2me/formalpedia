-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.constant_relation_extracts_coordinate_power_20261024
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T15:37:40.682177+00:00
-- url     : https://prove2.me/submissions/f582f04a-0a94-45a1-a9a1-4e9a62ef6501

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
open scoped BigOperators

theorem solution
    {d : Nat} (i : Fin d) (I : Ideal (MvPolynomial (Fin d) Complex))
    (N : Nat) (c : Fin (N + 1) → Complex)
    (hc0 : c 0 ≠ 0)
    (hvanish : ∀ k : Fin (N + 1), k.val ≠ 0 → c k = 0)
    (hmem : (∑ k : Fin (N + 1),
      MvPolynomial.C (c k) * MvPolynomial.X i ^ (k : Nat)) ∈ I) :
    ∃ n : Nat, 0 < n ∧ MvPolynomial.X i ^ n ∈ I := by
  have hsum :
      (∑ k : Fin (N + 1),
        MvPolynomial.C (c k) * MvPolynomial.X i ^ (k : Nat)) =
        MvPolynomial.C (c 0) := by
    classical
    rw [Finset.sum_eq_single (0 : Fin (N + 1))]
    · simp
    · intro k hk hne
      have hkval : k.val ≠ 0 := by
        intro hval
        apply hne
        exact Fin.ext hval
      simp [hvanish k hkval]
    · simp
  have hconst : MvPolynomial.C (c 0) ∈ I := by
    rw [← hsum]
    exact hmem
  have hunit : IsUnit (MvPolynomial.C (c 0) : MvPolynomial (Fin d) Complex) :=
    IsUnit.map
      (MvPolynomial.C : Complex →+* MvPolynomial (Fin d) Complex)
      (isUnit_iff_ne_zero.mpr hc0)
  have htop : I = (⊤ : Ideal (MvPolynomial (Fin d) Complex)) :=
    I.eq_top_of_isUnit_mem hconst hunit
  refine ⟨1, by norm_num, ?_⟩
  rw [htop]
  simp