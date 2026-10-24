-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinate_powers_from_monomial_tail_73aae4b1_866b_4d65_aa9b_b11def2b6aef
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:45:52.865181+00:00
-- url     : https://prove2.me/submissions/9ec07178-7e0e-47ad-8e0d-904fc17f044d

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (m : Nat) (p : Fin m → MvPolynomial (Fin d) ℂ)
    (B : ℚ)
    (hmono : ∀ (e : Fin d →₀ Nat) (t : ℚ),
      B < t → MvPolynomial.IsWeightedHomogeneous w
        (MvPolynomial.monomial e (1 : ℂ)) t →
        MvPolynomial.monomial e (1 : ℂ) ∈ Ideal.span (Set.range p)) :
    ∃ N : Nat, 0 < N ∧ ∀ i : Fin d,
      MvPolynomial.monomial (Finsupp.single i N) (1 : ℂ) ∈ Ideal.span (Set.range p) := by
  classical
  by_cases hd : d = 0
  · subst d
    exact ⟨1, by norm_num, fun i => Fin.elim0 i⟩
  · have hpos : 0 < d := Nat.pos_of_ne_zero hd
    have hqpos (i : Fin d) : 0 < w i := by
      have := hw i
      exact_mod_cast this
    have hex (i : Fin d) :
        ∃ n : Nat, 0 < n ∧ B < (n : ℚ) * w i := by
      obtain ⟨n, hn⟩ := exists_nat_gt (max (B / w i) 0)
      refine ⟨n, ?_, ?_⟩
      · exact_mod_cast (lt_of_le_of_lt (le_max_right (B / w i) 0) hn)
      · have hdiv : B / w i < (n : ℚ) :=
          lt_of_le_of_lt (le_max_left (B / w i) 0) hn
        exact (div_lt_iff₀ (hqpos i)).mp hdiv
    let f : Fin d → Nat := fun i => Classical.choose (hex i)
    have hf (i : Fin d) : 0 < f i ∧ B < (f i : ℚ) * w i :=
      Classical.choose_spec (hex i)
    let N : Nat := Finset.univ.sup f
    have hle (i : Fin d) : f i ≤ N := by
      exact Finset.le_sup (Finset.mem_univ i)
    have hN : 0 < N := by
      let i0 : Fin d := ⟨0, hpos⟩
      have hfi : 0 < f i0 := (hf i0).1
      have hbound : f i0 ≤ N := hle i0
      omega
    refine ⟨N, hN, ?_⟩
    intro i
    have hmul : (f i : ℚ) * w i ≤ (N : ℚ) * w i := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle i) (le_of_lt (hqpos i))
    have hdegree : B < (N : ℚ) * w i := lt_of_lt_of_le (hf i).2 hmul
    have hweight : Finsupp.weight w (Finsupp.single i N) = (N : ℚ) * w i := by
      simp [Finsupp.weight_single, nsmul_eq_mul]
    have hhom :
        MvPolynomial.IsWeightedHomogeneous w
          (MvPolynomial.monomial (Finsupp.single i N) (1 : ℂ))
          ((N : ℚ) * w i) := by
      apply MvPolynomial.isWeightedHomogeneous_monomial
      exact hweight
    exact hmono (Finsupp.single i N) ((N : ℚ) * w i) hdegree hhom