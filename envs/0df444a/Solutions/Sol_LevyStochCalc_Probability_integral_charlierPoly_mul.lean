-- Prove2me | solution 1 for LevyStochCalc.Probability.integral_charlierPoly_mul
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T06:13:59.394357+00:00
-- url     : https://prove2.me/submissions/1cb6df69-2eef-45e8-88c3-0b64042aec72

import Definitions.Def_LevyStochCalc_Probability_Charlier_F000
import Definitions.Def_LevyStochCalc_Probability_Charlier_F001
import Mathlib.Algebra.Group.ForwardDiff

namespace LevyStochCalc.Probability

open MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal ENNReal Nat

theorem AuxCh.monic_deg (lam : ℝ) (s : ℕ) :
    (charlierPoly lam s).Monic ∧ (charlierPoly lam s).natDegree = s := by
  induction s with
  | zero => simp
  | succ s ih =>
    obtain ⟨hm, hd⟩ := ih
    have hq : (X - C (1:ℝ)).Monic := monic_X_sub_C 1
    have hqd : (X - C (1:ℝ)).natDegree = 1 := natDegree_X_sub_C 1
    have hc : ((charlierPoly lam s).comp (X - C 1)).Monic := hm.comp hq (by rw [hqd]; norm_num)
    have hcd : ((charlierPoly lam s).comp (X - C 1)).natDegree = s := by
      rw [natDegree_comp, hqd, hd, mul_one]
    have hA : (X * (charlierPoly lam s).comp (X - C 1)).Monic := monic_X.mul hc
    have hAd : (X * (charlierPoly lam s).comp (X - C 1)).natDegree = s + 1 := by
      rw [natDegree_X_mul hc.ne_zero, hcd]
    have hB : (C lam * charlierPoly lam s).natDegree < s + 1 :=
      lt_of_le_of_lt (natDegree_C_mul_le _ _) (by rw [hd]; omega)
    rw [charlierPoly_succ]
    refine ⟨hA.sub_of_left (degree_lt_degree (by rw [hAd]; exact hB)), ?_⟩
    rw [natDegree_sub_eq_left_of_natDegree_lt (by rw [hAd]; exact hB), hAd]

theorem AuxCh.key (r : ℝ≥0) (s : ℕ) : ∀ q : ℝ[X],
    ∫ n : ℕ, (charlierPoly (r : ℝ) s).eval (n : ℝ) * q.eval (n : ℝ) ∂poissonMeasure r
      = (r : ℝ) ^ s * ∫ n : ℕ, ((fwdDiff (1:ℝ))^[s] q.eval) (n : ℝ) ∂poissonMeasure r := by
  induction s with
  | zero => intro q; simp
  | succ s ih =>
    intro q
    have e1 : ∀ n : ℕ, (charlierPoly (r : ℝ) (s + 1)).eval (n : ℝ) * q.eval (n : ℝ)
        = ((n : ℝ) * (charlierPoly (r : ℝ) s).eval ((n : ℝ) - 1)
            - (r : ℝ) * (charlierPoly (r : ℝ) s).eval (n : ℝ)) * q.eval (n : ℝ) := by
      intro n; simp [charlierPoly_succ]
    simp_rw [e1]
    rw [integral_charlier_step]
    have e2 : ∀ n : ℕ, (charlierPoly (r : ℝ) s).eval (n : ℝ) * (q.eval ((n : ℝ) + 1) - q.eval (n : ℝ))
        = (charlierPoly (r : ℝ) s).eval (n : ℝ) * (q.comp (X + C 1) - q).eval (n : ℝ) := by
      intro n; simp
    simp_rw [e2]
    rw [ih]
    have e3 : fwdDiff (1:ℝ) q.eval = (q.comp (X + C 1) - q).eval := by
      funext x; simp [fwdDiff]
    rw [Function.iterate_succ_apply, e3, pow_succ]
    ring

theorem AuxCh.le_case (r : ℝ≥0) (s t : ℕ) (h : s ≤ t) :
    ∫ n : ℕ, (charlierPoly (r : ℝ) t).eval (n : ℝ) * (charlierPoly (r : ℝ) s).eval (n : ℝ)
        ∂poissonMeasure r
      = if s = t then (s.factorial : ℝ) * (r : ℝ) ^ s else 0 := by
  rw [AuxCh.key]
  obtain ⟨hm, hd⟩ := AuxCh.monic_deg (r : ℝ) s
  split_ifs with hst
  · subst hst
    have := (charlierPoly (r : ℝ) s).fwdDiff_iter_degree_eq_factorial
    rw [hd, hm.leadingCoeff, one_smul] at this
    rw [this]
    simp [mul_comm]
  · rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (by rw [hd]; omega)]
    simp

theorem _root_.solution (r : ℝ≥0) (s t : ℕ) :
    ∫ n : ℕ, (charlierPoly (r : ℝ) s).eval (n : ℝ) * (charlierPoly (r : ℝ) t).eval (n : ℝ)
        ∂poissonMeasure r
      = if s = t then (s.factorial : ℝ) * (r : ℝ) ^ s else 0 := by
  rcases le_total s t with h | h
  · simp_rw [mul_comm ((charlierPoly (r : ℝ) s).eval _)]
    exact AuxCh.le_case r s t h
  · rw [AuxCh.le_case r t s h]
    by_cases hst : s = t
    · subst hst; simp
    · simp [hst, Ne.symm hst]

end LevyStochCalc.Probability
