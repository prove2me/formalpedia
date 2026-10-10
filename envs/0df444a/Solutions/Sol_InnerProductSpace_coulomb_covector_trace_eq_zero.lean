-- Prove2me | solution 1 for InnerProductSpace.coulomb_covector_trace_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T22:05:54.046479+00:00
-- url     : https://prove2.me/submissions/07a4d917-323f-4635-9d9a-1af1a5263547

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination

open MeasureTheory Set

theorem solution (n : ℕ) (hn : 2 ≤ n) (c : ℝ)
    (z : EuclideanSpace ℝ (Fin n)) (hz : z ≠ 0) :
    (∑ i : Fin n,
      fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) =>
        (c / ‖y‖ ^ n) • innerSL ℝ y) z
          (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ i)) = 0 := by
  classical
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let L : (EuclideanSpace ℝ (Fin n)) →L[ℝ] ((EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) := innerSL ℝ
  have hN : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hp : HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin n)) => ‖y‖ ^ n)
      (((n : ℝ) * ‖z‖ ^ (n - 2)) • innerSL ℝ z) z := by
    have he : (n : ℝ) - 2 = ((n - 2 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hn]; norm_num
    simpa only [he, Real.rpow_natCast] using
      (hasFDerivAt_norm_rpow (E := (EuclideanSpace ℝ (Fin n))) z hnR)
  have hq := ((hasDerivAt_inv (pow_ne_zero n hN)).const_mul c).comp_hasFDerivAt z hp
  have hQ := hq.smul L.hasFDerivAt
  have hfun : (((fun t : ℝ => c * t⁻¹) ∘
      (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ n)) • ⇑L) =
      (fun y : EuclideanSpace ℝ (Fin n) => (c / ‖y‖ ^ n) • L y) := by
    funext y
    rfl
  rw [hfun] at hQ
  have hL (a b : EuclideanSpace ℝ (Fin n)) : L a b = inner ℝ a b := rfl
  have hd (i : Fin n) :
      fderiv ℝ (fun y : (EuclideanSpace ℝ (Fin n)) => (c / ‖y‖ ^ n) • innerSL ℝ y) z (e i) (e i) =
        c / ‖z‖ ^ n - (c * (n : ℝ) * ‖z‖ ^ (n - 2) / (‖z‖ ^ n) ^ 2) *
          (inner ℝ z (e i)) ^ 2 := by
    change fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => (c / ‖y‖ ^ n) • L y) z (e i) (e i) = _
    rw [hQ.fderiv]
    simp [smul_eq_mul, pow_two, innerSL_apply_apply, hL, e.norm_eq_one, div_eq_mul_inv]
    ring
  change (∑ i : Fin n, fderiv ℝ (fun y : (EuclideanSpace ℝ (Fin n)) => (c / ‖y‖ ^ n) • innerSL ℝ y) z
    (e i) (e i)) = 0
  simp_rw [hd]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum, e.sum_sq_inner_left z]
  have he : ‖z‖ ^ (n - 2) * ‖z‖ ^ 2 = ‖z‖ ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hn]
  field_simp [hN]
  simp only [Fintype.card_fin]
  linear_combination -c * (n : ℝ) * he
