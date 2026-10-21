-- Prove2me | solution 1 for IntMul.Kappa.histMoment_one
-- status  : ACCEPTED   (prove)
-- author  : @Ethan
-- created : 2026-10-21T05:39:19.48954+00:00
-- url     : https://prove2.me/submissions/a4dce1f0-1854-4333-91b5-fedfa4168d19

import Definitions.Def_IntMul_KappaFramework

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa

/-- At exponent $1$, the child-width moment is the rank sum divided by the width. -/
theorem solution (h : List (ℕ × ℕ)) (m : ℕ) (hm : (m : ℝ) ≠ 0) :
    histMoment h m 1 = (histRankSum h : ℝ) / m := by
  unfold histMoment histRankSum
  simp only [Real.rpow_one]
  induction h with
  | nil =>
    simp
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    rw [ih]
    have hp : (p.2 : ℝ) * ((p.1 : ℝ) / m) = ((p.1 * p.2 : ℕ) : ℝ) / m := by
      field_simp
      norm_cast
      ring
    rw [hp]
    field_simp
