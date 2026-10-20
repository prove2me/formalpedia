-- Prove2me | solution 1 for OAI.SingleFold.DuplicationBound.height_dup_gt_five
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:16:35.801976+00:00
-- url     : https://prove2.me/submissions/9bddf890-bb52-4bd9-a22b-f05132a0c7de

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication

open OAI OAI.SingleFold OAI.SingleFold.DuplicationBound


theorem solution {x y : ℚ} (he : y^2=x^3-25*x) (hy : y ≠ 0) :
    5 < height (dupX x) := by
  have hy2 : y^2 ≠ 0 := pow_ne_zero 2 hy
  have hden : 4*x*(x^2-25) = 4*y^2 := by rw [he]; ring
  have hX : dupX x = ((x^2+25)/(2*y))^2 := by
    unfold dupX; rw [hden]; field_simp; ring
  have hX5 : dupX x - 5 = ((x^2-10*x-25)/(2*y))^2 := by
    unfold dupX; rw [hden]; field_simp; rw [he]; ring
  have hge : 5 ≤ dupX x := by nlinarith [sq_nonneg ((x^2-10*x-25)/(2*y))]
  by_contra hcon
  push_neg at hcon
  unfold height at hcon
  set X := dupX x with hXdef
  have hn : X.num.natAbs ≤ 5 := le_of_max_le_left hcon
  have hd : X.den ≤ 5 := le_of_max_le_right hcon
  have hdpos : (0:ℚ) < X.den := by exact_mod_cast X.den_pos
  have hnum : (X.num : ℚ) = X * X.den := by
    rw [Rat.mul_den_eq_num]
  have h5 : (5:ℚ) * X.den ≤ X.num := by rw [hnum]; nlinarith
  have hnum' : X.num ≤ 5 := by
    have := Int.le_natAbs (a := X.num); omega
  have h5' : 5 * (X.den : ℤ) ≤ X.num := by exact_mod_cast h5
  have hd1 : X.den = 1 := by have := X.den_pos; omega
  have hn5 : X.num = 5 := by rw [hd1] at h5'; omega
  have hX5' : X = 5 := by
    rw [← Rat.num_div_den X, hn5, hd1]; norm_num
  rw [hX] at hX5'
  have hirr : Irrational (Real.sqrt 5) := Nat.prime_five.irrational_sqrt
  apply hirr
  refine ⟨|(x^2+25)/(2*y)|, ?_⟩
  have : ((|(x^2+25)/(2*y)| : ℚ) : ℝ)^2 = 5 := by
    rw [← Rat.cast_pow, sq_abs, hX5']; norm_num
  rw [← this, Real.sqrt_sq (by positivity)]

