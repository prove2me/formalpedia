-- Prove2me | solution 1 for OAI.SingleFold.PellAnalytics.quotient_error
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:15:39.990334+00:00
-- url     : https://prove2.me/submissions/cbee91ff-077c-4e43-a960-d5609114963d

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
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell

open OAI OAI.SingleFold


theorem solution {b n c u : ℕ} (hu : (c+1)*(n+1)+4≤u)
    (hc : b^n≤c) {F H : ℝ} (_hH : 0<H)
    (hlo : (b:ℝ)^n≤F/H)
    (hhi : F/H≤(b:ℝ)^n*(1+1/(2*(u:ℝ)-1))^n) :
    0≤F/H-(b:ℝ)^n ∧ F/H-(b:ℝ)^n<1 := by
  have hu4 : (4:ℝ) ≤ u := by exact_mod_cast (show 4 ≤ u by nlinarith)
  have hden : (0:ℝ) < 2*(u:ℝ)-1 := by linarith
  set x : ℝ := 1/(2*(u:ℝ)-1) with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by rw [hx, div_le_one hden]; linarith
  set P : ℝ := (1+x)^n with hP
  have hP1 : 1 ≤ P := one_le_pow₀ (by linarith)
  have hbern : 1 + (n:ℝ)*(-x) ≤ (1 + -x)^n := one_add_mul_le_pow (by linarith) n
  have hprod : P * (1 + -x)^n ≤ 1 := by
    rw [hP, ← mul_pow]
    apply pow_le_one₀ <;> nlinarith
  set y : ℝ := (n:ℝ)*x with hy
  have hPy : P * (1 - y) ≤ 1 := by
    have : P * (1 - y) ≤ P * (1 + -x)^n := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      rw [hy]; linarith
    linarith
  have hcy : ((c:ℝ)+1) * y < 1 := by
    have hu' : ((c:ℝ)+1)*((n:ℝ)+1)+4 ≤ u := by exact_mod_cast hu
    rw [hy, hx, mul_one_div, ← mul_div_assoc, div_lt_one hden]
    have : (0:ℝ) ≤ c := by positivity
    nlinarith
  have hy0 : 0 ≤ y := by positivity
  have hc0 : (0:ℝ) ≤ c := by positivity
  have hbc : ((b:ℝ))^n ≤ c := by exact_mod_cast hc
  have hb0 : (0:ℝ) ≤ (b:ℝ)^n := by positivity
  have h1y : 0 < 1 - y := by nlinarith
  have hkey : (c:ℝ) * (P - 1) < 1 := by
    have e1 : (P - 1) * (1 - y) ≤ y := by nlinarith
    have e2 : (c:ℝ) * ((P - 1) * (1 - y)) ≤ c * y := mul_le_mul_of_nonneg_left e1 hc0
    by_contra hcon
    push_neg at hcon
    have : (1 - y) ≤ (c:ℝ) * (P - 1) * (1 - y) := by nlinarith
    nlinarith
  refine ⟨by linarith, ?_⟩
  have : (b:ℝ)^n * (P - 1) ≤ c * (P - 1) := mul_le_mul_of_nonneg_right hbc (by linarith)
  have : F/H - (b:ℝ)^n ≤ (b:ℝ)^n * (P - 1) := by rw [hP]; nlinarith
  linarith

