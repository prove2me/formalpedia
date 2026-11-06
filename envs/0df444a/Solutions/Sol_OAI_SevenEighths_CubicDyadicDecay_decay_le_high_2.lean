-- Prove2me | solution 2 for OAI.SevenEighths.CubicDyadicDecay.decay_le_high
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:48:48.376386+00:00
-- url     : https://prove2.me/submissions/b57231ec-62f2-41d9-aeec-871643c0b575

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicDyadicDecay
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicDyadicDecay
open scoped BigOperators
noncomputable section

theorem solution (t α : ℝ) (ht : 0 < t) (j : ℕ) :
    ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3 ≤
      t^(-3 : ℝ) * ((2 : ℝ)^(α - 3))^j := by
  have hx : (0 : ℝ) < (2 : ℝ)^j := by positivity
  have h1 : ((2 : ℝ)^(α - 3))^j = ((2 : ℝ)^j)^(α - 3) := by
    rw [← Real.rpow_natCast ((2 : ℝ)^(α - 3)) j, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm]
  have h2 : ((2 : ℝ)^j)^(α - 3) = ((2 : ℝ)^j)^α / ((2 : ℝ)^j)^3 := by
    rw [Real.rpow_sub hx]; norm_num
  have h3 : t^(-3 : ℝ) = (t^3)⁻¹ := by
    rw [Real.rpow_neg ht.le]; norm_num
  rw [h1, h2, h3]
  generalize (2 : ℝ)^j = x at hx ⊢
  have hxa : 0 ≤ x^α := Real.rpow_nonneg hx.le α
  have h4 : (t^3)⁻¹ * (x^α / x^3) = x^α / (t * x)^3 := by
    field_simp
  rw [h4]
  apply div_le_div_of_nonneg_left hxa (by positivity)
  exact pow_le_pow_left₀ (by positivity) (by linarith) 3
