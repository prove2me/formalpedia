-- Prove2me | solution 2 for OAI.SevenEighths.CubicDyadicDecay.decay_summable
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:48:36.074322+00:00
-- url     : https://prove2.me/submissions/782a70e0-0c88-4e59-a90a-e65f61a4ea62

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

theorem OA2Aux.decay_le_high (t α : ℝ) (ht : 0 < t) (j : ℕ) :
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

theorem solution (t α : ℝ) (ht : 0 < t) (hα : α < 3) :
    Summable (fun j : ℕ => ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3) := by
  have hr0 : (0 : ℝ) ≤ (2 : ℝ)^(α - 3) := by positivity
  have hr1 : (2 : ℝ)^(α - 3) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hs : Summable (fun j : ℕ => t^(-3 : ℝ) * ((2 : ℝ)^(α - 3))^j) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => OA2Aux.decay_le_high t α ht j) hs
  positivity
