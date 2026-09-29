-- Prove2me | solution 1 for MarkovMixing.group_walk_uniform_stationary
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T03:07:34.518499+00:00
-- url     : https://prove2.me/submissions/4cdf1d3a-519a-4e47-8efc-e59e96efbcc8

import Definitions.Def_mm_basic

open scoped BigOperators
open MarkovMixing

theorem solution {G : Type*} [Group G] [Fintype G]
    [DecidableEq G] (μ : G → ℝ) (hμ : IsDist μ) :
    IsStochastic (groupWalk μ) ∧
    IsStationary (groupWalk μ) (uniformDist G) ∧
    ((∀ g : G, μ g⁻¹ = μ g) → DetailedBalance (groupWalk μ) (uniformDist G)) := by
  have hcard : (0 : ℝ) < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  have hrow : ∀ a : G, ∑ b, groupWalk μ a b = 1 := by
    intro a
    have h := Equiv.sum_comp (Equiv.mulRight a⁻¹) μ
    simp only [Equiv.coe_mulRight] at h
    exact h.trans hμ.2
  have hstoch : IsStochastic (groupWalk μ) := ⟨fun x y => hμ.1 _, hrow⟩
  have hdist : IsDist (uniformDist G) := by
    refine ⟨fun x => inv_nonneg.mpr hcard.le, ?_⟩
    rw [show (∑ _x : G, uniformDist G _x) = (Fintype.card G : ℝ) * (Fintype.card G : ℝ)⁻¹ by
      simp [uniformDist, Finset.sum_const, Finset.card_univ]]
    exact mul_inv_cancel₀ hcard.ne'
  refine ⟨hstoch, ⟨hdist, ?_⟩, ?_⟩
  · funext x
    have h : (Matrix.vecMul (uniformDist G) (groupWalk μ)) x
        = ∑ a, (Fintype.card G : ℝ)⁻¹ * μ (x * a⁻¹) := rfl
    have hcol : ∑ a : G, μ (x * a⁻¹) = 1 := by
      have h2 := Equiv.sum_comp ((Equiv.inv G).trans (Equiv.mulLeft x)) μ
      simp only [Equiv.coe_trans, Function.comp_apply, Equiv.inv_apply,
        Equiv.coe_mulLeft] at h2
      exact h2.trans hμ.2
    rw [h, ← Finset.mul_sum, hcol, mul_one]
    rfl
  · intro hsym x y
    have hkey : μ (x * y⁻¹) = μ (y * x⁻¹) := by
      have h := hsym (y * x⁻¹)
      rw [mul_inv_rev, inv_inv] at h
      exact h
    show uniformDist G x * μ (y * x⁻¹) = uniformDist G y * μ (x * y⁻¹)
    rw [hkey]
    rfl
