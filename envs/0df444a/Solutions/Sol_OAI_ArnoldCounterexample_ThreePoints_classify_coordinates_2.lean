-- Prove2me | solution 2 for OAI.ArnoldCounterexample.ThreePoints.classify_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:10:36.19615+00:00
-- url     : https://prove2.me/submissions/dd7e5f83-becf-4fc5-a4c2-3c06b5a6622a

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/ThreePoints.lean:L37-L94
-- (upload_full_project.md Phase 4): solution for node OAI.ArnoldCounterexample.ThreePoints.classify_coordinates. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar
import Definitions.Def_OAI_Geometry_Arnold_Differentiation
import Definitions.Def_OAI_Geometry_Arnold_Orbit
import Definitions.Def_OAI_Geometry_Arnold_Symplectic
import Definitions.Def_OAI_Geometry_Arnold_Coordinates
import Definitions.Def_OAI_Geometry_Arnold_Extension
import Definitions.Def_OAI_Geometry_Arnold_Deformation
import Definitions.Def_OAI_Geometry_Arnold_Exterior
import Definitions.Def_OAI_Geometry_Arnold_Homotopy
import Definitions.Def_OAI_Geometry_Arnold_Volume
import Definitions.Def_OAI_Geometry_Arnold_Obstruction
import Definitions.Def_OAI_Geometry_Arnold_ThreePoints

-- ---- from OAI.Geometry.Arnold.ThreePoints ----
namespace OAI

noncomputable section
open scoped BigOperators ContDiff

open scoped BigOperators ContDiff

namespace ArnoldCounterexample
namespace ThreePoints

/-- Algebraic elimination of every solution, without a nondegeneracy assumption.
We eliminate using μ instead of t=|x-p|; μ²=t², so the remaining factor is μ²=3. -/
lemma classify_coordinates
    {x₀ x₁ x₂ y₀ y₁ y₂ lam μ : ℝ}
    (hx : x₀^2 + x₁^2 + x₂^2 = 1)
    (hy : y₀^2 + y₁^2 + y₂^2 = 1)
    (h₀ : 1 + y₀ = lam * x₀) (h₁ : y₁ = lam * x₁) (h₂ : y₂ = lam * x₂)
    (g₀ : x₀ = μ * y₀) (g₁ : x₁ = μ * y₁) (g₂ : x₂ - 1 = μ * y₂) :
    (x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 1 ∧ y₀ = -1 ∧ y₁ = 0 ∧ y₂ = 0) ∨
    (μ^2 = 3 ∧ x₀ = μ/2 ∧ x₁ = 0 ∧ x₂ = -1/2 ∧
      y₀ = 1/2 ∧ y₁ = 0 ∧ y₂ = -μ/2) := by
  by_cases hμ : μ = 0
  · left
    have hx₀ : x₀ = 0 := by simpa [hμ] using g₀
    have hx₁ : x₁ = 0 := by simpa [hμ] using g₁
    have hx₂ : x₂ = 1 := by simp [hμ] at g₂; linarith
    have hy₀ : y₀ = -1 := by rw [hx₀] at h₀; linarith
    have hy₁ : y₁ = 0 := by nlinarith [sq_nonneg y₂]
    have hy₂ : y₂ = 0 := by nlinarith [sq_nonneg y₁]
    exact ⟨hx₀, hx₁, hx₂, hy₀, hy₁, hy₂⟩
  · right
    have gx₂ : x₂ = 1 + μ * y₂ := by linarith
    have hn : μ * (μ + 2 * y₂) = 0 := by
      have he : μ^2 * (y₀^2 + y₁^2 + y₂^2 - 1) + μ * (μ + 2 * y₂) =
          x₀^2 + x₁^2 + x₂^2 - 1 := by
        rw [g₀, g₁, gx₂]
        ring
      simpa [hx, hy] using he
    have hμy : μ + 2 * y₂ = 0 := (mul_eq_zero.mp hn).resolve_left hμ
    have hy₂ : y₂ = -μ/2 := by linarith
    have hc₀ : (1 - lam * μ) * y₀ = -1 := by rw [g₀] at h₀; nlinarith
    have hc₁ : (1 - lam * μ) * y₁ = 0 := by rw [g₁] at h₁; nlinarith
    have hc : 1 - lam * μ ≠ 0 := by intro h; rw [h] at hc₀; norm_num at hc₀
    have hy₁ : y₁ = 0 := (mul_eq_zero.mp hc₁).resolve_left hc
    have hlam : lam ≠ 0 := by
      intro h
      rw [h] at h₂
      simp only [zero_mul] at h₂
      exact hμ (by linarith)
    have hdot : y₀ + 1 = lam * (μ + y₂) := by
      calc
        y₀ + 1 = (1 + y₀) * y₀ + y₁ * y₁ + y₂ * y₂ := by nlinarith [hy]
        _ = (lam * x₀) * y₀ + (lam * x₁) * y₁ + (lam * x₂) * y₂ := by
          rw [← h₀, ← h₁, ← h₂]
        _ = lam * (μ * (y₀^2 + y₁^2 + y₂^2) + y₂) := by rw [g₀, g₁, gx₂]; ring
        _ = lam * (μ + y₂) := by rw [hy]; ring
    have he : (lam * μ) * (2 * y₀ - 1) = 0 := by
      rw [g₀] at h₀
      rw [hy₂] at hdot
      nlinarith only [h₀, hdot]
    have hy₀ : y₀ = 1/2 := by
      have := (mul_eq_zero.mp he).resolve_left (mul_ne_zero hlam hμ)
      linarith
    have hμsq : μ^2 = 3 := by rw [hy₀, hy₁, hy₂] at hy; nlinarith only [hy]
    refine ⟨hμsq, ?_, ?_, ?_, hy₀, hy₁, hy₂⟩
    · rw [g₀, hy₀]; ring
    · rw [g₁, hy₁]; ring
    · rw [gx₂, hy₂]; nlinarith only [hμsq]

open scoped Matrix

end ThreePoints
end ArnoldCounterexample

end

end OAI

-- ---- platform node ----
open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.ThreePoints
open scoped BigOperators ContDiff
open scoped BigOperators ContDiff


theorem solution : type_of% @_root_.OAI.ArnoldCounterexample.ThreePoints.classify_coordinates := @_root_.OAI.ArnoldCounterexample.ThreePoints.classify_coordinates
