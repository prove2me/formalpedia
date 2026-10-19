-- Prove2me | solution 1 for OAI.ArnoldCounterexample.ThreePoints.multiplierCritical_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:00:37.334958+00:00
-- url     : https://prove2.me/submissions/46bcc665-0bba-42b1-a580-d9aa1f803261

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

open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.ThreePoints
open scoped BigOperators ContDiff
open scoped BigOperators ContDiff
theorem classify_aux
    {x₀ x₁ x₂ y₀ y₁ y₂ lam μ : ℝ}
    (hx : x₀^2 + x₁^2 + x₂^2 = 1)
    (hy : y₀^2 + y₁^2 + y₂^2 = 1)
    (h₀ : 1 + y₀ = lam * x₀) (h₁ : y₁ = lam * x₁) (h₂ : y₂ = lam * x₂)
    (g₀ : x₀ = μ * y₀) (g₁ : x₁ = μ * y₁) (g₂ : x₂ - 1 = μ * y₂) :
    (x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 1 ∧ y₀ = -1 ∧ y₁ = 0 ∧ y₂ = 0) ∨
    (μ^2 = 3 ∧ x₀ = μ/2 ∧ x₁ = 0 ∧ x₂ = -1/2 ∧
      y₀ = 1/2 ∧ y₁ = 0 ∧ y₂ = -μ/2) := by
  have hy0 : y₀ = lam * x₀ - 1 := by linarith
  set k := 1 - μ * lam with hk
  have e0 : x₀ * k = -μ := by rw [hk]; rw [hy0] at g₀; linear_combination g₀
  have e1 : x₁ * k = 0 := by rw [hk, h₁] at *; linear_combination g₁
  have e2 : x₂ * k = 1 := by rw [hk]; rw [h₂] at g₂; linear_combination g₂
  have hk0 : k ≠ 0 := by intro h; rw [h] at e2; simp at e2
  have hx1 : x₁ = 0 := by
    rcases mul_eq_zero.1 e1 with h | h
    · exact h
    · exact absurd h hk0
  have hy1 : y₁ = 0 := by rw [h₁, hx1, mul_zero]
  subst hx1
  -- k² = μ² + 1
  have hkk : k ^ 2 = μ ^ 2 + 1 := by
    have : (x₀ * k) ^ 2 + (x₂ * k) ^ 2 = k ^ 2 * (x₀ ^ 2 + 0 ^ 2 + x₂ ^ 2) := by ring
    rw [e0, e2, hx] at this; linarith
  -- λ (λ - 2 x₀) = 0
  have hl : lam * (lam - 2 * x₀) = 0 := by
    rw [hy0, h₂, hy1] at hy
    have : lam ^ 2 * (x₀ ^ 2 + 0 ^ 2 + x₂ ^ 2) - 2 * lam * x₀ = 0 := by linear_combination hy
    rw [hx] at this; linear_combination this
  rcases mul_eq_zero.1 hl with hl0 | hl0
  · -- λ = 0
    left
    have hk1 : k = 1 := by rw [hk, hl0]; ring
    rw [hk1] at e0 e2 hkk
    have hμ : μ = 0 := by nlinarith
    refine ⟨by linarith [e0, hμ], rfl, by linarith, by rw [hy0, hl0]; ring, hy1, by rw [h₂, hl0]; ring⟩
  · have hlam : lam = 2 * x₀ := by linarith
    -- k = 1 - μ²
    have hk2 : k * k = k + 2 * μ ^ 2 := by
      have : k * k = k * (1 - μ * lam) := by rw [hk]
      rw [this, hlam]; linear_combination (-2 * μ) * e0
    have hk3 : k = 1 - μ ^ 2 := by nlinarith
    have hμ : μ ^ 2 * (μ ^ 2 - 3) = 0 := by rw [hk3] at hkk; linear_combination hkk
    rcases mul_eq_zero.1 hμ with hm | hm
    · left
      have hμ0 : μ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hm
      have hk1 : k = 1 := by rw [hk3, hm]; ring
      rw [hk1] at e0 e2
      have hx0 : x₀ = 0 := by linarith
      refine ⟨hx0, rfl, by linarith, by rw [hy0, hx0]; ring, hy1, ?_⟩
      rw [h₂, hlam, hx0]; ring
    · right
      have hm3 : μ ^ 2 = 3 := by linarith
      have hkm : k = -2 := by rw [hk3, hm3]; norm_num
      rw [hkm] at e0 e2
      have hx0 : x₀ = μ / 2 := by linarith
      have hx2 : x₂ = -1 / 2 := by linarith
      refine ⟨hm3, hx0, rfl, hx2, ?_, hy1, ?_⟩
      · rw [hy0, hlam, hx0]; linear_combination hm3 / 2
      · rw [h₂, hlam, hx0, hx2]; ring

theorem solution (q : Pair) :
    MultiplierCritical q ↔ q = qzero ∨ q = qplus ∨ q = qminus := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  obtain ⟨x, y⟩ := q
  have pair_ext : ∀ a b c d e f : ℝ, ((x, y) : Pair) = (![a, b, c], ![d, e, f]) ↔
      (x 0 = a ∧ x 1 = b ∧ x 2 = c ∧ y 0 = d ∧ y 1 = e ∧ y 2 = f) := by
    intro a b c d e f
    constructor
    · intro h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
    · rintro ⟨h0, h1, h2, h4, h5, h6⟩
      refine Prod.ext ?_ ?_ <;> funext i <;> fin_cases i <;> simp [h0, h1, h2, h4, h5, h6]
  have hz : qzero = (![0, 0, 1], ![-1, 0, 0]) := by
    simp only [qzero, pole, east]; congr 1; funext i; fin_cases i <;> simp
  constructor
  · rintro ⟨⟨hx, hy⟩, lam, μ, h₀, h₁, h₂, g₀, g₁, g₂⟩
    simp only [sqNorm] at hx hy
    rcases classify_aux hx hy h₀ h₁ h₂ g₀ g₁ g₂ with
      ⟨a0, a1, a2, b0, b1, b2⟩ | ⟨hm, a0, a1, a2, b0, b1, b2⟩
    · left; rw [hz, pair_ext]; exact ⟨a0, a1, a2, b0, b1, b2⟩
    · right
      have hμ : μ = Real.sqrt 3 ∨ μ = -Real.sqrt 3 := by
        have : (μ - Real.sqrt 3) * (μ + Real.sqrt 3) = 0 := by nlinarith
        rcases mul_eq_zero.1 this with h | h
        · left; linarith
        · right; linarith
      rcases hμ with rfl | rfl
      · left; simp only [qplus]; rw [pair_ext]
        refine ⟨a0, a1, a2, b0, b1, ?_⟩; rw [b2]
      · right; simp only [qminus]; rw [pair_ext]
        refine ⟨a0.trans (by ring), a1, a2, b0, b1, b2.trans (by ring)⟩
  · rintro (h | h | h)
    · rw [hz, pair_ext] at h
      obtain ⟨a0, a1, a2, b0, b1, b2⟩ := h
      refine ⟨⟨?_, ?_⟩, 0, 0, ?_⟩
      · simp only [sqNorm, a0, a1, a2]; norm_num
      · simp only [sqNorm, b0, b1, b2]; norm_num
      · simp only [a0, a1, a2, b0, b1, b2]; norm_num
    · simp only [qplus] at h; rw [pair_ext] at h
      obtain ⟨a0, a1, a2, b0, b1, b2⟩ := h
      refine ⟨⟨?_, ?_⟩, Real.sqrt 3, Real.sqrt 3, ?_⟩
      · simp only [sqNorm, a0, a1, a2]; nlinarith
      · simp only [sqNorm, b0, b1, b2]; nlinarith
      · simp only [a0, a1, a2, b0, b1, b2]
        refine ⟨by nlinarith, by ring, by ring, by ring, by ring, by nlinarith⟩
    · simp only [qminus] at h; rw [pair_ext] at h
      obtain ⟨a0, a1, a2, b0, b1, b2⟩ := h
      refine ⟨⟨?_, ?_⟩, -Real.sqrt 3, -Real.sqrt 3, ?_⟩
      · simp only [sqNorm, a0, a1, a2]; nlinarith
      · simp only [sqNorm, b0, b1, b2]; nlinarith
      · simp only [a0, a1, a2, b0, b1, b2]
        refine ⟨by nlinarith, by ring, by ring, by ring, by ring, by nlinarith⟩
