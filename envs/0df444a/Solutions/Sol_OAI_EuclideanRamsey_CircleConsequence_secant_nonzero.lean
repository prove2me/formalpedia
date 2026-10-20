-- Prove2me | solution 1 for OAI.EuclideanRamsey.CircleConsequence.secant_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:36:37.756869+00:00
-- url     : https://prove2.me/submissions/53ff24c6-87c4-4d08-9a63-d8c0cc1351d1

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/CircleGeometry.lean:L27-L72
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.CircleConsequence.secant_nonzero. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyCircle

-- ---- from OAI.Combinatorics.EuclideanRamsey.CircleGeometry ----
namespace OAI

noncomputable section
namespace EuclideanRamsey.CircleConsequence

/-- Three points on a real circle cannot occupy three distinct parameters
on a secant. No positive-radius assumption is needed. -/
theorem circle_parameter_eq_zero_or_one
    (x₀ x₁ y₀ y₁ c₀ c₁ R t : ℝ)
    (hx : (x₀-c₀)^2 + (x₁-c₁)^2 = R)
    (hy : (y₀-c₀)^2 + (y₁-c₁)^2 = R)
    (hz : (x₀+t*(y₀-x₀)-c₀)^2 + (x₁+t*(y₁-x₁)-c₁)^2 = R)
    (hxy : x₀ ≠ y₀ ∨ x₁ ≠ y₁) : t = 0 ∨ t = 1 := by
  have hnorm : (y₀-x₀)^2 + (y₁-x₁)^2 ≠ 0 := by
    intro h
    have h₀ : y₀-x₀ = 0 := by nlinarith [sq_nonneg (y₁-x₁)]
    have h₁ : y₁-x₁ = 0 := by nlinarith [sq_nonneg (y₀-x₀)]
    rcases hxy with hxy | hxy <;> apply hxy <;> linarith
  have hprod : t * (t-1) * ((y₀-x₀)^2 + (y₁-x₁)^2) = 0 := by
    linear_combination hz - (1-t)*hx - t*hy
  rcases mul_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hnorm) with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-- The determinant of a secant line is nonzero at a third distinct
point on the same circle. Distinctness excludes radius zero. -/
theorem secant_nonzero
    (x₀ x₁ y₀ y₁ z₀ z₁ c₀ c₁ R : ℝ)
    (hx : (x₀-c₀)^2 + (x₁-c₁)^2 = R)
    (hy : (y₀-c₀)^2 + (y₁-c₁)^2 = R)
    (hz : (z₀-c₀)^2 + (z₁-c₁)^2 = R)
    (hxy : x₀ ≠ y₀ ∨ x₁ ≠ y₁)
    (hxz : x₀ ≠ z₀ ∨ x₁ ≠ z₁)
    (hyz : y₀ ≠ z₀ ∨ y₁ ≠ z₁) :
    (y₀-x₀)*(z₁-x₁) - (y₁-x₁)*(z₀-x₀) ≠ 0 := by
  intro hdet
  by_cases hdx : y₀-x₀ = 0
  · have hdy : y₁-x₁ ≠ 0 := by
      intro hdy
      rcases hxy with hxy | hxy <;> apply hxy <;> linarith
    have hzx : z₀ = x₀ := by
      have : (y₁-x₁)*(z₀-x₀) = 0 := by rw [hdx] at hdet; nlinarith
      have := (mul_eq_zero.mp this).resolve_left hdy
      linarith
    let t := (z₁-x₁)/(y₁-x₁)
    have ht : x₁+t*(y₁-x₁) = z₁ := by dsimp [t]; field_simp; ring
    have htx : x₀+t*(y₀-x₀) = z₀ := by rw [hdx]; simp [hzx]
    have he := circle_parameter_eq_zero_or_one x₀ x₁ y₀ y₁ c₀ c₁ R t hx hy
      (by rw [ht, htx]; exact hz) hxy
    rcases he with he | he
    · rcases hxz with h | h <;> apply h <;> simp_all
    · rcases hyz with h | h
      · apply h
        calc
          y₀ = x₀ := sub_eq_zero.mp hdx
          _ = z₀ := hzx.symm
      · apply h
        simpa [he] using ht
  · let t := (z₀-x₀)/(y₀-x₀)
    have ht : x₀+t*(y₀-x₀) = z₀ := by dsimp [t]; field_simp; ring
    have hty : x₁+t*(y₁-x₁) = z₁ := by
      dsimp [t]
      apply (mul_right_cancel₀ hdx)
      field_simp
      nlinarith [hdet]
    have he := circle_parameter_eq_zero_or_one x₀ x₁ y₀ y₁ c₀ c₁ R t hx hy
      (by rw [ht, hty]; exact hz) hxy
    rcases he with he | he
    · rcases hxz with h | h <;> apply h <;> simp_all
    · rcases hyz with h | h <;> apply h <;> simp_all

end EuclideanRamsey.CircleConsequence

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey OAI.EuclideanRamsey.CircleConsequence


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.CircleConsequence.secant_nonzero := @_root_.OAI.EuclideanRamsey.CircleConsequence.secant_nonzero
