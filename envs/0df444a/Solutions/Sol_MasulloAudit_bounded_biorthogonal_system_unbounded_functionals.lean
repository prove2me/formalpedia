-- Prove2me | solution 1 for MasulloAudit.bounded_biorthogonal_system_unbounded_functionals
-- status  : ACCEPTED   (prove)
-- author  : @lll
-- created : 2026-11-21T00:02:58.456444+00:00
-- url     : https://prove2.me/submissions/3ce65a7c-0962-47c3-9a02-fe11ce2af3b8

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.NormedSpace

open scoped InnerProductSpace

/-- (1) A functional separating `x₁` (value 1) from `x₂` (value 0) has norm at least
`1 / ‖x₁ - x₂‖`. -/
theorem norm_functional_ge_inv_dist {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (f : E →L[𝕜] 𝕜) (x₁ x₂ : E) (h₁ : f x₁ = 1) (h₂ : f x₂ = 0)
    (hne : x₁ ≠ x₂) : 1 / ‖x₁ - x₂‖ ≤ ‖f‖ := by
  have hpos : 0 < ‖x₁ - x₂‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have key : (1 : ℝ) ≤ ‖f‖ * ‖x₁ - x₂‖ := by
    have : f (x₁ - x₂) = 1 := by rw [map_sub, h₁, h₂, sub_zero]
    calc (1 : ℝ) = ‖f (x₁ - x₂)‖ := by rw [this, norm_one]
      _ ≤ ‖f‖ * ‖x₁ - x₂‖ := f.le_opNorm _
  rw [div_le_iff₀ hpos]
  exact key

abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- `x₁ = (1,0)`. -/
noncomputable def bx₁ : E2 := EuclideanSpace.single 0 1
/-- `x₂ = (1,ε)`. -/
noncomputable def bx₂ (ε : ℝ) : E2 := bx₁ + ε • EuclideanSpace.single 1 1

lemma norm_bx₁ : ‖bx₁‖ = 1 := by simp [bx₁]

lemma norm_sub_bx (ε : ℝ) : ‖bx₂ ε - bx₁‖ = |ε| := by
  simp [bx₂, norm_smul]

lemma norm_bx₂_sq (ε : ℝ) : ‖bx₂ ε‖ ^ 2 = 1 + ε ^ 2 := by
  rw [bx₂, sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℝ)]
  · simp [bx₁, norm_smul]; rw [← sq]
  · simp [bx₁, inner_smul_right, EuclideanSpace.inner_single_left]

/-- (2a) In `ℝ²` with `x₁ = (1,0)`, `x₂ = (1,ε)`, any functional with `f x₁ = 0`,
`f x₂ = 1` has norm at least `1/ε`. -/
theorem biorth_norm_ge (ε : ℝ) (hε : 0 < ε) (f : E2 →L[ℝ] ℝ)
    (h₁ : f bx₁ = 0) (h₂ : f (bx₂ ε) = 1) : 1 / ε ≤ ‖f‖ := by
  have hne : bx₂ ε ≠ bx₁ := by
    intro h
    have := norm_sub_bx ε
    rw [h, sub_self, norm_zero] at this
    linarith [abs_pos.mpr hε.ne']
  have := norm_functional_ge_inv_dist f (bx₂ ε) bx₁ h₂ h₁ hne
  rwa [norm_sub_bx, abs_of_pos hε] at this

/-- (2b) Family version: for every `M` there is a pair of vectors with norms in `[1,2]`,
admitting a biorthogonal system of functionals, such that every functional `f` with
`f x₁ = 0`, `f x₂ = 1` (in particular the biorthogonal functional of `x₂`) has `‖f‖ > M`. -/
theorem solution (M : ℝ) :
    ∃ x₁ x₂ : EuclideanSpace ℝ (Fin 2), 1 ≤ ‖x₁‖ ∧ ‖x₁‖ ≤ 2 ∧ 1 ≤ ‖x₂‖ ∧ ‖x₂‖ ≤ 2 ∧
      (∃ g₁ g₂ : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ,
        g₁ x₁ = 1 ∧ g₁ x₂ = 0 ∧ g₂ x₁ = 0 ∧ g₂ x₂ = 1) ∧
      ∀ f : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ, f x₁ = 0 → f x₂ = 1 → M < ‖f‖ := by
  set ε : ℝ := 1 / (|M| + 1) with hεdef
  have hM : 0 < |M| + 1 := by positivity
  have hε : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by
    rw [hεdef, div_le_one hM]; linarith [abs_nonneg M]
  have hsq : ‖bx₂ ε‖ ^ 2 = 1 + ε ^ 2 := norm_bx₂_sq ε
  have hn0 : 0 ≤ ‖bx₂ ε‖ := norm_nonneg _
  refine ⟨bx₁, bx₂ ε, by rw [norm_bx₁], by rw [norm_bx₁]; norm_num, ?_, ?_, ?_, ?_⟩
  · nlinarith [sq_nonneg ε]
  · nlinarith [sq_nonneg ε]
  · refine ⟨EuclideanSpace.proj 0 - (1 / ε) • EuclideanSpace.proj 1,
      (1 / ε) • EuclideanSpace.proj 1, ?_, ?_, ?_, ?_⟩
    · simp [bx₁]
    · simp [bx₂, bx₁]; field_simp; ring
    · simp [bx₁]
    · simp [bx₂, bx₁]; field_simp
  · intro f h₁ h₂
    have := biorth_norm_ge ε hε f h₁ h₂
    have : 1 / ε = |M| + 1 := by rw [hεdef, one_div_one_div]
    linarith [le_abs_self M, biorth_norm_ge ε hε f h₁ h₂]
