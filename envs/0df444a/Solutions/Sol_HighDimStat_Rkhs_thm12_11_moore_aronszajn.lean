-- Prove2me | solution 1 for HighDimStat.Rkhs.thm12_11_moore_aronszajn
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T01:50:36.00254+00:00
-- url     : https://prove2.me/submissions/689d4511-6981-4385-aa0c-b61387139970
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_HighDimStat_Rkhs_Core
import Theorems.Thm_HighDimStat_Rkhs_moore_aronszajn_existence
import Theorems.Thm_HighDimStat_Rkhs_rkhs_feature_isometry_of_dense

namespace HighDimStat.Rkhs

open scoped RealInnerProductSpace

/-- In any RKHS for a symmetric kernel `K`, the inner product of two feature vectors reproduces `K`:
`⟪feature x, feature y⟫ = K x y`. -/
lemma inner_feature_feature {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : X → X → ℝ) (hKsymm : ∀ x y, K x y = K y x)
    (toFun : H →ₗ[ℝ] (X → ℝ)) (feature : X → H) (h : IsRKHS K toFun feature) (x y : X) :
    ⟪feature x, feature y⟫ = K x y := by
  rw [h.reproducing (feature x) y, h.feature_eq x]
  exact hKsymm y x

/-- In any RKHS for a symmetric kernel `K`, the squared norm of `feature x` equals `K x x`. -/
lemma norm_sq_feature {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : X → X → ℝ) (hKsymm : ∀ x y, K x y = K y x)
    (toFun : H →ₗ[ℝ] (X → ℝ)) (feature : X → H) (h : IsRKHS K toFun feature) (x : X) :
    ‖feature x‖ ^ 2 = K x x := by
  rw [← real_inner_self_eq_norm_sq, inner_feature_feature K hKsymm toFun feature h x x]

/-- Every RKHS has bounded evaluation functionals with constant `‖feature x‖`:
`|toFun f x| ≤ ‖feature x‖ * ‖f‖`. -/
lemma hasBoundedEvalFunctionals_of_isRKHS {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : X → X → ℝ) (toFun : H →ₗ[ℝ] (X → ℝ)) (feature : X → H) (h : IsRKHS K toFun feature) :
    HasBoundedEvalFunctionals toFun := by
  intro x
  refine ⟨‖feature x‖, fun f => ?_⟩
  rw [← h.reproducing f x, mul_comm]
  exact abs_real_inner_le_norm f (feature x)

/-- The orthogonal complement of the span of `Set.range feature` in any RKHS is trivial (`⊥`),
because any `f` orthogonal to all `feature x` satisfies `toFun f x = ⟪f, feature x⟫ = 0` for all `x`,
which by injectivity of `toFun` forces `f = 0`. -/
lemma orthogonal_span_range_feature_eq_bot {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : X → X → ℝ) (toFun : H →ₗ[ℝ] (X → ℝ)) (feature : X → H) (h : IsRKHS K toFun feature) :
    (Submodule.span ℝ (Set.range feature))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  apply h.toFun_injective
  rw [map_zero]
  ext x
  have hmem : feature x ∈ Submodule.span ℝ (Set.range feature) :=
    Submodule.subset_span ⟨x, rfl⟩
  have horth : ⟪f, feature x⟫ = 0 := by
    rw [real_inner_comm]
    exact hf (feature x) hmem
  rw [← h.reproducing f x, horth]
  rfl

/-- Any linear isometry equivalence `e : H₁ ≃ₗᵢ[ℝ] H₂` between two RKHSs that sends `feature₁ x`
to `feature₂ x` for every `x ∈ X` automatically intertwines their function embeddings:
`∀ f : H₁, toFun₂ (e f) = toFun₁ f`. -/
lemma intertwining_of_feature_isometry {X : Type*} (K : X → X → ℝ)
    {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    (toFun₁ : H₁ →ₗ[ℝ] (X → ℝ)) (feature₁ : X → H₁) (h₁ : IsRKHS K toFun₁ feature₁)
    {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    (toFun₂ : H₂ →ₗ[ℝ] (X → ℝ)) (feature₂ : X → H₂) (h₂ : IsRKHS K toFun₂ feature₂)
    (e : H₁ ≃ₗᵢ[ℝ] H₂) (he : ∀ x : X, e (feature₁ x) = feature₂ x) (f : H₁) :
    toFun₂ (e f) = toFun₁ f := by
  ext x
  rw [← h₂.reproducing (e f) x, ← he x, e.inner_map_map, h₁.reproducing f x]

/-- Theorem 12.11 (the Moore-Aronszajn theorem, p. 389). -/
theorem thm12_11_moore_aronszajn {X : Type*} (K : X → X → ℝ) (hK : IsPSDKernel K) :
    (∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
        (toFun : H →ₗ[ℝ] (X → ℝ)) (feature : X → H), IsRKHS K toFun feature) ∧
      (∀ (H₁ : Type) (_ : NormedAddCommGroup H₁) (_ : InnerProductSpace ℝ H₁)
          (_ : CompleteSpace H₁) (toFun₁ : H₁ →ₗ[ℝ] (X → ℝ)) (feature₁ : X → H₁),
          IsRKHS K toFun₁ feature₁ →
        ∀ (H₂ : Type) (_ : NormedAddCommGroup H₂) (_ : InnerProductSpace ℝ H₂)
          (_ : CompleteSpace H₂) (toFun₂ : H₂ →ₗ[ℝ] (X → ℝ)) (feature₂ : X → H₂),
          IsRKHS K toFun₂ feature₂ →
        ∃ e : H₁ ≃ₗᵢ[ℝ] H₂, ∀ f : H₁, toFun₂ (e f) = toFun₁ f) := by
  refine ⟨moore_aronszajn_existence K hK, ?_⟩
  intro H₁ _ _ _ toFun₁ feature₁ h₁ H₂ _ _ _ toFun₂ feature₂ h₂
  have horth₁ := orthogonal_span_range_feature_eq_bot K toFun₁ feature₁ h₁
  have horth₂ := orthogonal_span_range_feature_eq_bot K toFun₂ feature₂ h₂
  have hgram : ∀ x y : X, ⟪feature₁ x, feature₁ y⟫ = ⟪feature₂ x, feature₂ y⟫ := by
    intro x y
    rw [inner_feature_feature K hK.1 toFun₁ feature₁ h₁ x y,
        inner_feature_feature K hK.1 toFun₂ feature₂ h₂ x y]
  obtain ⟨e, he⟩ := rkhs_feature_isometry_of_dense K hK H₁ toFun₁ feature₁ h₁ horth₁ H₂ toFun₂ feature₂ h₂ horth₂ hgram
  exact ⟨e, intertwining_of_feature_isometry K toFun₁ feature₁ h₁ toFun₂ feature₂ h₂ e he⟩

abbrev solution := @thm12_11_moore_aronszajn

end HighDimStat.Rkhs

abbrev solution := @HighDimStat.Rkhs.thm12_11_moore_aronszajn
