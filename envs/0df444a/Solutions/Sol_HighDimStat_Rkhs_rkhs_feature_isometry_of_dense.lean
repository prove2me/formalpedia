-- Prove2me | solution 1 for HighDimStat.Rkhs.rkhs_feature_isometry_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T02:56:39.80383+00:00
-- url     : https://prove2.me/submissions/cb51cfd1-c686-4cd3-9fa4-720a21e05b40

import Mathlib
import Definitions.Def_HighDimStat_Rkhs_Core

namespace HighDimStat.Rkhs

open scoped RealInnerProductSpace

section Isometry

variable {X : Type*}
variable {H₁ H₂ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
variable (feature₁ : X → H₁) (feature₂ : X → H₂)

/-- The graph submodule in `H₁ × H₂` spanned by the paired features `(feature₁ x, feature₂ x)`. -/
def G : Submodule ℝ (H₁ × H₂) :=
  Submodule.span ℝ (Set.range (fun x : X => (feature₁ x, feature₂ x)))

lemma inner_feature_of_mem_G (h_gram : ∀ x y : X, ⟪feature₁ x, feature₁ y⟫ = ⟪feature₂ x, feature₂ y⟫)
    {p : H₁ × H₂} (hp : p ∈ G feature₁ feature₂) (x : X) :
    ⟪p.1, feature₁ x⟫ = ⟪p.2, feature₂ x⟫ := by
  induction hp using Submodule.span_induction with
  | mem q hq =>
    rcases hq with ⟨y, rfl⟩
    exact h_gram y x
  | zero =>
    simp
  | add u v _ _ hu_ih hv_ih =>
    simp [inner_add_left, hu_ih, hv_ih]
  | smul c u _ hu_ih =>
    simp [inner_smul_left, hu_ih]

lemma inner_eq_of_mem_G (h_gram : ∀ x y : X, ⟪feature₁ x, feature₁ y⟫ = ⟪feature₂ x, feature₂ y⟫)
    {p q : H₁ × H₂} (hp : p ∈ G feature₁ feature₂) (hq : q ∈ G feature₁ feature₂) :
    ⟪p.1, q.1⟫ = ⟪p.2, q.2⟫ := by
  induction hq using Submodule.span_induction with
  | mem r hr =>
    rcases hr with ⟨x, rfl⟩
    exact inner_feature_of_mem_G feature₁ feature₂ h_gram hp x
  | zero =>
    simp
  | add u v _ _ hu_ih hv_ih =>
    simp [inner_add_right, hu_ih, hv_ih]
  | smul c u _ hu_ih =>
    simp [inner_smul_right, hu_ih]

lemma norm_eq_of_mem_G (h_gram : ∀ x y : X, ⟪feature₁ x, feature₁ y⟫ = ⟪feature₂ x, feature₂ y⟫)
    {p : H₁ × H₂} (hp : p ∈ G feature₁ feature₂) :
    ‖p.1‖ = ‖p.2‖ := by
  have h := inner_eq_of_mem_G feature₁ feature₂ h_gram hp hp
  rw [norm_eq_sqrt_real_inner (p.1), norm_eq_sqrt_real_inner (p.2), h]

/-- The feature span in `H₁`. -/
def S₁ : Submodule ℝ H₁ := Submodule.span ℝ (Set.range feature₁)

/-- The feature span in `H₂`. -/
def S₂ : Submodule ℝ H₂ := Submodule.span ℝ (Set.range feature₂)

lemma map_fst_G :
    (G feature₁ feature₂).map (LinearMap.fst ℝ H₁ H₂) = S₁ feature₁ := by
  dsimp [G, S₁]
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

lemma map_snd_G :
    (G feature₁ feature₂).map (LinearMap.snd ℝ H₁ H₂) = S₂ feature₂ := by
  dsimp [G, S₂]
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

lemma fst_mem_S₁ {p : H₁ × H₂} (hp : p ∈ G feature₁ feature₂) : p.1 ∈ S₁ feature₁ := by
  rw [← map_fst_G feature₁ feature₂]
  exact Submodule.mem_map_of_mem hp

lemma snd_mem_S₂ {p : H₁ × H₂} (hp : p ∈ G feature₁ feature₂) : p.2 ∈ S₂ feature₂ := by
  rw [← map_snd_G feature₁ feature₂]
  exact Submodule.mem_map_of_mem hp

/-- Projection from `G` to `S₁`. -/
def proj₁ : G feature₁ feature₂ →ₗ[ℝ] S₁ feature₁ :=
  LinearMap.codRestrict (S₁ feature₁)
    ((LinearMap.fst ℝ H₁ H₂).comp (G feature₁ feature₂).subtype)
    (fun ⟨_, hp⟩ => fst_mem_S₁ feature₁ feature₂ hp)

/-- Projection from `G` to `S₂`. -/
def proj₂ : G feature₁ feature₂ →ₗ[ℝ] S₂ feature₂ :=
  LinearMap.codRestrict (S₂ feature₂)
    ((LinearMap.snd ℝ H₁ H₂).comp (G feature₁ feature₂).subtype)
    (fun ⟨_, hp⟩ => snd_mem_S₂ feature₁ feature₂ hp)

lemma proj₁_injective (h_gram : ∀ x y : X, ⟪feature₁ x, feature₁ y⟫ = ⟪feature₂ x, feature₂ y⟫) :
    Function.Injective (proj₁ feature₁ feature₂) := by
  intro ⟨p, hp⟩ ⟨q, hq⟩ h
  have hfst : p.1 = q.1 := congr_arg Subtype.val h
  have hdiff_mem : p - q ∈ G feature₁ feature₂ := (G feature₁ feature₂).sub_mem hp hq
  have hdiff_fst : (p - q).1 = 0 := sub_eq_zero.mpr hfst
  have hdiff_norm : ‖(p - q).2‖ = ‖(p - q).1‖ := (norm_eq_of_mem_G feature₁ feature₂ h_gram hdiff_mem).symm
  rw [hdiff_fst, norm_zero] at hdiff_norm
  have hdiff_snd : (p - q).2 = 0 := norm_eq_zero.mp hdiff_norm
  have hpq : p = q := Prod.ext hfst (sub_eq_zero.mp hdiff_snd)
  exact Subtype.ext hpq

lemma proj₁_surjective :
    Function.Surjective (proj₁ feature₁ feature₂) := by
  intro ⟨u, hu⟩
  have hu_map : u ∈ (G feature₁ feature₂).map (LinearMap.fst ℝ H₁ H₂) := by
    rw [map_fst_G]
    exact hu
  rcases Submodule.mem_map.mp hu_map with ⟨p, hp, rfl⟩
  exact ⟨⟨p, hp⟩, Subtype.ext rfl⟩

lemma proj₁_bijective (h_gram : ∀ x y : X, ⟪feature₁ x, feature₁ y⟫ = ⟪feature₂ x, feature₂ y⟫) :
    Function.Bijective (proj₁ feature₁ feature₂) :=
  ⟨proj₁_injective feature₁ feature₂ h_gram, proj₁_surjective feature₁ feature₂⟩

lemma proj₂_injective (h_gram : ∀ x y : X, ⟪feature₁ x, feature₁ y⟫ = ⟪feature₂ x, feature₂ y⟫) :
    Function.Injective (proj₂ feature₁ feature₂) := by
  intro ⟨p, hp⟩ ⟨q, hq⟩ h
  have hsnd : p.2 = q.2 := congr_arg Subtype.val h
  have hdiff_mem : p - q ∈ G feature₁ feature₂ := (G feature₁ feature₂).sub_mem hp hq
  have hdiff_snd : (p - q).2 = 0 := sub_eq_zero.mpr hsnd
  have hdiff_norm : ‖(p - q).1‖ = ‖(p - q).2‖ := norm_eq_of_mem_G feature₁ feature₂ h_gram hdiff_mem
  rw [hdiff_snd, norm_zero] at hdiff_norm
  have hdiff_fst : (p - q).1 = 0 := norm_eq_zero.mp hdiff_norm
  have hpq : p = q := Prod.ext (sub_eq_zero.mp hdiff_fst) hsnd
  exact Subtype.ext hpq

lemma proj₂_surjective :
    Function.Surjective (proj₂ feature₁ feature₂) := by
  intro ⟨v, hv⟩
  have hv_map : v ∈ (G feature₁ feature₂).map (LinearMap.snd ℝ H₁ H₂) := by
    rw [map_snd_G]
    exact hv
  rcases Submodule.mem_map.mp hv_map with ⟨p, hp, rfl⟩
  exact ⟨⟨p, hp⟩, Subtype.ext rfl⟩

lemma proj₂_bijective (h_gram : ∀ x y : X, ⟪feature₁ x, feature₁ y⟫ = ⟪feature₂ x, feature₂ y⟫) :
    Function.Bijective (proj₂ feature₁ feature₂) :=
  ⟨proj₂_injective feature₁ feature₂ h_gram, proj₂_surjective feature₁ feature₂⟩

/-- Linear equivalence between the feature spans `S₁` and `S₂`. -/
noncomputable def equivS (h_gram : ∀ x y : X, ⟪feature₁ x, feature₁ y⟫ = ⟪feature₂ x, feature₂ y⟫) :
    S₁ feature₁ ≃ₗ[ℝ] S₂ feature₂ :=
  (LinearEquiv.ofBijective (proj₁ feature₁ feature₂) (proj₁_bijective feature₁ feature₂ h_gram)).symm.trans
    (LinearEquiv.ofBijective (proj₂ feature₁ feature₂) (proj₂_bijective feature₁ feature₂ h_gram))

lemma equivS_apply_feature (h_gram : ∀ x y : X, ⟪feature₁ x, feature₁ y⟫ = ⟪feature₂ x, feature₂ y⟫) (x : X) :
    equivS feature₁ feature₂ h_gram ⟨feature₁ x, Submodule.subset_span ⟨x, rfl⟩⟩ =
      ⟨feature₂ x, Submodule.subset_span ⟨x, rfl⟩⟩ := by
  change (LinearEquiv.ofBijective (proj₂ feature₁ feature₂) (proj₂_bijective feature₁ feature₂ h_gram))
    ((LinearEquiv.ofBijective (proj₁ feature₁ feature₂) (proj₁_bijective feature₁ feature₂ h_gram)).symm
      ⟨feature₁ x, Submodule.subset_span ⟨x, rfl⟩⟩) = ⟨feature₂ x, Submodule.subset_span ⟨x, rfl⟩⟩
  have hgen : (feature₁ x, feature₂ x) ∈ G feature₁ feature₂ :=
    Submodule.subset_span ⟨x, rfl⟩
  have he₁_apply : LinearEquiv.ofBijective (proj₁ feature₁ feature₂) (proj₁_bijective feature₁ feature₂ h_gram)
      ⟨(feature₁ x, feature₂ x), hgen⟩ = ⟨feature₁ x, Submodule.subset_span ⟨x, rfl⟩⟩ := by
    ext
    rfl
  have he₁_symm : (LinearEquiv.ofBijective (proj₁ feature₁ feature₂) (proj₁_bijective feature₁ feature₂ h_gram)).symm
      ⟨feature₁ x, Submodule.subset_span ⟨x, rfl⟩⟩ = ⟨(feature₁ x, feature₂ x), hgen⟩ := by
    rw [← he₁_apply, LinearEquiv.symm_apply_apply]
  rw [he₁_symm]
  ext
  rfl

lemma equivS_norm (h_gram : ∀ x y : X, ⟪feature₁ x, feature₁ y⟫ = ⟪feature₂ x, feature₂ y⟫)
    (u : S₁ feature₁) :
    ‖((equivS feature₁ feature₂ h_gram u : S₂ feature₂) : H₂)‖ = ‖(u : H₁)‖ := by
  set e₁ := LinearEquiv.ofBijective (proj₁ feature₁ feature₂) (proj₁_bijective feature₁ feature₂ h_gram)
  set p := e₁.symm u
  have hp : (p : H₁ × H₂) ∈ G feature₁ feature₂ := p.2
  have hu : (u : H₁) = (p : H₁ × H₂).1 := by
    have h1 := e₁.apply_symm_apply u
    exact (congr_arg (fun (w : S₁ feature₁) => (w : H₁)) h1).symm
  change ‖((proj₂ feature₁ feature₂ p : S₂ feature₂) : H₂)‖ = ‖(u : H₁)‖
  have hv : ((proj₂ feature₁ feature₂ p : S₂ feature₂) : H₂) = (p : H₁ × H₂).2 := rfl
  rw [hu, hv]
  exact (norm_eq_of_mem_G feature₁ feature₂ h_gram hp).symm

lemma denseRange_subtype_of_orthogonal_eq_bot
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Submodule ℝ E) (h : Kᗮ = ⊥) : DenseRange K.subtype := by
  rw [DenseRange, Submodule.coe_subtype, Subtype.range_val]
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  exact Submodule.topologicalClosure_eq_top_iff.mpr h

end Isometry

set_option linter.unusedVariables false

/-- **Feature-preserving linear isometry between two RKHSs of the same PSD kernel (Wainwright Theorem 12.11, p. 389).**
Given two RKHSs `(H₁, toFun₁, feature₁)` and `(H₂, toFun₂, feature₂)` for the same positive
semidefinite kernel `K` whose feature spans have trivial orthogonal complements and whose feature
inner products satisfy `⟪feature₁ x, feature₁ y⟫ = ⟪feature₂ x, feature₂ y⟫`, there exists
a linear isometry equivalence `e : H₁ ≃ₗᵢ[ℝ] H₂` sending `feature₁ x` to `feature₂ x` for all `x`. -/
theorem rkhs_feature_isometry_of_dense {X : Type*} (K : X → X → ℝ) (hK : IsPSDKernel K)
    (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (toFun₁ : H₁ →ₗ[ℝ] (X → ℝ)) (feature₁ : X → H₁) (h₁ : IsRKHS K toFun₁ feature₁)
    (h_orth₁ : (Submodule.span ℝ (Set.range feature₁))ᗮ = ⊥)
    (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
    (toFun₂ : H₂ →ₗ[ℝ] (X → ℝ)) (feature₂ : X → H₂) (h₂ : IsRKHS K toFun₂ feature₂)
    (h_orth₂ : (Submodule.span ℝ (Set.range feature₂))ᗮ = ⊥)
    (h_gram : ∀ x y : X, ⟪feature₁ x, feature₁ y⟫ = ⟪feature₂ x, feature₂ y⟫) :
    ∃ e : H₁ ≃ₗᵢ[ℝ] H₂, ∀ x : X, e (feature₁ x) = feature₂ x := by
  have hd₁ : DenseRange (S₁ feature₁).subtype :=
    denseRange_subtype_of_orthogonal_eq_bot (S₁ feature₁) h_orth₁
  have hd₂ : DenseRange (S₂ feature₂).subtype :=
    denseRange_subtype_of_orthogonal_eq_bot (S₂ feature₂) h_orth₂
  have hnorm : ∀ (u : S₁ feature₁), ‖(S₂ feature₂).subtype (equivS feature₁ feature₂ h_gram u)‖ =
      ‖(S₁ feature₁).subtype u‖ := by
    intro u
    exact equivS_norm feature₁ feature₂ h_gram u
  let e : H₁ ≃ₗᵢ[ℝ] H₂ :=
    (equivS feature₁ feature₂ h_gram).extendOfIsometry
      (S₁ feature₁).subtype (S₂ feature₂).subtype hd₁ hd₂ hnorm
  refine ⟨e, fun x => ?_⟩
  have hx : (S₁ feature₁).subtype ⟨feature₁ x, Submodule.subset_span ⟨x, rfl⟩⟩ = feature₁ x := rfl
  rw [← hx]
  have heq := LinearEquiv.extendOfIsometry_eq
    (equivS feature₁ feature₂ h_gram)
    (S₁ feature₁).subtype (S₂ feature₂).subtype hd₁ hd₂ hnorm
    ⟨feature₁ x, Submodule.subset_span ⟨x, rfl⟩⟩
  rw [heq]
  rw [equivS_apply_feature feature₁ feature₂ h_gram x]
  rfl

abbrev solution := @rkhs_feature_isometry_of_dense

end HighDimStat.Rkhs

abbrev solution := @HighDimStat.Rkhs.rkhs_feature_isometry_of_dense
