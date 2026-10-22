-- Prove2me | solution 1 for HarmonicGames.Decomposition.lemma_4_4_ii
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:16:18.414357+00:00
-- url     : https://prove2.me/submissions/ccaa5f2a-7165-43c4-aa2e-0356e4b19c52

import Mathlib
import Definitions.Def_HarmonicGames_Decomposition_Pinv
import Definitions.Def_HarmonicGames_Decomposition_Flows
import Definitions.Def_HarmonicGames_Decomposition_Games

set_option autoImplicit false

open HarmonicGames.Decomposition
open scoped InnerProductSpace

section Gen
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]

theorem qqd_pinv_eq (L : V →ₗ[ℝ] W) (y : W) (x : V) (hx : x ∈ (LinearMap.ker L)ᗮ)
    (hy : ∀ z, ⟪y - L x, L z⟫_ℝ = 0) : pinv L y = x := by
  unfold pinv
  have hxR : L x ∈ LinearMap.range (L ∘ₗ (LinearMap.ker L)ᗮ.subtype) := ⟨⟨x, hx⟩, rfl⟩
  have hP : (LinearMap.range (L ∘ₗ (LinearMap.ker L)ᗮ.subtype)).orthogonalProjectionOnto y
      = ⟨L x, hxR⟩ := by
    apply Subtype.ext
    rw [Submodule.coe_orthogonalProjectionOnto_apply]
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hxR
    intro w hw
    obtain ⟨⟨z, hz⟩, rfl⟩ := hw
    exact hy z
  have : (LinearEquiv.ofInjective _ (pinv_restrict_injective L)).symm ⟨L x, hxR⟩ = ⟨x, hx⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, LinearEquiv.coe_coe]
  rw [hP, this]
  rfl

theorem qqd_pinv_mem (L : V →ₗ[ℝ] W) (y : W) : pinv L y ∈ (LinearMap.ker L)ᗮ := by
  unfold pinv
  exact Submodule.coe_mem _

theorem qqd_L_pinv (L : V →ₗ[ℝ] W) (y : W) :
    L (pinv L y) = ((LinearMap.range (L ∘ₗ (LinearMap.ker L)ᗮ.subtype)).orthogonalProjectionOnto y : W) := by
  unfold pinv
  set t := (LinearMap.range (L ∘ₗ (LinearMap.ker L)ᗮ.subtype)).orthogonalProjectionOnto y with ht
  have h2 := congrArg Subtype.val
    ((LinearEquiv.ofInjective _ (pinv_restrict_injective L)).apply_symm_apply t)
  rw [LinearEquiv.ofInjective_apply] at h2
  exact h2

theorem qqd_pinv_orth (L : V →ₗ[ℝ] W) (y : W) (z : V) :
    ⟪y - L (pinv L y), L z⟫_ℝ = 0 := by
  rw [qqd_L_pinv]
  set R := LinearMap.range (L ∘ₗ (LinearMap.ker L)ᗮ.subtype)
  have hz : L z = L ((LinearMap.ker L)ᗮ.starProjection z) := by
    have : z - (LinearMap.ker L)ᗮ.starProjection z ∈ LinearMap.ker L := by
      have := Submodule.sub_starProjection_mem_orthogonal (K := (LinearMap.ker L)ᗮ) z
      rwa [Submodule.orthogonal_orthogonal] at this
    have h := LinearMap.mem_ker.1 this
    rw [map_sub, sub_eq_zero] at h
    exact h
  have hmem : L z ∈ R := by
    rw [hz]
    exact ⟨⟨_, Submodule.starProjection_apply_mem _ _⟩, rfl⟩
  have := Submodule.starProjection_inner_eq_zero (K := R) y (L z) hmem
  simpa [Submodule.coe_orthogonalProjectionOnto_apply] using this
end Gen

section Games
variable {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ m, Fintype (E m)]
  [∀ m, DecidableEq (E m)]

theorem qqd_Dm_apply (m : ι) (φ : Util E) (p q : ∀ k, E k) :
    Dm E m φ p q = Wm E m p q * (φ q - φ p) := rfl

theorem qqd_WW (j k : ι) (hjk : j ≠ k) (p q : ∀ l, E l) : Wm E j p q * Wm E k p q = 0 := by
  by_cases h1 : MComparable E j p q
  · by_cases h2 : MComparable E k p q
    · exfalso
      apply h1.1
      funext l
      by_cases hl : l = j
      · subst hl
        exact h2.2 l hjk
      · exact h1.2 l hl
    · simp [Wm, h2]
  · simp [Wm, h1]

theorem qqd_orth (j k : ι) (hjk : j ≠ k) (a b : Util E) : ⟪Dm E j a, Dm E k b⟫_ℝ = 0 := by
  change innerC1 (gameGraph E) (Dm E j a) (Dm E k b) = 0
  unfold innerC1
  have : ∀ p q, (if (gameGraph E).Adj p q then Dm E j a p q * Dm E k b p q else 0) = 0 := by
    intro p q
    split_ifs
    · rw [qqd_Dm_apply, qqd_Dm_apply]
      have := qqd_WW E j k hjk p q
      calc Wm E j p q * (a q - a p) * (Wm E k p q * (b q - b p))
          = (Wm E j p q * Wm E k p q) * ((a q - a p) * (b q - b p)) := by ring
        _ = 0 := by rw [this]; simp
    · rfl
  simp [this]

end Games

section GramGen
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]

theorem qqd_pinv_gram (L : V →ₗ[ℝ] W) (w : W) :
    pinv L w = pinv (LinearMap.adjoint L ∘ₗ L) (LinearMap.adjoint L w) := by
  have hker : LinearMap.ker (LinearMap.adjoint L ∘ₗ L) = LinearMap.ker L := by
    ext v
    simp only [LinearMap.mem_ker, LinearMap.comp_apply]
    constructor
    · intro h
      have h1 : ⟪L v, L v⟫_ℝ = 0 := by
        rw [← LinearMap.adjoint_inner_right, h]; simp
      exact inner_self_eq_zero.1 h1
    · intro h; rw [h]; simp
  symm
  apply qqd_pinv_eq
  · rw [hker]; exact qqd_pinv_mem L w
  · intro z
    have : LinearMap.adjoint L w - (LinearMap.adjoint L ∘ₗ L) (pinv L w) =
        LinearMap.adjoint L (w - L (pinv L w)) := by simp [map_sub]
    rw [this, LinearMap.adjoint_inner_left]
    exact qqd_pinv_orth L w ((LinearMap.adjoint L ∘ₗ L) z)
end GramGen

section Fin2
variable {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ m, Fintype (E m)]
  [∀ m, DecidableEq (E m)]

theorem qqd_adj_orth (i k : ι) (hik : i ≠ k) (b : Util E) :
    LinearMap.adjoint (Dm E i) (Dm E k b) = 0 := by
  apply ext_inner_left ℝ
  intro a
  rw [LinearMap.adjoint_inner_right]
  simp [qqd_orth E i k hik a b]

end Fin2

theorem solution (ι : Type) [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ m, Fintype (E m)]
    [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)] (j : ι) :
    pinv (∑ i, Dm E i) ∘ₗ Dm E j =
      pinv (∑ i, LinearMap.adjoint (Dm E i) ∘ₗ Dm E i) ∘ₗ
        (LinearMap.adjoint (Dm E j) ∘ₗ Dm E j) := by
  have hL : LinearMap.adjoint (∑ i, Dm E i) ∘ₗ Dm E j = LinearMap.adjoint (Dm E j) ∘ₗ Dm E j := by
    ext v : 1
    simp only [LinearMap.comp_apply, map_sum, LinearMap.sum_apply]
    rw [Finset.sum_eq_single j]
    · intro i _ hi; exact qqd_adj_orth E i j hi v
    · intro h; exact absurd (Finset.mem_univ j) h
  have hS : LinearMap.adjoint (∑ i, Dm E i) ∘ₗ (∑ i, Dm E i) = ∑ i, LinearMap.adjoint (Dm E i) ∘ₗ Dm E i := by
    ext v : 1
    simp only [LinearMap.comp_apply, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · intro k _ hk; exact qqd_adj_orth E k i hk v
    · intro h; exact absurd (Finset.mem_univ i) h
  ext v : 1
  simp only [LinearMap.comp_apply]
  rw [qqd_pinv_gram (∑ i, Dm E i) (Dm E j v), hS]
  have := congrArg (fun T => T v) hL
  simp only [LinearMap.comp_apply] at this
  rw [this]
