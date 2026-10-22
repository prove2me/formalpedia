-- Prove2me | solution 1 for HarmonicGames.Decomposition.lemma_4_4_iii
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:37:20.146233+00:00
-- url     : https://prove2.me/submissions/4ac8a6c3-838b-49c0-ad42-4fb68b60788a

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

theorem qqd_ker (u : Games E) (hu : u ∈ LinearMap.ker (Dop E)) (j : ι) : Dm E j (u j) = 0 := by
  have h0 : ∑ k, Dm E k (u k) = 0 := hu
  have h1 : ⟪Dm E j (u j), ∑ k, Dm E k (u k)⟫_ℝ = 0 := by rw [h0]; simp
  rw [inner_sum, Finset.sum_eq_single j] at h1
  · exact inner_self_eq_zero.1 h1
  · intro k _ hk
    exact qqd_orth E j k (Ne.symm hk) _ _
  · intro h; exact absurd (Finset.mem_univ j) h

theorem qqd_Dop_apply (u : Games E) : Dop E u = ∑ k, Dm E k (u k) := rfl

end Games

theorem solution (ι : Type) [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ m, Fintype (E m)]
    [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)] (X : Flow E) (m : ι) :
    pinv (Dop E) X m = pinv (Dm E m) X := by
  set x : Games E := WithLp.toLp 2 (fun k => pinv (Dm E k) X) with hx
  have hxm : ∀ k, x k = pinv (Dm E k) X := fun k => rfl
  have key : pinv (Dop E) X = x := by
    apply qqd_pinv_eq
    · rw [Submodule.mem_orthogonal]
      intro u hu
      rw [PiLp.inner_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      have hk := qqd_pinv_mem (Dm E k) X
      rw [Submodule.mem_orthogonal] at hk
      have := hk (u k) (LinearMap.mem_ker.2 (qqd_ker E u hu k))
      rw [hxm]
      exact this
    · intro z
      rw [qqd_Dop_apply, qqd_Dop_apply, inner_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [inner_sub_left, sum_inner]
      have : ∑ k, ⟪Dm E k (x k), Dm E j (z j)⟫_ℝ = ⟪Dm E j (x j), Dm E j (z j)⟫_ℝ := by
        rw [Finset.sum_eq_single j]
        · intro k _ hk; exact qqd_orth E k j hk _ _
        · intro h; exact absurd (Finset.mem_univ j) h
      rw [this, ← inner_sub_left, hxm]
      exact qqd_pinv_orth (Dm E j) X (z j)
  rw [key]
