-- Prove2me | solution 1 for HarmonicGames.Decomposition.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:35:08.057606+00:00
-- url     : https://prove2.me/submissions/40919ed5-f62b-4c5a-a1b8-9f87d9ed21c3

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

theorem qqd_Wm_symm (m : ι) (p q : ∀ k, E k) : Wm E m p q = Wm E m q p := by
  unfold Wm MComparable
  have : (p ≠ q ∧ ∀ k, k ≠ m → p k = q k) ↔ (q ≠ p ∧ ∀ k, k ≠ m → q k = p k) :=
    ⟨fun h => ⟨fun e => h.1 e.symm, fun k hk => (h.2 k hk).symm⟩,
     fun h => ⟨fun e => h.1 e.symm, fun k hk => (h.2 k hk).symm⟩⟩
  simp only [this]

theorem qqd_Wm_sq (m : ι) (p q : ∀ k, E k) : Wm E m p q * Wm E m p q = Wm E m p q := by
  unfold Wm; split_ifs <;> simp

theorem qqd_inner (m : ι) (ψ φ : Util E) :
    ⟪Dm E m ψ, Dm E m φ⟫_ℝ =
      (1 / 2 : ℝ) * ∑ p, ∑ q, Wm E m p q * ((ψ q - ψ p) * (φ q - φ p)) := by
  change innerC1 (gameGraph E) (Dm E m ψ) (Dm E m φ) = _
  unfold innerC1
  congr 1
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [qqd_Dm_apply, qqd_Dm_apply]
  by_cases h : MComparable E m p q
  · have hW : Wm E m p q = 1 := by simp [Wm, h]
    have hA : (gameGraph E).Adj p q := ⟨m, h⟩
    rw [if_pos hA, hW]; ring
  · have hW : Wm E m p q = 0 := by simp [Wm, h]
    rw [hW]; simp

theorem qqd_sum_W (m : ι) (q : ∀ k, E k) (f : (∀ k, E k) → ℝ) :
    ∑ p, Wm E m p q * f p = ∑ a : E m, f (Function.update q m a) - f q := by
  have h1 : ∑ p, (if ∀ k, k ≠ m → p k = q k then f p else 0) = ∑ a : E m, f (Function.update q m a) := by
    rw [← Finset.sum_filter]
    have : (Finset.univ.filter fun p : (∀ k, E k) => ∀ k, k ≠ m → p k = q k)
        = Finset.univ.image (fun a : E m => Function.update q m a) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro h
        refine ⟨p m, ?_⟩
        funext k
        by_cases hk : k = m
        · subst hk; simp
        · rw [Function.update_of_ne hk, h k hk]
      · rintro ⟨a, rfl⟩ k hk
        rw [Function.update_of_ne hk]
    rw [this, Finset.sum_image]
    intro a _ b _ hab
    have := congrFun hab m
    simpa using this
  have h2 : ∀ p, Wm E m p q * f p = (if ∀ k, k ≠ m → p k = q k then f p else 0) - (if p = q then f p else 0) := by
    intro p
    unfold Wm MComparable
    by_cases hp : p = q
    · subst hp; simp
    · by_cases hk : ∀ k, k ≠ m → p k = q k
      · simp [hp, hk]
      · simp [hp, hk]
  simp only [h2, Finset.sum_sub_distrib, h1]
  simp

theorem qqd_card_W (m : ι) (q : ∀ k, E k) :
    ∑ p, Wm E m p q = (Fintype.card (E m) : ℝ) - 1 := by
  have := qqd_sum_W E m q (fun _ => 1)
  simpa using this

theorem qqd_hc (m : ι) (φ : Util E) (q : ∀ k, E k) :
    ∑ p, Wm E m p q * (φ q - φ p) =
      (Fintype.card (E m) : ℝ) * φ q - ∑ a : E m, φ (Function.update q m a) := by
  have := qqd_sum_W E m q (fun p => φ p)
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, qqd_card_W]
  rw [this]; ring

theorem qqd_T (m : ι) (ψ φ : Util E) :
    ∑ p, ∑ q, Wm E m p q * ((ψ q - ψ p) * (φ q - φ p)) =
      2 * ∑ q, ψ q * ((Fintype.card (E m) : ℝ) * φ q - ∑ a : E m, φ (Function.update q m a)) := by
  have h1 : ∑ p, ∑ q, Wm E m p q * ((ψ q - ψ p) * (φ q - φ p)) =
      ∑ p, ∑ q, Wm E m p q * ψ q * (φ q - φ p) -
        ∑ p, ∑ q, Wm E m p q * ψ p * (φ q - φ p) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  have h2 : ∑ p, ∑ q, Wm E m p q * ψ p * (φ q - φ p) =
      - ∑ p, ∑ q, Wm E m p q * ψ q * (φ q - φ p) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [qqd_Wm_symm E m q p]; ring
  have h3 : ∑ p, ∑ q, Wm E m p q * ψ q * (φ q - φ p) =
      ∑ q, ψ q * ((Fintype.card (E m) : ℝ) * φ q - ∑ a : E m, φ (Function.update q m a)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← qqd_hc E m φ q, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  rw [h1, h2, h3]; ring

theorem qqd_Delta_vec (m : ι) (φ : Util E) :
    Delta0m E m φ = (WithLp.toLp 2 (fun p => (Fintype.card (E m) : ℝ) * φ p -
      ∑ a : E m, φ (Function.update p m a)) : Util E) := by
  apply ext_inner_left ℝ
  intro ψ
  have : Delta0m E m φ = LinearMap.adjoint (Dm E m) (Dm E m φ) := rfl
  rw [this, LinearMap.adjoint_inner_right, qqd_inner, qqd_T]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

theorem qqd_Delta_apply (m : ι) (φ : Util E) (p : ∀ k, E k) :
    Delta0m E m φ p = (Fintype.card (E m) : ℝ) * φ p - ∑ a : E m, φ (Function.update p m a) := by
  rw [qqd_Delta_vec]

theorem qqd_Dm_g (m : ι) (φ : Util E) :
    Dm E m (WithLp.toLp 2 (fun p : ∀ k, E k => ∑ a : E m, φ (Function.update p m a)) : Util E) = 0 := by
  apply C1.ext
  intro p q
  rw [qqd_Dm_apply]
  show _ = (0 : ℝ)
  by_cases h : MComparable E m p q
  · have : ∀ a : E m, Function.update q m a = Function.update p m a := by
      intro a
      funext k
      by_cases hk : k = m
      · subst hk; simp
      · rw [Function.update_of_ne hk, Function.update_of_ne hk, h.2 k hk]
    have hg : (∑ a : E m, φ (Function.update q m a)) = ∑ a : E m, φ (Function.update p m a) := by
      simp only [this]
    show Wm E m p q * (∑ a : E m, φ (Function.update q m a) - ∑ a : E m, φ (Function.update p m a)) = 0
    rw [hg]; simp
  · have hW : Wm E m p q = 0 := by simp [Wm, h]
    rw [hW]; simp

end Games

theorem solution (ι : Type) [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ m, Fintype (E m)]
    [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)] (m : ι) :
    Delta0m E m = (Fintype.card (E m) : ℝ) • Pim E m := by
  have hn : (Fintype.card (E m) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  apply LinearMap.ext
  intro φ
  set n : ℝ := (Fintype.card (E m) : ℝ) with hndef
  set g : Util E := (WithLp.toLp 2 (fun p : ∀ k, E k => ∑ a : E m, φ (Function.update p m a)) : Util E)
    with hgdef
  have hΔ : Delta0m E m φ = n • φ - g := by
    rw [qqd_Delta_vec]
    ext p
    simp [hndef, hgdef]
  set x : Util E := n⁻¹ • Delta0m E m φ with hxdef
  have hxφ : x = φ - n⁻¹ • g := by
    rw [hxdef, hΔ, smul_sub, smul_smul, inv_mul_cancel₀ hn, one_smul]
  have hDx : Dm E m x = Dm E m φ := by
    rw [hxφ, map_sub, map_smul, qqd_Dm_g]; simp
  have hx : x ∈ (LinearMap.ker (Dm E m))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro k hk
    have hk0 : Dm E m k = 0 := LinearMap.mem_ker.1 hk
    have : Delta0m E m φ = LinearMap.adjoint (Dm E m) (Dm E m φ) := rfl
    rw [hxdef, this, inner_smul_right, LinearMap.adjoint_inner_right, hk0]
    simp
  have hp : pinv (Dm E m) (Dm E m φ) = x := by
    apply qqd_pinv_eq _ _ _ hx
    intro z
    rw [hDx]; simp
  have hP : Pim E m φ = x := hp
  rw [LinearMap.smul_apply, hP, hxdef, smul_smul, mul_inv_cancel₀ hn, one_smul]
