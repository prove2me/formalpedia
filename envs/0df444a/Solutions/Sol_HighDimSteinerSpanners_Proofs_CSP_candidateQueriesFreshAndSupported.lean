-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.candidateQueriesFreshAndSupported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:51:07.671465+00:00
-- url     : https://prove2.me/submissions/dfd190d8-f7e6-4c59-85d5-882a712e40b0

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Calibration
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessMoments
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_candMWit_card_and_quad
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_candMWit_proj


set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
namespace HighDimSteinerSpanners.Proofs.CSP
theorem _root_.solution : ∀ {N q : ℕ} (C₁ r_star m : ℕ), 3 ≤ C₁ → 1000 * C₁ <
    r_star →
    ∀ (a b : Fin N → Fin q) (z_prev : Fin m → (Fin N → Fin q)) (x : Fin N → Fin q),
    x ∈ cspPoolCand C₁ r_star a b \ Finset.univ.image z_prev →
    candMFresh a b m z_prev x ⊆ disagreeSet x a ∩ disagreeSet x b ∧
    (∀ w ∈ candMWit C₁ r_star a b m z_prev x, candQCand C₁ a b m z_prev x w ⊆
      cspUCand a b (m + 1) (Fin.snoc z_prev x) \ cspUCand a b m z_prev) ∧
    (∀ ω : cspIota N q → Bool, ω (Sum.inr x) = true →
      x ∈ bicliqueWitnessList (symROf ω) C₁ r_star a b →
      ∃ w ∈ candMWit C₁ r_star a b m z_prev x, ∀ i ∈ candQCand C₁ a b m z_prev x w, ω i = true) ∧
    (∀ w, ∀ (p_edge p_keep : ℝ),
      ∏ i ∈ candQCand C₁ a b m z_prev x w, Sum.elim (fun _ => p_edge) (fun _ => p_keep) i =
        p_keep * p_edge ^ ((candA1 (candMFresh a b m z_prev x)).card +
          (candA2 C₁ a b x (candMFresh a b m z_prev x) w).card)) := by
  intro N q C₁ r_star m hC₁_loc hr_loc a b z_prev x hx
  have hx_sdiff := Finset.mem_sdiff.mp hx
  have hx_pool := hx_sdiff.1
  simp only [cspPoolCand, Finset.mem_filter, Finset.mem_univ, true_and] at hx_pool
  rcases hx_pool with ⟨hx_ne_a, hx_ne_b, hd_xa, hd_xb⟩
  have hx_not_img : ∀ t : Fin m, z_prev t ≠ x :=
    fun t ht => hx_sdiff.2 (Finset.mem_image.mpr ⟨t, Finset.mem_univ t, ht⟩)
  let R_old := cspRvc a b m z_prev
  let R_new := cspRvc a b (m + 1) (Fin.snoc z_prev x)
  let S := candMFresh a b m z_prev x
  let W_ab := disagreeSet x a ∪ disagreeSet x b
  have ha_old : ∀ v : Fin N, (v, a v) ∈ R_old := by
    intro v
    simp only [R_old, cspRvc, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inl (Or.inl ⟨v, rfl⟩)
  have hb_old : ∀ v : Fin N, (v, b v) ∈ R_old := by
    intro v
    simp only [R_old, cspRvc, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inl (Or.inr ⟨v, rfl⟩)
  have hcstar_old : ∀ v : Fin N, (v, activeColor x a b v) ∈ R_old := by
    intro v
    unfold activeColor
    split_ifs
    · exact ha_old v
    · exact hb_old v
  have hcstar_ne : ∀ v ∈ W_ab, activeColor x a b v ≠ x v := by
    intro v hv
    simp only [W_ab, disagreeSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        at hv
    unfold activeColor
    split_ifs with hax
    · exact hax
    · push Not at hax
      rcases hv with h1 | h2
      · exact absurd hax.symm h1
      · exact Ne.symm h2
  have hold_sub_new : R_old ⊆ R_new := by
    intro vc hvc
    simp only [R_old, R_new, cspRvc, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      true_and, Finset.mem_biUnion] at hvc ⊢
    rcases hvc with (h | h) | ⟨t, v, rfl⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨t.castSucc, v, by simp [Fin.snoc_castSucc]⟩
  have hx_new : ∀ v : Fin N, (v, x v) ∈ R_new := by
    intro v
    simp only [R_new, cspRvc, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      true_and, Finset.mem_biUnion]
    exact Or.inr ⟨Fin.last m, v, by simp [Fin.snoc_last]⟩
  have hPhi1_inj : Function.Injective (candPhi1 x) := by
    rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ heq
    simp only [candPhi1, Prod.mk.injEq] at heq
    exact Prod.ext heq.1 heq.2.1
  have hPhi2_injOn : ∀ w, Set.InjOn (candPhi2 a b x) (candA2 C₁ a b x S w) := by
    intro w ⟨u₁, v₁⟩ h₁ ⟨u₂, v₂⟩ h₂ heq
    simp only [candA2, Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at h₁ h₂
    have hu₁_not : (u₁, x u₁) ∉ R_old := by
      have hS₁ := h₁.1.1
      simpa [S, candMFresh, R_old] using hS₁
    have hu₂_not : (u₂, x u₂) ∉ R_old := by
      have hS₂ := h₂.1.1
      simpa [S, candMFresh, R_old] using hS₂
    have hv₁_in : (v₁, activeColor x a b v₁) ∈ R_old := hcstar_old v₁
    have hv₂_in : (v₂, activeColor x a b v₂) ∈ R_old := hcstar_old v₂
    dsimp [candPhi2] at heq
    split_ifs at heq with hlt₁ hlt₂ hlt₂
    · simp only [Prod.mk.injEq] at heq
      exact Prod.ext heq.1 heq.2.1
    · simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, _, hval, _⟩
      rw [hval] at hu₁_not
      exact absurd hv₂_in hu₁_not
    · simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, _, hval, _⟩
      rw [← hval] at hu₂_not
      exact absurd hv₁_in hu₂_not
    · simp only [Prod.mk.injEq] at heq
      exact Prod.ext heq.2.1 heq.1
  have hPhi_disj : ∀ w,
      Disjoint ((candA1 S).image (candPhi1 x)) ((candA2 C₁ a b x S w).image (candPhi2 a b x)) := by
    intro w
    rw [Finset.disjoint_left]
    intro t ht₁ ht₂
    rcases Finset.mem_image.mp ht₁ with ⟨⟨u₁, v₁⟩, _, rfl⟩
    rcases Finset.mem_image.mp ht₂ with ⟨⟨u₂, v₂⟩, h₂, heq⟩
    simp only [candA2, Finset.mem_filter, Finset.mem_product] at h₂
    have hv₂_ne : activeColor x a b v₂ ≠ x v₂ := hcstar_ne v₂ h₂.1.2
    dsimp [candPhi1, candPhi2] at heq
    split_ifs at heq with hlt₂
    · simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨_, rfl, _, hval⟩
      exact hv₂_ne hval
    · simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, _, hval, _⟩
      exact hv₂_ne hval
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    simp only [candMFresh, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp only [disagreeSet, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => hv (h ▸ ha_old v), fun h => hv (h ▸ hb_old v)⟩
  · intro w hw i hi
    simp only [candQCand, Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hi
    rw [Finset.mem_sdiff]
    rcases hi with ⟨_, rfl, rfl⟩ | ⟨t, ht | ht, rfl⟩
    · refine ⟨?_, ?_⟩
      · simp only [cspUCand, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
        exact Or.inl (Or.inr ⟨Fin.last m, by simp [Fin.snoc_last]⟩)
      · intro hmem
        simp only [cspUCand, Finset.mem_union, Finset.mem_image, Finset.mem_insert,
          Finset.mem_singleton, Finset.mem_univ, true_and] at hmem
        rcases hmem with (⟨z, rfl | rfl, h⟩ | ⟨t₀, h⟩) | ⟨_, _, h⟩
        · exact hx_ne_a (Sum.inr.inj h).symm
        · exact hx_ne_b (Sum.inr.inj h).symm
        · exact hx_not_img t₀ (Sum.inr.inj h)
        · cases h
    · rcases ht with ⟨⟨u, v⟩, huv, rfl⟩
      simp only [candA1, Finset.mem_filter, Finset.mem_univ, true_and] at huv
      refine ⟨?_, ?_⟩
      · simp only [cspUCand, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact Or.inr ⟨(u, v, x u, x v), ⟨huv.1, hx_new u, hx_new v⟩, rfl⟩
      · intro hmem
        simp only [cspUCand, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
          Finset.mem_univ, true_and] at hmem
        rcases hmem with (⟨_, _, h⟩ | ⟨_, h⟩) | ⟨t₀, ht₀, h⟩
        · cases h
        · cases h
        · have heq := Sum.inl.inj h
          subst heq
          rcases huv.2 with huS | hvS
          · have hu_not : (u, x u) ∉ R_old := by simpa [candMFresh, R_old] using huS
            exact hu_not ht₀.2.1
          · have hv_not : (v, x v) ∉ R_old := by simpa [candMFresh, R_old] using hvS
            exact hv_not ht₀.2.2
    · rcases ht with ⟨⟨u, v⟩, huv, rfl⟩
      have hne_uv : u ≠ v :=
        ((candMWit_card_and_quad C₁ r_star m hC₁_loc hr_loc a b z_prev x hd_xa hd_xb).2 w hw).1
          (u, v) huv
      have hu_not : (u, x u) ∉ R_old := by
        have huS := (Finset.mem_product.mp (Finset.mem_filter.mp huv).1).1
        simpa [candMFresh, R_old] using huS
      dsimp [candPhi2]
      split_ifs with hlt
      · refine ⟨?_, ?_⟩
        · simp only [cspUCand, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
            Finset.mem_univ, true_and]
          exact Or.inr ⟨(u, v, x u, activeColor x a b v),
            ⟨hlt, hx_new u, hold_sub_new (hcstar_old v)⟩, rfl⟩
        · intro hmem
          simp only [cspUCand, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
            Finset.mem_univ, true_and] at hmem
          rcases hmem with (⟨_, _, h⟩ | ⟨_, h⟩) | ⟨t₀, ht₀, h⟩
          · cases h
          · cases h
          · have heq := Sum.inl.inj h
            subst heq
            exact hu_not ht₀.2.1
      · have hgt : v < u := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne_uv)
        refine ⟨?_, ?_⟩
        · simp only [cspUCand, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
            Finset.mem_univ, true_and]
          exact Or.inr ⟨(v, u, activeColor x a b v, x u),
            ⟨hgt, hold_sub_new (hcstar_old v), hx_new u⟩, rfl⟩
        · intro hmem
          simp only [cspUCand, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
            Finset.mem_univ, true_and] at hmem
          rcases hmem with (⟨_, _, h⟩ | ⟨_, h⟩) | ⟨t₀, ht₀, h⟩
          · cases h
          · cases h
          · have heq := Sum.inl.inj h
            subst heq
            exact hu_not ht₀.2.2
  · intro ω hω_keep hx_wit
    exact candMWit_proj C₁ r_star m a b z_prev x ω hω_keep hx_wit
  · intro w p_edge p_keep
    have hdisj_sum : Disjoint
        (({x} : Finset (Fin N → Fin q)).image (Sum.inr : _ → cspIota N q))
        (((candA1 S).image (candPhi1 x) ∪
          (candA2 C₁ a b x S w).image (candPhi2 a b x)).image (Sum.inl : _ → cspIota N q)) := by
      rw [Finset.disjoint_left]
      intro i hi₁ hi₂
      rcases Finset.mem_image.mp hi₁ with ⟨_, _, rfl⟩
      rcases Finset.mem_image.mp hi₂ with ⟨_, _, h⟩
      cases h
    dsimp [candQCand]
    rw [Finset.prod_union hdisj_sum,
      Finset.prod_image (fun _ _ _ _ h => Sum.inr.inj h),
      Finset.prod_singleton,
      Finset.prod_image (fun _ _ _ _ h => Sum.inl.inj h),
      Finset.prod_union (hPhi_disj w),
      Finset.prod_image (fun _ _ _ _ h => hPhi1_inj h),
      Finset.prod_image (hPhi2_injOn w)]
    simp [S, pow_add]
end HighDimSteinerSpanners.Proofs.CSP
