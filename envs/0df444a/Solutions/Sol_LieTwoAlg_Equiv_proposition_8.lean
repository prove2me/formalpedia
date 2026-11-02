-- Prove2me | solution 1 for LieTwoAlg.Equiv.proposition_8
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T00:38:09.957205+00:00
-- url     : https://prove2.me/submissions/a519a04d-68ec-4aac-b648-95668782accd

import Definitions.Def_LieTwoAlg_Equiv_Model

set_option autoImplicit false
open LieTwoAlg.Equiv
universe u
variable {k : Type u} [Field k]

private theorem lin_ext {V W : TwoVect k} {F G : LinFunctor V W}
    (h0 : ∀ x, F.F0 x = G.F0 x) (h1 : ∀ f, F.F1 f = G.F1 f) : F = G := by
  have e0 : F.F0 = G.F0 := LinearMap.ext h0
  have e1 : F.F1 = G.F1 := LinearMap.ext h1
  cases F; cases G
  cases e0; cases e1
  rfl

private theorem chain_ext {C D : TwoTerm k} {φ ψ : ChainMap C D}
    (h0 : ∀ x, φ.φ0 x = ψ.φ0 x) (h1 : ∀ f, φ.φ1 f = ψ.φ1 f) : φ = ψ := by
  have e0 : φ.φ0 = ψ.φ0 := LinearMap.ext h0
  have e1 : φ.φ1 = ψ.φ1 := LinearMap.ext h1
  cases φ; cases ψ
  cases e0; cases e1
  rfl

private theorem lin_id (V : TwoVect k) : IsLinFunctor (LinFunctor.id V) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

private theorem lin_comp {V W X : TwoVect k} (F : LinFunctor V W) (G : LinFunctor W X)
    (hf : IsLinFunctor F) (hg : IsLinFunctor G) : IsLinFunctor (F.comp G) := by
  refine ⟨?_, ?_, ?_⟩
  · intro f
    change X.s (G.F1 (F.F1 f)) = G.F0 (F.F0 (V.s f))
    rw [hg.1, hf.1]
  · intro f
    change X.t (G.F1 (F.F1 f)) = G.F0 (F.F0 (V.t f))
    rw [hg.2.1, hf.2.1]
  · intro x
    change G.F1 (F.F1 (V.i x)) = X.i (G.F0 (F.F0 x))
    rw [hf.2.2, hg.2.2]

private theorem vect_category : (twoVectCat k).IsCategory := by
  refine ⟨lin_id, lin_comp, ?_, ?_⟩
  · intro V W X Y F G H _ _ _
    apply lin_ext <;> intro x <;> rfl
  · intro V W F _
    constructor <;> apply lin_ext <;> intro x <;> rfl

private theorem chain_id (C : TwoTerm k) : IsChainMap (ChainMap.id C) := fun _ => rfl

private theorem chain_comp {C D E : TwoTerm k} (φ : ChainMap C D) (ψ : ChainMap D E)
    (hφ : IsChainMap φ) (hψ : IsChainMap ψ) : IsChainMap (φ.comp ψ) := by
  intro h
  exact (hψ (φ.φ1 h)).trans (congrArg ψ.φ0 (hφ h))

private theorem term_category : (twoTermCat k).IsCategory := by
  refine ⟨chain_id, chain_comp, ?_, ?_⟩
  · intro C D E G φ ψ χ _ _ _
    apply chain_ext <;> intro x <;> rfl
  · intro C D φ _
    constructor <;> apply chain_ext <;> intro x <;> rfl

private theorem S_map_val {V W : TwoVect k} (F : LinFunctor V W)
    (hf : IsLinFunctor F) (h : LinearMap.ker V.s) :
    ((toTwoTermMap F).φ1 h : LinearMap.ker W.s).val = F.F1 h := by
  have hs : V.s h = 0 := h.property
  change F.F1 h - W.i (W.s (F.F1 h)) = F.F1 h
  rw [hf.1, hs, map_zero, map_zero, sub_zero]

private theorem S_law {V W : TwoVect k} (F : LinFunctor V W)
    (hf : IsLinFunctor F) : IsChainMap (toTwoTermMap F) := by
  intro h
  change LinearMap.ker V.s at h
  change W.t ((toTwoTermMap F).φ1 h : LinearMap.ker W.s).val = F.F0 (V.t h)
  rw [S_map_val F hf]
  exact hf.2.1 h

private theorem T_law {C D : TwoTerm k} (φ : ChainMap C D)
    (hφ : IsChainMap φ) : IsLinFunctor (ofTwoTermMap φ) := by
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · rintro ⟨x, h⟩
    change φ.φ0 x + D.d (φ.φ1 h) = φ.φ0 (x + C.d h)
    rw [hφ, map_add]
  · intro x
    change (φ.φ0 x, φ.φ1 0) = (φ.φ0 x, 0)
    rw [map_zero]

private def S : RawFunctor (twoVectCat k) (twoTermCat k) :=
  ⟨toTwoTerm, toTwoTermMap⟩

private def T : RawFunctor (twoTermCat k) (twoVectCat k) :=
  ⟨ofTwoTerm, ofTwoTermMap⟩

private theorem S_functor : (S (k := k)).IsFunctor := by
  refine ⟨S_law, ?_, ?_⟩
  · intro V
    change TwoVect k at V
    apply chain_ext
    · intro x; rfl
    · intro h
      change LinearMap.ker V.s at h
      apply Subtype.ext
      exact S_map_val (LinFunctor.id V) (lin_id V) h
  · intro V W X F G hf hg
    change TwoVect k at V W X
    change LinFunctor V W at F
    change LinFunctor W X at G
    change IsLinFunctor F at hf
    change IsLinFunctor G at hg
    apply chain_ext
    · intro x; rfl
    · intro h
      change LinearMap.ker V.s at h
      apply Subtype.ext
      change ((toTwoTermMap (F.comp G)).φ1 h : LinearMap.ker X.s).val =
        ((toTwoTermMap G).φ1 ((toTwoTermMap F).φ1 h) : LinearMap.ker X.s).val
      exact (S_map_val (F.comp G) (lin_comp F G hf hg) h).trans
        ((S_map_val G hg ((toTwoTermMap F).φ1 h)).trans
          (congrArg G.F1 (S_map_val F hf h))).symm

private theorem T_functor : (T (k := k)).IsFunctor := by
  refine ⟨T_law, ?_, ?_⟩
  · intro C
    apply lin_ext
    · intro x; rfl
    · rintro ⟨x, h⟩; rfl
  · intro C D E φ ψ _ _
    apply lin_ext
    · intro x; rfl
    · rintro ⟨x, h⟩; rfl

private def alpha (V : TwoVect k) : LinFunctor (ofTwoTerm (toTwoTerm V)) V where
  F0 := LinearMap.id
  F1 := V.i.comp (LinearMap.fst k V.V0 (LinearMap.ker V.s)) +
    (Submodule.subtype (LinearMap.ker V.s)).comp (LinearMap.snd k V.V0 (LinearMap.ker V.s))

private def alphaInv (V : TwoVect k) : LinFunctor V (ofTwoTerm (toTwoTerm V)) where
  F0 := LinearMap.id
  F1 := V.s.prod V.arrowK

private theorem alpha_law (V : TwoVect k) : IsLinFunctor (alpha V) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨x, h⟩
    change V.V0 at x
    change LinearMap.ker V.s at h
    have hs : V.s h = 0 := h.property
    change V.s (V.i x + h) = x
    rw [map_add, V.s_i, hs, add_zero]
  · rintro ⟨x, h⟩
    change V.V0 at x
    change LinearMap.ker V.s at h
    change V.t (V.i x + h) = x + V.t h
    rw [map_add, V.t_i]
  · intro x
    change V.i x + (0 : LinearMap.ker V.s).val = V.i x
    exact add_zero _

private theorem alphaInv_law (V : TwoVect k) : IsLinFunctor (alphaInv V) := by
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · intro f
    change V.s f + V.t (f - V.i (V.s f)) = V.t f
    rw [map_sub, V.t_i]
    abel
  · intro x
    apply Prod.ext
    · exact V.s_i x
    · apply Subtype.ext
      change V.i x - V.i (V.s (V.i x)) = 0
      rw [V.s_i, sub_self]

private theorem alpha_iso (V : TwoVect k) : (twoVectCat k).IsIso (alpha V) := by
  refine ⟨alpha_law V, alphaInv V, alphaInv_law V, ?_, ?_⟩
  · apply lin_ext
    · intro x; rfl
    · rintro ⟨x, h⟩
      change V.V0 at x
      change LinearMap.ker V.s at h
      have hs : V.s h = 0 := h.property
      apply Prod.ext
      · change V.s (V.i x + h) = x
        rw [map_add, V.s_i, hs, add_zero]
      · apply Subtype.ext
        change (V.i x + h) - V.i (V.s (V.i x + h)) = h
        rw [map_add, V.s_i, hs, add_zero]
        abel
  · apply lin_ext
    · intro x; rfl
    · intro f
      change V.i (V.s f) + (f - V.i (V.s f)) = f
      abel

private def beta (C : TwoTerm k) : ChainMap (toTwoTerm (ofTwoTerm C)) C where
  φ0 := LinearMap.id
  φ1 := (LinearMap.snd k C.C0 C.C1).comp
    (Submodule.subtype (LinearMap.ker (ofTwoTerm C).s))

private def betaInv (C : TwoTerm k) : ChainMap C (toTwoTerm (ofTwoTerm C)) where
  φ0 := LinearMap.id
  φ1 := {
    toFun := fun h => ⟨(0, h), rfl⟩
    map_add' := by
      intro a b
      apply Subtype.ext
      change ((0 : C.C0), a + b) = (0, a) + (0, b)
      apply Prod.ext
      · change (0 : C.C0) = 0 + 0
        simp
      · rfl
    map_smul' := by
      intro c a
      apply Subtype.ext
      change ((0 : C.C0), c • a) = c • (0, a)
      apply Prod.ext
      · change (0 : C.C0) = c • 0
        simp
      · rfl }

private theorem beta_law (C : TwoTerm k) : IsChainMap (beta C) := by
  intro h
  have hs : h.val.1 = 0 := h.property
  change C.d h.val.2 = h.val.1 + C.d h.val.2
  rw [hs, zero_add]

private theorem betaInv_law (C : TwoTerm k) : IsChainMap (betaInv C) := by
  intro h
  change 0 + C.d h = C.d h
  exact zero_add _

private theorem beta_iso (C : TwoTerm k) : (twoTermCat k).IsIso (beta C) := by
  refine ⟨beta_law C, betaInv C, betaInv_law C, ?_, ?_⟩
  · apply chain_ext
    · intro x; rfl
    · intro h
      apply Subtype.ext
      have hs : h.val.1 = 0 := h.property
      change (0, h.val.2) = h.val
      exact Prod.ext hs.symm rfl
  · apply chain_ext <;> intro x <;> rfl

private theorem alpha_natural {V W : TwoVect k} (F : LinFunctor V W)
    (hf : IsLinFunctor F) :
    (ofTwoTermMap (toTwoTermMap F)).comp (alpha W) = (alpha V).comp F := by
  apply lin_ext
  · intro x; rfl
  · rintro ⟨x, h⟩
    change V.V0 at x
    change LinearMap.ker V.s at h
    change W.i (F.F0 x) + ((toTwoTermMap F).φ1 h : LinearMap.ker W.s).val = F.F1 (V.i x + h)
    rw [S_map_val F hf, map_add, hf.2.2]

private theorem beta_natural {C D : TwoTerm k} (φ : ChainMap C D)
    (hφ : IsChainMap φ) :
    (toTwoTermMap (ofTwoTermMap φ)).comp (beta D) = (beta C).comp φ := by
  apply chain_ext
  · intro x; rfl
  · intro h
    change LinearMap.ker (ofTwoTerm C).s at h
    exact congrArg (fun p : D.C0 × D.C1 => p.2)
      (S_map_val (ofTwoTermMap φ) (T_law φ hφ) h)

theorem solution (k : Type u) [Field k] :
    RawCat.Equivalent (twoVectCat k) (twoTermCat k) := by
  exact ⟨vect_category, term_category, S, T, alpha, beta,
    S_functor, T_functor, alpha_iso, beta_iso, alpha_natural, beta_natural⟩

