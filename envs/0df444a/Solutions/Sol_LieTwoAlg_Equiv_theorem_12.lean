-- Prove2me | solution 1 for LieTwoAlg.Equiv.theorem_12
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T00:17:46.590782+00:00
-- url     : https://prove2.me/submissions/049db155-3687-4e08-b09c-8cded5a48ce1

import Definitions.Def_LieTwoAlg_Equiv_Model
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
open LieTwoAlg.Equiv
universe u
variable {k : Type u} [Field k] {V W : TwoVect k}

private theorem map_kernel (F : LinFunctor V W) (hf : IsLinFunctor F)
    (h : LinearMap.ker V.s) : ((toTwoTermMap F).φ1 h : LinearMap.ker W.s).val = F.F1 h := by
  have hs : V.s h = 0 := h.property
  change F.F1 h - W.i (W.s (F.F1 h)) = F.F1 h
  rw [hf.1, hs, map_zero, map_zero, sub_zero]

private def toHomotopy (θ : V.V0 →ₗ[k] W.V1) : V.V0 →ₗ[k] LinearMap.ker W.s :=
  W.arrowK.comp θ

private def toTransformation (F : LinFunctor V W)
    (τ : V.V0 →ₗ[k] LinearMap.ker W.s) : V.V0 →ₗ[k] W.V1 :=
  W.i.comp F.F0 + (Submodule.subtype (LinearMap.ker W.s)).comp τ

private theorem forward_law (F G : LinFunctor V W) (hF : IsLinFunctor F)
    (hG : IsLinFunctor G) (θ : V.V0 →ₗ[k] W.V1) (hθ : IsLinNat F G θ) :
    IsChainHtpy (toTwoTermMap F) (toTwoTermMap G) (toHomotopy θ) := by
  constructor
  · intro x
    change V.V0 at x
    change W.t (θ x - W.i (W.s (θ x))) = G.F0 x - F.F0 x
    rw [map_sub, W.t_i, hθ.1, hθ.2.1]
  · intro h
    change LinearMap.ker V.s at h
    apply Subtype.ext
    change θ (V.t h) - W.i (W.s (θ (V.t h))) =
      ((toTwoTermMap G).φ1 h : LinearMap.ker W.s).val - ((toTwoTermMap F).φ1 h : LinearMap.ker W.s).val
    rw [hθ.1, map_kernel G hG, map_kernel F hF]
    have hs : V.s h = 0 := h.property
    have hn := hθ.2.2 h
    change F.F1 h + θ (V.t h) - W.i (W.t (F.F1 h)) =
      θ (V.s h) + G.F1 h - W.i (W.t (θ (V.s h))) at hn
    rw [hF.2.1] at hn
    simp only [hs, map_zero, zero_add, sub_zero] at hn
    linear_combination (norm := abel) hn

private theorem backward_law (F G : LinFunctor V W) (hF : IsLinFunctor F)
    (hG : IsLinFunctor G) (τ : V.V0 →ₗ[k] LinearMap.ker W.s)
    (hτ : IsChainHtpy (toTwoTermMap F) (toTwoTermMap G) τ) :
    IsLinNat F G (toTransformation F τ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have hs : W.s (τ x) = 0 := (τ x).property
    change W.s (W.i (F.F0 x) + τ x) = F.F0 x
    rw [map_add, W.s_i, hs, add_zero]
  · intro x
    have ht : W.t (τ x) = G.F0 x - F.F0 x := hτ.1 x
    change W.t (W.i (F.F0 x) + τ x) = G.F0 x
    rw [map_add, W.t_i, ht]
    abel
  · intro f
    have he := congrArg (fun h : LinearMap.ker W.s => (h : W.V1)) (hτ.2 (V.arrowK f))
    change (τ (V.t (f - V.i (V.s f))) : W.V1) =
      ((toTwoTermMap G).φ1 (V.arrowK f) : LinearMap.ker W.s).val -
      ((toTwoTermMap F).φ1 (V.arrowK f) : LinearMap.ker W.s).val at he
    rw [map_kernel G hG, map_kernel F hF] at he
    change (τ (V.t (f - V.i (V.s f))) : W.V1) =
      G.F1 (f - V.i (V.s f)) - F.F1 (f - V.i (V.s f)) at he
    simp only [map_sub, V.t_i, hG.2.2, hF.2.2, Submodule.coe_sub] at he
    change F.F1 f + (W.i (F.F0 (V.t f)) + τ (V.t f)) - W.i (W.t (F.F1 f)) =
      (W.i (F.F0 (V.s f)) + τ (V.s f)) + G.F1 f -
        W.i (W.t (W.i (F.F0 (V.s f)) + τ (V.s f)))
    rw [hF.2.1, map_add, W.t_i]
    have ht : W.t (τ (V.s f)) = G.F0 (V.s f) - F.F0 (V.s f) := hτ.1 (V.s f)
    rw [ht]
    have hz : F.F0 (V.s f) + (G.F0 (V.s f) - F.F0 (V.s f)) = G.F0 (V.s f) := by abel
    rw [hz]
    linear_combination (norm := abel) he

theorem solution {k : Type u} [Field k] {V W : TwoVect k} (F G : LinFunctor V W)
    (hF : IsLinFunctor F) (hG : IsLinFunctor G) :
    ∃ e : {θ : V.V0 →ₗ[k] W.V1 // IsLinNat F G θ} ≃
        {τ : V.V0 →ₗ[k] LinearMap.ker W.s //
          IsChainHtpy (toTwoTermMap F) (toTwoTermMap G) τ},
      ∀ (θ : {θ : V.V0 →ₗ[k] W.V1 // IsLinNat F G θ}) (x : V.V0),
        ((e θ).1 x : W.V1) = W.arrow (θ.1 x) := by
  let e : {θ : V.V0 →ₗ[k] W.V1 // IsLinNat F G θ} ≃
      {τ : V.V0 →ₗ[k] LinearMap.ker W.s //
        IsChainHtpy (toTwoTermMap F) (toTwoTermMap G) τ} := {
    toFun := fun θ => ⟨toHomotopy θ.1, forward_law F G hF hG θ.1 θ.2⟩
    invFun := fun τ => ⟨toTransformation F τ.1, backward_law F G hF hG τ.1 τ.2⟩
    left_inv := by
      intro θ
      apply Subtype.ext
      apply LinearMap.ext
      intro x
      change W.i (F.F0 x) + (θ.1 x - W.i (W.s (θ.1 x))) = θ.1 x
      rw [θ.2.1]
      abel
    right_inv := by
      intro τ
      apply Subtype.ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      have hs : W.s (τ.1 x) = 0 := (τ.1 x).property
      change W.i (F.F0 x) + τ.1 x - W.i (W.s (W.i (F.F0 x) + τ.1 x)) = τ.1 x
      rw [map_add, W.s_i, hs, add_zero]
      abel }
  exact ⟨e, fun _ _ => rfl⟩

