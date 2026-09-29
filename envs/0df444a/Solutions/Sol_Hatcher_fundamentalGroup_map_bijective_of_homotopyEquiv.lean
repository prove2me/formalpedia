-- Prove2me | solution 1 for Hatcher.fundamentalGroup_map_bijective_of_homotopyEquiv
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-14T12:45:06.718561+00:00
-- url     : https://prove2.me/submissions/0356b531-9adc-4096-b23e-7176dec73531

import Theorems.Thm_Hatcher_fundamentalGroup_map_eq_changeOfBasepoint_comp_of_homotopy
import Mathlib

open CategoryTheory ContinuousMap FundamentalGroup FundamentalGroupoidFunctor

/-- Functoriality of the induced map on `π₁`; Mathlib has this at the groupoid level only. -/
private lemma map_comp' {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (g : C(Y, Z)) (f : C(X, Y)) (x : X) :
    FundamentalGroup.map (g.comp f) x
      = (FundamentalGroup.map g (f x)).comp (FundamentalGroup.map f x) := by
  ext γ; refine Quotient.inductionOn γ fun q => ?_; rfl

private lemma map_id' {X : Type*} [TopologicalSpace X] (x : X) :
    FundamentalGroup.map (ContinuousMap.id X) x = MonoidHom.id _ := by
  ext γ; refine Quotient.inductionOn γ fun q => ?_; rfl

/-- A map homotopic to the identity induces a bijection on `π₁`: by Lemma 1.19 it agrees with
the inverse of a change-of-basepoint isomorphism. -/
private lemma bijective_of_homotopy_id {X : Type*} [TopologicalSpace X] {ψ : C(X, X)}
    (H : ContinuousMap.Homotopy ψ (ContinuousMap.id X)) (x₀ : X) :
    Function.Bijective (FundamentalGroup.map ψ x₀) := by
  have h19 := Hatcher.fundamentalGroup_map_eq_changeOfBasepoint_comp_of_homotopy H x₀
  rw [map_id'] at h19
  set E := fundamentalGroupMulEquivOfPath (H.evalAt x₀) with hE
  have key : ∀ z, FundamentalGroup.map ψ x₀ z = E.symm z := by
    intro z
    have h := congrArg (fun m : FundamentalGroup X x₀ →* FundamentalGroup X x₀ => m z) h19
    simp only [MonoidHom.id_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h
    exact (E.symm_apply_eq.mpr h).symm
  have hfun : (FundamentalGroup.map ψ x₀ : _ → _) = (E.symm : _ → _) := funext key
  rw [hfun]; exact E.symm.bijective

theorem solution {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (x₀ : X) :
    Function.Bijective (FundamentalGroup.map e.toFun x₀) := by
  have h1 : Function.Bijective (FundamentalGroup.map (e.invFun.comp e.toFun) x₀) :=
    bijective_of_homotopy_id e.left_inv.some x₀
  rw [map_comp', MonoidHom.coe_comp] at h1
  have h2 : Function.Bijective (FundamentalGroup.map (e.toFun.comp e.invFun) (e.toFun x₀)) :=
    bijective_of_homotopy_id e.right_inv.some (e.toFun x₀)
  rw [map_comp', MonoidHom.coe_comp] at h2
  have hBinj : Function.Injective (FundamentalGroup.map e.invFun (e.toFun x₀)) := h2.1.of_comp
  refine ⟨h1.1.of_comp, fun y => ?_⟩
  obtain ⟨a, ha⟩ := h1.2 (FundamentalGroup.map e.invFun (e.toFun x₀) y)
  exact ⟨a, hBinj ha⟩
