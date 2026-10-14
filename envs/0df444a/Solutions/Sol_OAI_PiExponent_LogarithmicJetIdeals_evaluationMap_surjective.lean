-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.evaluationMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T09:33:55.796573+00:00
-- url     : https://prove2.me/submissions/f78c5c95-5d5f-42a5-995a-a05646901f25

import Definitions.Def_evaluationMap
import Mathlib.LinearAlgebra.Dual.Lemmas

theorem solution
    {K V ι : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [AddCommGroup V] [Module K V]
    (L : ι → V →ₗ[K] K) (hL : LinearIndependent K L) :
    Function.Surjective (evaluationMap L) := by
  -- Forgetting the linear-map structure is an injective linear map.
  let c : (V →ₗ[K] K) →ₗ[K] (V → K) :=
    { toFun := fun f => (f : V → K)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hc : Function.Injective c := by
    intro f g h
    exact LinearMap.coe_injective h
  have hfun : LinearIndependent K (fun i : ι => (L i : V → K)) :=
    hL.map' c (LinearMap.ker_eq_bot.mpr hc)
  -- Independence makes the evaluation vectors span the coordinate space.
  have hspan :
      Submodule.span K (Set.range (fun v : V => fun i : ι => L i v)) = ⊤ :=
    (span_flip_eq_top_iff_linearIndependent (f := fun i : ι => (L i : V → K))).2 hfun
  have hrange : (⊤ : Submodule K (ι → K)) ≤ LinearMap.range (evaluationMap L) := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro y ⟨v, rfl⟩
    exact ⟨v, rfl⟩
  exact LinearMap.range_eq_top.mp (top_unique hrange)