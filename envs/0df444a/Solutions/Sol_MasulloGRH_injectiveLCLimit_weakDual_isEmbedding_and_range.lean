-- Prove2me | solution 1 for MasulloGRH.injectiveLCLimit_weakDual_isEmbedding_and_range
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:41:01.53546+00:00
-- url     : https://prove2.me/submissions/4dcf13ad-239e-4a89-a68d-e6631dab5366

import Mathlib
import Definitions.Def_RiemannMasullo_AppC_InductiveLimits

open Topology

set_option autoImplicit false

namespace Sol_MasulloGRH_injectiveLCLimit_weakDual_isEmbedding_and_range

open RiemannMasullo Set Filter

/-- Extension of a compatible family of continuous functionals on the steps to a continuous
functional on the locally convex inductive limit. -/
theorem exists_extension {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E]
    {X : ℕ → Type*} [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)]
    [∀ k, TopologicalSpace (X k)]
    {j : ∀ k, X k →L[ℂ] X (k + 1)} {i : ∀ k, X k →L[ℂ] E}
    (h : RiemannMasullo.IsInjectiveLCLimit j i)
    (l : (k : ℕ) → StrongDual ℂ (X k)) (hl : ∀ (k : ℕ) (x : X k), l (k + 1) (j k x) = l k x) :
    ∃ L : StrongDual ℂ E, ∀ (k : ℕ) (x : X k), L (i k x) = l k x := by
  classical
  -- The union of the graphs of the `l k` (transported to `E × ℂ`) is the graph of a linear
  -- functional on `E`.
  let graph (k : ℕ) : Submodule ℂ (E × ℂ) :=
    LinearMap.range ((i k).toLinearMap.prod (l k).toLinearMap)
  have hm : Monotone graph := monotone_nat_of_le_succ fun k => by
    rintro _ ⟨a, rfl⟩
    refine ⟨j k a, ?_⟩
    exact Prod.ext (DFunLike.congr_fun (h.compatible k) a) (hl k a)
  let G : Submodule ℂ (E × ℂ) := ⨆ k, graph k
  let proj : G →ₗ[ℂ] E := (LinearMap.fst ℂ E ℂ).comp G.subtype
  have hmem (k : ℕ) (x : X k) : (i k x, l k x) ∈ G := le_iSup graph k ⟨x, rfl⟩
  have hinj : Function.Injective proj := by
    apply (injective_iff_map_eq_zero _).mpr
    rintro ⟨p, hp⟩ hp0
    obtain ⟨k, a, ha⟩ := (Submodule.mem_iSup_of_directed graph hm.directed_le).mp hp
    have hp0' : p.1 = 0 := hp0
    have ha1 : i k a = p.1 := congrArg Prod.fst ha
    have ha0 : a = 0 := h.injective k (ha1.trans (hp0'.trans (map_zero (i k)).symm))
    subst ha0
    apply Subtype.ext
    change p = 0
    rw [← ha]
    exact map_zero _
  have hsurj : Function.Surjective proj := by
    intro x
    obtain ⟨k, y, rfl⟩ := h.exhaustive x
    exact ⟨⟨_, hmem k y⟩, rfl⟩
  let e : G ≃ₗ[ℂ] E := LinearEquiv.ofBijective proj ⟨hinj, hsurj⟩
  let L : E →ₗ[ℂ] ℂ := ((LinearMap.snd ℂ E ℂ).comp G.subtype).comp e.symm.toLinearMap
  have hLi (k : ℕ) (x : X k) : L (i k x) = l k x := by
    have he : e.symm (i k x) = ⟨_, hmem k x⟩ := e.symm_apply_eq.mpr rfl
    change (e.symm (i k x)).val.2 = _
    rw [he]
  -- `x ↦ ‖L x‖` is one of the seminorms defining the final locally convex topology.
  let p : Seminorm ℂ E := (normSeminorm ℂ ℂ).comp L
  have hp (k : ℕ) : Continuous (p ∘ (i k).toLinearMap) := by
    have hfun : (p ∘ (i k).toLinearMap) = fun x => ‖l k x‖ := by
      funext x
      change ‖L (i k x)‖ = ‖l k x‖
      rw [hLi]
    rw [hfun]
    exact (l k).continuous.norm
  let P : SeminormFamily ℂ E {s : Seminorm ℂ E // ∀ k, Continuous (s ∘ (i k).toLinearMap)} :=
    Subtype.val
  have hP : WithSeminorms P := ⟨h.topology_eq⟩
  have hTAG : IsTopologicalAddGroup E := hP.topologicalAddGroup
  have hL : Continuous L := by
    apply continuous_of_continuousAt_zero L
    have hn := (hP.continuous_seminorm ⟨p, hp⟩).continuousAt (x := 0)
    rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
    change Tendsto (fun x => ‖L x‖) (𝓝 0) (𝓝 ‖L 0‖) at hn
    simpa only [map_zero, norm_zero] using hn
  exact ⟨⟨L, hL⟩, hLi⟩

end Sol_MasulloGRH_injectiveLCLimit_weakDual_isEmbedding_and_range

open Sol_MasulloGRH_injectiveLCLimit_weakDual_isEmbedding_and_range in
theorem solution {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]
    [PolynormableSpace ℂ E]
    {X : ℕ → Type*} [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)]
    [∀ k, TopologicalSpace (X k)] [∀ k, IsTopologicalAddGroup (X k)]
    [∀ k, ContinuousSMul ℂ (X k)] [∀ k, T2Space (X k)] [∀ k, PolynormableSpace ℂ (X k)]
    {j : ∀ k, X k →L[ℂ] X (k + 1)} {i : ∀ k, X k →L[ℂ] E}
    (h : RiemannMasullo.IsInjectiveLCLimit j i) :
    Topology.IsEmbedding (fun (L : WeakDual ℂ E) (k : ℕ) =>
        StrongDual.toWeakDual (L.toStrongDual.comp (i k))) ∧
      Set.range (fun (L : WeakDual ℂ E) (k : ℕ) =>
        StrongDual.toWeakDual (L.toStrongDual.comp (i k))) =
        {l : ∀ k, WeakDual ℂ (X k) | ∀ (k : ℕ) (x : X k), l (k + 1) (j k x) = l k x} := by
  refine ⟨?_, ?_⟩
  · -- Every evaluation on `E` is an evaluation on one step.
    choose k x hx using h.exhaustive
    let eval (l : (k : ℕ) → WeakDual ℂ (X k)) (a : E) : ℂ := l (k a) (x a)
    have heval : Continuous eval := continuous_pi fun a =>
      (WeakDual.eval_continuous (x a)).comp (continuous_apply (k a))
    let res (L : WeakDual ℂ E) (n : ℕ) : WeakDual ℂ (X n) :=
      StrongDual.toWeakDual (L.toStrongDual.comp (i n))
    have hc : Continuous res := continuous_pi fun n =>
      WeakDual.continuous_of_continuous_eval fun y => WeakDual.eval_continuous (𝕜 := ℂ) (i n y)
    change Topology.IsEmbedding res
    refine Topology.IsEmbedding.of_comp hc heval ?_
    have heq : eval ∘ res = fun (L : WeakDual ℂ E) (a : E) => L a := by
      funext L a
      exact congrArg L (hx a)
    rw [heq]
    exact WeakBilin.isEmbedding ContinuousLinearMap.coe_injective
  · apply Set.Subset.antisymm
    · rintro _ ⟨L, rfl⟩ k y
      change L (i (k + 1) (j k y)) = L (i k y)
      exact congrArg L (DFunLike.congr_fun (h.compatible k) y)
    · intro l hl
      obtain ⟨L, hL⟩ := exists_extension h (fun k => (l k).toStrongDual) hl
      refine ⟨StrongDual.toWeakDual L, ?_⟩
      funext n
      apply DFunLike.ext
      intro y
      exact hL n y
