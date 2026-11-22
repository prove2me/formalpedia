-- Prove2me | solution 1 for MasulloGRH.injectiveLCLimit_strongDual_isEmbedding_and_range
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:44:01.468324+00:00
-- url     : https://prove2.me/submissions/3971c43a-51e2-4b3e-8775-6a33fd702a2b

import Mathlib
import Definitions.Def_RiemannMasullo_AppC_InductiveLimits

open Topology

set_option autoImplicit false

namespace Sol_MasulloGRH_injectiveLCLimit_strongDual_isEmbedding_and_range

open Set Filter RiemannMasullo Bornology

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
variable {X : ℕ → Type*} [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)]
  [∀ k, TopologicalSpace (X k)] [∀ k, IsTopologicalAddGroup (X k)]
  [∀ k, ContinuousSMul ℂ (X k)]
variable {j : ∀ k, X k →L[ℂ] X (k + 1)} {i : ∀ k, X k →L[ℂ] E}

omit [ContinuousSMul ℂ E] [∀ k, IsTopologicalAddGroup (X k)] [∀ k, ContinuousSMul ℂ (X k)] in
/-- A compatible family of continuous linear functionals on the steps extends to a continuous
linear functional on the inductive limit. -/
theorem exists_extension (h : IsInjectiveLCLimit j i)
    (l : (k : ℕ) → StrongDual ℂ (X k)) (hl : ∀ k, (l (k + 1)).comp (j k) = l k) :
    ∃ L : StrongDual ℂ E, ∀ k, L.comp (i k) = l k := by
  -- The union of the stage graphs is the graph of a linear functional on E.
  let graph (k : ℕ) : Submodule ℂ (E × ℂ) :=
    LinearMap.range ((i k).toLinearMap.prod (l k).toLinearMap)
  have hm : Monotone graph := monotone_nat_of_le_succ fun k => by
    rintro _ ⟨a, rfl⟩
    refine ⟨j k a, ?_⟩
    exact Prod.ext (DFunLike.congr_fun (h.compatible k) a) (DFunLike.congr_fun (hl k) a)
  let G : Submodule ℂ (E × ℂ) := ⨆ k, graph k
  let proj : G →ₗ[ℂ] E := (LinearMap.fst ℂ E ℂ).comp G.subtype
  have hmem (k : ℕ) (x : X k) : (i k x, l k x) ∈ G := le_iSup graph k ⟨x, rfl⟩
  have hinj : Function.Injective proj := by
    apply (injective_iff_map_eq_zero _).mpr
    rintro ⟨p, hp⟩ hp0
    obtain ⟨k, a, ha⟩ := (Submodule.mem_iSup_of_directed graph hm.directed_le).mp hp
    have hp0' : p.1 = 0 := hp0
    have ha1 : i k a = p.1 := congrArg Prod.fst ha
    have ha0 : a = 0 := h.injective k ((ha1.trans hp0').trans (map_zero _).symm)
    subst ha0
    exact Subtype.ext (ha.symm.trans (map_zero _))
  have hsurj : Function.Surjective proj := by
    intro x
    obtain ⟨k, y, rfl⟩ := h.exhaustive x
    exact ⟨⟨_, hmem k y⟩, rfl⟩
  let e := LinearEquiv.ofBijective proj ⟨hinj, hsurj⟩
  let L : E →ₗ[ℂ] ℂ := ((LinearMap.snd ℂ E ℂ).comp G.subtype).comp e.symm.toLinearMap
  have hLi (k : ℕ) (x : X k) : L (i k x) = l k x := by
    have he : e.symm (i k x) = ⟨_, hmem k x⟩ := e.symm_apply_eq.mpr rfl
    change (e.symm (i k x)).val.2 = _
    rw [he]
  -- Its norm is one of the seminorms defining the final locally convex topology.
  let p : Seminorm ℂ E := (normSeminorm ℂ ℂ).comp L
  have hp (k : ℕ) : Continuous (p ∘ (i k).toLinearMap) := by
    have : (p ∘ (i k).toLinearMap) = fun x => ‖l k x‖ := by
      funext x
      change ‖L (i k x)‖ = ‖l k x‖
      rw [hLi]
    rw [this]
    exact (l k).continuous.norm
  let P : SeminormFamily ℂ E {s : Seminorm ℂ E // ∀ k, Continuous (s ∘ (i k).toLinearMap)} :=
    Subtype.val
  have hP : WithSeminorms P := ⟨h.topology_eq⟩
  have hL : Continuous L := by
    apply continuous_of_continuousAt_zero L
    have hn := (hP.continuous_seminorm ⟨p, hp⟩).continuousAt (x := 0)
    rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
    change Tendsto (fun x ↦ ‖L x‖) (𝓝 0) (𝓝 ‖L 0‖) at hn
    simpa only [map_zero, norm_zero] using hn
  exact ⟨⟨L, hL⟩, fun k ↦ ContinuousLinearMap.ext (hLi k)⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [∀ k, IsTopologicalAddGroup (X k)]
  [∀ k, ContinuousSMul ℂ (X k)] in
/-- Restriction to the steps is an embedding of strong duals when bounded sets are regular. -/
theorem isEmbedding_restrict (h : IsInjectiveLCLimit j i)
    (hreg : ∀ B : Set E, IsVonNBounded ℂ B →
      ∃ (k : ℕ) (A : Set (X k)), IsVonNBounded ℂ A ∧ B ⊆ i k '' A) :
    IsEmbedding (fun (L : StrongDual ℂ E) (k : ℕ) => L.comp (i k)) := by
  let res : StrongDual ℂ E →L[ℂ] ((k : ℕ) → StrongDual ℂ (X k)) :=
    ContinuousLinearMap.pi fun k ↦ ContinuousLinearMap.precomp ℂ (i k)
  change IsEmbedding res
  constructor
  · apply IsTopologicalAddGroup.isInducing_iff_nhds_zero.mpr
    refine le_antisymm (map_le_iff_le_comap.mp ?_) ?_
    · simpa only [Tendsto, map_zero] using res.continuous.tendsto 0
    · apply ContinuousLinearMap.hasBasis_nhds_zero.ge_iff.mpr
      rintro ⟨B, V⟩ ⟨hB, hV⟩
      obtain ⟨k, A, hA, hBA⟩ := hreg B hB
      have hA' : ∀ᶠ L : StrongDual ℂ (X k) in 𝓝 0, MapsTo L A V :=
        ContinuousLinearMap.eventually_nhds_zero_mapsTo hA hV
      have hpr := (continuous_apply k : Continuous
        (fun l : (k : ℕ) → StrongDual ℂ (X k) ↦ l k)).tendsto 0
      refine Filter.mem_comap.mpr ⟨{l | MapsTo (l k) A V}, hpr hA', ?_⟩
      intro L hL b hb
      obtain ⟨x, hx, rfl⟩ := hBA hb
      exact hL hx
  · intro L M he
    ext a
    obtain ⟨k, x, rfl⟩ := h.exhaustive a
    exact DFunLike.congr_fun (congrFun he k) x

end Sol_MasulloGRH_injectiveLCLimit_strongDual_isEmbedding_and_range

open Sol_MasulloGRH_injectiveLCLimit_strongDual_isEmbedding_and_range in
theorem solution {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]
    [PolynormableSpace ℂ E]
    {X : ℕ → Type*} [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)]
    [∀ k, TopologicalSpace (X k)] [∀ k, IsTopologicalAddGroup (X k)]
    [∀ k, ContinuousSMul ℂ (X k)] [∀ k, T2Space (X k)] [∀ k, PolynormableSpace ℂ (X k)]
    {j : ∀ k, X k →L[ℂ] X (k + 1)} {i : ∀ k, X k →L[ℂ] E}
    (h : RiemannMasullo.IsInjectiveLCLimit j i)
    (hreg : ∀ B : Set E, Bornology.IsVonNBounded ℂ B →
      ∃ (k : ℕ) (A : Set (X k)), Bornology.IsVonNBounded ℂ A ∧ B ⊆ i k '' A) :
    Topology.IsEmbedding (fun (L : StrongDual ℂ E) (k : ℕ) => L.comp (i k)) ∧
      Set.range (fun (L : StrongDual ℂ E) (k : ℕ) => L.comp (i k)) =
        {l : ∀ k, StrongDual ℂ (X k) | ∀ k : ℕ, (l (k + 1)).comp (j k) = l k} := by
  refine ⟨isEmbedding_restrict h hreg, ?_⟩
  ext l
  constructor
  · rintro ⟨L, rfl⟩ k
    change (L.comp (i (k + 1))).comp (j k) = L.comp (i k)
    rw [ContinuousLinearMap.comp_assoc, h.compatible k]
  · intro hl
    obtain ⟨L, hL⟩ := exists_extension h l hl
    exact ⟨L, funext hL⟩
