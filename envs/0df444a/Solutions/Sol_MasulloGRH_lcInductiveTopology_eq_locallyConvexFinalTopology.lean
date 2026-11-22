-- Prove2me | solution 1 for MasulloGRH.lcInductiveTopology_eq_locallyConvexFinalTopology
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T11:59:45.362826+00:00
-- url     : https://prove2.me/submissions/25d4e2f7-68b1-4ec4-b4c4-65833f194010

import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex
import Definitions.Def_RiemannMasullo_AppC_InductiveLimits

open Topology

set_option autoImplicit false

namespace Sol_MasulloGRH_lcInductiveTopology_eq_locallyConvexFinalTopology

/-- The family of all seminorms on `E` whose composition with every `f a` is continuous. -/
abbrev admissible {E : Type*} [AddCommGroup E] [Module ℂ E] {ι : Type*} {X : ι → Type*}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] [∀ a, TopologicalSpace (X a)]
    (f : ∀ a, X a →ₗ[ℂ] E) :
    SeminormFamily ℂ E {p : Seminorm ℂ E // ∀ a, Continuous (p ∘ f a)} :=
  Subtype.val

/-- The topology `locallyConvexFinalTopology f` is, by definition, the topology of the family of
admissible seminorms. -/
theorem withSeminorms_admissible {E : Type*} [AddCommGroup E] [Module ℂ E] {ι : Type*}
    {X : ι → Type*} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    [∀ a, TopologicalSpace (X a)] (f : ∀ a, X a →ₗ[ℂ] E) :
    @WithSeminorms ℂ E _ _ _ _ (admissible f) (RiemannMasullo.locallyConvexFinalTopology f) :=
  @WithSeminorms.mk ℂ E _ _ _ _ (admissible f) (RiemannMasullo.locallyConvexFinalTopology f) rfl

end Sol_MasulloGRH_lcInductiveTopology_eq_locallyConvexFinalTopology

open MasulloGRH
open Sol_MasulloGRH_lcInductiveTopology_eq_locallyConvexFinalTopology

theorem solution (E : Type*)
    [AddCommGroup E] [Module ℂ E] {ι : Type*} (X : ι → Type*) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] [∀ a, TopologicalSpace (X a)] [∀ a, IsTopologicalAddGroup (X a)]
    [∀ a, ContinuousSMul ℂ (X a)] (f : ∀ a, X a →ₗ[ℂ] E) :
    sInf {t | IsLocallyConvexTopology E t ∧ ∀ a, @Continuous (X a) E _ t (f a)} =
      RiemannMasullo.locallyConvexFinalTopology f := by
  have hW := withSeminorms_admissible f
  apply le_antisymm
  · -- the seminorm topology is locally convex and makes every `f a` continuous
    have hne : Nonempty {p : Seminorm ℂ E // ∀ a, Continuous (p ∘ f a)} := by
      refine ⟨⟨0, fun a => ?_⟩⟩
      have h0 : ((0 : Seminorm ℂ E) : E → ℝ) ∘ f a = fun _ => (0 : ℝ) := by
        funext x
        simp
      rw [h0]
      exact continuous_const
    have hcont : ∀ a, @Continuous (X a) E _ (RiemannMasullo.locallyConvexFinalTopology f)
        (f a) := by
      intro a
      let _ : TopologicalSpace E := RiemannMasullo.locallyConvexFinalTopology f
      refine WithSeminorms.continuous_of_continuous_comp hW (f a) fun p => ?_
      exact p.2 a
    exact sInf_le ⟨⟨_, hne, admissible f, hW⟩, hcont⟩
  · -- every seminorm of a locally convex topology making the `f a` continuous is admissible
    refine le_sInf ?_
    rintro t ⟨⟨κ, _, q, hq⟩, hf⟩
    -- the seminorms `q k` are admissible, hence continuous for the seminorm topology
    have hk : ∀ k a, Continuous ((q k : E → ℝ) ∘ f a) := by
      intro k a
      let _ : TopologicalSpace E := t
      exact (hq.continuous_seminorm k).comp (hf a)
    have hid : @Continuous E E (RiemannMasullo.locallyConvexFinalTopology f) t
        (LinearMap.id : E →ₗ[ℂ] E) := by
      let _ : TopologicalSpace E := RiemannMasullo.locallyConvexFinalTopology f
      have hgrp : IsTopologicalAddGroup E := hW.topologicalAddGroup
      refine @WithSeminorms.continuous_of_continuous_comp ℂ ℂ E E κ _ _ _ _ _ _ (RingHom.id ℂ) _ q
        _ hgrp t hq LinearMap.id fun k => ?_
      exact hW.continuous_seminorm ⟨q k, hk k⟩
    exact continuous_id_iff_le.1 hid
