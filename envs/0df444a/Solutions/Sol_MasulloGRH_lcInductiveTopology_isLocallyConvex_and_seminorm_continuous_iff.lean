-- Prove2me | solution 1 for MasulloGRH.lcInductiveTopology_isLocallyConvex_and_seminorm_continuous_iff
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T11:59:56.787814+00:00
-- url     : https://prove2.me/submissions/c7e5952f-9ddd-4202-b5db-9ec3bf794cb9

import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex

open Topology

set_option autoImplicit false

open MasulloGRH

theorem solution (E : Type*)
    [AddCommGroup E] [Module ℂ E] {ι : Type*} (X : ι → Type*) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] [∀ a, TopologicalSpace (X a)] [∀ a, IsTopologicalAddGroup (X a)]
    [∀ a, ContinuousSMul ℂ (X a)] (f : ∀ a, X a →ₗ[ℂ] E) :
    let t : TopologicalSpace E :=
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ a, @Continuous (X a) E _ t (f a)}
    IsLocallyConvexTopology E t ∧ (∀ a, @Continuous (X a) E _ t (f a)) ∧
      ∀ p : Seminorm ℂ E, @Continuous E ℝ t _ p ↔ ∀ a, Continuous (fun x : X a => p (f a x)) := by
  intro t
  -- the family `P` of all seminorms on `E` that are continuous on every stage
  let κ : Type _ := {p : Seminorm ℂ E // ∀ a, Continuous (fun x : X a => p (f a x))}
  have hκ : Nonempty κ := ⟨⟨0, fun a => by simpa using continuous_const⟩⟩
  let P : SeminormFamily ℂ E κ := fun i => i.1
  -- the topology `t₀` defined by the family `P`
  let t₀ : TopologicalSpace E := P.moduleFilterBasis.topology
  have hP : @WithSeminorms ℂ E κ _ _ _ P t₀ := @WithSeminorms.mk ℂ E κ _ _ _ P t₀ rfl
  have hgrp₀ : @IsTopologicalAddGroup E t₀ _ := by
    let _ : TopologicalSpace E := t₀
    exact hP.topologicalAddGroup
  -- every stage map is continuous for `t₀`
  have hf₀ : ∀ a, @Continuous (X a) E _ t₀ (f a) := by
    intro a
    let _ : TopologicalSpace E := t₀
    refine WithSeminorms.continuous_of_continuous_comp (q := P) hP (f a) ?_
    intro i
    exact i.2 a
  -- hence `t₀` is one of the topologies of which `t` is the infimum
  have hmem : t₀ ∈ {t | IsLocallyConvexTopology E t ∧ ∀ a, @Continuous (X a) E _ t (f a)} :=
    ⟨⟨κ, hκ, P, hP⟩, hf₀⟩
  have hle : t ≤ t₀ := sInf_le hmem
  -- conversely `t₀` is finer than every locally convex topology making the stage maps continuous
  have hge : t₀ ≤ t := by
    refine le_sInf ?_
    rintro s ⟨⟨κ', _, q, hq⟩, hs⟩
    -- every `q k` is `s`-continuous, hence continuous on every stage, hence a member of `P`,
    -- hence `t₀`-continuous
    have hqk : ∀ k, @Continuous E ℝ s _ (q k) := by
      intro k
      let _ : TopologicalSpace E := s
      exact hq.continuous_seminorm k
    have hstage : ∀ k a, Continuous (fun x : X a => q k (f a x)) := fun k a =>
      @Continuous.comp (X a) E ℝ _ s _ (fun x => f a x) (fun y => q k y) (hqk k) (hs a)
    have hcont : ∀ k, @Continuous E ℝ t₀ _ (q k) := by
      intro k
      let _ : TopologicalSpace E := t₀
      exact hP.continuous_seminorm ⟨q k, hstage k⟩
    have hid : @Continuous E E t₀ s (LinearMap.id : E →ₗ[ℂ] E) := by
      refine @WithSeminorms.continuous_of_continuous_comp ℂ ℂ E E κ' _ _ _ _ _ _ (RingHom.id ℂ) _ q t₀
        hgrp₀ s hq LinearMap.id ?_
      intro k
      simpa [Seminorm.comp_id] using hcont k
    exact continuous_id_iff_le.1 hid
  have heq : t = t₀ := le_antisymm hle hge
  refine ⟨?_, ?_, ?_⟩
  · rw [heq]; exact ⟨κ, hκ, P, hP⟩
  · intro a; rw [heq]; exact hf₀ a
  · intro p
    constructor
    · intro hp a
      have hfa : @Continuous (X a) E _ t (f a) := by rw [heq]; exact hf₀ a
      exact @Continuous.comp (X a) E ℝ _ t _ (fun x => f a x) (fun y => p y) hp hfa
    · intro hp
      rw [heq]
      let _ : TopologicalSpace E := t₀
      exact hP.continuous_seminorm ⟨p, hp⟩
