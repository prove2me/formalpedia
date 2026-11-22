-- Prove2me | solution 1 for MasulloGRH.lcInductiveTopology_continuous_iff
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T11:54:58.894795+00:00
-- url     : https://prove2.me/submissions/2ebacdb6-b1f9-453c-948e-5cdaa88d2b1f

import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex

open Topology

set_option autoImplicit false

namespace Sol_MasulloGRH_lcInductiveTopology_continuous_iff

open MasulloGRH

/-- The topology induced by a linear map into a locally convex space is a locally convex
topology.  The seminorm family `q ∘ g` is re-indexed by its range so that the index type lives in
the universe of the domain. -/
theorem isLocallyConvexTopology_induced {E : Type*} [AddCommGroup E] [Module ℂ E]
    {G : Type*} [AddCommGroup G] [Module ℂ G] [tG : TopologicalSpace G]
    (hG : IsLocallyConvexTopology G tG) (g : E →ₗ[ℂ] G) :
    IsLocallyConvexTopology E (TopologicalSpace.induced g tG) := by
  obtain ⟨κ, hκ, q, hq⟩ := hG
  -- the seminorms `q k ∘ g` define the induced topology
  have hind : @WithSeminorms ℂ E κ _ _ _ (q.comp g) (TopologicalSpace.induced g tG) :=
    LinearMap.withSeminorms_induced hq g
  -- re-index by the set of these seminorms
  let p : SeminormFamily ℂ E κ := q.comp g
  let ι : Type _ := Set.range p
  have hι : Nonempty ι := ⟨⟨p hκ.some, hκ.some, rfl⟩⟩
  let p' : SeminormFamily ℂ E ι := fun i => i.1
  refine ⟨ι, hι, p', ?_⟩
  let _ : TopologicalSpace E := TopologicalSpace.induced g tG
  refine WithSeminorms.congr (p := p) (q := p') hind ?_ ?_
  · rintro ⟨_, k, rfl⟩
    refine ⟨{k}, 1, ?_⟩
    intro x
    simp [p', Seminorm.comp_id]
  · intro k
    refine ⟨{⟨p k, k, rfl⟩}, 1, ?_⟩
    intro x
    simp [p', Seminorm.comp_id]

end Sol_MasulloGRH_lcInductiveTopology_continuous_iff

open MasulloGRH

theorem solution (E : Type*)
    [AddCommGroup E] [Module ℂ E] {ι : Type*} (X : ι → Type*) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] [∀ a, TopologicalSpace (X a)] [∀ a, IsTopologicalAddGroup (X a)]
    [∀ a, ContinuousSMul ℂ (X a)] (f : ∀ a, X a →ₗ[ℂ] E)
    (G : Type*) [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    (hG : IsLocallyConvexTopology G ‹TopologicalSpace G›) (g : E →ₗ[ℂ] G) :
    @Continuous E G
        (sInf {t | IsLocallyConvexTopology E t ∧ ∀ a, @Continuous (X a) E _ t (f a)}) _ g ↔
      ∀ a, Continuous (fun x : X a => g (f a x)) := by
  constructor
  · -- every `f a` is continuous into the infimum topology, so `g ∘ f a` is continuous
    intro hg a
    have hfa : @Continuous (X a) E _
        (sInf {t | IsLocallyConvexTopology E t ∧ ∀ a, @Continuous (X a) E _ t (f a)}) (f a) :=
      continuous_sInf_rng.2 fun t ht => ht.2 a
    exact @Continuous.comp (X a) E G _
      (sInf {t | IsLocallyConvexTopology E t ∧ ∀ a, @Continuous (X a) E _ t (f a)}) _
      (fun x => f a x) (fun y => g y) hg hfa
  · -- the topology induced by `g` is locally convex and makes every `f a` continuous
    intro h
    have hmem : TopologicalSpace.induced g ‹TopologicalSpace G› ∈
        {t | IsLocallyConvexTopology E t ∧ ∀ a, @Continuous (X a) E _ t (f a)} :=
      ⟨Sol_MasulloGRH_lcInductiveTopology_continuous_iff.isLocallyConvexTopology_induced hG g,
        fun a => continuous_induced_rng.2 (h a)⟩
    exact continuous_le_dom (sInf_le hmem) continuous_induced_dom
