-- Prove2me | solution 1 for MasulloGRH.strictLF_not_baireSpace_and_not_metrizableSpace
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:45:16.075563+00:00
-- url     : https://prove2.me/submissions/f2b5d9d1-c72f-4105-9b30-faf71f17c6b3

import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_strictLF_hlcs_and_closed_steps
import Theorems.Thm_MasulloGRH_strictLF_isCompleteTVS

open Topology

set_option autoImplicit false

namespace Sol_MasulloGRH_strictLF_not_baireSpace_and_not_metrizableSpace

open MasulloGRH

/-- A topological vector space that is complete in the sense of `IsCompleteTVS` (every Cauchy
filter for the additive uniform structure converges) and whose topology is first countable at `0`
is a Baire space: its additive uniformity is countably generated and complete, so the space is
completely pseudometrizable, and the Baire category theorem applies. -/
theorem baireSpace_of_isCompleteTVS (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] (hc : IsCompleteTVS E)
    [(𝓝 (0 : E)).IsCountablyGenerated] : BaireSpace E := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have : (uniformity E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : CompleteSpace E := by
    refine ⟨fun {f} hf => ?_⟩
    refine hc.2 f ⟨hf.1, fun U hU => ?_⟩
    have hmem : {p : E × E | p.2 - p.1 ∈ U} ∈ uniformity E := by
      rw [uniformity_eq_comap_nhds_zero E]
      exact Filter.preimage_mem_comap hU
    obtain ⟨A, hA, hAU⟩ := Filter.mem_prod_same_iff.1 (hf.2 hmem)
    refine ⟨A, hA, fun x hx y hy => ?_⟩
    have h : ((y, x) : E × E) ∈ {p : E × E | p.2 - p.1 ∈ U} := hAU (Set.mk_mem_prod hy hx)
    exact h
  infer_instance

end Sol_MasulloGRH_strictLF_not_baireSpace_and_not_metrizableSpace

open MasulloGRH Sol_MasulloGRH_strictLF_not_baireSpace_and_not_metrizableSpace

theorem solution (E : Type*) [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (hproper : ∀ n, X n ≠ ⊤) :
    ¬ BaireSpace E ∧ ¬ TopologicalSpace.MetrizableSpace E := by
  -- `E` is a Hausdorff locally convex space and every step is closed (platform theorem)
  obtain ⟨⟨⟨ι, _, p, hp⟩, _⟩, hclosed⟩ :=
    strictLF_hlcs_and_closed_steps E X hmono hexh hX htop
  have : IsTopologicalAddGroup E := hp.topologicalAddGroup
  have : ContinuousSMul ℂ E := hp.continuousSMul
  -- Baire category: countably many closed proper subspaces cannot cover a Baire space
  have hnotBaire : ¬ BaireSpace E := by
    intro hB
    have hU : ⋃ n, (X n : Set E) = Set.univ :=
      Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 (hexh x)
    obtain ⟨n, hn⟩ := nonempty_interior_of_iUnion_of_closed hclosed hU
    exact hproper n ((X n).eq_top_of_nonempty_interior' hn)
  refine ⟨hnotBaire, fun hM => hnotBaire ?_⟩
  -- a metrizable complete topological vector space is a Baire space
  have hcomplete : IsCompleteTVS E := strictLF_isCompleteTVS E ⟨X, hmono, hexh, hX, htop⟩
  exact baireSpace_of_isCompleteTVS E hcomplete
