-- Prove2me | solution 1 for MasulloGRH.strictLF_closed_subspace_bornological_of_limit_subspace
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T00:01:12.56577+00:00
-- url     : https://prove2.me/submissions/5f806447-028e-4259-a297-08f5533acd9c

import Theorems.Thm_MasulloGRH_bounded_in_strict_frechet_stages
import Mathlib.Analysis.LocallyConvex.ContinuousOfBounded

set_option autoImplicit false
open MasulloGRH

theorem solution
    (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hlim : (instTopologicalSpaceSubtype : TopologicalSpace V) =
        sInf {t | IsLocallyConvexTopology V t ∧
          ∀ n, @Continuous ↥(V ⊓ X n) V _ t (Submodule.inclusion inf_le_left)}) :
    IsBornological V := by
  classical
  intro p hp
  obtain ⟨hE, _⟩ := bounded_in_strict_frechet_stages E X hmono hexh hX htop
  obtain ⟨ι, _, s, hs⟩ := hE.1
  let q : SeminormFamily ℂ V V := fun _ => p
  have hq : WithSeminorms (topology := q.moduleFilterBasis.topology) q := by
    letI : TopologicalSpace V := q.moduleFilterBasis.topology
    exact ⟨rfl⟩
  have hpq : @Continuous V ℝ q.moduleFilterBasis.topology _ p := by
    letI : TopologicalSpace V := q.moduleFilterBasis.topology
    exact hq.continuous_seminorm (0 : V)
  suffices hle : (instTopologicalSpaceSubtype : TopologicalSpace V) ≤ q.moduleFilterBasis.topology from
    @Continuous.comp V V ℝ instTopologicalSpaceSubtype q.moduleFilterBasis.topology _ _ _
      hpq (continuous_id_of_le hle)
  rw [hlim]
  apply sInf_le
  refine ⟨⟨V, inferInstance, q, hq⟩, fun n => ?_⟩
  let Y : Submodule ℂ E := V ⊓ X n
  let j : Y →ₗ[ℂ] V := Submodule.inclusion inf_le_left
  let g : Y →ₗ[ℂ] X n := Submodule.inclusion inf_le_right
  have hg : Topology.IsInducing g :=
    (X n).isEmbedding_subtype.isInducing.of_comp_iff.mp Y.isEmbedding_subtype.isInducing
  letI : TopologicalSpace.MetrizableSpace (X n) := (hX n).2.2
  letI : FirstCountableTopology Y := hg.firstCountableTopology
  have hY := Y.subtype.withSeminorms_induced hs
  letI : IsTopologicalAddGroup Y := hY.topologicalAddGroup
  letI : ContinuousSMul ℂ Y := hY.continuousSMul
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  let c : Y →L[ℂ] V := ⟨j, hj⟩
  have hpb : ∀ B : Set Y, Bornology.IsVonNBounded ℂ B → BddAbove (p '' (j '' B)) :=
    fun B hB => hp _ (hB.image c)
  letI : TopologicalSpace V := q.moduleFilterBasis.topology
  letI : IsTopologicalAddGroup V := hq.topologicalAddGroup
  apply j.continuous_of_locally_bounded
  intro B hB
  apply hq.isVonNBounded_iff_seminorm_bddAbove.mpr
  intro _
  exact hpb B hB
