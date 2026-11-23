-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.isInvariant_iff_commute_starProjection
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:08.647121+00:00
-- url     : https://prove2.me/submissions/8498871d-47aa-4fd1-b91b-142ea6f4a034

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsInvariant_orthogonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap Filter Topology
open GroundTheory.Automorphic.UnitaryRep
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable (π : UnitaryRep G H)
variable {π}
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution (V : Submodule ℂ H) [V.HasOrthogonalProjection] :
    π.IsInvariant V ↔ ∀ g, Commute (π g) V.starProjection := by
  constructor
  · intro hV g
    ext v
    have hdec : v = V.starProjection v + (v - V.starProjection v) := by abel
    have hq : v - V.starProjection v ∈ Vᗮ := V.sub_starProjection_mem_orthogonal v
    have hp : V.starProjection v ∈ V := V.starProjection_apply_mem v
    have e1 : V.starProjection (π g v) = π g (V.starProjection v) := by
      conv_lhs => rw [hdec, map_add, map_add,
        Submodule.starProjection_eq_self_iff.mpr (hV g _ hp),
        (V.starProjection_apply_eq_zero_iff).mpr (hV.orthogonal g _ hq), add_zero]
    exact e1.symm
  · intro h g v hv
    rw [← Submodule.starProjection_eq_self_iff] at hv ⊢
    have : π g (V.starProjection v) = V.starProjection (π g v) :=
      congrArg (fun T : H →L[ℂ] H => T v) (h g)
    rw [← this, hv]
end GroundTheory.Automorphic.UnitaryRep
