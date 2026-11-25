-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.orthogonalProjection_coe_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:13:50.595825+00:00
-- url     : https://prove2.me/submissions/e1104587-45a7-47eb-80b3-378e0d95375c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaSpectral
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_ExistsEqAlgebraMapOfIsSelfAdjoint
import Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaMultiplicity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ContinuousLinearMap
open scoped InnerProductSpace
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.UnitaryRep
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {π : UnitaryRep G H} {J : Type*} {V : J → Submodule ℂ H} [∀ j, CompleteSpace (V j)]
  (hinv : ∀ j, π.IsInvariant (V j))
variable (hsum : IsHilbertSum ℂ (fun j => V j) fun j => (V j).subtypeₗᵢ)
include hsum
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution {i j : J} (hij : i ≠ j) (v : V j) :
    (V i).orthogonalProjectionOnto (v : H) = 0 := by
  rw [Submodule.orthogonalProjectionOnto_eq_zero_iff, Submodule.mem_orthogonal]
  intro u hu
  exact hsum.OrthogonalFamily hij ⟨u, hu⟩ v
end GroundTheory.Automorphic.UnitaryRep
