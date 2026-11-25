-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.IsEquivalent.isIrreducible_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:05:59.121064+00:00
-- url     : https://prove2.me/submissions/04fbb7e6-8ff5-4468-8d0f-a441a160265f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsIrreducible_of_equiv

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
variable {σ : UnitaryRep G K} {τ : UnitaryRep G L}
namespace GroundTheory.Automorphic.UnitaryRep
namespace IsEquivalent
theorem _root_.solution (h : π.IsEquivalent σ) :
    π.IsIrreducible ↔ σ.IsIrreducible :=
  ⟨fun hπ => hπ.of_equiv h.some, fun hσ => hσ.of_equiv h.some.symm⟩
end IsEquivalent
end GroundTheory.Automorphic.UnitaryRep
