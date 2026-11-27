-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.isEquivalent_directSum_of_isHilbertSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:44:21.576557+00:00
-- url     : https://prove2.me/submissions/5e39f448-cdfb-402d-9d54-46a38b9fbec2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_DirectSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.UnitaryRep
open scoped InnerProductSpace ENNReal
open ContinuousLinearMap
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℂ (E i)] [∀ i, CompleteSpace (E i)]
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution {π : UnitaryRep G H} {V : ι → Submodule ℂ H}
    [∀ i, CompleteSpace (V i)] (hinv : ∀ i, π.IsInvariant (V i))
    (hV : IsHilbertSum ℂ (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    π.IsEquivalent (directSum fun i => π.restrict (V i) (hinv i)) :=
  ⟨equivDirectSumOfIsHilbertSum hinv hV⟩
end GroundTheory.Automorphic.UnitaryRep
