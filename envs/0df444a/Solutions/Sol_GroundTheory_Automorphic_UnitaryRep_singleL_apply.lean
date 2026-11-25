-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.singleL_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:17:23.127795+00:00
-- url     : https://prove2.me/submissions/a56bf9ec-71ec-4054-9436-5a27b39dce35

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
variable (ρ : ∀ i, UnitaryRep G (E i))
omit [∀ i, CompleteSpace (E i)]
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution [DecidableEq ι] (i : ι) (a : E i) : singleL i a = lp.single 2 i a := rfl
end GroundTheory.Automorphic.UnitaryRep
