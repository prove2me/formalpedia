-- Prove2me | solution 1 for GroundTheory.Automorphic.fixedContragredientEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:02:55.549588+00:00
-- url     : https://prove2.me/submissions/987398a2-1f3d-49d9-968f-a2f689cb61ec

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}
variable (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
include hρ hKc hKo
namespace GroundTheory.Automorphic
theorem _root_.solution (x : fixedVectors (contragredient ρ) K) :
    fixedContragredientEquiv hρ hKc hKo x = restrictFixed ρ K x := rfl
end GroundTheory.Automorphic
