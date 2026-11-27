-- Prove2me | solution 1 for GroundTheory.Automorphic.toDoubleContragredient_apply_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:44:24.700091+00:00
-- url     : https://prove2.me/submissions/c94e0818-52c7-48c6-9172-d99dbaa3ad58

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
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V)
variable [TopologicalSpace G] [IsTopologicalGroup G]
namespace GroundTheory.Automorphic
theorem _root_.solution (hρ : IsSmooth ρ) (v : V)
    (x : smoothVectors (Representation.dual ρ)) :
    ((toDoubleContragredient hρ v : smoothVectors (Representation.dual (contragredient ρ))) :
      Module.Dual ℂ (smoothVectors (Representation.dual ρ))) x = (x : Module.Dual ℂ V) v := rfl
end GroundTheory.Automorphic
