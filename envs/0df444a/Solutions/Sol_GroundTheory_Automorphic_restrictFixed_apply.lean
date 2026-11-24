-- Prove2me | solution 1 for GroundTheory.Automorphic.restrictFixed_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:52.357794+00:00
-- url     : https://prove2.me/submissions/c2ec79e7-cb37-4c8a-b344-a7af59a40962

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
theorem _root_.solution (H : Subgroup G) (x : fixedVectors (contragredient ρ) H)
    (v : fixedVectors ρ H) :
    restrictFixed ρ H x v =
      ((x : smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) v := rfl
end GroundTheory.Automorphic
