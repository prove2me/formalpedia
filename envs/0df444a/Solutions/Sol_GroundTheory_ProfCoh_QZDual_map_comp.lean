-- Prove2me | solution 1 for GroundTheory.ProfCoh.QZDual.map_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:48:30.702711+00:00
-- url     : https://prove2.me/submissions/baedc2aa-af07-4c0f-96a4-28da51c640b1

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open Topology
open GroundTheory.ProfCoh.QZDual
variable {A B C : Type*} [AddCommGroup A] [TopologicalSpace A] [AddCommGroup B]
  [TopologicalSpace B] [AddCommGroup C] [TopologicalSpace C]
namespace GroundTheory.ProfCoh.QZDual
theorem _root_.solution (g : B →ₜ+ C) (f : A →ₜ+ B) :
    map (g.comp f) = (map f).comp (map g) :=
  rfl
end GroundTheory.ProfCoh.QZDual
