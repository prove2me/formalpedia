-- Prove2me | solution 1 for GroundTheory.ProfCoh.funDiagRepresentation_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:49:33.957948+00:00
-- url     : https://prove2.me/submissions/dcecd1aa-0918-4f17-8e4b-f8d280bb903f

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_ShapiroDefs

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
universe u
variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
namespace GroundTheory.ProfCoh
theorem _root_.solution (X : Type*) [MulAction G X] (ρ : Representation k G V) (g : G)
    (F : X → V) (x : X) : funDiagRepresentation X ρ g F x = ρ g (F (g⁻¹ • x)) :=
  rfl
end GroundTheory.ProfCoh
