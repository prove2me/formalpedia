-- Prove2me | solution 1 for GroundTheory.ProfCoh.finite_of_exact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:32.327541+00:00
-- url     : https://prove2.me/submissions/9e9459b3-2dca-4ffb-a265-6adfd00f07ca

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake

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
universe u v
open Representation
namespace GroundTheory.ProfCoh
theorem _root_.solution {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    (f : X →+ Y) (g : Y →+ Z) (hfg : Function.Exact f g) [Finite X] [Finite Z] : Finite Y := by
  refine (AddMonoidHom.finite_iff_finite_ker_range g).2 ⟨?_, inferInstance⟩
  have hs : (g.ker : Set Y) ⊆ Set.range f := fun y hy => (hfg y).1 hy
  exact ((Set.finite_range f).subset hs).to_subtype
end GroundTheory.ProfCoh
