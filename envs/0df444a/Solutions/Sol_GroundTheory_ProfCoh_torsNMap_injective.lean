-- Prove2me | solution 1 for GroundTheory.ProfCoh.torsNMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:05.101457+00:00
-- url     : https://prove2.me/submissions/3adc503c-cebc-418c-9cf0-6447873318e6

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
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (n : ℕ)
variable {n} (f : A →+ B) (h : B →+ C) (hh : Function.Surjective h)
variable {f h}
variable (hfh : Function.Exact f h)
include hh hfh
variable (hf : Function.Injective f)
include hf
omit hh hfh
namespace GroundTheory.ProfCoh
theorem _root_.solution : Function.Injective (torsNMap n f) := fun _ _ hxy =>
  Subtype.ext (hf (congrArg Subtype.val hxy))
end GroundTheory.ProfCoh
