-- Prove2me | solution 1 for GroundTheory.ProfCoh.finite_modN_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:49:23.660771+00:00
-- url     : https://prove2.me/submissions/f8304fbb-3d57-4cd0-8d27-4d6176162da9

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake
import Theorems.Thm_GroundTheory_ProfCoh_modNMap_surjective

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
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] {n : ℕ}
  {f : A →+ B} {h : B →+ C}
namespace GroundTheory.ProfCoh
theorem _root_.solution (hh : Function.Surjective h) [Finite (ModN B n)] :
    Finite (ModN C n) :=
  Finite.of_surjective _ (modNMap_surjective hh)
end GroundTheory.ProfCoh
