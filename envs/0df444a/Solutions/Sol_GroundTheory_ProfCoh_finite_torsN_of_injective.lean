-- Prove2me | solution 1 for GroundTheory.ProfCoh.finite_torsN_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:24:47.100806+00:00
-- url     : https://prove2.me/submissions/9c69bec7-e427-4610-a0e2-45b1d124af49

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake
import Theorems.Thm_GroundTheory_ProfCoh_torsNMap_injective

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
theorem _root_.solution (hf : Function.Injective f) [Finite (TorsN B n)] :
    Finite (TorsN A n) :=
  Finite.of_injective _ (torsNMap_injective hf)
end GroundTheory.ProfCoh
