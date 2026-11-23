-- Prove2me | solution 1 for GroundTheory.ProfCoh.connecting_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:32.107807+00:00
-- url     : https://prove2.me/submissions/6460abe1-d3bc-40d8-8395-76d8f3438607

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
namespace GroundTheory.ProfCoh
theorem _root_.solution (c : TorsN C n) (b : B) (a : A) (hb : h b = c) (ha : f a = n • b) :
    connecting hh hfh hf c = Submodule.Quotient.mk a :=
  connectingFun_spec hh hfh hf c b a hb ha
end GroundTheory.ProfCoh
