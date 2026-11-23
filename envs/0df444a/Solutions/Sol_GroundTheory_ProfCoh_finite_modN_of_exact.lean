-- Prove2me | solution 1 for GroundTheory.ProfCoh.finite_modN_of_exact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:55.437807+00:00
-- url     : https://prove2.me/submissions/85ae0fa8-a9d5-4575-a4af-957783aa8ac8

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake
import Theorems.Thm_GroundTheory_ProfCoh_finite_of_exact
import Theorems.Thm_GroundTheory_ProfCoh_exact_modNMap_modNMap

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
theorem _root_.solution (hh : Function.Surjective h) (hfh : Function.Exact f h)
    [Finite (ModN A n)] [Finite (ModN C n)] : Finite (ModN B n) :=
  finite_of_exact (modNMap n f).toAddMonoidHom (modNMap n h).toAddMonoidHom
    (exact_modNMap_modNMap hh hfh)
end GroundTheory.ProfCoh
