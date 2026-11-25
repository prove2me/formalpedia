-- Prove2me | solution 1 for GroundTheory.ProfCoh.finite_torsN_of_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:24:46.162861+00:00
-- url     : https://prove2.me/submissions/43358757-882d-458d-922d-afd7fe3f07ea

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake
import Theorems.Thm_GroundTheory_ProfCoh_finite_of_exact
import Theorems.Thm_GroundTheory_ProfCoh_exact_torsNMap_torsNMap

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
theorem _root_.solution (hfh : Function.Exact f h) (hf : Function.Injective f)
    [Finite (TorsN A n)] [Finite (TorsN C n)] : Finite (TorsN B n) :=
  finite_of_exact (torsNMap n f).toAddMonoidHom (torsNMap n h).toAddMonoidHom
    (exact_torsNMap_torsNMap hfh hf)
end GroundTheory.ProfCoh
