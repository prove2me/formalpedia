-- Prove2me | solution 1 for GlobalTheory.isPullback_closureMap_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:41:53.593401+00:00
-- url     : https://prove2.me/submissions/f4907301-caf3-4571-9adb-22b68df358ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
noncomputable section
variable {W P T' T Z : Scheme.{u}} (j : W ⟶ P)
namespace GlobalTheory
theorem _root_.solution {W' P' : Scheme.{u}} {j' : W' ⟶ P'} {w : W' ⟶ W}
    {g : P' ⟶ P} (H : IsPullback j' w g j) [Flat g] [QuasiCompact j] :
    IsPullback j'.imageι (closureMap j' j w g H.w) g j.imageι :=
  isPullback_of_isClosedImmersion _ _ _ _ (by simp) (by simp [ker_eq_comap_of_flat j H])
end GlobalTheory
