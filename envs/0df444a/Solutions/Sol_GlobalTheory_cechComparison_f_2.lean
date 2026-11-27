-- Prove2me | solution 2 for GlobalTheory.cechComparison_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:36:53.214265+00:00
-- url     : https://prove2.me/submissions/5f6102a2-46f5-42dc-99b9-4f2a55a81f6a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v v' u u'
open GlobalTheory
variable {ι : Type} {R : Type u} [Ring R] {S : Type u'} [Ring S]
  (F : ModuleCat.{v} R ⥤ ModuleCat.{v'} S)
variable [LinearOrder ι] [F.Additive]
namespace GlobalTheory
theorem _root_.solution (A : Cube.{v} ι R) (p : ℕ) :
    (cechComparison F A).f p = Cube.termComparison F A (p + 1) := rfl
end GlobalTheory
