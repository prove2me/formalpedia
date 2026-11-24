-- Prove2me | solution 1 for GlobalTheory.flat_image_of_valuationRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:07:29.065941+00:00
-- url     : https://prove2.me/submissions/640608dd-a280-4f9b-92a4-846a202f6933

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
import Theorems.Thm_GlobalTheory_flat_image_of_isBezout

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
theorem _root_.solution {O : CommRingCat.{u}} [IsDomain O] [ValuationRing O]
    (s : P ⟶ Spec O) [QuasiCompact j] [Flat (j ≫ s)] : Flat (j.imageι ≫ s) :=
  flat_image_of_isBezout j s
end GlobalTheory
