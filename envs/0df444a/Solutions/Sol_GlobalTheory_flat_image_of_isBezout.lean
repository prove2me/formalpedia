-- Prove2me | solution 1 for GlobalTheory.flat_image_of_isBezout
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:57:43.989331+00:00
-- url     : https://prove2.me/submissions/6ce09536-2584-4bc3-a3d5-59562e6519a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
import Theorems.Thm_GlobalTheory_flat_of_schemeDominant_of_isBezout

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
theorem _root_.solution {O : CommRingCat.{u}} [IsDomain O] [IsBezout O]
    (s : P ⟶ Spec O) [QuasiCompact j] [Flat (j ≫ s)] : Flat (j.imageι ≫ s) :=
  have : Flat (j.toImage ≫ j.imageι ≫ s) := by simpa
  flat_of_schemeDominant_of_isBezout j.toImage _
end GlobalTheory
