-- Prove2me | solution 1 for GlobalTheory.unramExt_law
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:44:31.834044+00:00
-- url     : https://prove2.me/submissions/1a6d86cf-2196-4027-88d3-9616a99c2456

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFiniteEtaleLocalSurjectiveOfIsSeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_UnramExtLaw
import Theorems.Thm_GlobalTheory_unramExt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : UnramExtSt := unramExt
end GlobalTheory
