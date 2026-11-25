-- Prove2me | solution 1 for GlobalTheory.FiniteCover.toField_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:27:14.783522+00:00
-- url     : https://prove2.me/submissions/34c3882e-8ceb-4899-8363-373b9c4c1d62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringDominatingSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecValEqIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.FiniteCover
variable {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X']
namespace GlobalTheory.FiniteCover
theorem _root_.solution {U : X.Opens} (h : genericPoint X ∈ U) :
    Function.Injective (toField h) := germ_injective_of_isIntegral X _ h
end GlobalTheory.FiniteCover
