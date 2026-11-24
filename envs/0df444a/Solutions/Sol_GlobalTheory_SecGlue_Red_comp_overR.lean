-- Prove2me | solution 1 for GlobalTheory.SecGlue.Red.comp_overR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:37:25.587886+00:00
-- url     : https://prove2.me/submissions/3b2a5190-a9e8-42f2-a89b-9dcb069dfaf3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AwayMapEqOfRed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationIndependentOfChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapCompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AlgHomEqMulPowOfEqLocalizationAwayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPowCocycle
import Theorems.Thm_GlobalTheory_SecGlue_Red_spMap_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.Red
namespace GlobalTheory.SecGlue.Red
theorem _root_.solution {R : Type} [CommRing R] (X : Over (Sp R)) (a : R) {S : Type} [CommRing S] [Algebra R S]
    (ρ : Localization.Away a →+* S) (hρ : ρ.comp (algebraMap R _) = algebraMap R S)
    (u : Sp (Localization.Away a) ⟶ X.left) (hu : u ≫ X.hom = spMap (algebraMap R _)) :
    (spMap ρ ≫ u) ≫ X.hom = spMap (algebraMap R S) := by
  rw [Category.assoc, hu, ← spMap_comp, hρ]
end GlobalTheory.SecGlue.Red
