-- Prove2me | solution 1 for GlobalTheory.SecGlue.Pair.comp_over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:40:49.080859+00:00
-- url     : https://prove2.me/submissions/d2702d1d-fd2f-4af7-9c87-d682b93b1b02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSqZeroExtendLocalizationAwayPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSquareZeroLiftBasicOpenPairAgree
import Theorems.Thm_P2M_GlobalTheory_SecGlue_Pair_spMap_comp__c0415674e1cb

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
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.Pair
namespace GlobalTheory.SecGlue.Pair
theorem _root_.solution {Y : Scheme.{0}} {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (e : Sp B ⟶ Y)
    (p : Y ⟶ Sp A) (f : A →+* B) (he : e ≫ p = spMap f) (r : B →+* C) (g : A →+* C) (hr : r.comp f = g) :
    (spMap r ≫ e) ≫ p = spMap g := by
  rw [Category.assoc, he, ← spMap_comp', hr]
end GlobalTheory.SecGlue.Pair
