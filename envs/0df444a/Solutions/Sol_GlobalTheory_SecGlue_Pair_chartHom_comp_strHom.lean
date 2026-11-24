-- Prove2me | solution 1 for GlobalTheory.SecGlue.Pair.chartHom_comp_strHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:37:29.861356+00:00
-- url     : https://prove2.me/submissions/2ef6bbb5-bd6e-4699-b8c7-00a15fbd02e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSqZeroExtendLocalizationAwayPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSquareZeroLiftBasicOpenPairAgree
import Theorems.Thm_P2M_GlobalTheory_SecGlue_Pair_spMap_comp__c0415674e1cb
import Theorems.Thm_GlobalTheory_SecGlue_Pair_chart_rebuild
import Theorems.Thm_GlobalTheory_SecGlue_Pair_fromSpec_over

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
theorem _root_.solution {R : Type} [CommRing R] (X : Over (Sp R)) {V : X.left.Opens}
    (hV : IsAffineOpen V) {S : Type} [CommRing S] (f : R →+* S) (u : Sp S ⟶ X.left) (hu : u ⁻¹ᵁ V = ⊤)
    (hf : u ≫ X.hom = spMap f) : (chartHom V u hu).comp (strHom X V) = f := by
  have e : spMap ((chartHom V u hu).comp (strHom X V)) = spMap f := by
    rw [spMap_comp', ← fromSpec_over X hV, ← Category.assoc, chart_rebuild, hf]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
end GlobalTheory.SecGlue.Pair
