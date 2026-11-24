-- Prove2me | solution 1 for GlobalTheory.SecGlue.Pair.red_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:52:53.483774+00:00
-- url     : https://prove2.me/submissions/258fa42e-073a-431b-86e1-9f84b06b299e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSqZeroExtendLocalizationAwayPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSquareZeroLiftBasicOpenPairAgree
import Theorems.Thm_P2M_GlobalTheory_SecGlue_Pair_spMap_comp__c0415674e1cb
import Theorems.Thm_GlobalTheory_SecGlue_Pair_awayMap_comp_algebraMap

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
theorem _root_.solution {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) {Y : Scheme.{0}} (g₀ : Sp R₀ ⟶ Y)
    (c d : R) (hcd : c ∣ d) (e : Sp (Localization.Away c) ⟶ Y)
    (he : spMap (Localization.awayMap π c) ≫ e = spMap (algebraMap R₀ (Localization.Away (π c))) ≫ g₀)
    (r : Localization.Away c →+* Localization.Away d)
    (hr : r.comp (algebraMap R (Localization.Away c)) = algebraMap R (Localization.Away d)) :
    spMap (Localization.awayMap π d) ≫ spMap r ≫ e =
      spMap (algebraMap R₀ (Localization.Away (π d))) ≫ g₀ := by
  have hu : IsUnit (algebraMap R₀ (Localization.Away (π d)) (π c)) :=
    isUnit_of_dvd_unit (map_dvd _ (map_dvd π hcd)) (IsLocalization.Away.algebraMap_isUnit (π d))
  let h : Localization.Away (π c) →+* Localization.Away (π d) := IsLocalization.Away.lift (π c) hu
  have e1 : (Localization.awayMap π d).comp r = h.comp (Localization.awayMap π c) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers c)
    rw [RingHom.comp_assoc, hr, awayMap_comp_algebraMap, RingHom.comp_assoc, awayMap_comp_algebraMap,
      ← RingHom.comp_assoc, IsLocalization.Away.lift_comp]
  rw [← Category.assoc, ← spMap_comp', e1, spMap_comp', Category.assoc, he, ← Category.assoc,
    ← spMap_comp', IsLocalization.Away.lift_comp]
end GlobalTheory.SecGlue.Pair
