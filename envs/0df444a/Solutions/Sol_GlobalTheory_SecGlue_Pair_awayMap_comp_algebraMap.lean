-- Prove2me | solution 1 for GlobalTheory.SecGlue.Pair.awayMap_comp_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:37:27.317508+00:00
-- url     : https://prove2.me/submissions/b80f1901-d947-41de-a1b5-195dc1b56f14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSqZeroExtendLocalizationAwayPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSquareZeroLiftBasicOpenPairAgree

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
theorem _root_.solution {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) (c : R) :
    (Localization.awayMap π c).comp (algebraMap R (Localization.Away c)) =
      (algebraMap R₀ (Localization.Away (π c))).comp π :=
  IsLocalization.map_comp _
end GlobalTheory.SecGlue.Pair
