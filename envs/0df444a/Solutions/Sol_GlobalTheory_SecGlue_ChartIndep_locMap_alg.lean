-- Prove2me | solution 1 for GlobalTheory.SecGlue.ChartIndep.locMap_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:37:14.982403+00:00
-- url     : https://prove2.me/submissions/32e43bfb-074d-4493-98db-d4e52fdb0804

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartUniqueStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapCompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationIndependentOfChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SecGlue
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.ChartIndep
variable {S T : Type} [CommRing S] [CommRing T] (q : S →+* T) (s : S)
namespace GlobalTheory.SecGlue.ChartIndep
theorem _root_.solution (x : S) :
    locMap q s (algebraMap S (Localization.Away s) x) =
      algebraMap T (Localization ((Submonoid.powers s).map q)) (q x) :=
  IsLocalization.map_eq (M := Submonoid.powers s) (S := Localization.Away s)
    (T := (Submonoid.powers s).map q) _ x
end GlobalTheory.SecGlue.ChartIndep
