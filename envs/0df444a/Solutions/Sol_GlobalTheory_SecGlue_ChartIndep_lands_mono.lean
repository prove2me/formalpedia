-- Prove2me | solution 1 for GlobalTheory.SecGlue.ChartIndep.lands_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:37:13.526504+00:00
-- url     : https://prove2.me/submissions/e42fb985-e5d1-478e-852b-07552d7e4b7e

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
namespace GlobalTheory.SecGlue.ChartIndep
theorem _root_.solution {Y : Scheme.{0}} {W V : Y.Opens} (hWV : W ≤ V) {S : Type} [CommRing S]
    (f : Sp S ⟶ Y) (hW : f ⁻¹ᵁ W = ⊤) : f ⁻¹ᵁ V = ⊤ :=
  top_le_iff.mp (hW.ge.trans (Scheme.Hom.preimage_mono f hWV))
end GlobalTheory.SecGlue.ChartIndep
