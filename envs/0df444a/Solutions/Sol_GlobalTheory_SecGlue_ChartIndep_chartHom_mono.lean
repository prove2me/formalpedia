-- Prove2me | solution 1 for GlobalTheory.SecGlue.ChartIndep.chartHom_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:41:11.6068+00:00
-- url     : https://prove2.me/submissions/780a5eb3-c16d-484e-a679-217602411e05

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
    (f : Sp S ⟶ Y) (hW : f ⁻¹ᵁ W = ⊤) (hV : f ⁻¹ᵁ V = ⊤) (x : Γ(Y, V)) :
    chartHom V f hV x = chartHom W f hW (Y.presheaf.map (homOfLE hWV).op x) := by
  unfold chartHom
  rw [← Scheme.Hom.map_appLE f hW.ge (homOfLE hWV).op]
  rfl
end GlobalTheory.SecGlue.ChartIndep
