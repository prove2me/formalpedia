-- Prove2me | solution 1 for GlobalTheory.SecGlue.ChartIndep.comb_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:56:05.317809+00:00
-- url     : https://prove2.me/submissions/f1d59fc5-0ebe-4e70-89ff-9f57fd220ded

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartUniqueStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapCompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationIndependentOfChart
import Theorems.Thm_GlobalTheory_SecGlue_ChartIndep_chartHom_mono
import Theorems.Thm_GlobalTheory_SecGlue_ChartIndep_lands_mono

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
    {ι : Type} [Fintype ι] (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S)
    (h : IsCombIn W u c w a) : IsCombIn V u c w a := by
  obtain ⟨hu, hc, hw, hx⟩ := h
  refine ⟨lands_mono hWV u hu, lands_mono hWV c hc, fun i => lands_mono hWV (w i) (hw i), fun x => ?_⟩
  rw [chartHom_mono hWV c hc, chartHom_mono hWV u hu, hx]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [chartHom_mono hWV (w i) (hw i)]
end GlobalTheory.SecGlue.ChartIndep
