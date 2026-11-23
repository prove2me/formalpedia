-- Prove2me | solution 1 for GlobalTheory.SecGlue.CombEx.chartHom_spMap_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:47:15.424611+00:00
-- url     : https://prove2.me/submissions/5537e97a-5343-4495-9389-8ff849a39a26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickening
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChart
import Theorems.Thm_GlobalTheory_SecGlue_CombEx_chart_rebuild
import Theorems.Thm_P2M_GlobalTheory_SecGlue_CombEx_spMap_comp__13427a5f2bdc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.CombEx
namespace GlobalTheory.SecGlue.CombEx
theorem _root_.solution {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S S' : Type} [CommRing S]
    [CommRing S'] (g : S →+* S') (x : Sp S ⟶ Y) (hx : x ⁻¹ᵁ V = ⊤) (h' : (spMap g ≫ x) ⁻¹ᵁ V = ⊤) :
    chartHom V (spMap g ≫ x) h' = g.comp (chartHom V x hx) := by
  have e : spMap (chartHom V (spMap g ≫ x) h') ≫ hV.fromSpec =
      spMap (g.comp (chartHom V x hx)) ≫ hV.fromSpec := by
    rw [chart_rebuild, spMap_comp', Category.assoc, chart_rebuild]
  rw [cancel_mono] at e
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
end GlobalTheory.SecGlue.CombEx
