-- Prove2me | solution 1 for GlobalTheory.SecGlue.Pair.chartHom_fromSpec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:37:32.437818+00:00
-- url     : https://prove2.me/submissions/4f76b1b7-0384-49ef-add0-90240f0ea6c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSqZeroExtendLocalizationAwayPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSquareZeroLiftBasicOpenPairAgree
import Theorems.Thm_GlobalTheory_SecGlue_Pair_chart_rebuild

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
theorem _root_.solution {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (χ : Γ(Y, V) →+* S) (hc : (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V = ⊤) :
    chartHom V (spMap χ ≫ hV.fromSpec) hc = χ := by
  have e := chart_rebuild hV (spMap χ ≫ hV.fromSpec) hc
  rw [cancel_mono] at e
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
end GlobalTheory.SecGlue.Pair
