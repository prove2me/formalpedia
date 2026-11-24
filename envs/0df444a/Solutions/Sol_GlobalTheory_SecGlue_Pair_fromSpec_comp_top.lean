-- Prove2me | solution 1 for GlobalTheory.SecGlue.Pair.fromSpec_comp_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:37:13.565805+00:00
-- url     : https://prove2.me/submissions/2d466178-56fa-4f05-8db2-0ccc90bd035c

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
theorem _root_.solution {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (χ : Γ(Y, V) →+* S) : (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V = ⊤ :=
  top_le_iff.1 fun _ _ => hV.range_fromSpec.subset ⟨_, rfl⟩
end GlobalTheory.SecGlue.Pair
