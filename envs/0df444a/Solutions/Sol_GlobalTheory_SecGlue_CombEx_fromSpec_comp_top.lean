-- Prove2me | solution 1 for GlobalTheory.SecGlue.CombEx.fromSpec_comp_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:37:25.297957+00:00
-- url     : https://prove2.me/submissions/d60e2573-adf2-4f4e-8fa3-0ee308d74a5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickening
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChart

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
theorem _root_.solution {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (χ : Γ(Y, V) →+* S) : (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V = ⊤ :=
  top_le_iff.1 fun _ _ => hV.range_fromSpec.subset ⟨_, rfl⟩
end GlobalTheory.SecGlue.CombEx
