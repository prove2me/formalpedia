-- Prove2me | solution 1 for GlobalTheory.SecGlue.CombEx.top_of_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:37:26.253355+00:00
-- url     : https://prove2.me/submissions/6a3c6b92-bab0-4838-8b35-c30e920e556f

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
theorem _root_.solution {A B Y : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ Y) (V : Y.Opens) (h : g ⁻¹ᵁ V = ⊤) :
    (f ≫ g) ⁻¹ᵁ V = ⊤ :=
  top_le_iff.1 fun x _ => h.ge (show f x ∈ (⊤ : B.Opens) from trivial)
end GlobalTheory.SecGlue.CombEx
