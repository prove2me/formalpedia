-- Prove2me | solution 1 for GlobalTheory.T.isAffineCombination_independent_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:41:28.72817+00:00
-- url     : https://prove2.me/submissions/c3c5a211-2e30-4f85-8efa-470be7b4e525

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationIndependentOfChart
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationIndependentOfChartStatement
import Theorems.Thm_GlobalTheory_SecGlue_isCombIn_of_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (Y : Scheme.{0}) (V V' : Y.Opens), IsAffineOpen V → IsAffineOpen V' →
    ∀ (S T : Type) [CommRing S] [CommRing T] (q : S →+* T), Function.Surjective q → RingHom.ker q ^ 2 = ⊥ →
    ∀ (ι : Type) [Fintype ι] (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S),
    (∀ i, spMap q ≫ w i = spMap q ≫ u) → GlobalTheory.SecGlue.IsCombIn V u c w a → u ⁻¹ᵁ V' = ⊤ →
    GlobalTheory.SecGlue.IsCombIn V' u c w a := by
  first | exact @GlobalTheory.SecGlue.isCombIn_of_chart | exact GlobalTheory.SecGlue.isCombIn_of_chart | (intros; apply GlobalTheory.SecGlue.isCombIn_of_chart <;> assumption)
end _root_.GlobalTheory.T
