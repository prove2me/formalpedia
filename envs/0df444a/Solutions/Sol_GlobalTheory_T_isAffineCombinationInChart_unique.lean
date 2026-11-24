-- Prove2me | solution 1 for GlobalTheory.T.isAffineCombinationInChart_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:15:03.798421+00:00
-- url     : https://prove2.me/submissions/da68d0bf-271a-4130-80be-ef4cd3f6f46f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartUnique
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartUniqueStatement
import Theorems.Thm_GlobalTheory_SecGlue_combIn_unique


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
theorem _root_.solution : ∀ (Y : Scheme.{0}) (V : Y.Opens), IsAffineOpen V → ∀ (S : Type) [CommRing S] (ι : Type) [Fintype ι]
    (u c c' : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S),
    GlobalTheory.SecGlue.IsCombIn V u c w a → GlobalTheory.SecGlue.IsCombIn V u c' w a → c = c' := by
  first | exact @GlobalTheory.SecGlue.combIn_unique | exact GlobalTheory.SecGlue.combIn_unique | (intros; apply GlobalTheory.SecGlue.combIn_unique <;> assumption)
end _root_.GlobalTheory.T
