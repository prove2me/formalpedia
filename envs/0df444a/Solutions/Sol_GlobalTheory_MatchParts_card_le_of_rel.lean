-- Prove2me | solution 1 for GlobalTheory.MatchParts.card_le_of_rel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:50.203497+00:00
-- url     : https://prove2.me/submissions/c70fab41-426b-4b7c-a2c1-aba229bbabf7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TxCosetCriterionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaRecognitionMatchedPartsDimEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.MatchParts
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ}
namespace GlobalTheory.MatchParts
theorem _root_.solution {α β : Type} [Finite β] (R : α → β → Prop) (h : ∀ a, ∃ b, R a b)
    (hi : ∀ a a' b, R a b → R a' b → a = a') : Nat.card α ≤ Nat.card β := by
  choose f hf using h
  exact Nat.card_le_card_of_injective f fun a a' e => hi a a' (f a) (hf a) (e ▸ hf a')
end GlobalTheory.MatchParts
