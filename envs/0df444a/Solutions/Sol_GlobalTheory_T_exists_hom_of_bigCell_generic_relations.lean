-- Prove2me | solution 1 for GlobalTheory.T.exists_hom_of_bigCell_generic_relations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:25:01.973996+00:00
-- url     : https://prove2.me/submissions/eac023a4-2879-4079-b906-a9922960609d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHomOfBigCellGenericRelations
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHomOfBigCellGenericRelationsStatement
import Theorems.Thm_GlobalTheory_bigCell_hom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G H : Type) [Group G] [Group H] (P : Subgroup G) (w : G) (ρ : P →* H) (W : H), (∀ p q : P, w * p = q * w → W * ρ p = ρ q * W) → (∀ p : P, (∃ p₁ p₂ : P, w * p * w = p₁ * w * p₂) → ∃ p₁ p₂ : P, w * p * w = p₁ * w * p₂ ∧ W * ρ p * W = ρ p₁ * W * ρ p₂) → (∀ s : Finset G, ∃ u : G, ∀ g ∈ s, ∃ p₁ p₂ : P, g * u = p₁ * w * p₂) → ∃ Φ : G →* H, (∀ p : P, Φ p = ρ p) ∧ Φ w = W := by
  first | exact @GlobalTheory.bigCell_hom | exact GlobalTheory.bigCell_hom | (intros; apply GlobalTheory.bigCell_hom <;> assumption)
end _root_.GlobalTheory.T
