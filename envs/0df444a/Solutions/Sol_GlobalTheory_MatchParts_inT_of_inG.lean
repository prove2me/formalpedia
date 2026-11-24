-- Prove2me | solution 1 for GlobalTheory.MatchParts.inT_of_inG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:13:26.613885+00:00
-- url     : https://prove2.me/submissions/e8b0a558-8b42-4e8d-bad3-e8799167be86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TxCosetCriterionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaRecognitionMatchedPartsDimEq
import Theorems.Thm_GlobalTheory_MatchParts_r_left
import Theorems.Thm_GlobalTheory_MatchParts_exists_rep

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
theorem _root_.solution (μ : Match N N' n) (j : ℕ)
    (hG : ∀ p p', μ.r (n ^ j) p p' → N'.InG p' → N.InG p)
    (hT : ∀ p : N.QT (n ^ j), N.InT p → ∀ p' : N.QT (n ^ j), p'.1.1 = 1 → N.wp p p' = 1)
    (hT' : ∀ p : N'.QT (n ^ j), (∀ p' : N'.QT (n ^ j), p'.1.1 = 1 → N'.wp p p' = 1) → N'.InT p)
    (p : N.QT (n ^ j)) (p' : N'.QT (n ^ j)) (h : μ.r _ p p') (hp : N.InT p) : N'.InT p' := by
  refine hT' p' fun t' ht' => ?_
  obtain ⟨t, ht⟩ := μ.cotot j t'
  obtain ⟨t₀, e, h0⟩ := exists_rep (hG t t' ht ⟨0, by simp [ht']⟩)
  rw [μ.wp _ p t₀ p' t' h (r_left μ ht e)]
  exact hT p hp t₀ h0
end GlobalTheory.MatchParts
