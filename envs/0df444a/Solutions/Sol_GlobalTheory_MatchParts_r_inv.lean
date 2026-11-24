-- Prove2me | solution 1 for GlobalTheory.MatchParts.r_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:54:28.023365+00:00
-- url     : https://prove2.me/submissions/558b3214-c8cb-4a43-b02a-9927e19209e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TxCosetCriterionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaRecognitionMatchedPartsDimEq
import Theorems.Thm_P2M_GlobalTheory_MatchParts_tot__1edb3291971f
import Theorems.Thm_GlobalTheory_MatchParts_qmul
import Theorems.Thm_GlobalTheory_MatchParts_r_one

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
theorem _root_.solution (μ : Match N N' n) {k : ℕ} (hk : ∃ j, k = n ^ j) {p : N.QT k} {p' : N'.QT k} (h : μ.r k p p') :
    μ.r k p⁻¹ p'⁻¹ := by
  obtain ⟨q', hq⟩ := tot' μ hk p⁻¹
  have h2 := μ.mul k _ _ _ _ h hq
  rw [mul_inv_cancel] at h2
  have h3 := qmul p'⁻¹ ((r_right μ h2).1 (r_one μ hk))
  rw [inv_mul_cancel_left, mul_one] at h3
  exact (r_right μ hq).2 h3
end GlobalTheory.MatchParts
