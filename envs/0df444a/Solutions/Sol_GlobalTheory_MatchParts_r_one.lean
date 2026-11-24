-- Prove2me | solution 1 for GlobalTheory.MatchParts.r_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:46.179493+00:00
-- url     : https://prove2.me/submissions/f0de2312-ac75-47c3-a672-2715c634b921

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TxCosetCriterionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaRecognitionMatchedPartsDimEq
import Theorems.Thm_P2M_GlobalTheory_MatchParts_tot__1edb3291971f
import Theorems.Thm_GlobalTheory_MatchParts_qmul
import Theorems.Thm_GlobalTheory_Ex_NumD_qEq_equivalence


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
theorem _root_.solution (μ : Match N N' n) {k : ℕ} (hk : ∃ j, k = n ^ j) : μ.r k 1 1 := by
  obtain ⟨p', h⟩ := tot' μ hk 1
  have h2 := μ.mul k _ _ _ _ h h
  rw [mul_one] at h2
  have h3 := qmul p'⁻¹ ((r_right μ h).1 h2)
  rw [inv_mul_cancel, inv_mul_cancel_left] at h3
  exact (r_right μ h).2 ((N'.qEq_equivalence k).symm h3)
end GlobalTheory.MatchParts
