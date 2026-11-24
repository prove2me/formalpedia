-- Prove2me | solution 1 for GlobalTheory.MatchParts.exists_rep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:40.981794+00:00
-- url     : https://prove2.me/submissions/cb82c64d-69fc-49a6-a0d5-33bf2ff7daba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TxCosetCriterionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaRecognitionMatchedPartsDimEq
import Theorems.Thm_GlobalTheory_Ex_NumD_qEq_iff


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
theorem _root_.solution {k : ℕ} {p : N.QT k} (h : N.InG p) : ∃ q, N.QEq p q ∧ q.1.1 = 1 := by
  obtain ⟨z, hz⟩ := h
  refine ⟨p * N.qTriv k (-z), (N.qEq_iff _ _).2 ⟨_, rfl⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  change p.1.1.toAdd + k • (-z) = 0
  rw [hz, smul_neg, add_neg_cancel]
end GlobalTheory.MatchParts
