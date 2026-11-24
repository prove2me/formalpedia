-- Prove2me | solution 1 for GlobalTheory.MatchParts.qmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:42.068382+00:00
-- url     : https://prove2.me/submissions/1b6cf210-9c0b-4b3d-b181-418d87d4602f

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
theorem _root_.solution {k : ℕ} {p q : N.QT k} (a : N.QT k) (h : N.QEq p q) : N.QEq (a * p) (a * q) := by
  rw [N.qEq_iff] at h ⊢
  obtain ⟨z, rfl⟩ := h
  exact ⟨z, (mul_assoc _ _ _).symm⟩
end GlobalTheory.MatchParts
