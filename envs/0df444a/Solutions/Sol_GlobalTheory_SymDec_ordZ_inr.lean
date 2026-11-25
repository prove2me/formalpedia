-- Prove2me | solution 1 for GlobalTheory.SymDec.ordZ_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:26:58.074622+00:00
-- url     : https://prove2.me/submissions/4d7cbe4e-6791-485d-a961-f3ed339f76c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPattern
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TypeFrameConjugationDecomposition
import Theorems.Thm_GlobalTheory_StepData_standardOrderExtendedBasis_apply_low_block


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.SymDec
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
variable {k : Type} [Field k] {κ c : ℕ} (t : Type) [Fintype t] [DecidableEq t]
namespace GlobalTheory.SymDec
theorem _root_.solution (hc : 0 + c = c) (i : Fin c) : ordZ (κ := κ) t hc (Sum.inr i) = Sum.inr i := by
  have h := standardOrderExtendedBasis_apply_low_block (Fin κ) t 0 c hc i
  simp only [Fin.eta] at h
  exact h
end GlobalTheory.SymDec
