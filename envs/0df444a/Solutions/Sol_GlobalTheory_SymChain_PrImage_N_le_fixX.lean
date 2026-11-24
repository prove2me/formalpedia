-- Prove2me | solution 1 for GlobalTheory.SymChain.PrImage.N_le_fixX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:38:07.599993+00:00
-- url     : https://prove2.me/submissions/47b2caf1-3564-4b8d-ab43-e61bd3c39123

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainProjectedLevelOfPattern

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.SymChain GlobalTheory.SymChain.PrImage
variable {k : Type*} [Field k] {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.SymChain.PrImage
theorem _root_.solution : N k n c 1 ≤ fixX k n c := by
  refine (Subgroup.closure_le _).2 fun g hg r x => hg r (.inl x) ?_
  rcases r with r | r <;> simp [RootEx.lev]
end GlobalTheory.SymChain.PrImage
