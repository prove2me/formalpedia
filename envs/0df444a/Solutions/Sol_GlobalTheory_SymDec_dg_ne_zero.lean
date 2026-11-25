-- Prove2me | solution 1 for GlobalTheory.SymDec.dg_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:24:46.85823+00:00
-- url     : https://prove2.me/submissions/26561f91-7046-4072-ab6a-6b9d00e746ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPattern
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TypeFrameConjugationDecomposition

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
variable {k : Type} [Field k] {ι n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.SymDec
theorem _root_.solution (ϖ : kˣ) (r : n ⊕ Fin c) : dg ϖ r ≠ 0 := by
  rcases r with r | r <;> simp [dg]
end GlobalTheory.SymDec
