-- Prove2me | solution 1 for GlobalTheory.SymChain.NonZeroAt.typeFrame_bas_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:14:07.592019+00:00
-- url     : https://prove2.me/submissions/0a3b4701-76b6-4e8f-b887-1912d3938d16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_StandardOrderSymmInr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
noncomputable section
open GlobalTheory GlobalTheory.SymChain GlobalTheory.SymChain.NonZeroAt
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι ι' n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SymChain.NonZeroAt
theorem _root_.solution (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    (typeFrame ϖ ord).bas.val = diagonal (Sum.elim (fun _ => (1 : k)) fun i : Fin c => (ϖ : k) ^ (i.val + 1)) := by
  change (fromBlocks 1 0 0 (diagonal _) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) = _
  rw [← diagonal_one, fromBlocks_diagonal]
  congr 1
end GlobalTheory.SymChain.NonZeroAt
