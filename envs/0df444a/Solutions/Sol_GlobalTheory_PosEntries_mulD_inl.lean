-- Prove2me | solution 1 for GlobalTheory.PosEntries.mulD_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:12:58.880649+00:00
-- url     : https://prove2.me/submissions/2c6f7c49-2927-48a5-9655-1d0309d16f68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_RootExchangeBlockDiagonalTargetEntryConditions

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
open GlobalTheory GlobalTheory.PosEntries
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
namespace GlobalTheory.PosEntries
theorem _root_.solution (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (ϖ : kˣ) (r : n ⊕ Fin c) (y : n') :
    (x * (embA n' (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => ϖ ^ (i.val + 1))).val) r (Sum.inl y) =
      x r (Sum.inl y) := by
  simp [embA, Matrix.mul_apply, Fintype.sum_sum_type, one_apply]
end GlobalTheory.PosEntries
