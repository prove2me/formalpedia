-- Prove2me | solution 1 for GlobalTheory.SymChain.PrImage.embX_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:37:41.32419+00:00
-- url     : https://prove2.me/submissions/025840f3-1202-459c-8761-75000761b8f9

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
theorem _root_.solution (g : GL n k) (r : n ⊕ Fin c) (i : Fin c) :
    (embX c g).val r (.inr i) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inr i) := by
  change (fromBlocks g.val 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inr i) = _
  rcases r with r | r <;> simp [Matrix.one_apply]
end GlobalTheory.SymChain.PrImage
