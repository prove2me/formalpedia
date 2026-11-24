-- Prove2me | solution 1 for GlobalTheory.SymChain.PrImage.mul_embX_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:37:58.369428+00:00
-- url     : https://prove2.me/submissions/73ee0f6b-2f18-48e9-b1fb-21968d979084

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
theorem _root_.solution {w : GL (n ⊕ Fin c) k} (hw : w ∈ fixX k n c) (g : GL n k) (r : n ⊕ Fin c) (x : n) :
    (w * embX c g).val r (.inl x) = (embX c g).val r (.inl x) := by
  have : (w.val * (fromBlocks g.val 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)) r (.inl x) =
      ((1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * (fromBlocks g.val 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k))
        r (.inl x) := by
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, hw r, fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero]
  rw [Matrix.one_mul] at this
  exact this
end GlobalTheory.SymChain.PrImage
