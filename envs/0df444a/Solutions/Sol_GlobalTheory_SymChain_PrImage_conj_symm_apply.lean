-- Prove2me | solution 1 for GlobalTheory.SymChain.PrImage.conj_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:38:08.228816+00:00
-- url     : https://prove2.me/submissions/77dbe20a-57c5-4ca9-8fd6-72cbe5c96cd6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainProjectedLevelOfPattern
import Theorems.Thm_GlobalTheory_StepData_LatFrame_conj_apply


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
theorem _root_.solution (F : LatFrame k ι (n ⊕ Fin c)) (y : GL (n ⊕ Fin c) k) :
    F.conj.symm y = (reGL F.ord).symm (F.bas⁻¹ * y * F.bas) := by
  rw [MulEquiv.symm_apply_eq, LatFrame.conj_apply]; simp [mul_assoc]
end GlobalTheory.SymChain.PrImage
