-- Prove2me | solution 1 for GlobalTheory.PartRed.UpperLaw.embA_elem_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:56:35.855893+00:00
-- url     : https://prove2.me/submissions/24e2ffad-f830-47da-a205-111be10e2b62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatCompAffineMatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralCoordinateShearHaarLocalFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionUpperFreeEntryTranslationLaw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.PartRed GlobalTheory.PartRed.UpperLaw
open GlobalTheory.PartRed
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
namespace GlobalTheory.PartRed.UpperLaw
theorem _root_.solution (l m : Fin c) (h : l ≠ m) (a : k) (r s : n ⊕ Fin c) :
    (embA n (elem l m h a)).val r s
      = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s + if r = Sum.inr l ∧ s = Sum.inr m then a else 0 := by
  have : (embA n (elem l m h a)).val = fromBlocks 1 0 0 (transvection l m a) := rfl
  rw [this]
  rcases r with r | r <;> rcases s with s | s <;>
    simp [transvection, Matrix.one_apply, Matrix.single_apply, eq_comm]
end GlobalTheory.PartRed.UpperLaw
