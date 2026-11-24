-- Prove2me | solution 1 for GlobalTheory.SliceTaylor.elim_add_padL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:49:08.580175+00:00
-- url     : https://prove2.me/submissions/547eb6ad-2fe7-406e-96bd-5c76e7067030

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormTranslateSubLineDerivLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivPdLe
import Theorems.Thm_GlobalTheory_SliceSchwartz_sliceR_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SliceSchwartz.sliceR_apply



set_option autoImplicit false
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.SliceTaylor
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace GlobalTheory.SliceTaylor
theorem _root_.solution {κ κ' : Type} [Fintype κ] [Fintype κ'] (x h : κ → V) (y : κ' → V) :
    (Sum.elim (x + h) y : κ ⊕ κ' → V) = Sum.elim x y + padL h := by
  funext i
  cases i with
  | inl i => simp [padL]
  | inr j => simp [padL]
end GlobalTheory.SliceTaylor
