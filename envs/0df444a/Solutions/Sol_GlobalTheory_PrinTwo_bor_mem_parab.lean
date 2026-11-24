-- Prove2me | solution 1 for GlobalTheory.PrinTwo.bor_mem_parab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:31:05.262862+00:00
-- url     : https://prove2.me/submissions/b5d1aa13-ffe8-4607-9ad4-8cccaf00ad5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WEMulNUMulTD
import Theorems.Thm_GlobalTheory_PrinTwo_val_bor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.PrinTwo.val_bor

set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct
open GlobalTheory GlobalTheory.PrinTwo
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.PrinTwo
theorem _root_.solution (a d : kˣ) (x : k) :
    bor a d x ∈ parab k (two (stdSum (rfl : 1 + 1 = 1 + 1))) := by
  refine mem_parab_iff.2 fun b c i j hbc => ?_
  cases b <;> cases c
  · exact absurd hbc (by decide)
  · exact absurd hbc (by decide)
  swap
  · exact absurd hbc (by decide)
  show (bor a d x : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) ((two (stdSum (rfl : 1 + 1 = 1 + 1))) ⟨true, i⟩)
    ((two (stdSum (rfl : 1 + 1 = 1 + 1))) ⟨false, j⟩) = 0
  rw [two_true, two_false, Subsingleton.elim i 0, Subsingleton.elim j 0]
  have h1 : stdSum (rfl : 1 + 1 = 1 + 1) (Sum.inr (0 : Fin 1)) = 1 := by decide
  have h0 : stdSum (rfl : 1 + 1 = 1 + 1) (Sum.inl (0 : Fin 1)) = 0 := by decide
  rw [h1, h0, val_bor]
  rfl
end GlobalTheory.PrinTwo
