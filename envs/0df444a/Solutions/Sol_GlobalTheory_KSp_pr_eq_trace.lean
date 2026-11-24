-- Prove2me | solution 1 for GlobalTheory.KSp.pr_eq_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:24:43.461849+00:00
-- url     : https://prove2.me/submissions/d9cf1f00-15c7-4580-b4ab-dad013f24bf8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianMatrixColumnPairingAlgebraicProperties
import Theorems.Thm_GlobalTheory_SplitUnitary_hTens_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
noncomputable section
open GlobalTheory GlobalTheory.KSp
variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]
namespace GlobalTheory.KSp
theorem _root_.solution (Q : Matrix α α E) (x y : Matrix α ν E) :
    pr c Q x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by
  have h : fromCols x (0 : Matrix α ν E) * stdJ ν E * ((fromCols (0 : Matrix α ν E) y).map c)ᵀ = x * (y.map c)ᵀ := by
    ext i k
    simp [stdJ, mul_apply, Fintype.sum_sum_type, one_apply]
  rw [pr, form, hTens_eq, h]
  congr 2
  simp only [Matrix.trace, diag, mul_apply, transpose_apply]
  rw [Finset.sum_comm]
end GlobalTheory.KSp
