-- Prove2me | solution 1 for GlobalTheory.KSp.pr_eq_half_trace_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:26:04.986621+00:00
-- url     : https://prove2.me/submissions/b983c7e5-944d-41a8-9008-08a4e5d78cc5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianMatrixColumnPairingDiagonalNorm

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
open GlobalTheory GlobalTheory.KSp
namespace GlobalTheory.KSp
theorem _root_.solution (F : Type) [Field F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {α : Type} [Fintype α] [DecidableEq α] {ν : Type} [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (x y : Matrix α ν E) :
  pr c Q x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by
  simp only [pr, form, GlobalTheory.WeilM.hTens, Fintype.sum_sum_type, fromCols_apply_inl, fromCols_apply_inr, stdJ, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Pi.zero_apply, Matrix.zero_apply, map_zero, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, one_apply, Matrix.trace, mul_apply, transpose_apply, map_apply, diag_apply]
  congr 2
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end GlobalTheory.KSp
