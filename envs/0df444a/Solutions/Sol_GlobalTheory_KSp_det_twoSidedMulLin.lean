-- Prove2me | solution 1 for GlobalTheory.KSp.det_twoSidedMulLin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:25:56.729334+00:00
-- url     : https://prove2.me/submissions/81cc620f-2394-469f-a4d1-7c184035e378

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetRestrictScalarsTwoSidedMatrixMul

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
namespace GlobalTheory.KSp
theorem _root_.solution {E : Type} [Field E] {α ν : Type} [Fintype α] [DecidableEq α]
    [Fintype ν] [DecidableEq ν] (u : Matrix α α E) (a : Matrix ν ν E) :
    LinearMap.det (twoSidedMulLin u a) = u.det ^ Fintype.card ν * a.det ^ Fintype.card α := by
  let e : (α × ν → E) ≃ₗ[E] Matrix α ν E := LinearEquiv.curry E E α ν
  have h : twoSidedMulLin u a =
      (e : _ →ₗ[E] _) ∘ₗ (Matrix.toLin' (Matrix.kroneckerMap (· * ·) u a.transpose)) ∘ₗ
        (e.symm : _ →ₗ[E] _) := by
    refine LinearMap.ext fun z => ?_
    funext i j
    change (u * z * a) i j = (Matrix.kroneckerMap (· * ·) u a.transpose).mulVec (Function.uncurry z) (i, j)
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.transpose_apply, Function.uncurry_apply_pair, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    rw [show Function.uncurry z (b, c) = z b c from rfl]
    ring
  rw [h, LinearMap.det_conj, LinearMap.det_toLin', Matrix.det_kronecker, Matrix.det_transpose]
end GlobalTheory.KSp
