-- Prove2me | solution 1 for GlobalTheory.GrassModel.trace_pow_blockPoly_add_trace_pow_neg_blockPolyBar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:20:01.223922+00:00
-- url     : https://prove2.me/submissions/2842c39b-092f-49fe-8256-c1a70c5f71af

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_VecMulVecComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TracePowGrassmannBlockCurvatureSupertraceZero
import Theorems.Thm_GlobalTheory_GrassModel_SuperTrace_sg_left
import Theorems.Thm_GlobalTheory_GrassModel_SuperTrace_trace_swap
import Theorems.Thm_GlobalTheory_GrassModel_SuperTrace_val_trace
import Theorems.Thm_GlobalTheory_GrassModel_SuperTrace_val_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial TensorProduct
open GlobalTheory.GrassModel GlobalTheory.GrassModel.SuperTrace
namespace GlobalTheory.GrassModel
theorem _root_.solution {n p q : ℕ}
    (e : Fin p × Fin q → Fin n) (k : ℕ) (hk : 1 ≤ k) :
    ((blockPoly e).map (toEven n) ^ k).trace + ((-blockPolyBar e).map (toEven n) ^ k).trace = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  set A : Matrix (Fin p) (Fin q) (Big n) := Matrix.of fun i b => vec n (e (i, b)) ⊗ₜ (1 : Ext n)
  set B : Matrix (Fin q) (Fin p) (Big n) := Matrix.of fun b j => (1 : Ext n) ⊗ₜ vec n (e (j, b))
  have hA : MSg 0 A := fun i b => sg_left _
  have hB : ∀ b i, ∃ a, B b i = (1 : Ext n) ⊗ₜ vec n a := fun b i => ⟨e (i, b), rfl⟩
  have hL : ((blockPoly e).map (toEven n)).map (EvenPart n).val = A * B := by
    ext i j
    simp [A, B, blockPoly, toEven, gen, Matrix.mul_apply, map_sum, Algebra.TensorProduct.tmul_mul_tmul]
  have hD : (Matrix.transpose ((blockPolyBar e).map (toEven n))).map (EvenPart n).val = B * A := by
    ext i j
    simp [A, B, blockPolyBar, toEven, gen, Matrix.mul_apply, map_sum, Algebra.TensorProduct.tmul_mul_tmul]
  have hneg : (-blockPolyBar e).map (toEven n) = -((blockPolyBar e).map (toEven n)) := by
    ext i j; simp
  apply Subtype.val_injective
  show (EvenPart n).val (_ + _) = (EvenPart n).val 0
  rw [map_add, map_zero, hneg, ← Matrix.trace_transpose (( -_ ) ^ _), Matrix.transpose_pow,
    Matrix.transpose_neg, val_trace, val_trace, val_pow, val_pow, hL]
  rw [show (-Matrix.transpose ((blockPolyBar e).map (toEven n))).map (EvenPart n).val = -(B * A) by
    rw [← hD]; ext i j; simp]
  rcases Nat.even_or_odd (m + 1) with h | h
  · rw [h.neg_pow, trace_swap A B hA hB m]
    have : Odd m := by rcases h with ⟨t, ht⟩; exact ⟨t - 1, by omega⟩
    rw [this.neg_one_pow]; simp
  · rw [h.neg_pow, Matrix.trace_neg, trace_swap A B hA hB m]
    have : Even m := by rcases h with ⟨t, ht⟩; exact ⟨t, by omega⟩
    rw [this.neg_one_pow]; simp
end GlobalTheory.GrassModel
