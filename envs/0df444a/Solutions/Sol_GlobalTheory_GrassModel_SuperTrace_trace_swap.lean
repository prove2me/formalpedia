-- Prove2me | solution 1 for GlobalTheory.GrassModel.SuperTrace.trace_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:01:21.476846+00:00
-- url     : https://prove2.me/submissions/037dead7-5eaf-4191-8c60-6c7d23d4db21

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_VecMulVecComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TracePowGrassmannBlockCurvatureSupertraceZero
import Theorems.Thm_GlobalTheory_GrassModel_SuperTrace_sg_right
import Theorems.Thm_GlobalTheory_GrassModel_SuperTrace_msg_mul
import Theorems.Thm_GlobalTheory_GrassModel_SuperTrace_msg_pow
import Theorems.Thm_GlobalTheory_GrassModel_SuperTrace_pow_mul_left

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
open GlobalTheory GlobalTheory.GrassModel GlobalTheory.GrassModel.SuperTrace
variable {n : ℕ}
namespace GlobalTheory.GrassModel.SuperTrace
theorem _root_.solution {p q : ℕ} (A : Matrix (Fin p) (Fin q) (Big n)) (B : Matrix (Fin q) (Fin p) (Big n))
    (hA : MSg 0 A) (hB : ∀ b i, ∃ a, B b i = (1 : Ext n) ⊗ₜ vec n a) (m : ℕ) :
    ((B * A) ^ (m + 1)).trace = (-1) ^ m * ((A * B) ^ (m + 1)).trace := by
  have hB1 : MSg 1 B := by
    intro b i; obtain ⟨a, ha⟩ := hB b i; rw [ha]; exact sg_right a
  have hY : MSg m (A * (B * A) ^ m) := by
    simpa using msg_mul hA (msg_pow (by simpa using msg_mul hB1 hA) m)
  have h1 : (B * A) ^ (m + 1) = B * (A * (B * A) ^ m) := by
    rw [pow_succ', Matrix.mul_assoc]
  have h2 : (A * B) ^ (m + 1) = (A * (B * A) ^ m) * B := by
    rw [pow_succ, ← Matrix.mul_assoc, pow_mul_left]
  generalize A * (B * A) ^ m = Y at hY h1 h2
  rw [h1, h2]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
  obtain ⟨a, ha⟩ := hB b i
  rw [ha, hY i b a]
end GlobalTheory.GrassModel.SuperTrace
