-- Prove2me | solution 1 for GlobalTheory.gaussian_pairing_moment_algebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:59:06.446463+00:00
-- url     : https://prove2.me/submissions/f0dc08ec-9d40-4f3e-9865-212a2070a0dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GaussianPairingMomentAlgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (S T : Matrix σ σ ℂ) (x y : σ → ℂ) (t f : ℂ) (p q : σ → ℂ) (m n : Matrix σ σ ℂ), Sᵀ = S → Tᵀ = T → IsUnit (1 - (t ^ 2) • (T * S)).det → p = t • (f • y + T *ᵥ q) → q = t • (f • x + S *ᵥ p) → m = (t * f) • (1 : Matrix σ σ ℂ) + t • vecMulVec y q + t • (T * n) → n = t • vecMulVec x q + t • (S * m) → let w : σ → ℂ := (1 - (t ^ 2) • (T * S))⁻¹ *ᵥ (y + t • T *ᵥ x); let u : σ → ℂ := x + t • S *ᵥ w; f * (x ⬝ᵥ y) + x ⬝ᵥ T *ᵥ q + y ⬝ᵥ S *ᵥ p + (S * m * Tᵀ).trace = f * (u ⬝ᵥ w + t * (T * S * (1 - (t ^ 2) • (T * S))⁻¹).trace) := by
  intro σ _ _ S T x y t f p q m n hS hT hA hp hq hm hn w u
  set A : Matrix σ σ ℂ := 1 - (t ^ 2) • (T * S) with hAdef
  have hKA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
  have hAK : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
  have hAv : ∀ v : σ → ℂ, A *ᵥ v = v - (t ^ 2) • T *ᵥ (S *ᵥ v) := by
    intro v
    rw [hAdef, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.mulVec_mulVec]
  have hAp : A *ᵥ p = (t * f) • (y + t • T *ᵥ x) := by
    have h1 : p = t • (f • y + T *ᵥ (t • (f • x + S *ᵥ p))) := by rw [← hq]; exact hp
    rw [hAv]
    rw [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul] at h1
    rw [sub_eq_iff_eq_add]
    refine h1.trans ?_
    module
  have hpw : p = (t * f) • w := by
    have : p = A⁻¹ *ᵥ (A *ᵥ p) := by rw [Matrix.mulVec_mulVec, hKA, Matrix.one_mulVec]
    rw [this, hAp, Matrix.mulVec_smul]
  have hqu : q = (t * f) • u := by
    rw [hq, hpw, Matrix.mulVec_smul]
    simp only [u]
    module
  have hAw : A *ᵥ w = y + t • T *ᵥ x := by
    simp only [w]
    rw [Matrix.mulVec_mulVec, hAK, Matrix.one_mulVec]
  have hw : w = y + t • T *ᵥ u := by
    rw [hAv, sub_eq_iff_eq_add] at hAw
    refine hAw.trans ?_
    simp only [u]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul]
    module
  have hAm : A * m = (t * f) • (1 : Matrix σ σ ℂ) + t • vecMulVec (y + t • T *ᵥ x) q := by
    have h1 : m = (t * f) • (1 : Matrix σ σ ℂ) + t • vecMulVec y q
        + t • (T * (t • vecMulVec x q + t • (S * m))) := by rw [← hn]; exact hm
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_vecMulVec,
      ← Matrix.mul_assoc] at h1
    rw [hAdef, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, sub_eq_iff_eq_add,
      Matrix.add_vecMulVec, Matrix.smul_vecMulVec]
    refine h1.trans ?_
    module
  have hmK : m = (t * f) • A⁻¹ + t • vecMulVec w q := by
    have : m = A⁻¹ * (A * m) := by rw [← Matrix.mul_assoc, hKA, Matrix.one_mul]
    rw [this, hAm, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.mul_vecMulVec]
  have htr : (S * m * Tᵀ).trace
      = (t * f) * (T * S * A⁻¹).trace + t * ((S *ᵥ w) ⬝ᵥ (T *ᵥ q)) := by
    rw [hmK, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.trace_vecMulVec, Matrix.vecMul_transpose,
      hT, Matrix.trace_mul_comm (S * A⁻¹) T, Matrix.mul_assoc T S, smul_eq_mul, smul_eq_mul]
  have huw : u ⬝ᵥ w = x ⬝ᵥ y + t * (x ⬝ᵥ T *ᵥ u) + t * (y ⬝ᵥ S *ᵥ w)
      + t ^ 2 * ((S *ᵥ w) ⬝ᵥ (T *ᵥ u)) := by
    have h1 : u ⬝ᵥ w = (x + t • S *ᵥ w) ⬝ᵥ (y + t • T *ᵥ u) := by rw [← hw]
    rw [h1]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm (S *ᵥ w) y]
    ring
  rw [htr, huw, hqu, hpw]
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  ring
end GlobalTheory
