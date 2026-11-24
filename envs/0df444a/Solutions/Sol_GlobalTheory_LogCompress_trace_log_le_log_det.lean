-- Prove2me | solution 1 for GlobalTheory.LogCompress.trace_log_le_log_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:10:25.853+00:00
-- url     : https://prove2.me/submissions/d9fcef14-d781-45b8-9d96-aee449dac33d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TraceLogLeLogDet
import Theorems.Thm_GlobalTheory_LogCompress_jensen_exp
import Theorems.Thm_GlobalTheory_LogCompress_compress_diag
import Theorems.Thm_GlobalTheory_LogCompress_exists_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.LogCompress
namespace GlobalTheory.LogCompress
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (H A : Matrix ι ι ℂ) (Q : Matrix ι κ ℂ), IsLog H A → Qᴴ * Q = 1 → (Matrix.trace (Qᴴ * H * Q)).re ≤ Real.log (Qᴴ * A * Q).det.re ∧ ((Matrix.trace (Qᴴ * H * Q)).re = Real.log (Qᴴ * A * Q).det.re → ∃ N : Matrix κ κ ℂ, A * Q = Q * N) := by
  intro ι _ _ κ _ _ H A Q ⟨U, d, hU, hH, hA⟩ hQ
  have hAh : A.IsHermitian := by
    rw [hA]
    refine Matrix.isHermitian_mul_mul_conjTranspose _ ?_
    rw [Matrix.isHermitian_diagonal_iff]
    intro i
    exact Complex.conj_ofReal _
  obtain ⟨V, m, hV, hV', hm⟩ := exists_diag _ (Matrix.isHermitian_conjTranspose_mul_mul Q hAh)
  set C : Matrix ι κ ℂ := Uᴴ * Q * V with hC
  have hCH : Cᴴ = Vᴴ * Qᴴ * U := by
    simp [hC, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have key : ∀ D : Matrix ι ι ℂ, Cᴴ * D * C = Vᴴ * (Qᴴ * (U * D * Uᴴ) * Q) * V := by
    intro D
    rw [hCH, hC]
    simp only [Matrix.mul_assoc]
  have hw : ∀ k, ∑ j, Complex.normSq (C j k) = 1 := by
    intro k
    have h := compress_diag C (fun _ => 1) k
    have h1 : diagonal (fun _ : ι => ((1 : ℝ) : ℂ)) = 1 := by simp
    rw [key, h1, Matrix.mul_one, hU, Matrix.mul_one, hQ, Matrix.mul_one, hV'] at h
    simp only [Matrix.one_apply_eq, mul_one] at h
    exact_mod_cast h.symm
  have hmk : ∀ k, m k = ((∑ j, Complex.normSq (C j k) * Real.exp (d j) : ℝ) : ℂ) := by
    intro k
    rw [← compress_diag C (fun j => Real.exp (d j)) k, key, ← hA, hm, Matrix.diagonal_apply_eq]
  have hJ := fun k => jensen_exp (fun j => Complex.normSq (C j k)) d
    (fun j => Complex.normSq_nonneg _) (hw k)
  have hdet : (Qᴴ * A * Q).det.re = ∏ k, ∑ j, Complex.normSq (C j k) * Real.exp (d j) := by
    have h := congrArg Matrix.det hm
    rw [Matrix.det_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul, Matrix.det_diagonal] at h
    rw [h]
    simp only [hmk]
    rw [← Complex.ofReal_prod, Complex.ofReal_re]
  have htr : (Matrix.trace (Qᴴ * H * Q)).re = ∑ k, ∑ j, Complex.normSq (C j k) * d j := by
    have h : Matrix.trace (Cᴴ * diagonal (fun i => (d i : ℂ)) * C) = Matrix.trace (Qᴴ * H * Q) := by
      rw [key, ← hH, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul]
    rw [← h, Matrix.trace]
    simp only [Matrix.diag_apply, compress_diag]
    rw [← Complex.ofReal_sum, Complex.ofReal_re]
  rw [hdet, htr, Real.log_prod (fun k _ => (hJ k).1.ne')]
  refine ⟨Finset.sum_le_sum fun k _ => (hJ k).2.1, fun h => ?_⟩
  have heq := (Finset.sum_eq_sum_iff_of_le fun k _ => (hJ k).2.1).1 h
  have hDC : diagonal (fun i => (Real.exp (d i) : ℂ)) * C = C * diagonal m := by
    ext j k
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases h0 : C j k = 0
    · simp [h0]
    · have := (hJ k).2.2 (heq k (Finset.mem_univ _)) j (by simpa using h0)
      rw [hmk, ← this, mul_comm]
  refine ⟨V * diagonal m * Vᴴ, ?_⟩
  have h1 : A * Q = U * (diagonal (fun i => (Real.exp (d i) : ℂ)) * C) * Vᴴ := by
    rw [hA, hC]
    simp only [Matrix.mul_assoc, hV, Matrix.mul_one]
  rw [h1, hDC, hC]
  simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]
end GlobalTheory.LogCompress
