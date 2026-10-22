-- Prove2me | solution 1 for IRLSM.RIP.eta_mem_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:56:22.342312+00:00
-- url     : https://prove2.me/submissions/bf193b52-2a88-4312-9610-dd53096ba62b

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic

set_option autoImplicit false
open HighDimStat.MatrixRank Matrix

theorem irr_frob_sq {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) :
    frobeniusNorm X ^ 2 = ∑ i, ∑ j, (X i j) ^ 2 := by
  unfold frobeniusNorm
  rw [Real.sq_sqrt]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

theorem irr_meas_le {n p m : ℕ} (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (X : Matrix (Fin n) (Fin p) ℝ) :
    IRLSM.Convergence.measSq A X ≤
      (∑ l, ∑ i, ∑ j, (A l i j) ^ 2) * frobeniusNorm X ^ 2 := by
  rw [irr_frob_sq, Finset.sum_mul]
  unfold IRLSM.Convergence.measSq
  refine Finset.sum_le_sum fun l _ => ?_
  unfold observationOp traceInner
  have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n × Fin p))
    (fun q => A l q.1 q.2) (fun q => X q.1 q.2)
  simpa [Fintype.sum_prod_type] using this

theorem irr_nonempty {n p m : ℕ} (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (k : ℕ) :
    {δ : ℝ | 0 ≤ δ ∧ ∀ X : Matrix (Fin n) (Fin p) ℝ, X.rank ≤ k →
      (1 - δ) * frobeniusNorm X ^ 2 ≤ IRLSM.Convergence.measSq A X ∧
        IRLSM.Convergence.measSq A X ≤ (1 + δ) * frobeniusNorm X ^ 2}.Nonempty := by
  set C : ℝ := ∑ l, ∑ i, ∑ j, (A l i j) ^ 2 with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg _
  refine ⟨C + 1, by linarith, fun X _ => ?_⟩
  have hF : 0 ≤ frobeniusNorm X ^ 2 := sq_nonneg _
  have hm0 : 0 ≤ IRLSM.Convergence.measSq A X :=
    Finset.sum_nonneg fun l _ => sq_nonneg _
  have := irr_meas_le A X
  constructor
  · nlinarith
  · nlinarith

theorem irr_mono {n p m : ℕ} (A : Fin m → Matrix (Fin n) (Fin p) ℝ) {k k' : ℕ}
    (h : k ≤ k') : IRLSM.Convergence.ripConst A k ≤ IRLSM.Convergence.ripConst A k' := by
  unfold IRLSM.Convergence.ripConst
  apply csInf_le_csInf
  · exact ⟨0, fun x hx => hx.1⟩
  · exact irr_nonempty A k'
  · intro δ hδ
    exact ⟨hδ.1, fun X hX => hδ.2 X (hX.trans h)⟩

theorem irr_nonneg {n p m : ℕ} (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (k : ℕ) :
    0 ≤ IRLSM.Convergence.ripConst A k :=
  Real.sInf_nonneg fun x hx => hx.1

theorem solution {n p m : ℕ} (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (k : ℕ)
    (hpos : 0 < IRLSM.Convergence.ripConst A (4 * k)) (h66 : IRLSM.Convergence.ripConst A (4 * k) < Real.sqrt 2 - 1) :
    0 < Real.sqrt 2 * IRLSM.Convergence.ripConst A (4 * k) / (1 - IRLSM.Convergence.ripConst A (3 * k)) ∧
      Real.sqrt 2 * IRLSM.Convergence.ripConst A (4 * k) / (1 - IRLSM.Convergence.ripConst A (3 * k)) < 1 := by
  have h34 : IRLSM.Convergence.ripConst A (3 * k) ≤ IRLSM.Convergence.ripConst A (4 * k) :=
    irr_mono A (by omega)
  have h3 := irr_nonneg A (3 * k)
  set a := IRLSM.Convergence.ripConst A (3 * k)
  set b := IRLSM.Convergence.ripConst A (4 * k)
  have s2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have s2p : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have s2lt : Real.sqrt 2 < 2 := by nlinarith
  have hpos1 : 0 < 1 - a := by linarith
  refine ⟨div_pos (mul_pos s2p hpos) hpos1, ?_⟩
  rw [div_lt_one hpos1]
  nlinarith
