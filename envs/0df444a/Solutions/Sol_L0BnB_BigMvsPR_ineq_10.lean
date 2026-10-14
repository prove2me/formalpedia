-- Prove2me | solution 1 for L0BnB.BigMvsPR.ineq_10
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:12:10.244841+00:00
-- url     : https://prove2.me/submissions/611fbf5b-87ab-43ae-92dd-8624ea3c4801

import Definitions.Def_L0BnB_BigMvsPR_Penalties
import Definitions.Def_L0BnB_BigMvsPR_Relaxations
import Theorems.Thm_L0BnB_BigMvsPR_eq_37
import Mathlib

open L0BnB.BigMvsPR L0BnB.Strength L0BnB.Reduced

namespace SparseIneq10Aux

lemma penalty_nonneg (lam0 lam2 b : ℝ) (h0 : 0 ≤ lam0) : 0 ≤ psi1 lam0 lam2 b := by
  unfold psi1 reverseHuber
  split_ifs <;> positivity

lemma penalty_small (lam0 lam2 M b : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2)
    (hM : 0 < M) (hMsmall : M ≤ (1/2)*Real.sqrt (lam0/lam2)) (hb : |b| ≤ M) :
    psi1 lam0 lam2 b ≤ lam0 / M * |b| + lam2*b^2 := by
  let r := Real.sqrt (lam2/lam0)
  have hr : 0 < r := Real.sqrt_pos_of_pos (div_pos hlam2 hlam0)
  have hsr : Real.sqrt (lam0/lam2)*r = 1 := by
    dsimp [r]
    rw [← Real.sqrt_mul (div_nonneg hlam0.le hlam2.le)]
    rw [show lam0/lam2*(lam2/lam0) = 1 by field_simp]
    norm_num
  have hMr : 2*M*r ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_right hMsmall hr.le]
  have hs : |b*r| ≤ 1 := by
    rw [abs_mul, abs_of_pos hr]
    nlinarith [mul_le_mul_of_nonneg_right hb hr.le]
  have hcoef : 2*lam0*r ≤ lam0/M := by
    apply (le_div_iff₀ hM).mpr
    nlinarith [mul_le_mul_of_nonneg_left hMr hlam0.le]
  change 2*lam0*reverseHuber (b*r) ≤ _
  rw [reverseHuber, if_pos hs, abs_mul, abs_of_pos hr]
  nlinarith [mul_le_mul_of_nonneg_right hcoef (abs_nonneg b),
    mul_nonneg hlam2.le (sq_nonneg b)]

end SparseIneq10Aux

theorem solution {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam0 lam2 M : ℝ)
    (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hMsmall : M ≤ (1 / 2) * Real.sqrt (lam0 / lam2)) :
    L0BnB.Strength.VPRinf X y lam0 lam2 ≤ L0BnB.Strength.VB X y lam0 lam2 M := by
  classical
  obtain ⟨b, hb, hval⟩ := (eq_37 X y lam0 lam2 M hlam0 hlam2 hM).1
  have hbounded : BddBelow (G X y lam0 lam2 '' Set.univ) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨β, _, rfl⟩
    unfold G lsLoss
    exact add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => sq_nonneg _))
      (Finset.sum_nonneg fun i _ => SparseIneq10Aux.penalty_nonneg _ _ _ hlam0.le)
  have hle : VPRinf X y lam0 lam2 ≤ G X y lam0 lam2 b :=
    csInf_le hbounded ⟨b, Set.mem_univ _, rfl⟩
  apply hle.trans
  rw [← hval]
  unfold G H
  gcongr with i
  exact SparseIneq10Aux.penalty_small lam0 lam2 M (b i) hlam0 hlam2 hM hMsmall (hb i)
