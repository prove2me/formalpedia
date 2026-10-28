-- Prove2me | solution 1 for L0BnB.DualGap.alphaStar_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:02:42.953715+00:00
-- url     : https://prove2.me/submissions/5d2e68aa-a6ed-4a24-b66c-aa924c77282f

import Mathlib
import Definitions.Def_L0BnB_DualGap_Setup
import Definitions.Def_L0BnB_DualGap_Duals

namespace Aux_L0BnB_alpha

open L0BnB.Reduced

lemma rh_nonneg (t : ℝ) : 0 ≤ reverseHuber t := by
  unfold reverseHuber
  split_ifs
  · exact abs_nonneg t
  · positivity

lemma psi_nonneg (lam0 lam2 M b : ℝ) (h0 : 0 < lam0) (h2 : 0 < lam2) (hM : 0 < M) :
    0 ≤ psi lam0 lam2 M b := by
  unfold psi psi1 psi2
  split_ifs
  · have := rh_nonneg (b * Real.sqrt (lam2 / lam0)); positivity
  · have : 0 ≤ lam0 / M + lam2 * M := by positivity
    exact mul_nonneg this (abs_nonneg b)

lemma psi_zero (lam0 lam2 M : ℝ) : psi lam0 lam2 M 0 = 0 := by
  unfold psi psi1 psi2 reverseHuber
  simp

end Aux_L0BnB_alpha

open L0BnB.DualGap in
theorem solution {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hy : ∑ r, y r ^ 2 = 1) (βs : Fin p → ℝ) (hβs : IsOptimal X y lam0 lam2 M βs) :
    Real.sqrt (∑ r, L0BnB.Duality.alphaStar X y βs r ^ 2) ≤ 1 := by
  have h0box : (0 : Fin p → ℝ) ∈ L0BnB.Reduced.box p M := by
    intro i; simp [hM.le]
  have hF := hβs.2 0 h0box
  have hF0 : L0BnB.Reduced.F X y lam0 lam2 M 0 = 1 / 2 := by
    unfold L0BnB.Reduced.F L0BnB.Reduced.lsLoss
    simp only [Matrix.mulVec_zero, Pi.zero_apply, sub_zero, Aux_L0BnB_alpha.psi_zero,
      Finset.sum_const_zero, add_zero, hy]
    norm_num
  have hpsi : 0 ≤ ∑ i, L0BnB.Reduced.psi lam0 lam2 M (βs i) :=
    Finset.sum_nonneg (fun i _ => Aux_L0BnB_alpha.psi_nonneg lam0 lam2 M (βs i) hlam0 hlam2 hM)
  have hsum : ∑ r, L0BnB.Duality.alphaStar X y βs r ^ 2
      = 2 * L0BnB.Reduced.lsLoss X y βs := by
    unfold L0BnB.Duality.alphaStar L0BnB.Duality.rStar L0BnB.Reduced.lsLoss
    simp only [neg_sq]
    ring
  have hle : ∑ r, L0BnB.Duality.alphaStar X y βs r ^ 2 ≤ 1 := by
    unfold L0BnB.Reduced.F at hF hF0
    rw [hsum]
    linarith
  rw [Real.sqrt_le_one]
  exact hle
