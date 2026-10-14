-- Prove2me | solution 1 for L0BnB.Strength.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:22:28.383982+00:00
-- url     : https://prove2.me/submissions/26272a65-b7fa-4ff0-89e3-8aa1b797d163

import Definitions.Def_L0BnB_Strength_Penalties
import Definitions.Def_L0BnB_Strength_Relaxations
import Mathlib
import Theorems.Thm_L0BnB_Strength_ineq_7
import Theorems.Thm_L0BnB_Strength_ineq_8

open L0BnB.Strength L0BnB.Reduced

theorem solution {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam0 lam2 M : ℝ)
    (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hregime : M < Real.sqrt (lam0 / lam2))
    (βs : Fin p → ℝ) (hβs_feas : ∀ i, |βs i| ≤ M)
    (hβs_opt : ∀ β : Fin p → ℝ, (∀ i, |β i| ≤ M) → L0BnB.Reduced.F X y lam0 lam2 M βs ≤ L0BnB.Reduced.F X y lam0 lam2 M β) :
    L0BnB.Reduced.VPR X y lam0 lam2 M ≥
        VB X y lam0 lam2 M + lam2 * (M * ∑ i, |βs i| - ∑ i, βs i ^ 2) ∧
      L0BnB.Reduced.VPR X y lam0 lam2 M ≥ VPRinf X y lam0 lam2 + hGap lam0 lam2 M * ∑ i, |βs i| := by
  exact ⟨ineq_7 X y lam0 lam2 M hlam0 hlam2 hM hregime βs hβs_feas hβs_opt,
    ineq_8 X y lam0 lam2 M hlam0 hlam2 hM hregime βs hβs_feas hβs_opt⟩
