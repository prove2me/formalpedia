-- Prove2me | solution 1 for L0BnB.Strength.ineq_8
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:17:02.803685+00:00
-- url     : https://prove2.me/submissions/5b43e865-3f17-4a88-9e1e-54fe1505796e

import Definitions.Def_L0BnB_Strength_Penalties
import Definitions.Def_L0BnB_Strength_Relaxations
import Mathlib
import Theorems.Thm_L0BnB_Strength_psi1_eq_on_box

open L0BnB.Strength L0BnB.Reduced

theorem solution {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam0 lam2 M : ℝ)
    (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hregime : M < Real.sqrt (lam0 / lam2))
    (βs : Fin p → ℝ) (hβs_feas : ∀ i, |βs i| ≤ M)
    (hβs_opt : ∀ β : Fin p → ℝ, (∀ i, |β i| ≤ M) → L0BnB.Reduced.F X y lam0 lam2 M βs ≤ L0BnB.Reduced.F X y lam0 lam2 M β) :
    L0BnB.Reduced.VPR X y lam0 lam2 M ≥ VPRinf X y lam0 lam2 + hGap lam0 lam2 M * ∑ i, |βs i| := by
  classical
  have hleast : IsLeast (F X y lam0 lam2 M '' box p M) (F X y lam0 lam2 M βs) := by
    refine ⟨⟨βs, hβs_feas, rfl⟩, ?_⟩
    rintro _ ⟨β, hβ, rfl⟩
    exact hβs_opt β hβ
  have hv : VPR X y lam0 lam2 M = F X y lam0 lam2 M βs := hleast.csInf_eq
  have hbounded : BddBelow (G X y lam0 lam2 '' Set.univ) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨β, _, rfl⟩
    apply add_nonneg
    · unfold lsLoss
      exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => sq_nonneg _)
    · apply Finset.sum_nonneg
      intro i _
      unfold psi1 reverseHuber
      split_ifs <;> positivity
  have hb : VPRinf X y lam0 lam2 ≤ G X y lam0 lam2 βs :=
    csInf_le hbounded ⟨βs, Set.mem_univ _, rfl⟩
  have hsum : (∑ i, psi1 lam0 lam2 (βs i)) =
      (2*Real.sqrt (lam0*lam2)) * ∑ i, |βs i| := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [psi1_eq_on_box lam0 lam2 M (βs i) hlam0 hlam2 hregime (hβs_feas i)]
    ring
  have heq : F X y lam0 lam2 M βs = G X y lam0 lam2 βs +
      hGap lam0 lam2 M * ∑ i, |βs i| := by
    unfold F G hGap
    rw [hsum]
    simp only [psi, not_le_of_gt hregime, ↓reduceIte, psi2]
    rw [← Finset.mul_sum]
    ring
  rw [hv, heq]
  linarith [hb]
