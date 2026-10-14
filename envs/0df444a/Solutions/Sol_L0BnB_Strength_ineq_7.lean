-- Prove2me | solution 1 for L0BnB.Strength.ineq_7
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:17:01.192286+00:00
-- url     : https://prove2.me/submissions/99cb6c7c-b7e9-4af3-aff5-442ad41a4178

import Definitions.Def_L0BnB_Strength_Penalties
import Definitions.Def_L0BnB_Strength_Relaxations
import Mathlib
import Theorems.Thm_L0BnB_Strength_eq_37

open L0BnB.Strength L0BnB.Reduced

theorem solution {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam0 lam2 M : ℝ)
    (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hregime : M < Real.sqrt (lam0 / lam2))
    (βs : Fin p → ℝ) (hβs_feas : ∀ i, |βs i| ≤ M)
    (hβs_opt : ∀ β : Fin p → ℝ, (∀ i, |β i| ≤ M) → L0BnB.Reduced.F X y lam0 lam2 M βs ≤ L0BnB.Reduced.F X y lam0 lam2 M β) :
    L0BnB.Reduced.VPR X y lam0 lam2 M ≥
      VB X y lam0 lam2 M + lam2 * (M * ∑ i, |βs i| - ∑ i, βs i ^ 2) := by
  classical
  have hleast : IsLeast (F X y lam0 lam2 M '' box p M) (F X y lam0 lam2 M βs) := by
    refine ⟨⟨βs, hβs_feas, rfl⟩, ?_⟩
    rintro _ ⟨β, hβ, rfl⟩
    exact hβs_opt β hβ
  have hv : VPR X y lam0 lam2 M = F X y lam0 lam2 M βs := hleast.csInf_eq
  have hb := (L0BnB.Strength.eq_37 X y lam0 lam2 M hlam0 hlam2 hM).2 ⟨βs, hβs_feas, rfl⟩
  have heq : F X y lam0 lam2 M βs = H X y lam0 lam2 M βs +
      lam2*(M*∑ i, |βs i| - ∑ i, βs i^2) := by
    unfold F H
    simp only [psi, not_le_of_gt hregime, ↓reduceIte, psi2]
    simp_rw [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [hv, heq]
  linarith [hb]
