-- Prove2me | solution 1 for LpSubspaceCoreset.SmallP.lemma_2_6
-- status  : ACCEPTED   (disprove)
-- author  : @DavidDenisov
-- created : 2026-11-26T23:53:10.72832+00:00
-- url     : https://prove2.me/submissions/b646b6b6-5ba9-4641-98da-a2df3ba28992

import Definitions.Def_LpSubspaceCoreset_SmallP_Cost

set_option autoImplicit false

open LpSubspaceCoreset.SmallP

theorem solution : ¬ (∀ (p : ℝ) (k : ℕ) {n d s₀ s₁ : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (S₀ : Matrix (Fin s₀) (Fin n) ℝ) (S₁ : Matrix (Fin s₁) (Fin s₀) ℝ) (ξ₀ ξ₁ : ℝ)
    (h₀ : IsStrongCoreset p k ξ₀ A S₀) (h₁ : IsStrongCoreset p k ξ₁ (S₀ * A) S₁),
    (∀ F : Submodule ℝ (EuclideanSpace ℝ (Fin d)), InFk k F →
      (1 - ξ₀) * (1 - ξ₁) * cost p A F ≤ cost p (S₁ * (S₀ * A)) F ∧
        cost p (S₁ * (S₀ * A)) F ≤ (1 + ξ₀) * (1 + ξ₁) * cost p A F) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ξ₀ = ε / 3 → ξ₁ = ε / 3 →
      IsStrongCoreset p k ε A (S₁ * S₀)) ∧
    IsRowSampling (S₁ * S₀)) := by
  intro claimed
  let A : Matrix (Fin 1) (Fin 1) ℝ := 1
  have sampling : IsRowSampling A := by
    intro j
    fin_cases j
    exact ⟨0, by norm_num [A], fun i _ => Subsingleton.elim i 0⟩
  have unchanged : A * A = A := by simp [A]
  have strong : IsStrongCoreset 1 1 3 A A := by
    refine ⟨sampling, ?_⟩
    intro F _
    have nonneg : 0 ≤ cost 1 A F := by simp [cost]
    rw [unchanged]
    constructor <;> linarith
  have strong' : IsStrongCoreset 1 1 3 (A * A) A := unchanged.symm ▸ strong
  let F : Submodule ℝ (EuclideanSpace ℝ (Fin 1)) := ⊥
  have admissible : InFk 1 F := by simp [InFk, F]
  have positive : 0 < cost 1 A F := by
    rw [cost, Fin.sum_univ_one, Real.rpow_one]
    apply norm_pos_iff.mpr
    intro hz
    have hrow : rowVec A 0 = 0 := by simpa [resid, F] using hz
    have hentry := congrArg (fun x : EuclideanSpace ℝ (Fin 1) => x 0) hrow
    change (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 = 0 at hentry
    exact one_ne_zero (by simpa only [Matrix.one_apply_eq] using hentry)
  have lower := ((claimed 1 1 A A A 3 3 strong strong').1 F admissible).1
  simp only [unchanged] at lower
  linarith
