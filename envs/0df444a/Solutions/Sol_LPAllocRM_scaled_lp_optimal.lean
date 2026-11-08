-- Prove2me | solution 1 for LPAllocRM.scaled_lp_optimal
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:19:06.660331+00:00
-- url     : https://prove2.me/submissions/0e32a387-ea00-4c5f-8e55-7b09ca9a0480

import Mathlib
import Definitions.Def_LPAllocRM_IsLPOptimal
open Matrix

namespace Aux_LPAllocRM_slo

theorem feas_smul {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {u : Fin n → ℝ}
    {x : Fin n → ℝ} (h : LPAllocRM.LPFeasible A b u x) {t : ℝ} (ht : 0 ≤ t) :
    LPAllocRM.LPFeasible A (t • b) (t • u) (t • x) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun i => ?_, smul_nonneg ht h2, smul_le_smul_of_nonneg_left h3 ht⟩
  rw [mulVec_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (h1 i) ht

end Aux_LPAllocRM_slo

open LPAllocRM in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ)
    (μ : Fin n → ℝ) (f : Fin n → ℝ) (xstar : Fin n → ℝ) (hx : IsLPOptimal A c μ f xstar)
    (k : ℕ+) :
    IsLPOptimal A (((k : ℕ) : ℝ) • c) (((k : ℕ) : ℝ) • μ) f (((k : ℕ) : ℝ) • xstar) ∧
      IsGreatest {z : ℝ | ∃ y : Fin n → ℝ,
          LPFeasible A (((k : ℕ) : ℝ) • c) (((k : ℕ) : ℝ) • μ) y ∧ z = f ⬝ᵥ y}
        (((k : ℕ) : ℝ) * (f ⬝ᵥ xstar)) := by
  have hk : (0 : ℝ) < ((k : ℕ) : ℝ) := by exact_mod_cast k.pos
  have hopt : IsLPOptimal A (((k : ℕ) : ℝ) • c) (((k : ℕ) : ℝ) • μ) f (((k : ℕ) : ℝ) • xstar) := by
    refine ⟨Aux_LPAllocRM_slo.feas_smul hx.1 hk.le, fun y hy => ?_⟩
    have hy' := Aux_LPAllocRM_slo.feas_smul hy (inv_nonneg.mpr hk.le)
    rw [smul_smul, smul_smul, inv_mul_cancel₀ hk.ne', one_smul, one_smul] at hy'
    have := hx.2 _ hy'
    rw [dotProduct_smul, smul_eq_mul] at this
    rw [dotProduct_smul, smul_eq_mul]
    have h2 := mul_le_mul_of_nonneg_left this hk.le
    rwa [← mul_assoc, mul_inv_cancel₀ hk.ne', one_mul] at h2
  refine ⟨hopt, ⟨((k : ℕ) : ℝ) • xstar, hopt.1, by rw [dotProduct_smul, smul_eq_mul]⟩, ?_⟩
  rintro z ⟨y, hy, rfl⟩
  have := hopt.2 y hy
  rwa [dotProduct_smul, smul_eq_mul] at this
