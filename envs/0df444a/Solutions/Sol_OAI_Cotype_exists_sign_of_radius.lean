-- Prove2me | solution 1 for OAI.Cotype.exists_sign_of_radius
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:40:07.078783+00:00
-- url     : https://prove2.me/submissions/af5e148f-31d5-44dd-ae56-9f7629921ffd

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity

open OAI OAI.Cotype
open scoped BigOperators
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
theorem t_sign {n : ℕ} {δ : ℝ}
    (h : ∀ y : Fin n → X, (∀ i, ‖y i‖ ≤ 1) →
      ∃ ε : Cube n, ‖rademacherSum X y ε‖ ≤ (n : ℝ)-δ)
    {R : ℝ} (hR : 0 ≤ R) (x : Fin n → X) (hx : ∀ i, ‖x i‖ ≤ R) :
    ∃ ε : Cube n, ‖rademacherSum X x ε‖ ≤ R*((n : ℝ)-δ) := by
  rcases hR.eq_or_lt with rfl | hR
  · have hx0 : ∀ i, x i = 0 := fun i => norm_le_zero_iff.mp (hx i)
    refine ⟨fun _ => false, ?_⟩
    simp [rademacherSum, hx0]
  · obtain ⟨ε, hε⟩ := h (fun i => R⁻¹ • x i) (fun i => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
      calc R⁻¹ * ‖x i‖ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left (hx i) (inv_nonneg.mpr hR.le)
        _ = 1 := inv_mul_cancel₀ hR.ne')
    refine ⟨ε, ?_⟩
    have e : rademacherSum X x ε = R • rademacherSum X (fun i => R⁻¹ • x i) ε := by
      simp only [rademacherSum, Finset.smul_sum, smul_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_left_comm, mul_inv_cancel₀ hR.ne', mul_one]
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    exact mul_le_mul_of_nonneg_left hε hR.le

theorem solution {n : ℕ} {δ : ℝ}
    (h : ∀ y : Fin n → X, (∀ i, ‖y i‖ ≤ 1) →
      ∃ ε : Cube n, ‖rademacherSum X y ε‖ ≤ (n : ℝ)-δ)
    {R : ℝ} (hR : 0 ≤ R) (x : Fin n → X) (hx : ∀ i, ‖x i‖ ≤ R) :
    ∃ ε : Cube n, ‖rademacherSum X x ε‖ ≤ R*((n : ℝ)-δ) := by
  exact t_sign h hR x hx

