-- Prove2me | solution 2 for OAI.Cotype.exists_sign_of_radius
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:48:04.762126+00:00
-- url     : https://prove2.me/submissions/f13a758f-3108-4f2f-b35c-511bf9a271f7

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/BConvexBlocking.lean:L11-L35
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.exists_sign_of_radius. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.Analysis.Cotype.BConvexBlocking ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem exists_sign_of_radius {n : ℕ} {δ : ℝ}
    (h : ∀ y : Fin n → X, (∀ i, ‖y i‖ ≤ 1) →
      ∃ ε : Cube n, ‖rademacherSum X y ε‖ ≤ (n : ℝ)-δ)
    {R : ℝ} (hR : 0 ≤ R) (x : Fin n → X) (hx : ∀ i, ‖x i‖ ≤ R) :
    ∃ ε : Cube n, ‖rademacherSum X x ε‖ ≤ R*((n : ℝ)-δ) := by
  by_cases hz : R = 0
  · have hx0 : ∀ i, x i = 0 := fun i => norm_eq_zero.mp (by have := hx i; rw [hz] at this; exact le_antisymm this (norm_nonneg _))
    exact ⟨fun _ => false, by simp [hz,rademacherSum,hx0]⟩
  have hRp : 0 < R := lt_of_le_of_ne hR (Ne.symm hz)
  let y : Fin n → X := fun i => R⁻¹ • x i
  have hy i : ‖y i‖ ≤ 1 := by
    rw [show y i = R⁻¹ • x i from rfl,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hRp)]
    exact (inv_mul_le_iff₀ hRp).mpr (by simpa using hx i)
  obtain ⟨ε,hε⟩ := h y hy
  have he : R • rademacherSum X y ε = rademacherSum X x ε := by
    simp only [y,rademacherSum,Finset.smul_sum,smul_smul]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    field_simp
  refine ⟨ε,?_⟩
  calc
    _ = ‖R • rademacherSum X y ε‖ := congrArg norm he.symm
    _ = R*‖rademacherSum X y ε‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hR]
    _ ≤ _ := mul_le_mul_of_nonneg_left hε hR

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.exists_sign_of_radius := @_root_.OAI.Cotype.exists_sign_of_radius
