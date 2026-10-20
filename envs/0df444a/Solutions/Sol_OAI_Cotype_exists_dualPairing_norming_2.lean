-- Prove2me | solution 2 for OAI.Cotype.exists_dualPairing_norming
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:37:35.268995+00:00
-- url     : https://prove2.me/submissions/b565d7e7-39fd-4d44-ac41-30753b00c82c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/WalshDuality.lean:L48-L74
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.exists_dualPairing_norming. The node keeps its source
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

-- ---- from OAI.Analysis.Cotype.VectorWalsh ----
namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem cubeL2_smul {n : ℕ} (a : ℝ) (f : Cube n → X) :
    cubeL2 X (fun ε => a • f ε) = |a| * cubeL2 X f := by
  simp only [cubeL2_eq_piLp]
  have he : (toLp 2 (fun ε => a • f ε) : PiLp 2 (fun _ : Cube n => X)) =
      a • toLp 2 f := rfl
  rw [he, norm_smul, Real.norm_eq_abs]
  ring

omit [NormedSpace ℝ X] in
theorem cubeL2_const {n : ℕ} (x : X) : cubeL2 X (fun _ : Cube n => x) = ‖x‖ := by
  simp [cubeL2, average, smul_eq_mul, Real.sqrt_sq (norm_nonneg x)]

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] in
theorem cubeL2_mono {n : ℕ} {f : Cube n → X} {g : Cube n → Y}
    (h : ∀ ε, ‖f ε‖ ≤ ‖g ε‖) : cubeL2 X f ≤ cubeL2 Y g := by
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum (fun ε _ => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (h ε))

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.WalshDuality ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

omit [NormedSpace ℝ X] in
theorem cubeL2_norms {n : ℕ} (f : Cube n → X) :
    cubeL2 ℝ (fun u => ‖f u‖) = cubeL2 X f := by simp [cubeL2]

theorem exists_dualPairing_norming {n : ℕ} (f : Cube n → X) :
    ∃ g : Cube n → (X →L[ℝ] ℝ), cubeL2 (X →L[ℝ] ℝ) g ≤ 1 ∧
      dualPairing f g = cubeL2 X f := by
  by_cases hz : cubeL2 X f = 0
  · exact ⟨fun _ => 0, by simp [cubeL2_const], by simp [dualPairing, average, hz]⟩
  have hp : 0 < cubeL2 X f := lt_of_le_of_ne (cubeL2_nonneg f) (Ne.symm hz)
  choose g hg he0 using (fun u => exists_dual_vector'' ℝ (f u))
  have he : ∀ u, g u (f u) = ‖f u‖ := by intro u; exact_mod_cast he0 u
  let y := fun u => ((cubeL2 X f)⁻¹ * ‖f u‖) • g u
  refine ⟨y, ?_, ?_⟩
  · have h := cubeL2_mono (f := y) (g := fun u => (cubeL2 X f)⁻¹ • ‖f u‖) (fun u => by
      dsimp [y]
      rw [norm_smul]
      simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), abs_mul]
      exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (norm_nonneg _)) (hg u))
    change cubeL2 (X →L[ℝ] ℝ) y ≤
      cubeL2 ℝ (fun u => (cubeL2 X f)⁻¹ • ‖f u‖) at h
    rw [cubeL2_smul, cubeL2_norms, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hz] at h
    exact h
  · calc
      dualPairing f y = (cubeL2 X f)⁻¹ * average (fun u => ‖f u‖ ^ 2) := by
        simp only [dualPairing, y, smul_apply, smul_eq_mul, he,
          average, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        ring
      _ = cubeL2 X f := by rw [← cubeL2_sq]; field_simp

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.exists_dualPairing_norming := @_root_.OAI.Cotype.exists_dualPairing_norming
