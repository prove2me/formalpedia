-- Prove2me | solution 2 for OAI.Cotype.operatorWalsh_L2_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:32:45.295802+00:00
-- url     : https://prove2.me/submissions/e897620c-8465-4905-8b46-ac610c075131

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/VectorWalsh.lean:L124-L137
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.operatorWalsh_L2_lipschitz. The node keeps its source
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

-- ---- from OAI.Analysis.Cotype.VectorWalsh ----
namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

omit [NormedSpace ℝ X] in
theorem cubeL2_add_le {n : ℕ} (f g : Cube n → X) :
    cubeL2 X (fun ε => f ε + g ε) ≤ cubeL2 X f + cubeL2 X g := by
  simp only [cubeL2_eq_piLp]
  have he : (toLp 2 (fun ε => f ε + g ε) : PiLp 2 (fun _ : Cube n => X)) =
      toLp 2 f + toLp 2 g := rfl
  rw [he, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.sqrt_nonneg _)

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

omit [NormedSpace ℝ X] in
theorem cubeL2_bound {n : ℕ} {f : Cube n → X} {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ ε, ‖f ε‖ ≤ M) : cubeL2 X f ≤ M := by
  have h := cubeL2_mono (g := fun _ : Cube n => M) (by simpa [Real.norm_eq_abs, abs_of_nonneg hM] using hf)
  simpa [cubeL2_const, Real.norm_eq_abs, abs_of_nonneg hM] using h

theorem cubeL2_clm {n : ℕ} (T : X →L[ℝ] Y) (f : Cube n → X) :
    cubeL2 Y (fun ε => T (f ε)) ≤ ‖T‖ * cubeL2 X f := by
  have hh := cubeL2_mono (g := fun ε => ‖T‖ • f ε) (fun ε => by
    simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg T)] using T.le_opNorm (f ε))
  simpa [cubeL2_smul, abs_of_nonneg (norm_nonneg T)] using hh

theorem vectorWalsh_L2_le {n : ℕ} (f : Cube n → X) :
    cubeL2 X (vectorWalsh f) ≤ cubeL2 X f :=
  cubeL2_bound (cubeL2_nonneg f) (vectorWalsh_bound f)

theorem operatorWalsh_L2_le {n : ℕ} (T : X →L[ℝ] Y) (f : Cube n → X) :
    cubeL2 Y (operatorWalsh T f) ≤ ‖T‖ * cubeL2 X f :=
  (vectorWalsh_L2_le _).trans (cubeL2_clm T f)

theorem vectorWalsh_sub {n : ℕ} (f g : Cube n → X) :
    vectorWalsh (fun ε => f ε - g ε) = fun ε => vectorWalsh f ε - vectorWalsh g ε := by
  funext ε
  simp [vectorWalsh, average, smul_sub, Finset.sum_sub_distrib]

theorem operatorWalsh_sub {n : ℕ} (A B : X →L[ℝ] Y) (f : Cube n → X) :
    operatorWalsh (A-B) f = fun v => operatorWalsh A f v - operatorWalsh B f v := by
  exact vectorWalsh_sub _ _

theorem operatorWalsh_L2_lipschitz {n : ℕ} (A B : X →L[ℝ] Y) (f : Cube n → X) :
    |cubeL2 Y (operatorWalsh A f) - cubeL2 Y (operatorWalsh B f)| ≤ ‖A-B‖ * cubeL2 X f := by
  have hA : cubeL2 Y (operatorWalsh A f) ≤ cubeL2 Y (operatorWalsh (A-B) f) +
      cubeL2 Y (operatorWalsh B f) := by
    have h := cubeL2_add_le (operatorWalsh (A-B) f) (operatorWalsh B f)
    simpa [operatorWalsh_sub] using h
  have hB : cubeL2 Y (operatorWalsh B f) ≤ cubeL2 Y (operatorWalsh (B-A) f) +
      cubeL2 Y (operatorWalsh A f) := by
    have h := cubeL2_add_le (operatorWalsh (B-A) f) (operatorWalsh A f)
    simpa [operatorWalsh_sub] using h
  have huA := operatorWalsh_L2_le (A-B) f
  have huB := operatorWalsh_L2_le (B-A) f
  rw [norm_sub_rev] at huB
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators
open WithLp


theorem solution : type_of% @_root_.OAI.Cotype.operatorWalsh_L2_lipschitz := @_root_.OAI.Cotype.operatorWalsh_L2_lipschitz
