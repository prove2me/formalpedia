-- Prove2me | solution 2 for OAI.Cotype.rademacher_L2_le_four_L1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:26:02.110331+00:00
-- url     : https://prove2.me/submissions/eb763a3c-43cb-41e2-90e6-14aa20801d3f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/RademacherComparison.lean:L72-L94
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.rademacher_L2_le_four_L1. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour
import Definitions.Def_OAI_Analysis_Cotype_NoiseHypercontractivity
import Definitions.Def_OAI_Analysis_Cotype_QuadraticTypeTensor
import Theorems.Thm_OAI_Cotype_average_norm_mul_le
import Theorems.Thm_OAI_Cotype_cubeNoise_fourth_le
import Theorems.Thm_OAI_Cotype_cubeNoise_norm_le

-- ---- from OAI.Analysis.Cotype.CubeNoise ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem cubeNoise_add {n : ℕ} (f g : Cube n → X) :
    cubeNoise (fun u => f u + g u) = fun u => cubeNoise f u + cubeNoise g u := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext u
    simp only [cubeNoise, ih]
    split <;> module

theorem cubeNoise_const {n : ℕ} (x : X) : cubeNoise (fun _ : Cube n => x) = fun _ => x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext u
    simp only [cubeNoise, ih]
    split <;> module

theorem rademacherSum_cons {n : ℕ} (x : Fin (n+1) → X) (b : Bool) (u : Cube n) :
    rademacherSum X x (Fin.cons b u) = sign b • x 0 + rademacherSum X (fun i => x i.succ) u := by
  simp [rademacherSum, Fin.sum_univ_succ]

theorem cubeNoise_rademacherSum {n : ℕ} (x : Fin n → X) :
    cubeNoise (rademacherSum X x) = fun u => (1/2 : ℝ) • rademacherSum X x u := by
  induction n with
  | zero => funext u; simp [cubeNoise, rademacherSum]
  | succ n ih =>
    funext u
    obtain ⟨⟨b,v⟩, rfl⟩ := (cubeCons n).surjective u
    change cubeNoise (rademacherSum X x) (Fin.cons b v) =
      (1/2 : ℝ) • rademacherSum X x (Fin.cons b v)
    cases b <;> simp only [cubeNoise_cons_false, cubeNoise_cons_true, rademacherSum_cons,
      sign_false, sign_true, one_smul, neg_smul, cubeNoise_add, cubeNoise_const, ih]
    all_goals module

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.NoiseHypercontractivity ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype

theorem average_nonneg {α : Type*} [Fintype α] {f : α → ℝ} (h : ∀ a, 0 ≤ f a) :
    0 ≤ average f := mul_nonneg (by positivity) (Finset.sum_nonneg (fun a _ => h a))

theorem average_mul_sq_le {n : ℕ} (f g : Cube n → ℝ) :
    average (fun u => f u * g u) ^ 2 ≤
      average (fun u => f u ^ 2) * average (fun u => g u ^ 2) := by
  have h : |average (fun u => f u * g u)| ≤ cubeL2 ℝ f * cubeL2 ℝ g := by
    calc
      _ ≤ average (fun u => |f u * g u|) := by
        simpa only [Real.norm_eq_abs] using norm_average_le (fun u => f u * g u)
      _ ≤ _ := by simpa only [abs_mul, Real.norm_eq_abs] using average_norm_mul_le f g
  have hh := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (cubeL2_nonneg _) (cubeL2_nonneg _))).mpr h
  simpa only [sq_abs, mul_pow, cubeL2_sq, Real.norm_eq_abs, sq_abs] using hh

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.RademacherComparison ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem rademacher_fourth_moment {n : ℕ} (x : Fin n → X) :
    average (fun u => ‖rademacherSum X x u‖ ^ 4) ≤
      16 * average (fun u => ‖rademacherSum X x u‖ ^ 2) ^ 2 := by
  let S := rademacherSum X x
  have h (u : Cube n) : ‖S u‖ / 2 ≤ cubeNoise (fun v => ‖S v‖) u := by
    have hh := cubeNoise_norm_le S u
    rw [cubeNoise_rademacherSum, norm_smul] at hh
    norm_num at hh
    simpa [S, div_eq_mul_inv, mul_comm] using hh
  have h4 := average_mono (fun u => pow_le_pow_left₀ (by positivity) (h u) 4)
  have hc := cubeNoise_fourth_le (fun u => ‖S u‖)
  have he : average (fun u => (‖S u‖ / 2) ^ 4) =
      (1/16 : ℝ) * average (fun u => ‖S u‖ ^ 4) := by
    simp only [average, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring
  rw [he] at h4
  change average (fun u => ‖S u‖ ^ 4) ≤ 16 * average (fun u => ‖S u‖ ^ 2) ^ 2
  linarith

theorem average_interpolation_124 {n : ℕ} (f : Cube n → ℝ) (hf : ∀ u, 0 ≤ f u) :
    average (fun u => f u ^ 2) ^ 3 ≤ average f ^ 2 * average (fun u => f u ^ 4) := by
  let M1 := average f
  let M2 := average (fun u => f u ^ 2)
  let M3 := average (fun u => f u ^ 3)
  let M4 := average (fun u => f u ^ 4)
  have h1 : 0 ≤ M1 := average_nonneg hf
  have h2 : 0 ≤ M2 := average_nonneg (fun u => sq_nonneg _)
  have h3 : 0 ≤ M3 := average_nonneg (fun u => pow_nonneg (hf u) 3)
  have hcs1 : M2 ^ 2 ≤ M1 * M3 := by
    have h := average_mul_sq_le (fun u => Real.sqrt (f u)) (fun u => f u * Real.sqrt (f u))
    have he (u : Cube n) : Real.sqrt (f u) * (f u * Real.sqrt (f u)) = f u ^ 2 := by
      nlinarith [Real.sq_sqrt (hf u)]
    have he' (u : Cube n) : (f u * Real.sqrt (f u)) ^ 2 = f u ^ 3 := by
      rw [mul_pow, Real.sq_sqrt (hf u)]
      ring
    simpa only [he, he', Real.sq_sqrt (hf _)] using h
  have hcs2 : M3 ^ 2 ≤ M2 * M4 := by
    have h := average_mul_sq_le f (fun u => f u ^ 2)
    have he : average (fun u => f u * f u ^ 2) = M3 := by
      dsimp [M3]; congr 1; funext u; ring
    have he' : average (fun u => (f u ^ 2) ^ 2) = M4 := by
      dsimp [M4]; congr 1; funext u; ring
    rw [he, he'] at h
    exact h
  by_cases hz : M2 = 0
  · change M2^3 ≤ M1^2*M4
    rw [hz]
    norm_num only [zero_pow]
    exact mul_nonneg (sq_nonneg M1) (average_nonneg (fun u => pow_nonneg (hf u) 4))
  have hp : 0 < M2 := lt_of_le_of_ne h2 (Ne.symm hz)
  have hcs : M2^4 ≤ M1^2 * (M2*M4) := by
    calc
      M2^4 = (M2^2)^2 := by ring
      _ ≤ (M1*M3)^2 := (sq_le_sq₀ (sq_nonneg _) (mul_nonneg h1 h3)).mpr hcs1
      _ = M1^2*M3^2 := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hcs2 (sq_nonneg _)
  apply (mul_le_mul_iff_right₀ hp).mp
  change M2*M2^3 ≤ M2*(M1^2*M4)
  nlinarith [hcs]

theorem rademacher_L2_le_four_L1 {n : ℕ} (x : Fin n → X) :
    cubeL2 X (rademacherSum X x) ≤ 4 * average (fun u => ‖rademacherSum X x u‖) := by
  let f := fun u => ‖rademacherSum X x u‖
  let M1 := average f
  let M2 := average (fun u => f u ^ 2)
  have h1 : 0 ≤ M1 := average_nonneg (fun u => norm_nonneg _)
  have h2 : 0 ≤ M2 := average_nonneg (fun u => sq_nonneg _)
  have hint := average_interpolation_124 f (fun u => norm_nonneg _)
  have hfour := rademacher_fourth_moment x
  have hfinal : M2 ≤ 16 * M1^2 := by
    by_cases hz : M2 = 0
    · rw [hz]; positivity
    have hp : 0 < M2 := lt_of_le_of_ne h2 (Ne.symm hz)
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hp)).mp
    calc
      M2^2 * M2 = M2^3 := by ring
      _ ≤ M1^2 * average (fun u => f u ^ 4) := hint
      _ ≤ M1^2 * (16*M2^2) := mul_le_mul_of_nonneg_left hfour (sq_nonneg M1)
      _ = _ := by ring
  apply (sq_le_sq₀ (cubeL2_nonneg _) (mul_nonneg (by positivity) h1)).mp
  rw [cubeL2_sq]
  change M2 ≤ (4*M1)^2
  nlinarith

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.rademacher_L2_le_four_L1 := @_root_.OAI.Cotype.rademacher_L2_le_four_L1
