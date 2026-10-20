-- Prove2me | solution 2 for OAI.Cotype.cubeNoise_fourth_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:16:21.637233+00:00
-- url     : https://prove2.me/submissions/91910bd5-44cf-4a01-8aaf-dd4197e0e6ec

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/NoiseHypercontractivity.lean:L27-L100
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.cubeNoise_fourth_le. The node keeps its source
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
import Theorems.Thm_OAI_Cotype_average_norm_mul_le

-- ---- from OAI.Analysis.Cotype.WalshCoordinates ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem average_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → X) : average (fun a => f (e a)) = average f := by
  simp only [average, Fintype.card_congr e, Equiv.sum_comp]

theorem average_prod {α β : Type*} [Fintype α] [Fintype β]
    (f : α × β → X) : average f = average (fun a => average (fun b => f (a,b))) := by
  simp only [average, Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type, Finset.smul_sum, smul_smul]
  simp [mul_comm]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.CubeNoise ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem average_cons {n : ℕ} (f : Cube (n+1) → X) :
    average f = (1/2 : ℝ) • (average (fun u => f (Fin.cons false u)) +
      average (fun u => f (Fin.cons true u))) := by
  rw [← average_equiv (cubeCons n) f, average_prod]
  simp [average, cubeCons, smul_add, smul_smul, add_comm]

theorem cubeNoise_add {n : ℕ} (f g : Cube n → X) :
    cubeNoise (fun u => f u + g u) = fun u => cubeNoise f u + cubeNoise g u := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext u
    simp only [cubeNoise, ih]
    split <;> module

theorem cubeNoise_smul {n : ℕ} (c : ℝ) (f : Cube n → X) :
    cubeNoise (fun u => c • f u) = fun u => c • cubeNoise f u := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext u
    simp only [cubeNoise, ih]
    split <;> module

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

theorem cubeNoise_fourth_le {n : ℕ} (f : Cube n → ℝ) :
    average (fun u => cubeNoise f u ^ 4) ≤ average (fun u => f u ^ 2) ^ 2 := by
  induction n with
  | zero => simp [cubeNoise, average, Cube]; ring_nf; rfl
  | succ n ih =>
    let f0 : Cube n → ℝ := fun u => f (Fin.cons false u)
    let f1 : Cube n → ℝ := fun u => f (Fin.cons true u)
    let a : Cube n → ℝ := fun u => (1/2 : ℝ) • f0 u + (1/2 : ℝ) • f1 u
    let b : Cube n → ℝ := fun u => (1/2 : ℝ) • f0 u + (-1/2 : ℝ) • f1 u
    let A := cubeNoise a
    let B := cubeNoise b
    have ha (u : Cube n) : A u = (cubeNoise f0 u + cubeNoise f1 u) / 2 := by
      have h0 := congrFun (cubeNoise_smul (1/2 : ℝ) f0) u
      have h1 := congrFun (cubeNoise_smul (1/2 : ℝ) f1) u
      have hlin := congrFun (cubeNoise_add (fun u => (1/2 : ℝ) • f0 u)
        (fun u => (1/2 : ℝ) • f1 u)) u
      change A u = _ at hlin
      simp only [smul_eq_mul] at h0 h1 hlin
      linarith
    have hb (u : Cube n) : B u = (cubeNoise f0 u - cubeNoise f1 u) / 2 := by
      have h0 := congrFun (cubeNoise_smul (1/2 : ℝ) f0) u
      have h1 := congrFun (cubeNoise_smul (-1/2 : ℝ) f1) u
      have hlin := congrFun (cubeNoise_add (fun u => (1/2 : ℝ) • f0 u)
        (fun u => (-1/2 : ℝ) • f1 u)) u
      change B u = _ at hlin
      simp only [smul_eq_mul] at h0 h1 hlin
      linarith
    have hfalse (u : Cube n) : cubeNoise f (Fin.cons false u) = A u + B u / 2 := by
      rw [cubeNoise_cons_false, ha, hb]
      change (3/4 : ℝ) * cubeNoise f0 u + (1/4 : ℝ) * cubeNoise f1 u = _
      ring
    have htrue (u : Cube n) : cubeNoise f (Fin.cons true u) = A u - B u / 2 := by
      rw [cubeNoise_cons_true, ha, hb]
      change (1/4 : ℝ) * cubeNoise f0 u + (3/4 : ℝ) * cubeNoise f1 u = _
      ring
    let a2 := average (fun u => a u ^ 2)
    let b2 := average (fun u => b u ^ 2)
    let A4 := average (fun u => A u ^ 4)
    let B4 := average (fun u => B u ^ 4)
    let C := average (fun u => A u ^ 2 * B u ^ 2)
    have ha2 : 0 ≤ a2 := average_nonneg (fun u => sq_nonneg _)
    have hb2 : 0 ≤ b2 := average_nonneg (fun u => sq_nonneg _)
    have hA4 : 0 ≤ A4 := average_nonneg (fun u => by positivity)
    have hB4 : 0 ≤ B4 := average_nonneg (fun u => by positivity)
    have hA : A4 ≤ a2 ^ 2 := ih a
    have hB : B4 ≤ b2 ^ 2 := ih b
    have hC : C ^ 2 ≤ A4 * B4 := by
      have h := average_mul_sq_le (fun u => A u ^ 2) (fun u => B u ^ 2)
      have hpa : average (fun u => (A u ^ 2) ^ 2) = A4 := by
        dsimp [A4]; congr 1; funext u; ring
      have hpb : average (fun u => (B u ^ 2) ^ 2) = B4 := by
        dsimp [B4]; congr 1; funext u; ring
      rw [hpa, hpb] at h
      exact h
    have hCle : C ≤ a2 * b2 := by
      have hprod := mul_le_mul hA hB hB4 (sq_nonneg a2)
      nlinarith [mul_nonneg ha2 hb2]
    have hsum : a2 + b2 = average (fun u => f u ^ 2) := by
      rw [average_cons]
      dsimp [a2, b2, a, b, f0, f1]
      simp only [average, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u _
      ring
    have hout : average (fun u => cubeNoise f u ^ 4) = A4 + (3/2 : ℝ) * C + (1/16 : ℝ) * B4 := by
      rw [average_cons]
      simp_rw [hfalse, htrue]
      dsimp [A4, B4, C]
      simp only [average, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u _
      ring
    rw [hout, ← hsum]
    nlinarith [mul_nonneg ha2 hb2, sq_nonneg b2]

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.cubeNoise_fourth_le := @_root_.OAI.Cotype.cubeNoise_fourth_le
