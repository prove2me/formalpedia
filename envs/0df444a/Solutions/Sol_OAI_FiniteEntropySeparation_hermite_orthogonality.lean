-- Prove2me | solution 1 for OAI.FiniteEntropySeparation.hermite_orthogonality
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:11:36.781484+00:00
-- url     : https://prove2.me/submissions/aa4a401d-1a90-4b4c-a484-9f693dcd08cf

import Mathlib
import Definitions.Def_OAIQWFE000
import Definitions.Def_OAIQWFE001
import Theorems.Thm_HighDimProb_RandomProcesses_gaussian_integration_by_parts

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianIBP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open scoped ENNReal NNReal Polynomial
open MeasureTheory ProbabilityTheory Filter
namespace FiniteEntropySeparation

 theorem gaussian_integrationByParts {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hi : Integrable f (gaussianReal μ v)) (hi' : Integrable f' (gaussianReal μ v))
    (hx : Integrable (fun x => (x-μ)*f x) (gaussianReal μ v)) :
    (∫ x, (x-μ)*f x ∂gaussianReal μ v) = (v : ℝ) * ∫ x, f' x ∂gaussianReal μ v := by
  -- from the published standard-Gaussian Stein identity
  -- HighDimProb.RandomProcesses.gaussian_integration_by_parts, by x = μ + √v y
  set s : ℝ := Real.sqrt v with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by exact_mod_cast pos_iff_ne_zero.mpr hv)
  have hss : s * s = v := Real.mul_self_sqrt (NNReal.coe_nonneg v)
  let T : ℝ → ℝ := fun y => μ + s * y
  have hT : Measurable T := by fun_prop
  have hmap : (gaussianReal 0 1).map T = gaussianReal μ v := by
    have h1 := gaussianReal_map_const_mul (μ := (0:ℝ)) (v := 1) s
    rw [show T = (fun x => x + μ) ∘ (fun y => s * y) by funext y; simp [T, add_comm]]
    rw [← Measure.map_map (by fun_prop) (by fun_prop), h1, gaussianReal_map_add_const]
    congr 1
    · ring
    · ext; simp [sq, hss]
  have hint (g : ℝ → ℝ) (hg : AEStronglyMeasurable g (gaussianReal μ v)) :
      Integrable g (gaussianReal μ v) ↔ Integrable (g ∘ T) (gaussianReal 0 1) := by
    rw [← hmap]; exact integrable_map_measure (hmap ▸ hg) hT.aemeasurable
  have hcomp (g : ℝ → ℝ) (hg : AEStronglyMeasurable g (gaussianReal μ v)) :
      ∫ x, g x ∂gaussianReal μ v = ∫ y, g (T y) ∂gaussianReal 0 1 := by
    rw [← hmap]; exact integral_map hT.aemeasurable (hmap ▸ hg)
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hm1 : AEStronglyMeasurable f (gaussianReal μ v) := hfc.aestronglyMeasurable
  have hm2 : AEStronglyMeasurable f' (gaussianReal μ v) := hi'.aestronglyMeasurable
  have hm3 : AEStronglyMeasurable (fun x => (x-μ)*f x) (gaussianReal μ v) := hx.aestronglyMeasurable
  have h := HighDimProb.RandomProcesses.gaussian_integration_by_parts (f := fun y => f (T y))
    (f' := fun y => s * f' (T y))
    (fun y => by
      have := (hf (T y)).comp y (((hasDerivAt_id y).const_mul s).const_add μ)
      exact this.congr_deriv (by simp only [T, id]; ring))
    ((hint f hm1).mp hi) (((hint f' hm2).mp hi').const_mul s)
    (by
      have := ((hint _ hm3).mp hx).const_mul s⁻¹
      refine this.congr (ae_of_all _ fun y => ?_)
      simp only [Function.comp, T, add_sub_cancel_left]
      rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hs0.ne', one_mul])
  rw [integral_const_mul] at h
  rw [hcomp _ hm3, hcomp _ hm2]
  have he : ∫ y, (T y - μ) * f (T y) ∂gaussianReal 0 1 =
      s * ∫ y, y * f (T y) ∂gaussianReal 0 1 := by
    rw [← integral_const_mul]; congr 1; funext y; simp only [T]; ring
  rw [he, ← h, ← mul_assoc, hss]
 theorem gaussian_pow_integrable (μ : ℝ) (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => x^n) (gaussianReal μ v) := by
  by_cases hn : n = 0
  · subst n; simp
  have h := (memLp_id_gaussianReal' (μ := μ) (v := v) (n : ℝ≥0∞) (by simp)).integrable_norm_pow hn
  apply h.mono' (by fun_prop)
  exact Filter.Eventually.of_forall (fun x => by simp [norm_pow])
 theorem gaussian_polynomial_integrable (μ : ℝ) (v : ℝ≥0) (P : ℝ[X]) :
    Integrable (fun x => P.eval x) (gaussianReal μ v) := by
  classical
  simp only [Polynomial.eval_eq_sum_range]
  exact integrable_finsetSum _ (fun i _ => (gaussian_pow_integrable μ v i).const_mul _)
 theorem gaussian_polynomial_stein (P : ℝ[X]) :
    (∫ x, x*P.eval x ∂gaussianReal 0 1) = ∫ x, P.derivative.eval x ∂gaussianReal 0 1 := by
  have hi := gaussian_polynomial_integrable 0 1 (Polynomial.X * P)
  simpa only [sub_zero, NNReal.coe_one, one_mul] using gaussian_integrationByParts (by norm_num : (1 : ℝ≥0) ≠ 0)
    (fun x => P.hasDerivAt x) (gaussian_polynomial_integrable 0 1 P)
    (gaussian_polynomial_integrable 0 1 P.derivative) (by simpa using hi)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianHermite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Polynomial
open MeasureTheory ProbabilityTheory Polynomial Finset
namespace FiniteEntropySeparation
 theorem realHermite_succ (n : ℕ) : realHermite (n+1) = X * realHermite n - (realHermite n).derivative := by
  simp [realHermite, Polynomial.hermite_succ, Polynomial.derivative_map]
 theorem realHermite_derivative (n : ℕ) : (realHermite (n+1)).derivative = (n+1 : ℝ) • realHermite n := by
  induction n with
  | zero => simp [realHermite_succ]
  | succ n ih =>
    rw [realHermite_succ (n+1), derivative_sub, derivative_mul, derivative_X, one_mul, ih,
      derivative_smul, mul_smul_comm]
    calc
      _ = realHermite (n+1) + (n+1 : ℝ) • (X * realHermite n - (realHermite n).derivative) := by module
      _ = _ := by rw [← realHermite_succ]; push_cast; module
 theorem gaussianPolyIntegral_add (P Q : ℝ[X]) :
    gaussianPolyIntegral (P+Q) = gaussianPolyIntegral P + gaussianPolyIntegral Q := by
  simp only [gaussianPolyIntegral, eval_add]
  exact integral_add (gaussian_polynomial_integrable _ _ _) (gaussian_polynomial_integrable _ _ _)
 theorem gaussianPolyIntegral_sub (P Q : ℝ[X]) :
    gaussianPolyIntegral (P-Q) = gaussianPolyIntegral P - gaussianPolyIntegral Q := by
  simp only [gaussianPolyIntegral, eval_sub]
  exact integral_sub (gaussian_polynomial_integrable _ _ _) (gaussian_polynomial_integrable _ _ _)
 theorem gaussianPolyIntegral_smul (r : ℝ) (P : ℝ[X]) :
    gaussianPolyIntegral (r • P) = r * gaussianPolyIntegral P := by
  simp [gaussianPolyIntegral, eval_smul, integral_const_mul]
 theorem hermite_raising_lowering (n : ℕ) (Q : ℝ[X]) :
    gaussianPolyIntegral (realHermite (n+1) * Q) = gaussianPolyIntegral (realHermite n * Q.derivative) := by
  have hs := gaussian_polynomial_stein (realHermite n * Q)
  have hstein : gaussianPolyIntegral (X * (realHermite n * Q)) =
      gaussianPolyIntegral ((realHermite n * Q).derivative) := by
    simpa only [gaussianPolyIntegral, eval_mul, eval_X] using hs
  rw [realHermite_succ, sub_mul, gaussianPolyIntegral_sub, mul_assoc, hstein,
    derivative_mul, gaussianPolyIntegral_add]
  ring
 theorem realHermite_mean (n : ℕ) : gaussianPolyIntegral (realHermite n) = if n=0 then 1 else 0 := by
  cases n with
  | zero => simp
  | succ n => simpa using hermite_raising_lowering n 1
 theorem realHermite_inner_core (n m : ℕ) :
    gaussianPolyIntegral (realHermite n * realHermite m) = if n=m then (n.factorial : ℝ) else 0 := by
  induction n generalizing m with
  | zero => simpa [eq_comm] using realHermite_mean m
  | succ n ih =>
    cases m with
    | zero => simp [realHermite_mean]
    | succ m =>
      rw [hermite_raising_lowering, realHermite_derivative, mul_smul_comm, gaussianPolyIntegral_smul, ih]
      by_cases h : n=m
      · subst m; simp [Nat.factorial_succ]
      · simp [h]
 theorem hermite_orthogonality_oai (n m : ℕ) :
    (∫ x, (((Polynomial.hermite n).map (Int.castRingHom ℝ)) *
        ((Polynomial.hermite m).map (Int.castRingHom ℝ))).eval x ∂gaussianReal 0 1) =
      if n = m then (n.factorial : ℝ) else 0 :=
  realHermite_inner_core n m
end FiniteEntropySeparation

end

end OAI
end

theorem solution : type_of% @OAI.FiniteEntropySeparation.hermite_orthogonality_oai := @OAI.FiniteEntropySeparation.hermite_orthogonality_oai
