-- Prove2me | solution 1 for MasulloRH.finite_laplace_evaluations_weighted_energy_bound
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T01:16:48.413147+00:00
-- url     : https://prove2.me/submissions/2f06693d-1402-4e08-8ec1-2bfc48b570b2

import Theorems.Thm_MasulloRH_windowed_laplace_waves_exact_gram
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

open MeasureTheory MasulloRH.WindowLaplaceGram MasulloRH.GaussianApproximation
open scoped ComplexConjugate

theorem solution {n : ℕ} (c b : ℝ) (f : ℝ → ℂ) (s d : Fin n → ℂ)
    (hs : ∀ i, |(s i).re-c| < b)
    (hi : Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|)*‖f x‖^2))
    (hm : ∀ i, Integrable (fun x : ℝ => Complex.exp (s i*x)*f x)) :
    (∫ x : ℝ, ‖∑ i, d i * wave c b (s i) x‖^2) = gramValue c b s d ∧
    ‖∑ i, d i * moment f (s i)‖^2 ≤ energy c b f * gramValue c b s d := by
  classical
  let A (x : ℝ) := Real.exp (c*x+b*|x|)*‖f x‖
  let B (x : ℝ) := ∑ i, d i * wave c b (s i) x
  let g (i j : Fin n) (x : ℝ) := d i * conj (d j) * (wave c b (s i) x * conj (wave c b (s j) x))
  have hK (i j : Fin n) := MasulloRH.windowed_laplace_waves_exact_gram c b (s i) (s j) (hs i) (hs j)
  have hg (i j : Fin n) : Integrable (g i j) := (hK i j).1.const_mul _
  have hgs := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hg i j))
  have prod (x : ℝ) : B x*conj (B x) = ∑ i, ∑ j, g i j x := by
    simp only [B,map_sum,map_mul,g]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have heq (x : ℝ) : ‖B x‖^2 = (∑ i, ∑ j, g i j x).re := by
    rw [← prod,Complex.mul_conj,Complex.ofReal_re,Complex.sq_norm]
  have hB : Integrable (fun x => ‖B x‖^2) := by
    simpa only [heq,RCLike.re_to_complex] using hgs.re
  have value : (∫ x : ℝ, ‖B x‖^2) = gramValue c b s d := by
    simp_rw [heq]
    have real_split := integral_re hgs
    simp only [RCLike.re_to_complex] at real_split
    rw [real_split,integral_finsetSum _ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hg i j))]
    simp_rw [integral_finsetSum _ (fun j _ => hg _ j)]
    simp only [g,integral_const_mul,(hK _ _).2,gramValue]
  have hA (x : ℝ) : 0 ≤ A x := mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  have sqA (x : ℝ) : A x^2 = Real.exp (2*c*x+2*b*|x|)*‖f x‖^2 := by
    simp only [A,mul_pow,←Real.exp_nat_mul];congr 2;push_cast;ring
  have meas : AEStronglyMeasurable A volume := by
    have eq : A = fun x => Real.sqrt (Real.exp (2*c*x+2*b*|x|)*‖f x‖^2) := by
      funext x;rw [←sqA,Real.sqrt_sq (hA _)]
    rw [eq];exact Real.continuous_sqrt.comp_aestronglyMeasurable hi.1
  have la := (memLp_two_iff_integrable_sq meas).2 (by simpa only [sqA] using hi)
  have bc : Continuous B := by unfold B wave;fun_prop
  have lb := (memLp_two_iff_integrable_sq bc.norm.aestronglyMeasurable).2 hB
  have hold := integral_mul_le_Lp_mul_Lq_of_nonneg (μ:=volume) (p:=2) (q:=2)
    (by norm_num [Real.holderConjugate_iff]) (f:=A) (g:=fun x => ‖B x‖)
    (ae_of_all _ hA) (ae_of_all _ (fun x => norm_nonneg _)) (by simpa using la) (by simpa using lb)
  let U (x : ℝ) := ∑ i, d i*(Complex.exp (s i*x)*f x)
  have integralU : (∫ x : ℝ, U x) = ∑ i, d i * moment f (s i) := by
    dsimp only [U,moment]
    rw [integral_finsetSum _ (fun i _ => (hm i).const_mul (d i))]
    simp only [integral_const_mul]
  have identity (x : ℝ) : ‖U x‖ = A x * ‖B x‖ := by
    have fac : U x = (Real.exp (c*x+b*|x|):ℂ)*B x*f x := by
      dsimp only [B,U]
      simp only [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl;intro i _
      have hh : (Real.exp (c*x+b*|x|):ℂ)*wave c b (s i) x = Complex.exp (s i*x) := by
        rw [wave,Complex.ofReal_exp,←Complex.exp_add]
        congr 1;ring
      rw [←hh]
      ring
    rw [fac,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    dsimp only [A];ring
  have bound : ‖∫ x : ℝ, U x‖ ≤ Real.sqrt (energy c b f) * Real.sqrt (gramValue c b s d) := by
    apply (norm_integral_le_integral_norm _).trans
    simpa only [identity,Real.rpow_two,sqA,value,←Real.sqrt_eq_rpow,energy] using hold
  have e0 : 0 ≤ energy c b f := integral_nonneg (fun _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  have g0 : 0 ≤ gramValue c b s d := value ▸ integral_nonneg (fun _ => sq_nonneg _)
  have hh := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2 bound
  refine ⟨value,?_⟩
  simpa only [integralU,mul_pow,Real.sq_sqrt e0,Real.sq_sqrt g0] using hh
