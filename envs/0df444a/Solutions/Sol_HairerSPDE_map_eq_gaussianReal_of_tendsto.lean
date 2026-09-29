-- Prove2me | solution 1 for HairerSPDE.map_eq_gaussianReal_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T17:13:13.717392+00:00
-- url     : https://prove2.me/submissions/572e0c6c-b930-4816-875e-1c193e714ffa

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace HairerSPDE

private lemma integral_sq_toLp_eq_norm_sq {B : Type*} [MeasurableSpace B]
    (mu : Measure B) (g : B -> Real) (hg : MemLp g 2 mu) :
    (integral mu (fun x => (g x) ^ 2)) = ‖hg.toLp g‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx]
  simp [pow_two]

theorem mapEqGaussianRealOfTendsto {B : Type*} [NormedAddCommGroup B]
    [NormedSpace Real B] [MeasurableSpace B] [BorelSpace B] [CompleteSpace B]
    [SecondCountableTopology B]
    (mu : Measure B) [IsGaussian mu] (hmu : mu[id] = 0)
    (f : B -> Real) (hf : MemLp f 2 mu) (L : Nat -> StrongDual Real B)
    (hL : Tendsto (fun n => integral mu (fun x => (L n x - f x) ^ 2))
      atTop (nhds 0)) :
    mu.map f = gaussianReal 0 (integral mu (fun x => (f x) ^ 2)).toNNReal := by
  have hLn : ∀ n, MemLp (L n) 2 mu := fun n =>
    IsGaussian.memLp_dual mu (L n) 2 (by norm_num)
  have hsub : ∀ n, MemLp (fun x => L n x - f x) 2 mu := fun n =>
    (hLn n).sub hf
  let F : Lp Real 2 mu := hf.toLp f
  let FL : Nat -> Lp Real 2 mu := fun n => (hLn n).toLp (L n)
  let D : Nat -> Lp Real 2 mu := fun n => (hsub n).toLp (fun x => L n x - f x)
  have hD_sq : Tendsto (fun n => ‖D n‖ ^ 2) atTop (nhds 0) := by
    convert hL using 1
    funext n
    exact (integral_sq_toLp_eq_norm_sq mu _ (hsub n)).symm
  have hD : Tendsto (fun n => ‖D n‖) atTop (nhds 0) := by
    have hsqrt := hD_sq.sqrt
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt
  have hFL : Tendsto FL atTop (nhds F) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    convert hD using 1
    funext n
    congr 1
  have hvar : Tendsto
      (fun n => integral mu (fun x => (L n x) ^ 2))
      atTop (nhds (integral mu (fun x => (f x) ^ 2))) := by
    have hn := hFL.norm.pow 2
    simpa only [FL, F, integral_sq_toLp_eq_norm_sq mu (L _) (hLn _),
      integral_sq_toLp_eq_norm_sq mu f hf] using hn
  have hvarNN : Tendsto
      (fun n => (integral mu (fun x => (L n x) ^ 2)).toNNReal)
      atTop (nhds (integral mu (fun x => (f x) ^ 2)).toNNReal) :=
    tendsto_real_toNNReal hvar
  let Pn : Nat -> ProbabilityMeasure Real := fun n =>
    ⟨gaussianReal 0 (integral mu (fun x => (L n x) ^ 2)).toNNReal, inferInstance⟩
  let P0 : ProbabilityMeasure Real :=
    ⟨gaussianReal 0 (integral mu (fun x => (f x) ^ 2)).toNNReal, inferInstance⟩
  have hmeasure : Tendsto Pn atTop (nhds P0) := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
    simp only [Pn, P0, ProbabilityMeasure.coe_mk, charFun_gaussianReal]
    convert ((by fun_prop : Continuous (fun v : NNReal =>
      Complex.exp (-((v : Complex) * (t : Complex) ^ 2 / 2)))).tendsto _).comp hvarNN using 1
    · funext n
      simp [Function.comp_apply, Real.coe_toNNReal']
    · congr 2
      norm_num
  have hmean : integral mu (fun x => x) = 0 := by
    simpa only [id_eq] using hmu
  have hmaps : ∀ n, mu.map (L n) =
      gaussianReal 0 (integral mu (fun x => (L n x) ^ 2)).toNNReal := by
    intro n
    rw [IsGaussian.map_eq_gaussianReal]
    congr 2
    · simp [IsGaussian.integral_dual, hmean]
    · rw [variance_eq_integral (hLn n).1.aemeasurable]
      simp [IsGaussian.integral_dual, hmean]
  have hgauss : TendstoInDistribution (fun n => (L n : B -> Real)) atTop
      (id : Real -> Real) (fun _ => mu)
      (gaussianReal 0 (integral mu (fun x => (f x) ^ 2)).toNNReal) := by
    refine ⟨fun n => (hLn n).1.aemeasurable, by fun_prop, ?_⟩
    simpa only [hmaps, Pn, P0, Measure.map_id] using hmeasure
  have hInMeasure : TendstoInMeasure mu (fun n => (L n : B -> Real)) atTop f := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      (fun n => (hLn n).1) hf.1
    have hnorm : Tendsto (fun n => eLpNorm ((L n : B -> Real) - f) 2 mu)
        atTop (nhds 0) := by
      have hcoe : Tendsto (fun n => ((eLpNorm ((L n : B -> Real) - f) 2 mu).toReal))
          atTop (nhds 0) := by
        convert hD using 1
        funext n
        rw [← Lp.norm_toLp ((L n : B -> Real) - f) ((hLn n).sub hf)]
        congr 1
      exact (ENNReal.tendsto_toReal_zero_iff (fun n => by
        exact ((hLn n).sub hf).2.ne)).mp hcoe
    simpa only [Pi.sub_apply] using hnorm
  have hfromL2 : TendstoInDistribution (fun n => (L n : B -> Real)) atTop
      f (fun _ => mu) mu := hInMeasure.tendstoInDistribution
        (fun n => (hLn n).1.aemeasurable)
  simpa using
    tendstoInDistribution_unique (fun n => (L n : B -> Real)) hfromL2 hgauss

end HairerSPDE

theorem solution {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0)
    (f : B → ℝ) (hf : MemLp f 2 μ) (L : ℕ → StrongDual ℝ B)
    (hL : Tendsto (fun n ↦ ∫ x, (L n x - f x) ^ 2 ∂μ) atTop (𝓝 0)) :
    μ.map f = gaussianReal 0 (∫ x, (f x) ^ 2 ∂μ).toNNReal :=
  HairerSPDE.mapEqGaussianRealOfTendsto μ hμ f hf L hL
