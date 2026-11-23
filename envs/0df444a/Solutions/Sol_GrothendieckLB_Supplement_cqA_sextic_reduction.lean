-- Prove2me | solution 1 for GrothendieckLB.Supplement.cqA_sextic_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T17:24:09.695834+00:00
-- url     : https://prove2.me/submissions/388ae6ee-f59d-4746-a8d3-61c91ddc9e00

import Definitions.Def_GrothendieckLB_Supplement_cqA
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open Real Set Polynomial MeasureTheory ProbabilityTheory Filter
open scoped Topology
open GrothendieckLB GrothendieckLB.Supplement

private noncomputable def weight (x : ℝ) := exp (-(x^2)/2)
private noncomputable def herm (n : ℕ) (x : ℝ) : ℝ := aeval x (hermite n)
private noncomputable def hg (n : ℕ) (x : ℝ) := herm n x * weight x
private noncomputable def sgn (u w : ℝ) : ℝ := if -u ≤ w then 1 else -1

private theorem poly_integrable (p : ℤ[X]) :
    Integrable fun x : ℝ => aeval x p * weight x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have hi : Integrable (fun x : ℝ => aeval x p * weight x + aeval x q * weight x) := hp.add hq
    simpa only [map_add,add_mul] using hi
  | monomial n a =>
    have h : Integrable fun x : ℝ => x^n * exp (-(1/2:ℝ)*x^2) := by
      simpa only [rpow_natCast] using integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)
        (lt_of_lt_of_le (by norm_num : (-1:ℝ)<0) (Nat.cast_nonneg n))
    convert h.const_mul ((algebraMap ℤ ℝ) a) using 1
    ext x
    rw [aeval_monomial]
    dsimp only [weight]
    ring_nf

private theorem int_hg (n : ℕ) : Integrable (hg n) := poly_integrable (hermite n)

private theorem continuous_hg (n : ℕ) : Continuous (hg n) := by
  exact ((hermite n).continuous_aeval).mul (by unfold weight; fun_prop)

private theorem deriv_hg (n : ℕ) (x : ℝ) : HasDerivAt (hg n) (-hg (n+1) x) x := by
  have hw : HasDerivAt weight ((-x)*weight x) x := by
    apply ((((hasDerivAt_pow 2 x).neg).div_const 2).exp).congr_deriv
    dsimp [weight]
    ring
  apply (((hermite n).hasDerivAt_aeval x).mul hw).congr_deriv
  simp only [hg,herm,hermite_succ,map_sub,map_mul,aeval_X]
  ring

private theorem abs_sgn (u w : ℝ) : |sgn u w| = 1 := by unfold sgn; split <;> norm_num

private theorem signed_integral (F : ℝ → ℝ) (hF : Integrable F) (u : ℝ) :
    (∫ w, sgn u w * F w) = 2*(∫ w in Ioi (-u), F w) - ∫ w, F w := by
  have he (w : ℝ) : sgn u w * F w = 2*(Ici (-u)).indicator F w - F w := by
    by_cases h : -u ≤ w <;> simp [sgn,Set.indicator,Set.mem_Ici,h] <;> ring
  simp_rw [he]
  rw [integral_sub ((hF.indicator measurableSet_Ici).const_mul 2) hF, integral_const_mul,
    integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]

private theorem signed_hg_succ (n : ℕ) (u : ℝ) :
    (∫ w, sgn u w * hg (n+1) w) = 2*hg n (-u) := by
  have hd (x : ℝ) : HasDerivAt (fun y => -hg n y) (hg (n+1) x) x := by
    have ht : HasDerivAt (fun y => -hg n y) (-(-hg (n+1) x)) x := (deriv_hg n x).neg
    simpa only [neg_neg] using ht
  have htop := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := -u)
    (fun x _ => hd x) (int_hg (n+1)).integrableOn (int_hg n).neg.integrableOn
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto' (a := -u)
    (fun x _ => hd x) (int_hg (n+1)).integrableOn htop
  have hall := integral_eq_zero_of_hasDerivAt_of_integrable hd (int_hg (n+1)) (int_hg n).neg
  rw [signed_integral _ (int_hg _) u, hi, hall]
  ring

private noncomputable def thresholdMean (u : ℝ) := ∫ w, sgn u w * weight w

private theorem int_weight : Integrable weight := by
  have h : hg 0 = weight := by funext x; simp [hg,herm,hermite_zero]
  rw [← h]
  exact int_hg 0

private theorem mean_deriv (u : ℝ) : HasDerivAt thresholdMean (2*weight u) u := by
  let J (u : ℝ) := ∫ w in (0:ℝ)..u, weight w
  have hc : Continuous weight := by unfold weight; fun_prop
  have hJ (x : ℝ) : HasDerivAt J (weight x) x := intervalIntegral.integral_hasDerivAt_right
    int_weight.intervalIntegrable hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have heq : thresholdMean = fun v : ℝ =>
      2*((∫ w in Ioi (0:ℝ), weight w) - J (-v)) - ∫ w, weight w := by
    funext v
    have hi := intervalIntegral.integral_interval_add_Ioi
      (a := (0 : ℝ)) (b := -v) int_weight.integrableOn int_weight.integrableOn
    rw [thresholdMean, signed_integral _ int_weight]
    dsimp only [J]
    linarith only [hi]
  rw [heq]
  have hcomp := (hJ (-u)).comp u (hasDerivAt_id u).neg
  apply (((hcomp.const_sub (∫ w in Ioi (0:ℝ), weight w)).const_mul 2).sub_const _).congr_deriv
  simp [weight]

private theorem mean_bound (u : ℝ) : ‖thresholdMean u‖ ≤ ∫ x, weight x := by
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  filter_upwards with w
  simp [Real.norm_eq_abs,abs_mul,abs_sgn,weight,abs_of_pos (Real.exp_pos _)]

private theorem int_by_parts (s : ℝ) (b : ℕ) :
    (∫ x, thresholdMean (s*(x^3-3*x))*hg (b+1) x) =
      6*s * ∫ x, (x^2-1)*herm b x * exp (-(x^2+(s*(x^3-3*x))^2)/2) := by
  let T (x : ℝ) := s*(x^3-3*x)
  let Q (x : ℝ) := thresholdMean (T x)
  have hQ (x : ℝ) : HasDerivAt Q (6*s*(x^2-1)*weight (T x)) x := by
    have hT := ((hasDerivAt_pow 3 x).sub (hasDerivAt_const_mul (x := x) 3)).const_mul s
    apply ((mean_deriv (T x)).comp x hT).congr_deriv
    norm_num
    ring
  have hintQ (n : ℕ) : Integrable (fun x => Q x * hg n x) := by
    apply ((int_hg n).norm.const_mul (∫ y, weight y)).mono'
    · exact ((continuous_iff_continuousAt.mpr fun x => (hQ x).continuousAt).mul
          (continuous_hg n)).aestronglyMeasurable
    · filter_upwards with x
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (mean_bound _) (norm_nonneg _)
  let P (x : ℝ) := (x^2-1)*hg b x
  have hintP : Integrable P := by
    have h := poly_integrable ((X^2-1)*hermite b)
    simpa only [P,hg,herm,map_mul,map_sub,map_pow,aeval_X,map_one,mul_assoc] using h
  have hleft : Integrable (fun x => 6*s*(x^2-1)*weight (T x)*hg b x) := by
    apply (hintP.norm.const_mul |6*s|).mono'
    · apply Continuous.aestronglyMeasurable
      exact (by dsimp [weight,T]; fun_prop : Continuous (fun x : ℝ => 6*s*(x^2-1)*weight (T x))).mul
        (continuous_hg b)
    · filter_upwards with x
      have hw : |weight (T x)| ≤ 1 := by
        rw [weight, abs_of_pos (Real.exp_pos _), exp_le_one_iff]
        linarith only [sq_nonneg (T x)]
      calc
        _ = |6*s| * ‖P x‖ * |weight (T x)| := by simp only [P,Real.norm_eq_abs,abs_mul]; ring
        _ ≤ _ := mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (norm_nonneg _)) hw
  have hd (x : ℝ) : HasDerivAt (fun x => Q x*hg b x)
      (6*s*(x^2-1)*weight (T x)*hg b x-Q x*hg (b+1) x) x := by
    apply ((hQ x).mul (deriv_hg b x)).congr_deriv
    ring
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable hd (hleft.sub (hintQ (b+1))) (hintQ b)
  rw [integral_sub hleft (hintQ (b+1))] at hz
  change (∫ x, Q x*hg (b+1) x) = _
  rw [← sub_eq_zero.mp hz, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  dsimp [hg,T,weight]
  rw [show -(x^2+(s*(x^3-3*x))^2)/2 = -(s*(x^3-3*x))^2/2 + -(x^2)/2 by ring, Real.exp_add]
  ring

private noncomputable def hermiteSlope (η s₃ s₅ : ℝ) :=
  η / Real.sqrt (6*(1+s₃^2+s₅^2))

private theorem normalise (η s₃ s₅ : ℝ) (a b : ℕ) :
    2*Real.pi*Real.sqrt (a.factorial:ℝ)*Real.sqrt (b.factorial:ℝ)*cqA η s₃ s₅ a b =
      ∫ x, (∫ w, sgn (hermiteSlope η s₃ s₅*(x^3-3*x)) w * hg a w) * hg b x := by
  let s := hermiteSlope η s₃ s₅
  let T (x : ℝ) := s*(x^3-3*x)
  have hf (w x : ℝ) : cqF η s₃ s₅ w x = sgn (T x) w := by
    dsimp [cqF,sgn,T,s,hermiteSlope,he]
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 6)]
    congr 1
    apply propext
    rw [neg_le_iff_add_nonneg]
    simp only [div_eq_mul_inv,mul_inv_rev]
    constructor <;> intro h <;> linarith only [h]
  let E (w x : ℝ) := sgn (T x) w * hg a w * hg b x
  have hsmeas : Measurable (fun p : ℝ×ℝ => sgn (T p.2) p.1) := by
    unfold sgn
    apply Measurable.ite (measurableSet_le ?_ measurable_fst) measurable_const measurable_const
    dsimp only [T]
    fun_prop
  have hE : Integrable (Function.uncurry E) (volume.prod volume) := by
    apply ((int_hg a).mul_prod (int_hg b)).mono
    · exact ((hsmeas.mul ((continuous_hg a).measurable.comp measurable_fst)).mul
        ((continuous_hg b).measurable.comp measurable_snd)).aestronglyMeasurable
    · filter_upwards with p
      simp [Function.uncurry,E,Real.norm_eq_abs,abs_mul,abs_sgn]
  have hnorm (w x : ℝ) :
      (2*Real.pi*Real.sqrt (a.factorial:ℝ)*Real.sqrt (b.factorial:ℝ)) *
        (cqF η s₃ s₅ w x * QuadSDE.hermiteN a w * QuadSDE.hermiteN b x *
          (gaussianPDFReal 0 1 w * gaussianPDFReal 0 1 x)) = E w x := by
    let d := Real.sqrt (2*Real.pi)
    have h2 : 2*Real.pi = d^2 := (Real.sq_sqrt (by positivity)).symm
    have hd : d ≠ 0 := by dsimp [d]; positivity
    have hpdf (y : ℝ) : gaussianPDFReal 0 1 y = d⁻¹ * weight y := by simp [gaussianPDFReal,d,weight]
    rw [h2,hpdf,hpdf,hf]
    dsimp only [QuadSDE.hermiteN,E,hg,herm]
    field_simp [hd,show Real.sqrt (a.factorial:ℝ) ≠ 0 by positivity,
      show Real.sqrt (b.factorial:ℝ) ≠ 0 by positivity]
    <;> ring
  calc
    _ = ∫ w, ∫ x, E w x := by
      rw [cqA, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with w
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ (hnorm w))
    _ = ∫ x, ∫ w, E w x := integral_integral_swap hE
    _ = _ := by simp only [E,integral_mul_const,T,s]

theorem solution (η s₃ s₅ : ℝ) :
    let s := η / Real.sqrt (6*(1+s₃^2+s₅^2))
    let K (x : ℝ) := Real.exp (-(x^2+(s*(x^3-3*x))^2)/2)
    let H (n : ℕ) (x : ℝ) : ℝ := Polynomial.aeval x (Polynomial.hermite n)
    (∀ a b : ℕ, Real.pi * Real.sqrt ((a+1).factorial:ℝ) * Real.sqrt (b.factorial:ℝ) *
      cqA η s₃ s₅ (a+1) b =
        ∫ x : ℝ, H a (-s*(x^3-3*x)) * H b x * K x) ∧
    (∀ b : ℕ, Real.pi * Real.sqrt ((b+1).factorial:ℝ) * cqA η s₃ s₅ 0 (b+1) =
      3*s * ∫ x : ℝ, (x^2-1)*H b x*K x) := by
  let s := hermiteSlope η s₃ s₅
  constructor
  · intro a b
    have h := normalise η s₃ s₅ (a+1) b
    simp_rw [signed_hg_succ] at h
    have he (x : ℝ) : 2*hg a (-(s*(x^3-3*x)))*hg b x =
        2*(herm a (-s*(x^3-3*x))*herm b x*exp (-(x^2+(s*(x^3-3*x))^2)/2)) := by
      simp only [hg,weight,neg_mul,neg_sq]
      rw [show -(x^2+(s*(x^3-3*x))^2)/2 = -(s*(x^3-3*x))^2/2 + -(x^2)/2 by ring, Real.exp_add]
      ring
    change 2*Real.pi*_*_*_ = ∫ x, 2*hg a (-(s*(x^3-3*x)))*hg b x at h
    simp_rw [he] at h
    rw [integral_const_mul] at h
    change Real.pi*_*_*_ = ∫ x, herm a (-s*(x^3-3*x))*herm b x*exp (-(x^2+(s*(x^3-3*x))^2)/2)
    linarith only [h]
  · intro b
    have h := normalise η s₃ s₅ 0 (b+1)
    have hzero : hg 0 = weight := by funext x; simp [hg,herm,hermite_zero]
    simp only [hzero,Nat.factorial_zero,Nat.cast_one,Real.sqrt_one,mul_one] at h
    change 2*Real.pi*_*_ = ∫ x, thresholdMean (s*(x^3-3*x))*hg (b+1) x at h
    rw [int_by_parts] at h
    change Real.pi*_*_ = 3*s*(∫ x, (x^2-1)*herm b x*exp (-(x^2+(s*(x^3-3*x))^2)/2))
    linarith only [h]
