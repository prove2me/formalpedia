-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_threshold_real_representation
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T22:13:29.948898+00:00
-- url     : https://prove2.me/submissions/0a049af2-2685-4e0f-966d-56cfb2c2c4db

import Definitions.Def_GrothendieckLB_Supplement_cqPriceKernels
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_GrothendieckLB_Supplement_cqThresholdKernel
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.RealDeriv
import Theorems.Thm_GrothendieckLB_Supplement_cq_complex_gaussian_density_envelope
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Integral
import Definitions.Def_GrothendieckLB_Supplement_cqCorr
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Algebra.Polynomial.Eval.Defs

section
open MeasureTheory Real GrothendieckLB.Supplement.CQPrice
namespace CQGaussianMoment

noncomputable def raw (b : ℝ) (k : ℕ) := ∫ x : ℝ, |x|^k * exp (-b*x^2)

theorem raw_integrable (b : ℝ) (hb : 0<b) (k : ℕ) :
    Integrable (fun x : ℝ => |x|^k*exp (-b*x^2)) := by
  have hk : -1 < (k:ℝ) := by linarith [(show 0≤(k:ℝ) by positivity)]
  have h := (integrable_rpow_mul_exp_neg_mul_sq hb hk).norm
  simpa only [Real.rpow_natCast, Real.norm_eq_abs,abs_mul,abs_pow,abs_of_pos (exp_pos _)] using h

theorem normal_integrable (k : ℕ) : Integrable (fun x : ℝ => normalTwo x * |x|^k) := by
  convert (raw_integrable (1/4) (by norm_num) k).const_mul (1/(2*Real.sqrt Real.pi)) using 1
  funext x
  dsimp [normalTwo]
  rw [show -(1/4:ℝ)*x^2= -(x^2)/4 by ring]
  ring

end CQGaussianMoment
end

section
open MeasureTheory Set Filter
open scoped Topology Interval
namespace GrothendieckLB.Supplement.CQThreshold
theorem normS (u x : ℝ) : ‖S u x‖=1 := by unfold S;split <;> simp
theorem measurableS {X : Type*} [MeasurableSpace X] {u x : X→ℝ} (hu : Measurable u) (hx : Measurable x) :
    Measurable (fun w => S (u w) (x w)) :=
  Measurable.ite (measurableSet_le hu.neg hx) measurable_const measurable_const

end GrothendieckLB.Supplement.CQThreshold
end

section
open MeasureTheory GrothendieckLB.Supplement GrothendieckLB.Supplement.CQPrice CQGaussianMoment
namespace GrothendieckLB.Supplement.CQThreshold
theorem nint : Integrable normalTwo := by simpa only [pow_zero,mul_one] using normal_integrable 0
noncomputable def constD (q : ℂ) := 2/Real.sqrt ‖1-q^2‖
end GrothendieckLB.Supplement.CQThreshold
end

section
open GrothendieckLB.Supplement.CQPrice
namespace CQMixedIntegrals
private theorem rho_sum (ts : List (ℕ×ℤ)) (z : ℂ) (hz : ‖z‖≤1) (h : ∀ e∈ts,0<e.1) :
    ‖(ts.map (fun e => (e.2:ℂ)*z^e.1)).sum‖ ≤
      (ts.map (fun e => |(e.2:ℝ)|)).sum*‖z‖ := by
  induction ts with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons,List.sum_cons,add_mul]
    apply (norm_add_le _ _).trans
    apply add_le_add _ (ih fun j hj => h j (by simp [hj]))
    rw [norm_mul,norm_pow,show ‖(e.2:ℂ)‖=|(e.2:ℝ)| by norm_cast]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (h e (by simp)))
    rw [hj,pow_succ]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)

theorem rho_norm (z : ℂ) (hz : ‖z‖<1) : ‖eval rho z‖≤‖z‖ := by
  rw [eval,norm_div]
  have h : ∀ t∈rho.terms,0<t.1 := by simp [rho]
  have ht := rho_sum rho.terms z hz.le h
  norm_num [rho] at ht ⊢
  linarith

theorem rho_re (z : ℂ) (hz : ‖z‖<1) : |(eval rho z).re|<1 :=
  ((Complex.abs_re_le_norm _).trans (rho_norm z hz)).trans_lt hz

theorem rho_formula : eval rho=(fun z : ℂ => (10000000000000000*z-1162886658063376*z^3+27837347284321*z^5)/11190724005347697) := by
  funext z
  norm_num [eval,rho] <;> ring

end CQMixedIntegrals
end

section
open MeasureTheory MeasureTheory.Measure
namespace CQRealShuffle
abbrev P := ℝ×ℝ
private abbrev assoc (α β γ : Type) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    (α×β)×γ ≃ᵐ α×(β×γ) := MeasurableEquiv.prodAssoc

private def rot : ℝ×(ℝ×ℝ) ≃ᵐ ℝ×(ℝ×ℝ) :=
  ((assoc ℝ ℝ ℝ).symm.trans (MeasurableEquiv.prodCongr (MeasurableEquiv.prodComm : P≃ᵐP) (MeasurableEquiv.refl ℝ))).trans (assoc ℝ ℝ ℝ)
private def shuffle : P×P ≃ᵐ P×P :=
  ((assoc ℝ ℝ P).trans (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) rot)).trans (assoc ℝ ℝ P).symm

private theorem preserving : MeasurePreserving shuffle volume volume := by
  have a : MeasurePreserving (assoc ℝ ℝ ℝ) volume volume := volume_preserving_prodAssoc
  have b : MeasurePreserving (assoc ℝ ℝ P) volume volume := volume_preserving_prodAssoc
  have flip : MeasurePreserving (MeasurableEquiv.prodComm : P≃ᵐP) volume volume := measurePreserving_swap
  have mid : MeasurePreserving rot volume volume :=
    a.comp ((flip.prod (MeasurePreserving.id (volume : Measure ℝ))).comp (MeasurePreserving.symm _ a))
  exact (MeasurePreserving.symm _ b).comp (((MeasurePreserving.id (volume : Measure ℝ)).prod mid).comp b)

theorem regroup (F : P×P→ℂ) (hF : Integrable F) :
    (∫ x : Fin 2→ℝ, ∫ y : Fin 2→ℝ, F ((x 0,y 0),(x 1,y 1))) =
      ∫ xy : P, ∫ st : P,F (st,xy) := by
  have fin : MeasurePreserving (MeasurableEquiv.finTwoArrow : (Fin 2→ℝ)≃ᵐP) volume volume :=
    volume_preserving_finTwoArrow ℝ
  have inner (x : Fin 2→ℝ) :
      (∫ y : Fin 2→ℝ,F ((x 0,y 0),(x 1,y 1)))=∫ y : P,F ((x 0,y.1),(x 1,y.2)) :=
    fin.integral_comp' (fun y : P => F ((x 0,y.1),(x 1,y.2)))
  simp_rw [inner]
  have outer : (∫ x : Fin 2→ℝ, ∫ y : P,F ((x 0,y.1),(x 1,y.2))) =
      ∫ x : P, ∫ y : P,F ((x.1,y.1),(x.2,y.2)) :=
    fin.integral_comp' (fun x : P => ∫ y : P,F ((x.1,y.1),(x.2,y.2)))
  rw [outer]
  have hi : Integrable (fun w : P×P => F (shuffle w)) :=
    (preserving.integrable_comp_emb shuffle.measurableEmbedding).2 hF
  calc
    _ = ∫ w : P×P,F (shuffle w) := (integral_prod (μ:=volume) (ν:=volume) _ hi).symm
    _ = ∫ w : P×P,F w := preserving.integral_comp' F
    _ = _ := integral_prod_symm (μ:=volume) (ν:=volume) _ hF

theorem reflect (F : P→ℂ) : (∫ w : P,F (w.1,-w.2))=∫ w : P,F w := by
  let e := MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (Homeomorph.neg ℝ).toMeasurableEquiv
  have hp : MeasurePreserving e volume volume :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod (Measure.measurePreserving_neg (volume : Measure ℝ))
  exact hp.integral_comp' F

end CQRealShuffle
end

section
open MeasureTheory GrothendieckConstant GrothendieckLB GrothendieckLB.Supplement GrothendieckLB.Supplement.CQPrice
open CQThreshold CQMixedIntegrals CQRealShuffle
namespace CQRealRepresentation
private noncomputable def gaussPref (w : ℂ) : ℂ :=
  (1 - w^2) ^ ((-(1/2 : ℝ) : ℝ) : ℂ) / ((2 * Real.pi : ℝ) : ℂ)

private noncomputable def gaussKernel (w : ℂ) (x y : ℝ) : ℂ :=
  gaussPref w * Complex.exp (-(
    ((((x+y)^2/4 : ℝ) : ℂ) * (1+w)⁻¹) +
    ((((x-y)^2/4 : ℝ) : ℂ) * (1-w)⁻¹)))

private theorem kernel_real {t : ℝ} (ht : |t| < 1) (x y : ℝ) :
    gaussKernel t x y =
      (((1 / (2 * Real.pi * Real.sqrt (1-t^2))) *
        Real.exp (-(x^2 - 2*t*x*y + y^2)/(2*(1-t^2))) : ℝ) : ℂ) := by
  have h₁ : 0 < 1+t := by linarith [(abs_lt.mp ht).1]
  have h₂ : 0 < 1-t := by linarith [(abs_lt.mp ht).2]
  have hsq : 0 < 1-t^2 := by nlinarith [mul_pos h₁ h₂]
  have hpre : gaussPref t = ((1/(2 * Real.pi * Real.sqrt (1-t^2)) : ℝ) : ℂ) := by
    unfold gaussPref
    rw [show (1 : ℂ) - (t : ℂ)^2 = ((1-t^2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hsq.le, Real.rpow_neg hsq.le, ← Real.sqrt_eq_rpow]
    push_cast
    ring
  have har : -(((x+y)^2/4)*(1+t)⁻¹ + ((x-y)^2/4)*(1-t)⁻¹) =
      -(x^2 - 2*t*x*y + y^2)/(2*(1-t^2)) := by
    field_simp [h₁.ne',h₂.ne',hsq.ne'] <;> ring
  unfold gaussKernel
  rw [hpre, Complex.ofReal_mul]
  congr 1
  rw [← har]
  push_cast
  ring

private theorem density_real (t : ℝ) (ht : |t|<1) (x y : ℝ) :
    density t x y=((gaussianPairDensity 1 t (fun _ => x) (fun _ => y):ℝ):ℂ) := by
  simpa only [density,gaussKernel,gaussPref,gaussianPairDensity,Fin.prod_univ_one] using kernel_real ht x y

private theorem rhoreal (t : ℝ) : eval rho t = (((cqRhoPoly 0.34101124 0.05276111).eval t:ℝ):ℂ) := by
  rw [rho_formula]
  norm_num [cqRhoPoly]
  push_cast
  ring

private theorem slope (x : ℝ) : 0.136419125 / Real.sqrt (1+0.34101124^2+0.05276111^2)*he 3 x=threshold x := by
  change 0.136419125 / Real.sqrt (1+0.34101124^2+0.05276111^2)*((x^3-3*x)/Real.sqrt 6)=_
  rw [threshold,delta,Real.sqrt_mul (by norm_num : (0:ℝ)≤6)]
  ring

private theorem fq (s x : ℝ) : (cqF 0.136419125 0.34101124 0.05276111 s x:ℂ)=S (threshold x) s := by
  unfold cqF S
  rw [slope]
  by_cases h : -threshold x ≤ s
  · simp [h,show 0 ≤ s+threshold x by linarith]
  · simp [h,show ¬0 ≤ s+threshold x by linarith]
private theorem gq (s x : ℝ) : (cqG 0.136419125 0.34101124 0.05276111 s x:ℂ)=S (-threshold x) s := by
  unfold cqG S
  rw [slope,neg_neg]
  by_cases h : threshold x ≤ s
  · simp [h,show 0 ≤ s-threshold x by linarith]
  · simp [h,show ¬0 ≤ s-threshold x by linarith]

private theorem reflected (z : ℂ) (x y : ℝ) : density (-z) x (-y)=density z x y := by
  unfold density
  rw [neg_sq,sub_neg_eq_add,← sub_eq_add_neg]
  push_cast
  congr 2
  ring

private noncomputable def raw (q t : ℂ) (w : P×P) : ℂ :=
  (S (threshold w.2.1) w.1.1*S (-threshold w.2.2) w.1.2)*
  (density q w.1.1 w.1.2*density t w.2.1 w.2.2)

private theorem raw_int (q t : ℂ) (hq : ‖q‖<1) (ht : ‖t‖<1) : Integrable (raw q t) := by
  have hh (r : ℂ) (hr : ‖r‖<1) : Integrable (fun w : P => ‖density r w.1 w.2‖) := by
    apply ((nint.mul_prod nint).const_mul (constD r)).mono'
    · unfold density;fun_prop
    · filter_upwards with w;simp only [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
      exact cq_complex_gaussian_density_envelope r hr w.1 w.2
  apply ((hh q hq).mul_prod (hh t ht)).mono'
  · apply Measurable.aestronglyMeasurable
    unfold raw
    apply Measurable.mul
    · apply Measurable.mul
      · apply measurableS <;> (try unfold threshold) <;> fun_prop
      · apply measurableS <;> (try unfold threshold) <;> fun_prop
    · unfold density;fun_prop
  · filter_upwards with w
    simp only [raw,norm_mul,normS,one_mul,le_refl]

private theorem H_integral (z : ℂ) :
    H z=((Real.pi/2:ℝ):ℂ)*(∫ xy : P,∫ st : P,raw (eval rho z) z (st,xy)) := by
  unfold H
  rw [← CQRealShuffle.reflect,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with xy
  have hn : threshold (-xy.2) = -threshold xy.2 := by unfold threshold;ring
  rw [reflected,hn,K]
  calc
    _ = ((Real.pi/2:ℝ):ℂ)*(∫ st : P, density z xy.1 xy.2*
        (density (eval rho z) st.1 st.2*(S (threshold xy.1) st.1*S (-threshold xy.2) st.2))) := by
      rw [integral_const_mul];ring
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with st
      unfold raw
      ring

end CQRealRepresentation

open CQRealRepresentation
theorem solution (t : ℝ) (ht : |t|<1) : H (t:ℂ)=(cqCorr 0.136419125 0.34101124 0.05276111 t:ℂ) := by
  let r := (cqRhoPoly 0.34101124 0.05276111).eval t
  have ht' : ‖(t:ℂ)‖<1 := by simpa using ht
  have hr : |r|<1 := by simpa only [rhoreal,Complex.ofReal_re,r] using rho_re (t:ℂ) ht'
  have hq := (rho_norm (t:ℂ) ht').trans_lt ht'
  rw [H_integral,← regroup _ (raw_int _ _ hq ht')]
  unfold cqCorr multiCorr
  rw [Complex.ofReal_mul]
  congr 1
  rw [←integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with x
  rw [←integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with y
  unfold raw
  simp only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,
    Complex.ofReal_mul,fq,gq,rhoreal,density_real ((cqRhoPoly 0.34101124 0.05276111).eval t) hr,density_real t ht]
end
