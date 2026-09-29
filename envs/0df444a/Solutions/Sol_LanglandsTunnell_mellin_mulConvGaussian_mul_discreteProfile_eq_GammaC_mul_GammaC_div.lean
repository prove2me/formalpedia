-- Prove2me | solution 1 for LanglandsTunnell.mellin_mulConvGaussian_mul_discreteProfile_eq_GammaC_mul_GammaC_div
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/ef9a680a-0caf-54c9-ab9f-e4f1d4f0c7d0

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Theorems.Thm_LanglandsTunnell_integrableOn_and_integral_cpow_mul_one_add_cpow_neg_eq_betaIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_mellin_mulConvGaussian_mul_discreteProfile_eq_GammaC_mul_GammaC_div

set_option autoImplicit false

open scoped Real
open MeasureTheory Set Complex

namespace K8PD

noncomputable def hIn (α β : ℂ) (y t : ℝ) : ℂ :=
  ((t : ℂ) ^ α * (Real.exp (-(π * t ^ 2)) : ℂ)) * ((((y / t : ℝ) : ℂ) ^ β * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ))

noncomputable def J (α β : ℂ) (y q : ℝ) : ℂ :=
  (1 / 2 : ℂ) * ((y : ℂ) ^ ((α + β) / 2) * ((q : ℂ) ^ ((β - α) / 2 - 1) * (Real.exp (-(π * y * (q + q⁻¹))) : ℂ)))

theorem arg_ne_pi_of_pos {x : ℝ} (hx : 0 < x) : (x : ℂ).arg ≠ π := by
  rw [arg_ofReal_of_nonneg hx.le]; exact Real.pi_pos.ne

theorem subst_pointwise (α β : ℂ) (y : ℝ) (hy : 0 < y) (q : ℝ) (hq : 0 < q) :
    (Real.sqrt y) • ((|((-(1 / 2)) : ℝ)| * q ^ (((-(1 / 2)) : ℝ) - 1)) • hIn α β y (Real.sqrt y * q ^ ((-(1 / 2)) : ℝ))) =
      J α β y q := by
  have hmh : ((-(1 / 2)) : ℝ) = -(1 / 2 : ℝ) := by norm_num

  have ha0 : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have hr0 : 0 < q ^ ((-(1 / 2)) : ℝ) := Real.rpow_pos_of_pos hq _
  have ht0 : 0 < Real.sqrt y * q ^ ((-(1 / 2)) : ℝ) := mul_pos ha0 hr0
  have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 hy.ne'
  have hq0 : (q : ℂ) ≠ 0 := ofReal_ne_zero.2 hq.ne'

  have ha2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
  have hr2 : (q ^ ((-(1 / 2)) : ℝ)) ^ 2 = q⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, ← Real.rpow_neg_one q]; norm_num
  have ht2 : (Real.sqrt y * q ^ ((-(1 / 2)) : ℝ)) ^ 2 = y * q⁻¹ := by rw [mul_pow, ha2, hr2]
  have hs : q ^ (1 / 2 : ℝ) = (q ^ ((-(1 / 2)) : ℝ))⁻¹ := by
    rw [← Real.rpow_neg hq.le]; norm_num
  have hyt : y / (Real.sqrt y * q ^ ((-(1 / 2)) : ℝ)) = Real.sqrt y * q ^ (1 / 2 : ℝ) := by
    rw [hs, div_eq_iff ht0.ne']
    calc y = Real.sqrt y * Real.sqrt y * 1 := by rw [Real.mul_self_sqrt hy.le, mul_one]
      _ = Real.sqrt y * Real.sqrt y * ((q ^ ((-(1 / 2)) : ℝ))⁻¹ * q ^ ((-(1 / 2)) : ℝ)) := by
          rw [inv_mul_cancel₀ hr0.ne']
      _ = _ := by ring
  have hyt2 : (y / (Real.sqrt y * q ^ ((-(1 / 2)) : ℝ))) ^ 2 = y * q := by
    rw [hyt, mul_pow, ha2, ← Real.rpow_natCast, ← Real.rpow_mul hq.le]; norm_num

  have hsq : Real.sqrt y = y ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow y
  have hta : (((Real.sqrt y * q ^ ((-(1 / 2)) : ℝ)) : ℝ) : ℂ) ^ α =
      (y : ℂ) ^ (((1 / 2 : ℝ) : ℂ) * α) * (q : ℂ) ^ ((((-(1 / 2)) : ℝ) : ℂ) * α) := by
    rw [ofReal_mul, mul_cpow_ofReal_nonneg ha0.le hr0.le, hsq, ← cpow_mul_ofReal_nonneg hy.le,
      ← cpow_mul_ofReal_nonneg hq.le]
  have htb : (((y / (Real.sqrt y * q ^ ((-(1 / 2)) : ℝ))) : ℝ) : ℂ) ^ β =
      (y : ℂ) ^ (((1 / 2 : ℝ) : ℂ) * β) * (q : ℂ) ^ (((1 / 2 : ℝ) : ℂ) * β) := by
    rw [hyt, ofReal_mul, mul_cpow_ofReal_nonneg ha0.le (Real.rpow_nonneg hq.le _), hsq, ← cpow_mul_ofReal_nonneg hy.le,
      ← cpow_mul_ofReal_nonneg hq.le]
  have htc : (((Real.sqrt y * q ^ ((-(1 / 2)) : ℝ)) : ℝ) : ℂ) =
      (y : ℂ) ^ (((1 / 2 : ℝ) : ℂ)) * (q : ℂ) ^ ((((-(1 / 2)) : ℝ) : ℂ)) := by
    rw [ofReal_mul, hsq, ofReal_cpow hy.le, ofReal_cpow hq.le]
  have hsa : ((Real.sqrt y : ℝ) : ℂ) = (y : ℂ) ^ (((1 / 2 : ℝ) : ℂ)) := by rw [hsq, ofReal_cpow hy.le]
  have h32 : ((q ^ (((-(1 / 2)) : ℝ) - 1) : ℝ) : ℂ) = (q : ℂ) ^ (((((-(1 / 2)) : ℝ) - 1 : ℝ)) : ℂ) := ofReal_cpow hq.le _
  have hexp : ((Real.exp (-(π * (Real.sqrt y * q ^ ((-(1 / 2)) : ℝ)) ^ 2)) : ℝ) : ℂ) *
      ((Real.exp (-(π * (y / (Real.sqrt y * q ^ ((-(1 / 2)) : ℝ))) ^ 2)) : ℝ) : ℂ) =
      ((Real.exp (-(π * y * (q + q⁻¹))) : ℝ) : ℂ) := by
    rw [← ofReal_mul, ← Real.exp_add, ht2, hyt2]
    congr 1
    congr 1
    ring

  have hY : (y : ℂ) ^ ((α + β) / 2) =
      (y : ℂ) ^ (((1 / 2 : ℝ) : ℂ)) * ((y : ℂ) ^ (((1 / 2 : ℝ) : ℂ) * α) * (y : ℂ) ^ (((1 / 2 : ℝ) : ℂ) * β)) *
        ((y : ℂ) ^ (((1 / 2 : ℝ) : ℂ)))⁻¹ := by
    rw [mul_comm, ← mul_assoc, inv_mul_cancel₀ (by rw [← hsa]; exact ofReal_ne_zero.2 ha0.ne'), one_mul,
      ← cpow_add _ _ hy0]
    congr 1; push_cast; ring
  have hQ : (q : ℂ) ^ ((β - α) / 2 - 1) =
      (q : ℂ) ^ (((((-(1 / 2)) : ℝ) - 1 : ℝ)) : ℂ) * ((q : ℂ) ^ ((((-(1 / 2)) : ℝ) : ℂ) * α) * (q : ℂ) ^ (((1 / 2 : ℝ) : ℂ) * β)) *
        ((q : ℂ) ^ ((((-(1 / 2)) : ℝ) : ℂ)))⁻¹ := by
    rw [← cpow_neg, ← cpow_add _ _ hq0, ← cpow_add _ _ hq0, ← cpow_add _ _ hq0]
    congr 1; push_cast; ring

  unfold hIn J
  rw [hta, htb, htc, abs_of_neg (by norm_num : ((-(1 / 2)) : ℝ) < 0), Complex.real_smul, Complex.real_smul, ofReal_mul,
    h32, hsa, hY, hQ, ← hexp]
  push_cast
  field_simp

theorem inner_subst (α β : ℂ) (y : ℝ) (hy : 0 < y) :
    ∫ t in Ioi (0 : ℝ), hIn α β y t = ∫ q in Ioi (0 : ℝ), J α β y q := by
  have ha0 : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have e1 := integral_comp_mul_left_Ioi (fun t => hIn α β y t) 0 ha0
  rw [mul_zero] at e1
  have e2 := integral_comp_rpow_Ioi (fun r => hIn α β y (Real.sqrt y * r)) (p := ((-(1 / 2)) : ℝ)) (by norm_num)
  have e3 : ∫ t in Ioi (0 : ℝ), hIn α β y t = Real.sqrt y • ∫ r in Ioi (0 : ℝ), hIn α β y (Real.sqrt y * r) := by
    rw [e1, smul_smul, mul_inv_cancel₀ ha0.ne', one_smul]
  rw [e3, ← e2, ← integral_smul]
  exact setIntegral_congr_fun measurableSet_Ioi fun q hq => subst_pointwise α β y hy q hq

noncomputable def muq (q : ℝ) : ℝ := π * (q + 2 + q⁻¹)

theorem muq_pos {q : ℝ} (hq : 0 < q) : 0 < muq q := by
  unfold muq; positivity

theorem muq_eq {q : ℝ} (hq : 0 < q) : muq q = π * (1 + q) ^ 2 / q := by
  unfold muq; field_simp; ring

noncomputable def Ψ (α β ν s : ℂ) (y q : ℝ) : ℂ :=
  (8 : ℂ) * ((y : ℂ) ^ (s - 1) * ((y : ℂ) ^ ν * (Real.exp (-(2 * π * y)) : ℂ))) * J α β y q

theorem Ψ_eq (α β ν s : ℂ) {y q : ℝ} (hy : 0 < y) (hq : 0 < q) :
    Ψ α β ν s y q = (4 : ℂ) * (q : ℂ) ^ ((β - α) / 2 - 1) *
      ((y : ℂ) ^ (s + ν + (α + β) / 2 - 1) * (Real.exp (-(muq q * y)) : ℂ)) := by
  have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 hy.ne'
  have hpow : (y : ℂ) ^ (s + ν + (α + β) / 2 - 1) = (y : ℂ) ^ (s - 1) * (y : ℂ) ^ ν * (y : ℂ) ^ ((α + β) / 2) := by
    rw [← cpow_add _ _ hy0, ← cpow_add _ _ hy0]; congr 1; ring
  have hexp : ((Real.exp (-(muq q * y)) : ℝ) : ℂ) =
      ((Real.exp (-(2 * π * y)) : ℝ) : ℂ) * ((Real.exp (-(π * y * (q + q⁻¹))) : ℝ) : ℂ) := by
    rw [← ofReal_mul, ← Real.exp_add]; congr 1; congr 1; unfold muq; ring
  unfold Ψ J
  rw [hpow, hexp]
  ring

theorem integral_Ψ_section (α β ν s : ℂ) (hw : 0 < (s + ν + (α + β) / 2).re) {q : ℝ} (hq : 0 < q) :
    ∫ y in Ioi (0 : ℝ), Ψ α β ν s y q =
      (4 : ℂ) * (q : ℂ) ^ ((β - α) / 2 - 1) * ((1 / (muq q : ℂ)) ^ (s + ν + (α + β) / 2) * Gamma (s + ν + (α + β) / 2)) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun y (hy : y ∈ Ioi (0 : ℝ)) => Ψ_eq α β ν s hy hq), integral_const_mul,
    ← integral_cpow_mul_exp_neg_mul_Ioi hw (muq_pos hq)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  push_cast
  ring_nf

theorem norm_section_eq (α β ν s : ℂ) {q : ℝ} (hq : 0 < q) :
    q ^ ((β - α) / 2 - 1).re * (1 / muq q) ^ (s + ν + (α + β) / 2).re =
      π ^ (-(s + ν + (α + β) / 2).re) * (q ^ ((s + ν + β).re - 1) * (1 + q) ^ (-((s + ν + α).re + (s + ν + β).re))) := by
  have hQ : (0 : ℝ) < 1 + q := by positivity
  set x : ℝ := (s + ν + (α + β) / 2).re with hx
  have h1 : 1 / muq q = q * (π * (1 + q) ^ 2)⁻¹ := by rw [muq_eq hq]; field_simp
  have h2 : (1 / muq q) ^ x = q ^ x * (π ^ (-x) * (1 + q) ^ (-(2 * x))) := by
    rw [h1, Real.mul_rpow hq.le (by positivity), Real.inv_rpow (by positivity), Real.mul_rpow Real.pi_pos.le (by positivity),
      ← Real.rpow_natCast (1 + q) 2, ← Real.rpow_mul hQ.le, Real.rpow_neg Real.pi_pos.le, Real.rpow_neg hQ.le, mul_inv]
    norm_num
  have hre1 : ((β - α) / 2 - 1).re + x = (s + ν + β).re - 1 := by
    rw [hx]; simp only [sub_re, add_re, div_ofNat_re, one_re]; ring
  have hre2 : 2 * x = (s + ν + α).re + (s + ν + β).re := by
    rw [hx]; simp only [add_re, div_ofNat_re]; ring
  rw [h2, ← hre2]
  calc q ^ ((β - α) / 2 - 1).re * (q ^ x * (π ^ (-x) * (1 + q) ^ (-(2 * x))))
      = π ^ (-x) * ((q ^ ((β - α) / 2 - 1).re * q ^ x) * (1 + q) ^ (-(2 * x))) := by ring
    _ = _ := by rw [← Real.rpow_add hq, hre1]

theorem integral_norm_Ψ_section (α β ν s : ℂ) (hw : 0 < (s + ν + (α + β) / 2).re) {q : ℝ} (hq : 0 < q) :
    ∫ y in Ioi (0 : ℝ), ‖Ψ α β ν s y q‖ =
      4 * (π ^ (-(s + ν + (α + β) / 2).re) *
        (q ^ ((s + ν + β).re - 1) * (1 + q) ^ (-((s + ν + α).re + (s + ν + β).re)))) * Real.Gamma (s + ν + (α + β) / 2).re := by
  have hpt : ∀ y ∈ Ioi (0 : ℝ), ‖Ψ α β ν s y q‖ =
      4 * q ^ ((β - α) / 2 - 1).re * (y ^ ((s + ν + (α + β) / 2).re - 1) * Real.exp (-(muq q * y))) := by
    intro y hy
    have hy' : (0 : ℝ) < y := hy
    rw [Ψ_eq α β ν s hy' hq, norm_mul, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hq, norm_cpow_eq_rpow_re_of_pos hy',
      Complex.norm_of_nonneg (Real.exp_pos _).le, sub_re, one_re]
    norm_num
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hw (muq_pos hq),
    ← norm_section_eq α β ν s hq]
  ring

theorem continuousAt_cpow_pos {x : ℝ} (hx : 0 < x) (z : ℂ) : ContinuousAt (fun t : ℝ => (t : ℂ) ^ z) x :=
  continuousAt_ofReal_cpow_const x z (Or.inr hx.ne')

theorem aestronglyMeasurable_Ψ (α β ν s : ℂ) :
    AEStronglyMeasurable (Function.uncurry fun (y q : ℝ) => Ψ α β ν s y q)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  rw [Measure.prod_restrict]
  refine ContinuousOn.aestronglyMeasurable ?_ (measurableSet_Ioi.prod measurableSet_Ioi)
  refine continuousOn_of_forall_continuousAt fun p hp => ?_
  have hy : (0 : ℝ) < p.1 := hp.1
  have hq : (0 : ℝ) < p.2 := hp.2
  have hcexp : ∀ g : ℝ × ℝ → ℝ, Continuous g → ContinuousAt (fun z : ℝ × ℝ => ((Real.exp (g z) : ℝ) : ℂ)) p :=
    fun g hg => (continuous_ofReal.comp (Real.continuous_exp.comp hg)).continuousAt
  have c1 : ContinuousAt (fun z : ℝ × ℝ => (z.1 : ℂ) ^ (s - 1)) p := (continuousAt_cpow_pos hy _).comp continuous_fst.continuousAt
  have c2 : ContinuousAt (fun z : ℝ × ℝ => (z.1 : ℂ) ^ ν) p := (continuousAt_cpow_pos hy _).comp continuous_fst.continuousAt
  have c3 : ContinuousAt (fun z : ℝ × ℝ => ((Real.exp (-(2 * π * z.1)) : ℝ) : ℂ)) p := hcexp _ (by fun_prop)
  have c4 : ContinuousAt (fun z : ℝ × ℝ => (z.1 : ℂ) ^ ((α + β) / 2)) p := (continuousAt_cpow_pos hy _).comp continuous_fst.continuousAt
  have c5 : ContinuousAt (fun z : ℝ × ℝ => (z.2 : ℂ) ^ ((β - α) / 2 - 1)) p := (continuousAt_cpow_pos hq _).comp continuous_snd.continuousAt
  have c6 : ContinuousAt (fun z : ℝ × ℝ => ((Real.exp (-(π * z.1 * (z.2 + z.2⁻¹))) : ℝ) : ℂ)) p := by
    refine (continuous_ofReal.comp Real.continuous_exp).continuousAt.comp ?_
    refine ((continuous_const.mul continuous_fst).continuousAt.mul
      (continuous_snd.continuousAt.add (continuous_snd.continuousAt.inv₀ hq.ne'))).neg
  unfold Ψ J
  exact ((continuousAt_const.mul (c1.mul (c2.mul c3))).mul (continuousAt_const.mul (c4.mul (c5.mul c6))))

theorem integrableOn_cpow_mul_exp_neg_mul {w : ℂ} (hw : 0 < w.re) {μ : ℝ} (hμ : 0 < μ) :
    IntegrableOn (fun y : ℝ => (y : ℂ) ^ (w - 1) * (Real.exp (-(μ * y)) : ℂ)) (Ioi 0) := by
  have h : MellinConvergent (fun y : ℝ => ((Real.exp (-(μ * y)) : ℝ) : ℂ)) w := by
    refine (MellinConvergent.comp_mul_left (f := fun u : ℝ => ((Real.exp (-u) : ℝ) : ℂ)) (s := w) hμ).mpr ?_
    refine (Complex.GammaIntegral_convergent hw).congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [smul_eq_mul]
    push_cast
    ring
  simpa only [MellinConvergent, smul_eq_mul] using h

theorem integrable_Ψ (α β ν s : ℂ) (ha : 0 < (s + ν + α).re) (hb : 0 < (s + ν + β).re) :
    Integrable (Function.uncurry fun (y q : ℝ) => Ψ α β ν s y q)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hw : 0 < (s + ν + (α + β) / 2).re := by
    have : (s + ν + (α + β) / 2).re = ((s + ν + α).re + (s + ν + β).re) / 2 := by
      simp only [add_re, div_ofNat_re]; ring
    rw [this]; positivity
  rw [integrable_prod_iff' (aestronglyMeasurable_Ψ α β ν s)]
  constructor
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun q hq => ?_
    have hq' : (0 : ℝ) < q := hq
    have hI : IntegrableOn (fun y : ℝ => (4 : ℂ) * (q : ℂ) ^ ((β - α) / 2 - 1) *
        ((y : ℂ) ^ (s + ν + (α + β) / 2 - 1) * (Real.exp (-(muq q * y)) : ℂ))) (Ioi 0) :=
      (integrableOn_cpow_mul_exp_neg_mul hw (muq_pos hq')).const_mul ((4 : ℂ) * (q : ℂ) ^ ((β - α) / 2 - 1))
    refine IntegrableOn.congr_fun hI (fun y hy => ?_) measurableSet_Ioi
    rw [Function.uncurry_apply_pair, Ψ_eq α β ν s hy hq']
  ·
    have hB := (LanglandsTunnell.integrableOn_and_integral_cpow_mul_one_add_cpow_neg_eq_betaIntegral
      ((s + ν + α).re : ℂ) ((s + ν + β).re : ℂ) (by simpa using ha) (by simpa using hb)).1
    have hBn : IntegrableOn (fun q : ℝ => ‖(q : ℂ) ^ (((s + ν + β).re : ℂ) - 1) * ((1 + q : ℝ) : ℂ) ^ (-(((s + ν + α).re : ℂ) + ((s + ν + β).re : ℂ)))‖) (Ioi 0) :=
      hB.norm
    have hBr : IntegrableOn (fun q : ℝ => q ^ ((s + ν + β).re - 1) * (1 + q) ^ (-((s + ν + α).re + (s + ν + β).re))) (Ioi 0) := by
      refine IntegrableOn.congr_fun hBn (fun q hq => ?_) measurableSet_Ioi
      have hq' : (0 : ℝ) < q := hq
      have hQ : (0 : ℝ) < 1 + q := by positivity
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hq', show ((1 + q : ℝ) : ℂ) = ((1 + q : ℝ) : ℂ) from rfl,
        norm_cpow_eq_rpow_re_of_pos hQ]
      simp only [sub_re, ofReal_re, one_re, neg_re, add_re]
    have hN : Integrable (fun q : ℝ => 4 * (π ^ (-(s + ν + (α + β) / 2).re) *
        (q ^ ((s + ν + β).re - 1) * (1 + q) ^ (-((s + ν + α).re + (s + ν + β).re))) * Real.Gamma (s + ν + (α + β) / 2).re))
        (volume.restrict (Ioi (0 : ℝ))) :=
      ((hBr.const_mul (π ^ (-(s + ν + (α + β) / 2).re))).mul_const (Real.Gamma (s + ν + (α + β) / 2).re)).const_mul 4
    refine hN.congr ((ae_restrict_mem measurableSet_Ioi).mono fun q hq => ?_)
    have hq' : (0 : ℝ) < q := hq
    simp only [Function.uncurry_apply_pair]
    rw [integral_norm_Ψ_section α β ν s hw hq']
    ring

theorem cpow_pos_ne_zero {x : ℝ} (hx : 0 < x) (z : ℂ) : (x : ℂ) ^ z ≠ 0 := by
  rw [Ne, cpow_eq_zero_iff, not_and_or]; exact Or.inl (ofReal_ne_zero.2 hx.ne')

theorem section_eq (α β ν s : ℂ) {q : ℝ} (hq : 0 < q) :
    (4 : ℂ) * (q : ℂ) ^ ((β - α) / 2 - 1) * ((1 / (muq q : ℂ)) ^ (s + ν + (α + β) / 2) * Gamma (s + ν + (α + β) / 2)) =
      ((4 : ℂ) * Gamma (s + ν + (α + β) / 2) * (π : ℂ) ^ (-(s + ν + (α + β) / 2))) *
        ((q : ℂ) ^ ((s + ν + β) - 1) * ((1 + q : ℝ) : ℂ) ^ (-((s + ν + α) + (s + ν + β)))) := by
  have hQ : (0 : ℝ) < 1 + q := by positivity
  have hq0 : (q : ℂ) ≠ 0 := ofReal_ne_zero.2 hq.ne'
  have hQ0 : ((1 + q : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 hQ.ne'
  have hπ0 : ((π : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_pos.ne'
  set w : ℂ := s + ν + (α + β) / 2 with hw

  have h1 : (1 / (muq q : ℂ)) = (q : ℂ) * ((((π * (1 + q) ^ 2)⁻¹ : ℝ)) : ℂ) := by
    rw [muq_eq hq]; push_cast; field_simp
  have hpos : (0 : ℝ) < π * (1 + q) ^ 2 := by positivity
  have h2 : ((((π * (1 + q) ^ 2)⁻¹ : ℝ)) : ℂ) ^ w = ((π : ℂ) ^ w)⁻¹ * (((1 + q : ℝ) : ℂ) ^ (((2 : ℝ) : ℂ) * w))⁻¹ := by
    rw [ofReal_inv, inv_cpow _ _ (arg_ne_pi_of_pos hpos), ofReal_mul, mul_cpow_ofReal_nonneg Real.pi_pos.le (by positivity),
      mul_inv, show ((((1 + q) ^ 2 : ℝ)) : ℂ) = ((((1 + q) ^ (2 : ℝ) : ℝ)) : ℂ) by rw [Real.rpow_two],
      ← cpow_mul_ofReal_nonneg hQ.le]
  have h3 : (1 / (muq q : ℂ)) ^ w = (q : ℂ) ^ w * (((π : ℂ) ^ w)⁻¹ * (((1 + q : ℝ) : ℂ) ^ (((2 : ℝ) : ℂ) * w))⁻¹) := by
    rw [h1, mul_cpow_ofReal_nonneg hq.le (by positivity), h2]
  have h4 : (q : ℂ) ^ ((β - α) / 2 - 1) * (q : ℂ) ^ w = (q : ℂ) ^ ((s + ν + β) - 1) := by
    rw [← cpow_add _ _ hq0]; congr 1; rw [hw]; ring
  have h5 : (((1 + q : ℝ) : ℂ) ^ (((2 : ℝ) : ℂ) * w))⁻¹ = ((1 + q : ℝ) : ℂ) ^ (-((s + ν + α) + (s + ν + β))) := by
    rw [← cpow_neg]; congr 1; rw [hw]; push_cast; ring
  have h6 : ((π : ℂ) ^ w)⁻¹ = (π : ℂ) ^ (-w) := by rw [cpow_neg]
  rw [h3, ← h4, h5, h6]
  ring

theorem const_identity (a b : ℂ) (ha : 0 < a.re) (hb : 0 < b.re) :
    (4 : ℂ) * Gamma ((a + b) / 2) * (π : ℂ) ^ (-((a + b) / 2)) * Complex.betaIntegral b a =
      2 * (Gammaℂ a * Gammaℂ b) / Gammaℝ (a + b + 1) := by
  set w : ℂ := (a + b) / 2 with hw
  have hwre : 0 < w.re := by rw [hw]; simp only [add_re, div_ofNat_re]; positivity
  have hw2 : 0 < (w + 1 / 2).re := by simp only [add_re, one_div, inv_re, re_ofNat]; norm_num; linarith
  have hab : 0 < (b + a).re := by simp only [add_re]; positivity
  have hΓw : Gamma w ≠ 0 := Gamma_ne_zero_of_re_pos hwre
  have hΓw2 : Gamma (w + 1 / 2) ≠ 0 := Gamma_ne_zero_of_re_pos hw2
  have hΓab : Gamma (b + a) ≠ 0 := Gamma_ne_zero_of_re_pos hab
  have hπ0 : ((π : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_pos.ne'
  have h20 : (2 : ℂ) ≠ 0 := two_ne_zero

  have hB : Complex.betaIntegral b a = Gamma b * Gamma a / Gamma (b + a) := by
    rw [eq_div_iff hΓab, mul_comm, ← Complex.Gamma_mul_Gamma_eq_betaIntegral hb ha]

  have hL : Gamma (b + a) = Gamma w * Gamma (w + 1 / 2) * ((2 : ℂ) ^ (1 - 2 * w))⁻¹ * ((Real.sqrt π : ℝ) : ℂ)⁻¹ := by
    have h := Complex.Gamma_mul_Gamma_add_half w
    have e : 2 * w = b + a := by rw [hw]; ring
    have hs0 : ((Real.sqrt π : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 Real.pi_pos).ne'
    have h2w : (2 : ℂ) ^ (1 - 2 * w) ≠ 0 := by rw [Ne, cpow_eq_zero_iff, not_and_or]; exact Or.inl h20
    rw [eq_mul_inv_iff_mul_eq₀ hs0, eq_mul_inv_iff_mul_eq₀ h2w, h, e]
    ring

  have hR : Gammaℝ (a + b + 1) = (π : ℂ) ^ (-w) * ((π : ℂ) ^ ((1 / 2 : ℂ)))⁻¹ * Gamma (w + 1 / 2) := by
    rw [Gammaℝ_def, ← cpow_neg, ← cpow_add _ _ hπ0]
    congr 1
    · congr 1; rw [hw]; ring
    · congr 1; rw [hw]; ring
  have hCa : Gammaℂ a = 2 * ((2 : ℂ) ^ (-a) * (π : ℂ) ^ (-a)) * Gamma a := by
    rw [Gammaℂ_def, show (2 : ℂ) * (π : ℂ) = ((2 : ℝ) : ℂ) * ((π : ℝ) : ℂ) by push_cast; ring,
      mul_cpow_ofReal_nonneg (by norm_num) Real.pi_pos.le]
    push_cast
    ring
  have hCb : Gammaℂ b = 2 * ((2 : ℂ) ^ (-b) * (π : ℂ) ^ (-b)) * Gamma b := by
    rw [Gammaℂ_def, show (2 : ℂ) * (π : ℂ) = ((2 : ℝ) : ℂ) * ((π : ℝ) : ℂ) by push_cast; ring,
      mul_cpow_ofReal_nonneg (by norm_num) Real.pi_pos.le]
    push_cast
    ring

  have hπab : (π : ℂ) ^ (-a) * (π : ℂ) ^ (-b) = (π : ℂ) ^ (-w) * (π : ℂ) ^ (-w) := by
    rw [← cpow_add _ _ hπ0, ← cpow_add _ _ hπ0]; congr 1; rw [hw]; ring
  have h2ab : (2 : ℂ) ^ (1 - 2 * w) = 2 * ((2 : ℂ) ^ (-a) * (2 : ℂ) ^ (-b)) := by
    rw [← cpow_add _ _ h20, show (2 : ℂ) * (2 : ℂ) ^ (-a + -b) = (2 : ℂ) ^ (1 : ℂ) * (2 : ℂ) ^ (-a + -b) by rw [cpow_one],
      ← cpow_add _ _ h20]
    congr 1; rw [hw]; ring
  have hsq : ((Real.sqrt π : ℝ) : ℂ) = (π : ℂ) ^ ((1 / 2 : ℂ)) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]; norm_num

  have hPw : (π : ℂ) ^ (-w) ≠ 0 := cpow_pos_ne_zero Real.pi_pos _
  have hPh : (π : ℂ) ^ ((1 / 2 : ℂ)) ≠ 0 := cpow_pos_ne_zero Real.pi_pos _
  have hA2 : (2 : ℂ) ^ (-a) ≠ 0 := by rw [Ne, cpow_eq_zero_iff, not_and_or]; exact Or.inl h20
  have hB2 : (2 : ℂ) ^ (-b) ≠ 0 := by rw [Ne, cpow_eq_zero_iff, not_and_or]; exact Or.inl h20
  rw [hB, hL, hR, hCa, hCb, h2ab, hsq]
  set Gh : ℂ := Gamma (w + 1 / 2) with hGh
  field_simp
  linear_combination (-4 * Gamma b * Gamma a) * hπab

end K8PD

open K8PD in

theorem solution
    (α β u s : ℂ) (k : ℕ) (hk : 1 ≤ k)
    (h₁ : 0 < (s + α + u + (k : ℂ) / 2).re) (h₂ : 0 < (s + β + u + (k : ℂ) / 2).re) :
    MellinConvergent (fun y : ℝ =>
        ((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
          ((t : ℂ) ^ α * (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) *
            (((y / t : ℝ) : ℂ) ^ β * (Real.exp (-(Real.pi * (y / t) ^ 2)) : ℂ)) / (t : ℂ)) *
        ((2 : ℂ) • ((y : ℂ) ^ (u + (k : ℂ) / 2) • ((Real.exp (-(2 * Real.pi * y)) : ℝ) : ℂ)))) s ∧
    mellin (fun y : ℝ =>
        ((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
          ((t : ℂ) ^ α * (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) *
            (((y / t : ℝ) : ℂ) ^ β * (Real.exp (-(Real.pi * (y / t) ^ 2)) : ℂ)) / (t : ℂ)) *
        ((2 : ℂ) • ((y : ℂ) ^ (u + (k : ℂ) / 2) • ((Real.exp (-(2 * Real.pi * y)) : ℝ) : ℂ)))) s
      = 2 * (Complex.Gammaℂ (s + α + u + (k : ℂ) / 2) * Complex.Gammaℂ (s + β + u + (k : ℂ) / 2)) /
        Complex.Gammaℝ (2 * s + α + β + 2 * u + (k : ℂ) + 1) := by
  set ν : ℂ := u + (k : ℂ) / 2 with hν
  have ha : 0 < (s + ν + α).re := by
    have e : s + ν + α = s + α + u + (k : ℂ) / 2 := by rw [hν]; ring
    rw [e]; exact h₁
  have hb : 0 < (s + ν + β).re := by
    have e : s + ν + β = s + β + u + (k : ℂ) / 2 := by rw [hν]; ring
    rw [e]; exact h₂
  have hw : 0 < (s + ν + (α + β) / 2).re := by
    have : (s + ν + (α + β) / 2).re = ((s + ν + α).re + (s + ν + β).re) / 2 := by
      simp only [add_re, div_ofNat_re]; ring
    rw [this]; positivity

  have hF : ∀ y : ℝ, (∫ t in Set.Ioi (0 : ℝ),
          ((t : ℂ) ^ α * (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) *
            (((y / t : ℝ) : ℂ) ^ β * (Real.exp (-(Real.pi * (y / t) ^ 2)) : ℂ)) / (t : ℂ)) =
      ∫ t in Set.Ioi (0 : ℝ), hIn α β y t := by
    intro y
    unfold hIn
    congr 1
    funext t
    ring

  have hM : ∀ y ∈ Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) • (((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ), hIn α β y t) *
        ((2 : ℂ) • ((y : ℂ) ^ ν • ((Real.exp (-(2 * Real.pi * y)) : ℝ) : ℂ)))) = ∫ q in Ioi (0 : ℝ), Ψ α β ν s y q := by
    intro y hy
    rw [inner_subst α β y hy]
    unfold Ψ
    rw [integral_const_mul]
    simp only [smul_eq_mul]
    ring
  have hInt := integrable_Ψ α β ν s ha hb
  refine ⟨?_, ?_⟩
  ·
    have h : IntegrableOn (fun y : ℝ => ∫ q in Ioi (0 : ℝ), Ψ α β ν s y q) (Ioi 0) := hInt.integral_prod_left
    refine IntegrableOn.congr_fun h (fun y hy => ?_) measurableSet_Ioi
    dsimp only
    rw [hF y, hM y hy]
  ·
    rw [mellin, setIntegral_congr_fun measurableSet_Ioi (fun y hy => by dsimp only; rw [hF y, hM y hy]
        : EqOn (fun y : ℝ => (y : ℂ) ^ (s - 1) • (((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
          ((t : ℂ) ^ α * (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) *
            (((y / t : ℝ) : ℂ) ^ β * (Real.exp (-(Real.pi * (y / t) ^ 2)) : ℂ)) / (t : ℂ)) *
        ((2 : ℂ) • ((y : ℂ) ^ ν • ((Real.exp (-(2 * Real.pi * y)) : ℝ) : ℂ)))))
        (fun y : ℝ => ∫ q in Ioi (0 : ℝ), Ψ α β ν s y q) (Ioi 0)),
      integral_integral_swap hInt,
      setIntegral_congr_fun measurableSet_Ioi (fun q (hq : q ∈ Ioi (0 : ℝ)) => integral_Ψ_section α β ν s hw hq),
      setIntegral_congr_fun measurableSet_Ioi (fun q (hq : q ∈ Ioi (0 : ℝ)) => section_eq α β ν s hq), integral_const_mul,
      (LanglandsTunnell.integrableOn_and_integral_cpow_mul_one_add_cpow_neg_eq_betaIntegral (s + ν + α) (s + ν + β) ha hb).2]
    have hc := const_identity (s + ν + α) (s + ν + β) ha hb
    have e1 : (s + ν + α + (s + ν + β)) / 2 = s + ν + (α + β) / 2 := by ring
    rw [e1] at hc
    rw [hc]
    have ea : s + ν + α = s + α + u + (k : ℂ) / 2 := by rw [hν]; ring
    have eb : s + ν + β = s + β + u + (k : ℂ) / 2 := by rw [hν]; ring
    have er : s + ν + α + (s + ν + β) + 1 = 2 * s + α + β + 2 * u + (k : ℂ) + 1 := by rw [hν]; ring
    rw [er, ea, eb]

end S_LanglandsTunnell_mellin_mulConvGaussian_mul_discreteProfile_eq_GammaC_mul_GammaC_div
end P2MW
export P2MW.S_LanglandsTunnell_mellin_mulConvGaussian_mul_discreteProfile_eq_GammaC_mul_GammaC_div (solution)
