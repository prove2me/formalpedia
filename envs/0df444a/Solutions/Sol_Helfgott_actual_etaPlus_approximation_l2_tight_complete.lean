-- Prove2me | solution 1 for Helfgott.actual_etaPlus_approximation_l2_tight_complete
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T06:37:21.186043+00:00
-- url     : https://prove2.me/submissions/ae20cdb5-a660-42c7-ba0d-8ed570ec45f2

import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Tactic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_Helfgott_etaPlus_approximation_l1_l2

section

open MeasureTheory Set

namespace Helfgott

lemma phi_moment_integrable (k : ℕ) :
    IntegrableOn (fun t : ℝ => t^k*phi t) (Ioi (0 : ℝ)) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)
    (s := ((k+2 : ℕ) : ℝ)) (by have hk := Nat.cast_nonneg (α := ℝ) (k+2); linarith : (-1 : ℝ) < ((k+2 : ℕ) : ℝ))
  convert! h using 1
  funext t
  rw [Real.rpow_natCast]
  unfold phi
  rw [pow_add]
  have he : -(1/2 : ℝ)*t^2 = -(t^2)/2 := by ring
  rw [he]
  ring

lemma gaussian_power_integral (k : ℕ) :
    (∫ t in Ioi (0 : ℝ), t^k*Real.exp (-(t^2)/2)) =
      (1/2 : ℝ)^(-(((k : ℝ)+1)/2))*(1/2)*Real.Gamma (((k : ℝ)+1)/2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (k : ℝ)) (b := (1/2 : ℝ))
    (by norm_num) (by have hk := Nat.cast_nonneg (α := ℝ) k; linarith) (by norm_num)
  simp only [neg_div] at h ⊢
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [Real.rpow_natCast,Real.rpow_two]
  congr 1 <;> ring

theorem phi_mass : (∫ t in Ioi (0 : ℝ), phi t) = Real.sqrt (Real.pi/2) := by
  have h := gaussian_power_integral 2
  norm_num only [Nat.cast_ofNat] at h
  have hg : Real.Gamma (3/2 : ℝ) = (1/2)*Real.sqrt Real.pi := by
    rw [show (3/2 : ℝ) = 1/2+1 by norm_num,
      Real.Gamma_add_one (by norm_num),Real.Gamma_one_half_eq]
  have he : (1/2 : ℝ)^(-(3/2 : ℝ)) = 2*Real.sqrt 2 := by
    rw [show (-(3/2 : ℝ)) = -1+ -(1/2 : ℝ) by norm_num,
      Real.rpow_add (by norm_num : (0 : ℝ) < 1/2),Real.rpow_neg_one,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1/2),← Real.sqrt_eq_rpow]
    norm_num
  change (∫ t in Ioi (0 : ℝ), t^2*Real.exp (-(t^2)/2)) = _
  rw [h]
  norm_num
  rw [hg,he]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  field_simp
  nlinarith

theorem phi_first_moment : (∫ t in Ioi (0 : ℝ), t*phi t) = 2 := by
  have h := gaussian_power_integral 3
  have hg : Real.Gamma (2 : ℝ) = 1 := by
    rw [show (2 : ℝ) = 1+1 by norm_num,Real.Gamma_add_one (by norm_num),Real.Gamma_one]
    norm_num
  have he : (1/2 : ℝ)^(-(2 : ℝ)) = 4 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1/2),Real.rpow_two]
    norm_num
  have heq : (fun t : ℝ => t*phi t) = fun t => t^3*Real.exp (-(t^2)/2) := by
    funext t; unfold phi; ring
  rw [heq,h]
  norm_num [hg,he]

theorem phi_second_moment : (∫ t in Ioi (0 : ℝ), t^2*phi t) =
    3*Real.sqrt (Real.pi/2) := by
  have h := gaussian_power_integral 4
  have hg : Real.Gamma (5/2 : ℝ) = (3/4)*Real.sqrt Real.pi := by
    rw [show (5/2 : ℝ) = 3/2+1 by norm_num,Real.Gamma_add_one (by norm_num),
      show (3/2 : ℝ) = 1/2+1 by norm_num,Real.Gamma_add_one (by norm_num),Real.Gamma_one_half_eq]
    ring
  have he : (1/2 : ℝ)^(-(5/2 : ℝ)) = 4*Real.sqrt 2 := by
    rw [show (-(5/2 : ℝ)) = -2+ -(1/2 : ℝ) by norm_num,
      Real.rpow_add (by norm_num : (0 : ℝ) < 1/2),Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1/2),
      Real.rpow_two,Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1/2),← Real.sqrt_eq_rpow]
    norm_num
  have heq : (fun t : ℝ => t^2*phi t) = fun t => t^4*Real.exp (-(t^2)/2) := by
    funext t; unfold phi; ring
  rw [heq,h]
  norm_num
  rw [hg,he]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  field_simp
  nlinarith

end Helfgott

end

section

open MeasureTheory Set

namespace Helfgott

noncomputable def gaussianApproxFactor : ℝ → ℝ :=
  (Ioi (0 : ℝ)).indicator (fun t => t*Real.exp (-(t^2)/2))

noncomputable def gaussianApproxSquareFactor : ℝ → ℝ :=
  (Ioi (0 : ℝ)).indicator (fun t => t^2*Real.exp (-(t^2)))

lemma gaussianApproxFactor_nonneg (t : ℝ) : 0 ≤ gaussianApproxFactor t := by
  unfold gaussianApproxFactor
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem ht]
    exact mul_nonneg ht.le (Real.exp_pos _).le
  · simp [Set.indicator_of_notMem ht]

lemma gaussianApproxSquareFactor_nonneg (t : ℝ) : 0 ≤ gaussianApproxSquareFactor t := by
  unfold gaussianApproxSquareFactor
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem ht]
    positivity
  · simp [Set.indicator_of_notMem ht]

lemma gaussianApproxFactor_integrable : Integrable gaussianApproxFactor := by
  apply (integrable_indicator_iff measurableSet_Ioi).mpr
  have h := (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)).integrableOn (s := Ioi (0 : ℝ))
  convert! h using 1
  funext t
  congr 1
  ring

lemma gaussianApproxSquareFactor_integrable : Integrable gaussianApproxSquareFactor := by
  apply (integrable_indicator_iff measurableSet_Ioi).mpr
  simpa using integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
    (s := (2 : ℝ)) (by norm_num)

lemma gaussianApproxFactor_integral : (∫ t : ℝ, gaussianApproxFactor t) = 1 := by
  rw [gaussianApproxFactor,integral_indicator measurableSet_Ioi]
  have h := gaussian_power_integral 1
  norm_num [Real.rpow_neg_one,Real.Gamma_one] at h
  exact h

lemma gaussianApproxSquareFactor_integral :
    (∫ t : ℝ, gaussianApproxSquareFactor t) = Real.sqrt Real.pi/4 := by
  rw [gaussianApproxSquareFactor,integral_indicator measurableSet_Ioi]
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (2 : ℝ)) (b := (1 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  norm_num [Real.rpow_two] at h
  have hg : Real.Gamma (3/2 : ℝ) = (1/2)*Real.sqrt Real.pi := by
    rw [show (3/2 : ℝ) = 1/2+1 by norm_num,
      Real.Gamma_add_one (by norm_num),Real.Gamma_one_half_eq]
  rw [h,hg]
  ring

lemma gaussianApproxSquareFactor_integral_le :
    (∫ t : ℝ, gaussianApproxSquareFactor t) ≤ 1/2 := by
  rw [gaussianApproxSquareFactor_integral]
  have hs := Real.sq_sqrt Real.pi_pos.le
  have hn := Real.sqrt_nonneg Real.pi
  nlinarith [Real.pi_lt_four]

lemma gaussianApproxFactor_square (t : ℝ) :
    (gaussianApproxFactor t)^2 = gaussianApproxSquareFactor t := by
  unfold gaussianApproxFactor gaussianApproxSquareFactor
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem ht,Set.indicator_of_mem ht,mul_pow]
    have he : (Real.exp (-(t^2)/2))^2 = Real.exp (-(t^2)) := by
      rw [sq,← Real.exp_add]
      congr 1
      ring
    rw [he]
  · simp [Set.indicator_of_notMem ht]

end Helfgott

end

section

open MeasureTheory Set Filter

namespace Helfgott

noncomputable def logMajorKernel (u : ℝ) : ℝ := majorKernel (Real.exp u)

private noncomputable def logKernelBody (u : ℝ) : ℝ :=
  (Real.exp u)^2*(2-Real.exp u)^3*Real.exp (Real.exp u-1/2)

private noncomputable def logKernelDBody (u : ℝ) : ℝ :=
  (Real.exp u)^2*(2-Real.exp u)^2*(Real.exp u+4)*(1-Real.exp u)*Real.exp (Real.exp u-1/2)

private noncomputable def logKernelD2Body (u : ℝ) : ℝ :=
  (Real.exp u)^2*(2-Real.exp u)*
    (16-26*Real.exp u-3*(Real.exp u)^2+7*(Real.exp u)^3+(Real.exp u)^4)*
      Real.exp (Real.exp u-1/2)

noncomputable def logMajorKernelD (u : ℝ) : ℝ :=
  (Iic (Real.log 2)).indicator logKernelDBody u

noncomputable def logMajorKernelD2 (u : ℝ) : ℝ :=
  (Iic (Real.log 2)).indicator logKernelD2Body u

private lemma logKernelBody_hasDerivAt (u : ℝ) :
    HasDerivAt logKernelBody (logKernelDBody u) u := by
  have h := Real.hasDerivAt_exp u
  convert! ((h.pow 2).mul (((hasDerivAt_const u (2 : ℝ)).sub h).pow 3)).mul
    ((h.sub_const (1/2 : ℝ)).exp) using 1 <;>
    dsimp [logKernelBody,logKernelDBody] <;> ring

private lemma logKernelDBody_hasDerivAt (u : ℝ) :
    HasDerivAt logKernelDBody (logKernelD2Body u) u := by
  have h := Real.hasDerivAt_exp u
  convert! (((((h.pow 2).mul (((hasDerivAt_const u (2 : ℝ)).sub h).pow 2)).mul
    (h.add_const 4)).mul ((hasDerivAt_const u (1 : ℝ)).sub h)).mul
      ((h.sub_const (1/2 : ℝ)).exp)) using 1 <;>
    dsimp [logKernelDBody,logKernelD2Body] <;> ring

private lemma indicator_Iic_hasDerivAt (f df : ℝ → ℝ) (c : ℝ)
    (hd : ∀ u, HasDerivAt f (df u) u) (hfc : f c = 0) (hdfc : df c = 0) (u : ℝ) :
    HasDerivAt ((Iic c).indicator f) ((Iic c).indicator df u) u := by
  by_cases hu : u ≤ c
  · rw [Set.indicator_of_mem (show u ∈ Iic c from hu)]
    by_cases heq : u = c
    · subst u
      rw [hdfc]
      have hin : HasDerivWithinAt ((Iic c).indicator f) 0 (Iic c) c := by
        have h := (hd c).hasDerivWithinAt (s := Iic c)
        rw [hdfc] at h
        apply h.congr
        · intro t ht; simp [Set.indicator_of_mem ht]
        · simp [hfc]
      have hout : HasDerivWithinAt ((Iic c).indicator f) 0 (Iic c)ᶜ c := by
        apply (hasDerivAt_const c (0 : ℝ)).hasDerivWithinAt.congr
        · intro t ht; simp [Set.indicator_of_notMem ht]
        · simp [hfc]
      simpa only [union_compl_self,hasDerivWithinAt_univ] using hin.union hout
    · have hlt : u < c := lt_of_le_of_ne hu heq
      apply (hd u).congr_of_eventuallyEq
      filter_upwards [Iic_mem_nhds hlt] with t ht
      simp [Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem (show u ∉ Iic c from hu)]
    apply (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [isClosed_Iic.isOpen_compl.mem_nhds hu] with t ht
    simp [Set.indicator_of_notMem ht]

lemma logMajorKernel_eq_indicator :
    logMajorKernel = (Iic (Real.log 2)).indicator logKernelBody := by
  funext u
  have he : Real.exp u ≤ 2 ↔ u ≤ Real.log 2 := by
    have htwo : Real.exp (Real.log 2) = (2 : ℝ) := Real.exp_log (by norm_num)
    constructor
    · intro h
      apply Real.exp_le_exp.mp
      rw [htwo]
      exact h
    · intro h
      simpa only [htwo] using Real.exp_le_exp.mpr h
  by_cases hu : u ≤ Real.log 2
  · have ht : Real.exp u ∈ Icc (0 : ℝ) 2 := ⟨(Real.exp_pos _).le,he.mpr hu⟩
    simp [logMajorKernel,majorKernel,Set.indicator_of_mem ht,
      Set.indicator_of_mem (show u ∈ Iic (Real.log 2) from hu),logKernelBody]
  · have ht : Real.exp u ∉ Icc (0 : ℝ) 2 := fun h => hu (he.mp h.2)
    simp [logMajorKernel,majorKernel,Set.indicator_of_notMem ht,
      Set.indicator_of_notMem (show u ∉ Iic (Real.log 2) from hu)]

theorem logMajorKernel_hasDerivAt (u : ℝ) :
    HasDerivAt logMajorKernel (logMajorKernelD u) u := by
  rw [logMajorKernel_eq_indicator]
  exact indicator_Iic_hasDerivAt logKernelBody logKernelDBody (Real.log 2)
    logKernelBody_hasDerivAt (by norm_num [logKernelBody,Real.exp_log])
    (by norm_num [logKernelDBody,Real.exp_log]) u

theorem logMajorKernelD_hasDerivAt (u : ℝ) :
    HasDerivAt logMajorKernelD (logMajorKernelD2 u) u := by
  exact indicator_Iic_hasDerivAt logKernelDBody logKernelD2Body (Real.log 2)
    logKernelDBody_hasDerivAt (by norm_num [logKernelDBody,Real.exp_log])
    (by norm_num [logKernelD2Body,Real.exp_log]) u

lemma logMajorKernel_continuous : Continuous logMajorKernel :=
  continuous_iff_continuousAt.mpr (fun u => (logMajorKernel_hasDerivAt u).continuousAt)

lemma logMajorKernelD_continuous : Continuous logMajorKernelD :=
  continuous_iff_continuousAt.mpr (fun u => (logMajorKernelD_hasDerivAt u).continuousAt)

end Helfgott

end

section

open MeasureTheory Set Filter
open scoped Topology

namespace Helfgott

noncomputable def logRawFn (P : ℝ → ℝ) (u : ℝ) : ℝ :=
  (Real.exp u)^2*P (Real.exp u)*Real.exp (Real.exp u-1/2)

lemma logRawFn_hasDerivAt (P : ℝ → ℝ) (q u : ℝ)
    (hp : HasDerivAt P q (Real.exp u)) :
    HasDerivAt (logRawFn P)
      ((Real.exp u)^2*((2+Real.exp u)*P (Real.exp u)+Real.exp u*q)*
        Real.exp (Real.exp u-1/2)) u := by
  have h := Real.hasDerivAt_exp u
  convert! ((h.pow 2).mul (hp.comp u h)).mul ((h.sub_const (1/2 : ℝ)).exp) using 1
  dsimp
  norm_num
  ring

lemma logRawFn_tendsto_zero (P : ℝ → ℝ) (hp : Continuous P) :
    Tendsto (logRawFn P) atBot (𝓝 0) := by
  have hc : Continuous (fun t : ℝ => t^2*P t*Real.exp (t-1/2)) := by fun_prop
  change Tendsto (fun u : ℝ => (Real.exp u)^2*P (Real.exp u)*Real.exp (Real.exp u-1/2)) atBot (𝓝 0)
  simpa only [Function.comp_def,logRawFn,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_mul]
    using hc.continuousAt.tendsto.comp Real.tendsto_exp_atBot

lemma logRawFn_integrableOn (P : ℝ → ℝ) (hp : Continuous P) :
    IntegrableOn (logRawFn P) (Iic (Real.log 2)) := by
  let g : ℝ → ℝ := fun t => t*P t*Real.exp (t-1/2)
  have hg : IntegrableOn g (Real.exp '' Iic (Real.log 2)) := by
    rw [Real.image_exp_Iic,Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    have hc : Continuous g := by dsimp only [g]; fun_prop
    exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hi := (integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Iic (Real.log 2)) measurableSet_Iic
    (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt)
    (fun u _ v _ h => Real.exp_injective h) g).mp hg
  apply hi.congr_fun _ measurableSet_Iic
  intro u _
  simp only [abs_of_pos (Real.exp_pos _),smul_eq_mul]
  dsimp only [g,logRawFn]
  ring

noncomputable def logRawPoly0 (t : ℝ) : ℝ :=
  (8 : ℝ) + (-12 : ℝ)*t^1 + (6 : ℝ)*t^2 + (-1 : ℝ)*t^3

noncomputable def logRawPoly1 (t : ℝ) : ℝ :=
  (16 : ℝ) + (-28 : ℝ)*t^1 + (12 : ℝ)*t^2 + (1 : ℝ)*t^3 + (-1 : ℝ)*t^4

noncomputable def logRawPoly2 (t : ℝ) : ℝ :=
  (32 : ℝ) + (-68 : ℝ)*t^1 + (20 : ℝ)*t^2 + (17 : ℝ)*t^3 + (-5 : ℝ)*t^4 + (-1 : ℝ)*t^5

noncomputable def logRawPoly3 (t : ℝ) : ℝ :=
  (64 : ℝ) + (-172 : ℝ)*t^1 + (12 : ℝ)*t^2 + (105 : ℝ)*t^3 + (-13 : ℝ)*t^4 + (-12 : ℝ)*t^5 + (-1 : ℝ)*t^6

noncomputable def logRawPoly4 (t : ℝ) : ℝ :=
  (128 : ℝ) + (-452 : ℝ)*t^1 + (-124 : ℝ)*t^2 + (537 : ℝ)*t^3 + (27 : ℝ)*t^4 + (-97 : ℝ)*t^5 + (-20 : ℝ)*t^6 + (-1 : ℝ)*t^7

lemma logRawPoly0_continuous : Continuous logRawPoly0 := by
  unfold logRawPoly0; fun_prop

lemma logRawPoly0_integrable : IntegrableOn (logRawFn logRawPoly0) (Iic (Real.log 2)) :=
  logRawFn_integrableOn _ logRawPoly0_continuous

lemma logRawPoly0_tendsto : Tendsto (logRawFn logRawPoly0) atBot (𝓝 0) :=
  logRawFn_tendsto_zero _ logRawPoly0_continuous

lemma logRawPoly0_hasDerivAt (u : ℝ) :
    HasDerivAt (logRawFn logRawPoly0) (logRawFn logRawPoly1 u) u := by
  have hp := ((((hasDerivAt_const (Real.exp u) (8 : ℝ)).add (((hasDerivAt_id (Real.exp u)).pow 1).const_mul (-12 : ℝ))).add (((hasDerivAt_id (Real.exp u)).pow 2).const_mul (6 : ℝ))).add (((hasDerivAt_id (Real.exp u)).pow 3).const_mul (-1 : ℝ)))
  have h := logRawFn_hasDerivAt _ _ u hp
  convert! h using 1
  dsimp [logRawFn,logRawPoly0,logRawPoly1]; norm_num; ring

lemma logRawPoly1_continuous : Continuous logRawPoly1 := by
  unfold logRawPoly1; fun_prop

lemma logRawPoly1_integrable : IntegrableOn (logRawFn logRawPoly1) (Iic (Real.log 2)) :=
  logRawFn_integrableOn _ logRawPoly1_continuous

lemma logRawPoly1_tendsto : Tendsto (logRawFn logRawPoly1) atBot (𝓝 0) :=
  logRawFn_tendsto_zero _ logRawPoly1_continuous

lemma logRawPoly1_hasDerivAt (u : ℝ) :
    HasDerivAt (logRawFn logRawPoly1) (logRawFn logRawPoly2 u) u := by
  have hp := (((((hasDerivAt_const (Real.exp u) (16 : ℝ)).add (((hasDerivAt_id (Real.exp u)).pow 1).const_mul (-28 : ℝ))).add (((hasDerivAt_id (Real.exp u)).pow 2).const_mul (12 : ℝ))).add (((hasDerivAt_id (Real.exp u)).pow 3).const_mul (1 : ℝ))).add (((hasDerivAt_id (Real.exp u)).pow 4).const_mul (-1 : ℝ)))
  have h := logRawFn_hasDerivAt _ _ u hp
  convert! h using 1
  dsimp [logRawFn,logRawPoly1,logRawPoly2]; norm_num; ring

lemma logRawPoly2_continuous : Continuous logRawPoly2 := by
  unfold logRawPoly2; fun_prop

lemma logRawPoly2_integrable : IntegrableOn (logRawFn logRawPoly2) (Iic (Real.log 2)) :=
  logRawFn_integrableOn _ logRawPoly2_continuous

lemma logRawPoly2_tendsto : Tendsto (logRawFn logRawPoly2) atBot (𝓝 0) :=
  logRawFn_tendsto_zero _ logRawPoly2_continuous

lemma logRawPoly2_hasDerivAt (u : ℝ) :
    HasDerivAt (logRawFn logRawPoly2) (logRawFn logRawPoly3 u) u := by
  have hp := ((((((hasDerivAt_const (Real.exp u) (32 : ℝ)).add (((hasDerivAt_id (Real.exp u)).pow 1).const_mul (-68 : ℝ))).add (((hasDerivAt_id (Real.exp u)).pow 2).const_mul (20 : ℝ))).add (((hasDerivAt_id (Real.exp u)).pow 3).const_mul (17 : ℝ))).add (((hasDerivAt_id (Real.exp u)).pow 4).const_mul (-5 : ℝ))).add (((hasDerivAt_id (Real.exp u)).pow 5).const_mul (-1 : ℝ)))
  have h := logRawFn_hasDerivAt _ _ u hp
  convert! h using 1
  dsimp [logRawFn,logRawPoly2,logRawPoly3]; norm_num; ring

lemma logRawPoly3_continuous : Continuous logRawPoly3 := by
  unfold logRawPoly3; fun_prop

lemma logRawPoly3_integrable : IntegrableOn (logRawFn logRawPoly3) (Iic (Real.log 2)) :=
  logRawFn_integrableOn _ logRawPoly3_continuous

lemma logRawPoly3_tendsto : Tendsto (logRawFn logRawPoly3) atBot (𝓝 0) :=
  logRawFn_tendsto_zero _ logRawPoly3_continuous

lemma logRawPoly3_hasDerivAt (u : ℝ) :
    HasDerivAt (logRawFn logRawPoly3) (logRawFn logRawPoly4 u) u := by
  have hp := (((((((hasDerivAt_const (Real.exp u) (64 : ℝ)).add (((hasDerivAt_id (Real.exp u)).pow 1).const_mul (-172 : ℝ))).add (((hasDerivAt_id (Real.exp u)).pow 2).const_mul (12 : ℝ))).add (((hasDerivAt_id (Real.exp u)).pow 3).const_mul (105 : ℝ))).add (((hasDerivAt_id (Real.exp u)).pow 4).const_mul (-13 : ℝ))).add (((hasDerivAt_id (Real.exp u)).pow 5).const_mul (-12 : ℝ))).add (((hasDerivAt_id (Real.exp u)).pow 6).const_mul (-1 : ℝ)))
  have h := logRawFn_hasDerivAt _ _ u hp
  convert! h using 1
  dsimp [logRawFn,logRawPoly3,logRawPoly4]; norm_num; ring

lemma logRawPoly4_continuous : Continuous logRawPoly4 := by
  unfold logRawPoly4; fun_prop

lemma logRawPoly4_integrable : IntegrableOn (logRawFn logRawPoly4) (Iic (Real.log 2)) :=
  logRawFn_integrableOn _ logRawPoly4_continuous

lemma logRawPoly4_tendsto : Tendsto (logRawFn logRawPoly4) atBot (𝓝 0) :=
  logRawFn_tendsto_zero _ logRawPoly4_continuous

lemma logRawPoly_endpoint :
    logRawFn logRawPoly0 (Real.log 2)=0 ∧
    logRawFn logRawPoly1 (Real.log 2)=0 ∧
    logRawFn logRawPoly2 (Real.log 2)=0 ∧
    logRawFn logRawPoly3 (Real.log 2)= -192*Real.exp (3/2) := by
  norm_num [logRawFn,logRawPoly0,logRawPoly1,logRawPoly2,logRawPoly3,Real.exp_log]

lemma logMajorKernel_eq_raw_indicator :
    logMajorKernel = (Iic (Real.log 2)).indicator (logRawFn logRawPoly0) := by
  rw [logMajorKernel_eq_indicator]
  congr 1
  funext u
  change (Real.exp u)^2*(2-Real.exp u)^3*Real.exp (Real.exp u-1/2) = _
  dsimp [logRawFn,logRawPoly0]
  ring

end Helfgott

end

section

open MeasureTheory Set

set_option backward.isDefEq.respectTransparency false

namespace Helfgott

lemma exp_three_halves_le : Real.exp (3/2 : ℝ) ≤ 9/2 := by
  have he1 : Real.exp (1/2 : ℝ) ≤ 33/20 := by
    have hs : (Real.exp (1/2 : ℝ))^2 = Real.exp 1 := by
      rw [sq,← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_d9,Real.exp_pos (1/2 : ℝ)]
  rw [show (3/2 : ℝ) = 1+1/2 by norm_num,Real.exp_add]
  calc
    _ ≤ (27183/10000 : ℝ)*(33/20) := by
      gcongr
      exact Real.exp_one_lt_d9.le.trans (by norm_num)
    _ ≤ _ := by norm_num

private lemma poly_abs_bounds {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    |t^2*(2-t)^3| ≤ 2 ∧
    |t*(2-t)^2*(4-5*t)| ≤ 12 ∧
    |(2-t)*(8-32*t+20*t^2)| ≤ 48 ∧
    |-72+144*t-60*t^2| ≤ 72 ∧
    |144-120*t| ≤ 144 := by
  have h0 := ht.1
  have h2 := ht.2
  have h20 : 0 ≤ 2-t := by linarith
  have h01 : 0 ≤ t*(2-t) := mul_nonneg h0 h20
  have h11 : t*(2-t) ≤ 1 := by nlinarith [sq_nonneg (t-1)]
  have hp : |t^2*(2-t)^3| ≤ 2 := by
    rw [show t^2*(2-t)^3 = (t*(2-t))^2*(2-t) by ring,
      abs_of_nonneg (by positivity)]
    calc
      (t*(2-t))^2*(2-t) ≤ (1 : ℝ)^2*2 := by gcongr <;> linarith
      _ = _ := by norm_num
  have hp1 : |t*(2-t)^2*(4-5*t)| ≤ 12 := by
    have ha : |4-5*t| ≤ 6 := abs_le.mpr ⟨by linarith,by linarith⟩
    rw [show t*(2-t)^2*(4-5*t) = (t*(2-t))*(2-t)*(4-5*t) by ring,
      abs_mul,abs_mul,abs_of_nonneg h01,abs_of_nonneg h20]
    calc
      (t*(2-t))*(2-t)*|4-5*t| ≤ (1 : ℝ)*2*6 := by gcongr <;> linarith
      _ = _ := by norm_num
  have hp2 : |(2-t)*(8-32*t+20*t^2)| ≤ 48 := by
    have ha : |8-32*t+20*t^2| ≤ 24 := by
      apply abs_le.mpr
      constructor
      · nlinarith [sq_nonneg (5*t-4)]
      · nlinarith
    rw [abs_mul,abs_of_nonneg h20]
    calc
      (2-t)*|8-32*t+20*t^2| ≤ (2 : ℝ)*24 := by gcongr <;> linarith
      _ = _ := by norm_num
  have hp3 : |-72+144*t-60*t^2| ≤ 72 := by
    apply abs_le.mpr
    constructor
    · have hs : 0 ≤ t*(12-5*t) := mul_nonneg h0 (by linarith)
      nlinarith
    · nlinarith [sq_nonneg (5*t-6)]
  have hp4 : |144-120*t| ≤ 144 := abs_le.mpr ⟨by linarith,by linarith⟩
  exact ⟨hp,hp1,hp2,hp3,hp4⟩

lemma logRawPoly4_density_bound {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    |t*logRawPoly4 t| ≤ 770*t^3+1524*t^2+518*t+14 := by
  have h0 : 0 ≤ t := ht.1
  rcases poly_abs_bounds ht with ⟨hp,hp1,hp2,hp3,hp4⟩
  let p := t^2*(2-t)^3
  let p1 := t*(2-t)^2*(4-5*t)
  let p2 := (2-t)*(8-32*t+20*t^2)
  let p3 := -72+144*t-60*t^2
  let p4 := 144-120*t
  let a := t^3
  let b := 4*t^3+6*t^2
  let c := 6*t^3+18*t^2+7*t
  let d := 4*t^3+18*t^2+14*t+1
  let e := t^3+6*t^2+7*t+1
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hsum : t*logRawPoly4 t = a*p4+b*p3+c*p2+d*p1+e*p := by
    dsimp [logRawPoly4,a,b,c,d,e,p,p1,p2,p3,p4]; ring
  rw [hsum]
  calc
    _ ≤ |a*p4|+|b*p3|+|c*p2|+|d*p1|+|e*p| := by
      have h1 := abs_add_le (a*p4) (b*p3)
      have h2 := abs_add_le (a*p4+b*p3) (c*p2)
      have h3 := abs_add_le (a*p4+b*p3+c*p2) (d*p1)
      have h4 := abs_add_le (a*p4+b*p3+c*p2+d*p1) (e*p)
      linarith
    _ = a*|p4|+b*|p3|+c*|p2|+d*|p1|+e*|p| := by
      simp only [abs_mul,abs_of_nonneg ha,abs_of_nonneg hb,abs_of_nonneg hc,
        abs_of_nonneg hd,abs_of_nonneg he]
    _ ≤ a*144+b*72+c*48+d*12+e*2 := by
      gcongr
    _ = _ := by dsimp [a,b,c,d,e]; ring

lemma logRawPoly4_density_exp_bound {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    |t*logRawPoly4 t*Real.exp (t-1/2)| ≤
      (770*t^3+1524*t^2+518*t+14)*(9/2) := by
  have h0 : 0 ≤ t := ht.1
  rw [abs_mul,abs_of_pos (Real.exp_pos _)]
  have hb := logRawPoly4_density_bound ht
  have he : Real.exp (t-1/2) ≤ 9/2 :=
    (Real.exp_le_exp.mpr (by linarith [ht.2])).trans exp_three_halves_le
  gcongr

lemma logRawFn_abs_integral (P : ℝ → ℝ) :
    (∫ u in Iic (Real.log 2), |logRawFn P u|) =
      ∫ t in Ioc (0 : ℝ) 2, |t*P t*Real.exp (t-1/2)| := by
  have hi := integral_image_eq_integral_abs_deriv_smul
    (s := Iic (Real.log 2)) measurableSet_Iic
    (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt)
    (fun u _ v _ h => Real.exp_injective h)
    (fun t : ℝ => |t*P t*Real.exp (t-1/2)|)
  rw [Real.image_exp_Iic,Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hi
  rw [hi]
  apply setIntegral_congr_fun measurableSet_Iic
  intro u _
  simp only [abs_of_pos (Real.exp_pos _),smul_eq_mul,logRawFn,abs_mul,abs_pow]
  ring

lemma logRawPoly4_abs_integral_le :
    (∫ u in Iic (Real.log 2), |logRawFn logRawPoly4 u|) ≤ 36936 := by
  rw [logRawFn_abs_integral,← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]
  let f : ℝ → ℝ := fun t => |t*logRawPoly4 t*Real.exp (t-1/2)|
  let g : ℝ → ℝ := fun t => 770*t^3+1524*t^2+518*t+14
  have hf : Continuous f := by unfold f logRawPoly4; fun_prop
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hm := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 2)
    (hf.intervalIntegrable (μ := volume) 0 2) ((hg.intervalIntegrable (μ := volume) 0 2).mul_const (9/2))
    (fun t ht => logRawPoly4_density_exp_bound ht)
  have ha (t : ℝ) : HasDerivAt
      (fun t : ℝ => (385/2)*t^4+508*t^3+259*t^2+14*t) (g t) t := by
    convert! (((((hasDerivAt_id t).pow 4).const_mul (385/2 : ℝ)).add
      (((hasDerivAt_id t).pow 3).const_mul (508 : ℝ))).add
      (((hasDerivAt_id t).pow 2).const_mul (259 : ℝ))).add
      ((hasDerivAt_id t).const_mul (14 : ℝ)) using 1
    dsimp [g]; norm_num; ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => ha t)
    (hg.intervalIntegrable (μ := volume) 0 2)
  rw [intervalIntegral.integral_mul_const,hi] at hm
  norm_num at hm
  exact hm

lemma logRawPoly3_endpoint_abs_le :
    |logRawFn logRawPoly3 (Real.log 2)| ≤ 864 := by
  rw [logRawPoly_endpoint.2.2.2,abs_mul,abs_of_pos (Real.exp_pos _)]
  norm_num
  linarith [exp_three_halves_le]

end Helfgott

end

section

open MeasureTheory Set

namespace Helfgott

lemma integral_comp_exp_univ (g : ℝ → ℝ) :
    (∫ u : ℝ, Real.exp u*g (Real.exp u)) = ∫ t in Ioi (0 : ℝ), g t := by
  have him : Real.exp '' (univ : Set ℝ) = Ioi (0 : ℝ) := by
    rw [image_univ,Real.range_exp]
  rw [← him]
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt)
    (fun u _ v _ h => Real.exp_injective h) g
  simpa only [Measure.restrict_univ,abs_of_pos (Real.exp_pos _),smul_eq_mul] using h.symm

lemma integrable_comp_exp_univ (g : ℝ → ℝ) :
    Integrable (fun u : ℝ => Real.exp u*g (Real.exp u)) ↔ IntegrableOn g (Ioi (0 : ℝ)) := by
  have him : Real.exp '' (univ : Set ℝ) = Ioi (0 : ℝ) := by
    rw [image_univ,Real.range_exp]
  rw [← him]
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt)
    (fun u _ v _ h => Real.exp_injective h) g
  simpa only [integrableOn_univ,abs_of_pos (Real.exp_pos _),smul_eq_mul] using h.symm

end Helfgott

end

section

open MeasureTheory Set Filter

namespace Helfgott

noncomputable def logKernelDensity (t : ℝ) : ℝ :=
  (Icc (0 : ℝ) 2).indicator (fun t => t*(2-t)^3*Real.exp (t-1/2)) t

noncomputable def logKernelDensityD (t : ℝ) : ℝ :=
  (Icc (0 : ℝ) 2).indicator
    (fun t => t*(2-t)^2*(t+4)*(1-t)*Real.exp (t-1/2)) t

noncomputable def logKernelDensityD2 (t : ℝ) : ℝ :=
  (Icc (0 : ℝ) 2).indicator
    (fun t => t*(2-t)*(16-26*t-3*t^2+7*t^3+t^4)*Real.exp (t-1/2)) t

private lemma exp_mem_interval (u : ℝ) :
    Real.exp u ∈ Icc (0 : ℝ) 2 ↔ u ∈ Iic (Real.log 2) := by
  have ht : Real.exp (Real.log 2) = (2 : ℝ) := Real.exp_log (by norm_num)
  constructor
  · intro h
    apply Real.exp_le_exp.mp
    simpa only [ht] using h.2
  · intro h
    exact ⟨(Real.exp_pos _).le,by simpa only [ht] using Real.exp_le_exp.mpr h⟩

lemma logMajorKernel_density (u : ℝ) :
    logMajorKernel u = Real.exp u*logKernelDensity (Real.exp u) := by
  by_cases hu : u ∈ Iic (Real.log 2)
  · have ht := (exp_mem_interval u).mpr hu
    simp only [logMajorKernel,majorKernel,logKernelDensity,Set.indicator_of_mem ht]
    ring
  · have ht : Real.exp u ∉ Icc (0 : ℝ) 2 := fun h => hu ((exp_mem_interval u).mp h)
    simp [logMajorKernel,majorKernel,logKernelDensity,Set.indicator_of_notMem ht]

lemma logMajorKernelD_density (u : ℝ) :
    logMajorKernelD u = Real.exp u*logKernelDensityD (Real.exp u) := by
  by_cases hu : u ∈ Iic (Real.log 2)
  · have ht := (exp_mem_interval u).mpr hu
    simp only [logMajorKernelD,logKernelDensityD,Set.indicator_of_mem hu,
      Set.indicator_of_mem ht]
    change (Real.exp u)^2*(2-Real.exp u)^2*(Real.exp u+4)*(1-Real.exp u)*
      Real.exp (Real.exp u-1/2) = _
    ring
  · have ht : Real.exp u ∉ Icc (0 : ℝ) 2 := fun h => hu ((exp_mem_interval u).mp h)
    simp [logMajorKernelD,logKernelDensityD,Set.indicator_of_notMem ht,
      Set.indicator_of_notMem hu]

lemma logMajorKernelD2_density (u : ℝ) :
    logMajorKernelD2 u = Real.exp u*logKernelDensityD2 (Real.exp u) := by
  by_cases hu : u ∈ Iic (Real.log 2)
  · have ht := (exp_mem_interval u).mpr hu
    simp only [logMajorKernelD2,logKernelDensityD2,Set.indicator_of_mem hu,
      Set.indicator_of_mem ht]
    change (Real.exp u)^2*(2-Real.exp u)*
      (16-26*Real.exp u-3*(Real.exp u)^2+7*(Real.exp u)^3+(Real.exp u)^4)*
        Real.exp (Real.exp u-1/2) = _
    ring
  · have ht : Real.exp u ∉ Icc (0 : ℝ) 2 := fun h => hu ((exp_mem_interval u).mp h)
    simp [logMajorKernelD2,logKernelDensityD2,Set.indicator_of_notMem ht,
      Set.indicator_of_notMem hu]

private lemma integrable_interval_density (f : ℝ → ℝ) (hf : Continuous f)
    (h0 : f 0 = 0) (h2 : f 2 = 0) :
    Integrable ((Icc (0 : ℝ) 2).indicator f) := by
  have hc : Continuous ((Icc (0 : ℝ) 2).indicator f) := by
    apply continuous_indicator
    · intro t ht
      have hb := frontier_subset_closure ht
      rw [isClosed_Icc.closure_eq] at hb
      have hn : t ∉ interior (Icc (0 : ℝ) 2) := ht.2
      rw [interior_Icc] at hn
      have he : t=0 ∨ t=2 := by
        by_contra hh
        apply hn
        have h0 : t ≠ 0 := by tauto
        have h2 : t ≠ 2 := by tauto
        exact ⟨lt_of_le_of_ne hb.1 (Ne.symm h0),lt_of_le_of_ne hb.2 h2⟩
      rcases he with rfl | rfl <;> assumption
    · exact hf.continuousOn
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (K := Icc (0 : ℝ) 2) isCompact_Icc
  intro t ht
  exact Set.indicator_of_notMem ht f

lemma logKernelDensity_integrable : Integrable logKernelDensity := by
  exact integrable_interval_density _ (by fun_prop) (by norm_num) (by norm_num)

lemma logKernelDensityD_integrable : Integrable logKernelDensityD := by
  exact integrable_interval_density _ (by fun_prop) (by norm_num) (by norm_num)

lemma logKernelDensityD2_integrable : Integrable logKernelDensityD2 := by
  exact integrable_interval_density _ (by fun_prop) (by norm_num) (by norm_num)

lemma logMajorKernel_integrable : Integrable logMajorKernel := by
  have h := (integrable_comp_exp_univ logKernelDensity).mpr
    logKernelDensity_integrable.integrableOn
  simpa only [← logMajorKernel_density] using h

lemma logMajorKernelD_integrable : Integrable logMajorKernelD := by
  have h := (integrable_comp_exp_univ logKernelDensityD).mpr
    logKernelDensityD_integrable.integrableOn
  simpa only [← logMajorKernelD_density] using h

lemma logMajorKernelD2_integrable : Integrable logMajorKernelD2 := by
  have h := (integrable_comp_exp_univ logKernelDensityD2).mpr
    logKernelDensityD2_integrable.integrableOn
  simpa only [← logMajorKernelD2_density] using h

lemma logMajorKernelD2_abs_integral :
    (∫ u : ℝ, |logMajorKernelD2 u|) = ∫ t in Ioi (0 : ℝ), |logKernelDensityD2 t| := by
  simpa only [logMajorKernelD2_density,abs_mul,abs_of_pos (Real.exp_pos _)]
    using integral_comp_exp_univ (fun t => |logKernelDensityD2 t|)

end Helfgott

end

section

open MeasureTheory Set

namespace Helfgott

private noncomputable def variationP (t : ℝ) := t^2*(2-t)^2
private noncomputable def variationPD (t : ℝ) := 4*t*(2-t)*(1-t)
private noncomputable def variationA (t : ℝ) := variationP t*(t+4)*Real.exp (t-1/2)
private noncomputable def variationAD (t : ℝ) :=
  (variationPD t*(t+4)+variationP t*(t+5))*Real.exp (t-1/2)
private noncomputable def variationB (t : ℝ) := (t+4)*(t-1)*Real.exp (t-1/2)
private noncomputable def variationBD (t : ℝ) := (t^2+5*t-1)*Real.exp (t-1/2)
private noncomputable def secondDensityBody (t : ℝ) :=
  t*(2-t)*(16-26*t-3*t^2+7*t^3+t^4)*Real.exp (t-1/2)

private lemma variationP_hasDerivAt (t : ℝ) :
    HasDerivAt variationP (variationPD t) t := by
  convert! ((hasDerivAt_id t).pow 2).mul
    (((hasDerivAt_const t (2 : ℝ)).sub (hasDerivAt_id t)).pow 2) using 1 <;>
    dsimp [variationP,variationPD] <;> ring

private lemma variationA_hasDerivAt (t : ℝ) :
    HasDerivAt variationA (variationAD t) t := by
  convert! ((variationP_hasDerivAt t).mul ((hasDerivAt_id t).add_const 4)).mul
    (((hasDerivAt_id t).sub_const (1/2 : ℝ)).exp) using 1 <;>
    dsimp [variationA,variationAD] <;> ring

private lemma variationB_hasDerivAt (t : ℝ) :
    HasDerivAt variationB (variationBD t) t := by
  convert! (((hasDerivAt_id t).add_const 4).mul ((hasDerivAt_id t).sub_const 1)).mul
    (((hasDerivAt_id t).sub_const (1/2 : ℝ)).exp) using 1 <;>
    dsimp [variationB,variationBD] <;> ring

private lemma variationP_nonneg (t : ℝ) : 0 ≤ variationP t := by
  dsimp [variationP]; positivity

private lemma variationP_le_one {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) : variationP t ≤ 1 := by
  have h0 : 0 ≤ t*(2-t) := mul_nonneg ht.1 (by linarith [ht.2])
  have h1 : t*(2-t) ≤ 1 := by nlinarith [sq_nonneg (t-1)]
  have h2 := mul_nonneg h0 (sub_nonneg.mpr h1)
  dsimp [variationP]
  nlinarith

private lemma first_interval_bound {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |secondDensityBody t| ≤ variationAD t+5*Real.exp (1/2) := by
  have hp : 0 ≤ variationP t := variationP_nonneg t
  have hpd : 0 ≤ variationPD t := by
    dsimp [variationPD]
    have ht0 : 0 ≤ t := ht.1
    have h2 : 0 ≤ 2-t := by linarith [ht.2]
    have h1 : 0 ≤ 1-t := by linarith [ht.2]
    positivity
  have had : 0 ≤ variationAD t := by
    dsimp [variationAD]
    have h4 : 0 ≤ t+4 := by linarith [ht.1]
    have h5 : 0 ≤ t+5 := by linarith [ht.1]
    positivity
  have ha : 0 ≤ variationA t := by
    dsimp [variationA]
    have h4 : 0 ≤ t+4 := by linarith [ht.1]
    positivity
  have ha_le : variationA t ≤ 5*Real.exp (1/2) := by
    have hp_le := variationP_le_one (show t ∈ Icc (0 : ℝ) 2 from ⟨ht.1,by linarith [ht.2]⟩)
    have he : Real.exp (t-1/2) ≤ Real.exp (1/2) := Real.exp_le_exp.mpr (by linarith [ht.2])
    dsimp [variationA]
    calc
      _ ≤ 1*5*Real.exp (1/2) := by gcongr <;> linarith [ht.1,ht.2]
      _ = _ := by ring
  have heq : secondDensityBody t = variationAD t*(1-t)-variationA t := by
    dsimp [secondDensityBody,variationAD,variationA,variationPD,variationP]
    ring
  rw [heq]
  calc
    _ ≤ |variationAD t*(1-t)|+|variationA t| := abs_sub _ _
    _ = variationAD t*(1-t)+variationA t := by
      rw [abs_of_nonneg (mul_nonneg had (by linarith [ht.2])),abs_of_nonneg ha]
    _ ≤ variationAD t+5*Real.exp (1/2) := by
      have h := mul_nonneg had ht.1
      nlinarith

private lemma second_interval_bound {t : ℝ} (ht : t ∈ Icc (1 : ℝ) 2) :
    |secondDensityBody t| ≤ (-variationPD t)*(6*Real.exp (3/2))+variationBD t := by
  have hp := variationP_nonneg t
  have hp_le := variationP_le_one (show t ∈ Icc (0 : ℝ) 2 from ⟨by linarith [ht.1],ht.2⟩)
  have hpd : 0 ≤ -variationPD t := by
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have h2 : 0 ≤ 2-t := by linarith [ht.2]
    have h1 : 0 ≤ t-1 := by linarith [ht.1]
    have h := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) ht0) h2) h1
    dsimp [variationPD]; nlinarith
  have hb : 0 ≤ variationB t := by
    dsimp [variationB]
    have h4 : 0 ≤ t+4 := by linarith [ht.1]
    have h1 : 0 ≤ t-1 := by linarith [ht.1]
    positivity
  have hbd : 0 ≤ variationBD t := by
    dsimp [variationBD]
    have hq : 0 ≤ t^2+5*t-1 := by nlinarith [sq_nonneg t,ht.1]
    positivity
  have hb_le : variationB t ≤ 6*Real.exp (3/2) := by
    dsimp [variationB]
    have he : Real.exp (t-1/2) ≤ Real.exp (3/2) := Real.exp_le_exp.mpr (by linarith [ht.2])
    calc
      _ ≤ 6*1*Real.exp (3/2) := by gcongr <;> linarith [ht.1,ht.2]
      _ = _ := by ring
  have heq : secondDensityBody t = (-variationPD t)*variationB t-variationP t*variationBD t := by
    dsimp [secondDensityBody,variationPD,variationB,variationP,variationBD]; ring
  rw [heq]
  calc
    _ ≤ |(-variationPD t)*variationB t|+|variationP t*variationBD t| := abs_sub _ _
    _ = (-variationPD t)*variationB t+variationP t*variationBD t := by
      rw [abs_of_nonneg (mul_nonneg hpd hb),abs_of_nonneg (mul_nonneg hp hbd)]
    _ ≤ (-variationPD t)*(6*Real.exp (3/2))+1*variationBD t := by gcongr
    _ = _ := by ring

private lemma first_interval_integral :
    (∫ t in (0 : ℝ)..1, |secondDensityBody t|) ≤ 10*Real.exp (1/2) := by
  have hf : IntervalIntegrable (fun t => |secondDensityBody t|) volume 0 1 :=
    (by dsimp [secondDensityBody]; fun_prop : Continuous (fun t => |secondDensityBody t|)).intervalIntegrable _ _
  have hd : IntervalIntegrable variationAD volume 0 1 :=
    (by unfold variationAD variationPD variationP; fun_prop : Continuous variationAD).intervalIntegrable _ _
  have hc : IntervalIntegrable (fun _ : ℝ => 5*Real.exp (1/2)) volume 0 1 :=
    intervalIntegrable_const
  have hm := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hf (hd.add hc)
    (fun t ht => first_interval_bound ht)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => variationA_hasDerivAt t) hd
  rw [intervalIntegral.integral_add hd hc,hi,intervalIntegral.integral_const] at hm
  norm_num [variationA,variationP,smul_eq_mul] at hm ⊢
  linarith

private lemma second_interval_integral :
    (∫ t in (1 : ℝ)..2, |secondDensityBody t|) ≤ 12*Real.exp (3/2) := by
  have hf : IntervalIntegrable (fun t => |secondDensityBody t|) volume 1 2 :=
    (by dsimp [secondDensityBody]; fun_prop : Continuous (fun t => |secondDensityBody t|)).intervalIntegrable _ _
  have hp : IntervalIntegrable variationPD volume 1 2 :=
    (by unfold variationPD; fun_prop : Continuous variationPD).intervalIntegrable _ _
  have hb : IntervalIntegrable variationBD volume 1 2 :=
    (by unfold variationBD; fun_prop : Continuous variationBD).intervalIntegrable _ _
  have hm := intervalIntegral.integral_mono_on (by norm_num : (1 : ℝ) ≤ 2) hf
    ((hp.neg.mul_const (6*Real.exp (3/2))).add hb) (fun t ht => second_interval_bound ht)
  have hpi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => variationP_hasDerivAt t) hp
  have hbi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => variationB_hasDerivAt t) hb
  rw [intervalIntegral.integral_add (hp.neg.mul_const _) hb,
    intervalIntegral.integral_mul_const] at hm
  simp only [Pi.neg_apply] at hm
  rw [intervalIntegral.integral_neg,hpi,hbi] at hm
  norm_num [variationP,variationB] at hm ⊢
  linarith

private lemma density_abs_interval :
    (∫ t in Ioi (0 : ℝ), |logKernelDensityD2 t|) = ∫ t in (0 : ℝ)..2, |secondDensityBody t| := by
  have h : (fun t => |logKernelDensityD2 t|) = (Icc (0 : ℝ) 2).indicator
      (fun t => |secondDensityBody t|) := by
    funext t
    by_cases ht : t ∈ Icc (0 : ℝ) 2
    · simp [logKernelDensityD2,secondDensityBody,Set.indicator_of_mem ht]
    · simp [logKernelDensityD2,Set.indicator_of_notMem ht]
  rw [h,integral_indicator measurableSet_Icc,Measure.restrict_restrict measurableSet_Icc]
  have hs : Icc (0 : ℝ) 2 ∩ Ioi 0 = Ioc 0 2 := by ext t; simp; constructor <;> intro h <;> grind
  rw [hs,intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]

theorem logMajorKernelD2_abs_integral_le : (∫ u : ℝ, |logMajorKernelD2 u|) ≤ 80 := by
  rw [logMajorKernelD2_abs_integral,density_abs_interval]
  have hc : Continuous (fun t => |secondDensityBody t|) := by dsimp [secondDensityBody]; fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 1)
    (hc.intervalIntegrable 1 2)]
  have he1 : Real.exp (1/2 : ℝ) ≤ 33/20 := by
    have hs : (Real.exp (1/2 : ℝ))^2 = Real.exp 1 := by
      rw [sq,← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_d9,Real.exp_pos (1/2 : ℝ)]
  have he3 : Real.exp (3/2 : ℝ) ≤ 9/2 := by
    rw [show (3/2 : ℝ) = 1+1/2 by norm_num,Real.exp_add]
    calc
      _ ≤ (27183/10000 : ℝ)*(33/20) := by
        gcongr
        exact Real.exp_one_lt_d9.le.trans (by norm_num)
      _ ≤ _ := by norm_num
  linarith [first_interval_integral,second_interval_integral]

end Helfgott

end

section

open MeasureTheory
open scoped FourierTransform

namespace Helfgott

theorem fourier_second_derivative_decay {f f₁ f₂ : ℝ → ℂ}
    (h₀ : Integrable f) (h₁ : Integrable f₁) (h₂ : Integrable f₂)
    (hd₀ : ∀ u, HasDerivAt f (f₁ u) u) (hd₁ : ∀ u, HasDerivAt f₁ (f₂ u) u)
    (ξ : ℝ) :
    (2*Real.pi*|ξ|)^2 * ‖𝓕 f ξ‖ ≤ ∫ u : ℝ, ‖f₂ u‖ := by
  have he₀ : deriv f = f₁ := funext (fun u => (hd₀ u).deriv)
  have he₁ : deriv f₁ = f₂ := funext (fun u => (hd₁ u).deriv)
  have hf₀ := congrFun (Real.fourier_deriv h₀ (fun u => (hd₀ u).differentiableAt)
    (by rw [he₀]; exact h₁)) ξ
  rw [he₀] at hf₀
  have hf₁ := congrFun (Real.fourier_deriv h₁ (fun u => (hd₁ u).differentiableAt)
    (by rw [he₁]; exact h₂)) ξ
  rw [he₁] at hf₁
  have hidentity : 𝓕 f₂ ξ = ((2*Real.pi*Complex.I*(ξ : ℂ))^2)*𝓕 f ξ := by
    rw [hf₁,hf₀]
    simp only [smul_eq_mul,pow_two,mul_assoc]
  have hn : ‖𝓕 f₂ ξ‖ = (2*Real.pi*|ξ|)^2 * ‖𝓕 f ξ‖ := by
    rw [hidentity,norm_mul,norm_pow]
    simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,Complex.norm_I,mul_one]
  rw [← hn,Real.fourier_eq]
  exact VectorFourier.norm_fourierIntegral_le_integral_norm
    Real.fourierChar volume (innerₗ ℝ) f₂ ξ

end Helfgott

end

section

open MeasureTheory Set
open scoped FourierTransform

namespace Helfgott

lemma integrable_of_quadratic_decay (F : ℝ → ℂ) (hc : Continuous F) (A C : ℝ)
    (hb : ∀ ξ : ℝ, ‖F ξ‖ ≤ A) (hd : ∀ ξ : ℝ, ξ^2*‖F ξ‖ ≤ C) : Integrable F := by
  apply (integrable_inv_one_add_sq.const_mul (A+C)).mono' hc.aestronglyMeasurable
  exact ae_of_all _ (fun ξ => by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 1+ξ^2)).mpr
    nlinarith [hb ξ,hd ξ])

lemma inv_square_integrableOn {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun ξ : ℝ => (ξ^2)⁻¹) (Ioi R) := by
  simpa using integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hR

lemma inv_square_integral {R : ℝ} (hR : 0 < R) :
    (∫ ξ in Ioi R, (ξ^2)⁻¹) = R⁻¹ := by
  have h := integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hR
  norm_num [Real.rpow_neg_one] at h
  exact h

lemma quadratic_decay_right_tail (F : ℝ → ℂ) (hi : Integrable F) (C : ℝ)
    (hd : ∀ ξ : ℝ, ξ^2*‖F ξ‖ ≤ C) {R : ℝ} (hR : 0 < R) :
    (∫ ξ in Ioi R, ‖F ξ‖) ≤ C/R := by
  calc
    _ ≤ ∫ ξ in Ioi R, C*(ξ^2)⁻¹ := by
      apply setIntegral_mono_on hi.norm.integrableOn ((inv_square_integrableOn hR).const_mul C)
        measurableSet_Ioi
      intro ξ hξ
      rw [← div_eq_mul_inv]
      apply (le_div_iff₀ (sq_pos_of_pos (hR.trans hξ))).mpr
      nlinarith [hd ξ]
    _ = C/R := by rw [integral_const_mul,inv_square_integral hR,div_eq_mul_inv]

lemma integral_left_tail (F : ℝ → ℝ) (R : ℝ) :
    (∫ ξ in Iio (-R), F ξ) = ∫ ξ in Ioi R, F (-ξ) := by
  have him : (fun ξ : ℝ => -ξ) '' Ioi R = Iio (-R) := by
    ext ξ
    simp only [mem_image,mem_Ioi,mem_Iio]
    constructor
    · rintro ⟨u,hu,rfl⟩; linarith
    · intro h; exact ⟨-ξ,by linarith,by simp⟩
  rw [← him]
  have h := integral_image_eq_integral_abs_deriv_smul (s := Ioi R) measurableSet_Ioi
    (fun ξ _ => (hasDerivAt_id ξ).neg.hasDerivWithinAt)
    (fun ξ _ υ _ h => neg_injective h) F
  simpa using h

lemma quadratic_decay_left_tail (F : ℝ → ℂ) (hi : Integrable F) (C : ℝ)
    (hd : ∀ ξ : ℝ, ξ^2*‖F ξ‖ ≤ C) {R : ℝ} (hR : 0 < R) :
    (∫ ξ in Iio (-R), ‖F ξ‖) ≤ C/R := by
  rw [integral_left_tail]
  apply quadratic_decay_right_tail (fun ξ => F (-ξ)) hi.comp_neg C _ hR
  intro ξ
  simpa only [neg_sq] using hd (-ξ)

noncomputable def logKernelComplex (u : ℝ) : ℂ := (logMajorKernel u : ℂ)

lemma logKernelComplex_integrable : Integrable logKernelComplex :=
  Complex.ofRealCLM.integrable_comp logMajorKernel_integrable

lemma logKernelComplex_continuous : Continuous logKernelComplex :=
  Complex.continuous_ofReal.comp logMajorKernel_continuous

lemma logKernelComplex_fourier_decay (ξ : ℝ) :
    ξ^2*‖𝓕 logKernelComplex ξ‖ ≤ 80/(4*Real.pi^2) := by
  have h := fourier_second_derivative_decay logKernelComplex_integrable
    (Complex.ofRealCLM.integrable_comp logMajorKernelD_integrable)
    (Complex.ofRealCLM.integrable_comp logMajorKernelD2_integrable)
    (fun u => (logMajorKernel_hasDerivAt u).ofReal_comp)
    (fun u => (logMajorKernelD_hasDerivAt u).ofReal_comp) ξ
  simp only [Function.comp_def,Complex.ofRealCLM_apply,Complex.norm_real,Real.norm_eq_abs] at h
  have hm := logMajorKernelD2_abs_integral_le
  have he : (2*Real.pi*|ξ|)^2 = (4*Real.pi^2)*ξ^2 := by
    nlinarith [sq_abs ξ]
  rw [he] at h
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4*Real.pi^2)).mpr
  nlinarith

lemma logKernelComplex_fourier_integrable : Integrable (𝓕 logKernelComplex) := by
  have hc : Continuous (𝓕 logKernelComplex) := by
    have he : 𝓕 logKernelComplex = VectorFourier.fourierIntegral Real.fourierChar volume
        (innerₗ ℝ) logKernelComplex := by
      funext ξ
      rw [Real.fourier_eq]
      rfl
    rw [he]
    exact VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (by fun_prop : Continuous (fun p : ℝ × ℝ => (innerₗ ℝ) p.1 p.2))
      logKernelComplex_integrable
  apply integrable_of_quadratic_decay _ hc (∫ u : ℝ, ‖logKernelComplex u‖) (80/(4*Real.pi^2))
  · intro ξ
    rw [Real.fourier_eq]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) logKernelComplex ξ
  · exact logKernelComplex_fourier_decay

end Helfgott

end

section

open MeasureTheory Set Filter
open scoped Topology FourierTransform

set_option backward.isDefEq.respectTransparency false

namespace Helfgott

noncomputable def fourierPhase (ξ u : ℝ) : ℂ := Real.fourierChar (-ξ*u)
noncomputable def fourierCoefficient (ξ : ℝ) : ℂ := 2*Real.pi*Complex.I*(ξ : ℂ)

lemma fourierPhase_norm (ξ u : ℝ) : ‖fourierPhase ξ u‖ = 1 := by
  exact Circle.norm_coe _

lemma fourierPhase_hasDerivAt (ξ u : ℝ) :
    HasDerivAt (fourierPhase ξ) (-fourierCoefficient ξ*fourierPhase ξ u) u := by
  have hi : HasDerivAt (fun v : ℝ => -ξ*v) (-ξ) u := by
    simpa using (hasDerivAt_id u).const_mul (-ξ)
  have h := (Real.hasDerivAt_fourierChar (-ξ*u)).scomp u hi
  have he : (-ξ) • (2*(Real.pi : ℂ)*Complex.I*(Real.fourierChar (-ξ*u) : ℂ)) =
      -fourierCoefficient ξ*fourierPhase ξ u := by
    rw [Complex.real_smul]
    dsimp only [fourierCoefficient,fourierPhase]
    rw [Complex.ofReal_neg]
    ring
  change HasDerivAt (fun v : ℝ => (Real.fourierChar (-ξ*v) : ℂ))
    (-fourierCoefficient ξ*fourierPhase ξ u) u
  rw [← he]
  exact h

lemma fourierPhase_continuous (ξ : ℝ) : Continuous (fourierPhase ξ) :=
  continuous_iff_continuousAt.mpr (fun u => (fourierPhase_hasDerivAt ξ u).continuousAt)

lemma fourierPhase_mul_integrableOn (ξ : ℝ) (f : ℝ → ℂ) (s : Set ℝ)
    (hf : IntegrableOn f s) : IntegrableOn (fun u => fourierPhase ξ u*f u) s := by
  apply hf.norm.mono' ((fourierPhase_continuous ξ).aestronglyMeasurable.mul hf.aestronglyMeasurable)
  exact ae_of_all _ (fun u => by simp only [Pi.mul_apply,norm_mul,fourierPhase_norm,one_mul,le_refl])

lemma fourierPhase_mul_tendsto (ξ : ℝ) (f : ℝ → ℂ)
    (hf : Tendsto f atBot (𝓝 0)) :
    Tendsto (fun u => fourierPhase ξ u*f u) atBot (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [norm_mul,fourierPhase_norm,one_mul,norm_zero] using hf.norm

lemma fourier_halfline_derivative (ξ c : ℝ) (f f' : ℝ → ℂ)
    (hf : IntegrableOn f (Iic c)) (hf' : IntegrableOn f' (Iic c))
    (hd : ∀ u ∈ Iic c, HasDerivAt f (f' u) u)
    (hz : Tendsto f atBot (𝓝 0)) :
    (∫ u in Iic c, fourierPhase ξ u*f' u) =
      fourierPhase ξ c*f c+fourierCoefficient ξ*(∫ u in Iic c, fourierPhase ξ u*f u) := by
  have hi0 := fourierPhase_mul_integrableOn ξ f (Iic c) hf
  have hi1 := fourierPhase_mul_integrableOn ξ f' (Iic c) hf'
  have hi := hi1.sub (hi0.const_mul (fourierCoefficient ξ))
  have hd' (u : ℝ) (hu : u ∈ Iic c) :
      HasDerivAt (fun u => fourierPhase ξ u*f u)
        (fourierPhase ξ u*f' u-fourierCoefficient ξ*(fourierPhase ξ u*f u)) u := by
    convert! (fourierPhase_hasDerivAt ξ u).mul (hd u hu) using 1
    ring
  have hftc := integral_Iic_of_hasDerivAt_of_tendsto' hd' hi
    (fourierPhase_mul_tendsto ξ f hz)
  rw [integral_sub hi1 (hi0.const_mul _),integral_const_mul,sub_zero] at hftc
  linear_combination hftc

lemma logKernelComplex_fourier_halfline (ξ : ℝ) :
    𝓕 logKernelComplex ξ =
      ∫ u in Iic (Real.log 2), fourierPhase ξ u*(logRawFn logRawPoly0 u : ℂ) := by
  have he : (fun u : ℝ => fourierPhase ξ u*logKernelComplex u) =
      (Iic (Real.log 2)).indicator
        (fun u => fourierPhase ξ u*(logRawFn logRawPoly0 u : ℂ)) := by
    funext u
    dsimp only [logKernelComplex]
    rw [logMajorKernel_eq_raw_indicator]
    by_cases hu : u ∈ Iic (Real.log 2)
    · simp [Set.indicator_of_mem hu]
    · simp [Set.indicator_of_notMem hu]
  rw [Real.fourier_eq]
  simp only [Real.inner_apply,Circle.smul_def,smul_eq_mul]
  have he' : (fun u : ℝ => (Real.fourierChar (-(u*ξ)) : ℂ)*logKernelComplex u) =
      (fun u : ℝ => fourierPhase ξ u*logKernelComplex u) := by
    funext u
    dsimp only [fourierPhase]
    congr 2
    ring
  rw [he',he,integral_indicator measurableSet_Iic]

lemma logKernelComplex_fourier_fourth_identity (ξ : ℝ) :
    (fourierCoefficient ξ)^4*𝓕 logKernelComplex ξ =
      (∫ u in Iic (Real.log 2), fourierPhase ξ u*(logRawFn logRawPoly4 u : ℂ))-
        fourierPhase ξ (Real.log 2)*(logRawFn logRawPoly3 (Real.log 2) : ℂ) := by
  have h0 := fourier_halfline_derivative ξ (Real.log 2)
    (fun u => (logRawFn logRawPoly0 u : ℂ)) (fun u => (logRawFn logRawPoly1 u : ℂ))
    (Complex.ofRealCLM.integrable_comp logRawPoly0_integrable)
    (Complex.ofRealCLM.integrable_comp logRawPoly1_integrable)
    (fun u _ => (logRawPoly0_hasDerivAt u).ofReal_comp)
    (Complex.continuous_ofReal.continuousAt.tendsto.comp logRawPoly0_tendsto)
  have h1 := fourier_halfline_derivative ξ (Real.log 2)
    (fun u => (logRawFn logRawPoly1 u : ℂ)) (fun u => (logRawFn logRawPoly2 u : ℂ))
    (Complex.ofRealCLM.integrable_comp logRawPoly1_integrable)
    (Complex.ofRealCLM.integrable_comp logRawPoly2_integrable)
    (fun u _ => (logRawPoly1_hasDerivAt u).ofReal_comp)
    (Complex.continuous_ofReal.continuousAt.tendsto.comp logRawPoly1_tendsto)
  have h2 := fourier_halfline_derivative ξ (Real.log 2)
    (fun u => (logRawFn logRawPoly2 u : ℂ)) (fun u => (logRawFn logRawPoly3 u : ℂ))
    (Complex.ofRealCLM.integrable_comp logRawPoly2_integrable)
    (Complex.ofRealCLM.integrable_comp logRawPoly3_integrable)
    (fun u _ => (logRawPoly2_hasDerivAt u).ofReal_comp)
    (Complex.continuous_ofReal.continuousAt.tendsto.comp logRawPoly2_tendsto)
  have h3 := fourier_halfline_derivative ξ (Real.log 2)
    (fun u => (logRawFn logRawPoly3 u : ℂ)) (fun u => (logRawFn logRawPoly4 u : ℂ))
    (Complex.ofRealCLM.integrable_comp logRawPoly3_integrable)
    (Complex.ofRealCLM.integrable_comp logRawPoly4_integrable)
    (fun u _ => (logRawPoly3_hasDerivAt u).ofReal_comp)
    (Complex.continuous_ofReal.continuousAt.tendsto.comp logRawPoly3_tendsto)
  simp only [Function.comp_def,Complex.ofRealCLM_apply,logRawPoly_endpoint.1,
    logRawPoly_endpoint.2.1,logRawPoly_endpoint.2.2.1,Complex.ofReal_zero,mul_zero,zero_add] at h0 h1 h2 h3
  rw [logKernelComplex_fourier_halfline]
  linear_combination -h3-(fourierCoefficient ξ)*h2-(fourierCoefficient ξ)^2*h1-
    (fourierCoefficient ξ)^3*h0

lemma logKernelComplex_fourier_fourth_decay (ξ : ℝ) :
    (2*Real.pi*|ξ|)^4*‖𝓕 logKernelComplex ξ‖ ≤ 40000 := by
  have hn : ‖fourierCoefficient ξ‖ = 2*Real.pi*|ξ| := by
    dsimp [fourierCoefficient]
    simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,Complex.norm_I,mul_one]
  have hi : ‖∫ u in Iic (Real.log 2), fourierPhase ξ u*(logRawFn logRawPoly4 u : ℂ)‖ ≤
      ∫ u in Iic (Real.log 2), |logRawFn logRawPoly4 u| := by
    calc
      _ ≤ ∫ u in Iic (Real.log 2), ‖fourierPhase ξ u*(logRawFn logRawPoly4 u : ℂ)‖ :=
        norm_integral_le_integral_norm _
      _ = _ := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro u _
        simp only [norm_mul,fourierPhase_norm,one_mul,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ = ‖(fourierCoefficient ξ)^4*𝓕 logKernelComplex ξ‖ := by rw [norm_mul,norm_pow,hn]
    _ = ‖(∫ u in Iic (Real.log 2), fourierPhase ξ u*(logRawFn logRawPoly4 u : ℂ))-
        fourierPhase ξ (Real.log 2)*(logRawFn logRawPoly3 (Real.log 2) : ℂ)‖ := by
      rw [logKernelComplex_fourier_fourth_identity]
    _ ≤ ‖∫ u in Iic (Real.log 2), fourierPhase ξ u*(logRawFn logRawPoly4 u : ℂ)‖+
        ‖fourierPhase ξ (Real.log 2)*(logRawFn logRawPoly3 (Real.log 2) : ℂ)‖ := norm_sub_le _ _
    _ ≤ 40000 := by
      simp only [norm_mul,fourierPhase_norm,one_mul,Complex.norm_real,Real.norm_eq_abs]
      linarith [logRawPoly4_abs_integral_le,logRawPoly3_endpoint_abs_le]

end Helfgott

end

section

open MeasureTheory Set
open scoped FourierTransform

namespace Helfgott

noncomputable def fourierCutoff (F : ℝ → ℂ) (R u : ℝ) : ℂ :=
  ∫ ξ in Icc (-R) R, Real.fourierChar (inner ℝ ξ u) • F ξ

lemma quadratic_decay_outside (F : ℝ → ℂ) (hi : Integrable F) (C : ℝ)
    (hd : ∀ ξ : ℝ, ξ^2*‖F ξ‖ ≤ C) {R : ℝ} (hR : 0 < R) :
    (∫ ξ in (Icc (-R) R)ᶜ, ‖F ξ‖) ≤ 2*C/R := by
  have hs : (Icc (-R) R)ᶜ = Iio (-R) ∪ Ioi R := by
    ext ξ
    simp only [mem_compl_iff,mem_Icc,mem_union,mem_Iio,mem_Ioi]
    constructor
    · intro h
      by_cases hx : ξ < -R
      · exact Or.inl hx
      · exact Or.inr (lt_of_not_ge (fun hr => h ⟨le_of_not_gt hx,hr⟩))
    · rintro (h | h) ⟨hl,hr⟩
      · exact (not_lt_of_ge hl) h
      · exact (not_lt_of_ge hr) h
  have hj : Disjoint (Iio (-R)) (Ioi R) := by
    apply disjoint_left.mpr
    intro ξ hl hr
    simp only [mem_Iio,mem_Ioi] at hl hr
    linarith
  rw [hs,setIntegral_union hj measurableSet_Ioi hi.norm.integrableOn hi.norm.integrableOn]
  rw [show 2*C/R=C/R+C/R by ring]
  exact add_le_add (quadratic_decay_left_tail F hi C hd hR)
    (quadratic_decay_right_tail F hi C hd hR)

lemma fourierCutoff_error (F : ℝ → ℂ) (hi : Integrable F) (C : ℝ)
    (hd : ∀ ξ : ℝ, ξ^2*‖F ξ‖ ≤ C) {R : ℝ} (hR : 0 < R) (u : ℝ) :
    ‖fourierCutoff F R u - 𝓕⁻ F u‖ ≤ 2*C/R := by
  have hint : Integrable (fun ξ => Real.fourierChar (inner ℝ ξ u) • F ξ) := by
    apply hi.norm.mono'
    · exact (Real.continuous_fourierChar.comp (by fun_prop)).aestronglyMeasurable.smul
        hi.aestronglyMeasurable
    · exact ae_of_all _ (fun ξ => (Circle.norm_smul _ _).le)
  have h := integral_add_compl (s := Icc (-R) R) measurableSet_Icc hint
  have heq : fourierCutoff F R u - 𝓕⁻ F u =
      -(∫ ξ in (Icc (-R) R)ᶜ, Real.fourierChar (inner ℝ ξ u) • F ξ) := by
    rw [fourierCutoff,Real.fourierInv_eq,← h]
    abel
  rw [heq,norm_neg]
  calc
    _ ≤ ∫ ξ in (Icc (-R) R)ᶜ, ‖Real.fourierChar (inner ℝ ξ u) • F ξ‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ ξ in (Icc (-R) R)ᶜ, ‖F ξ‖ := by simp only [Circle.norm_smul]
    _ ≤ _ := quadratic_decay_outside F hi C hd hR

theorem logKernel_fourierCutoff_error {H : ℝ} (hH : 0 < H) (u : ℝ) :
    ‖fourierCutoff (𝓕 logKernelComplex) (H/(2*Real.pi)) u-logKernelComplex u‖ ≤
      80/(Real.pi*H) := by
  have h := fourierCutoff_error (𝓕 logKernelComplex) logKernelComplex_fourier_integrable
    (80/(4*Real.pi^2)) logKernelComplex_fourier_decay
    (div_pos hH (by positivity : (0 : ℝ) < 2*Real.pi)) u
  rw [logKernelComplex_integrable.fourierInv_fourier_eq logKernelComplex_fourier_integrable
    logKernelComplex_continuous.continuousAt] at h
  have he : 2*(80/(4*Real.pi^2))/(H/(2*Real.pi)) = 80/(Real.pi*H) := by
    field_simp
    <;> ring
  rwa [he] at h

end Helfgott

end

section

open MeasureTheory Set
open scoped FourierTransform

namespace Helfgott

lemma inv_fourth_integrableOn {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun ξ : ℝ => (ξ^4)⁻¹) (Ioi R) := by
  simpa using integrableOn_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1) hR

lemma inv_fourth_integral {R : ℝ} (hR : 0 < R) :
    (∫ ξ in Ioi R, (ξ^4)⁻¹) = 1/(3*R^3) := by
  have h := integral_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1) hR
  norm_num [Real.rpow_neg_ofNat] at h
  convert! h using 1 <;> ring

lemma quartic_decay_right_tail (F : ℝ → ℂ) (hi : Integrable F) (C : ℝ)
    (hd : ∀ ξ : ℝ, ξ^4*‖F ξ‖ ≤ C) {R : ℝ} (hR : 0 < R) :
    (∫ ξ in Ioi R, ‖F ξ‖) ≤ C/(3*R^3) := by
  calc
    _ ≤ ∫ ξ in Ioi R, C*(ξ^4)⁻¹ := by
      apply setIntegral_mono_on hi.norm.integrableOn ((inv_fourth_integrableOn hR).const_mul C)
        measurableSet_Ioi
      intro ξ hξ
      rw [← div_eq_mul_inv]
      apply (le_div_iff₀ (pow_pos (hR.trans hξ) 4)).mpr
      nlinarith [hd ξ]
    _ = C/(3*R^3) := by rw [integral_const_mul,inv_fourth_integral hR]; ring

lemma quartic_decay_left_tail (F : ℝ → ℂ) (hi : Integrable F) (C : ℝ)
    (hd : ∀ ξ : ℝ, ξ^4*‖F ξ‖ ≤ C) {R : ℝ} (hR : 0 < R) :
    (∫ ξ in Iio (-R), ‖F ξ‖) ≤ C/(3*R^3) := by
  rw [integral_left_tail]
  apply quartic_decay_right_tail (fun ξ => F (-ξ)) hi.comp_neg C _ hR
  intro ξ
  convert! hd (-ξ) using 1 <;> ring

lemma quartic_decay_outside (F : ℝ → ℂ) (hi : Integrable F) (C : ℝ)
    (hd : ∀ ξ : ℝ, ξ^4*‖F ξ‖ ≤ C) {R : ℝ} (hR : 0 < R) :
    (∫ ξ in (Icc (-R) R)ᶜ, ‖F ξ‖) ≤ 2*C/(3*R^3) := by
  have hs : (Icc (-R) R)ᶜ = Iio (-R) ∪ Ioi R := by
    ext ξ
    simp only [mem_compl_iff,mem_Icc,mem_union,mem_Iio,mem_Ioi]
    constructor
    · intro h
      by_cases hx : ξ < -R
      · exact Or.inl hx
      · exact Or.inr (lt_of_not_ge (fun hr => h ⟨le_of_not_gt hx,hr⟩))
    · rintro (h | h) ⟨hl,hr⟩
      · exact (not_lt_of_ge hl) h
      · exact (not_lt_of_ge hr) h
  have hj : Disjoint (Iio (-R)) (Ioi R) := by
    apply disjoint_left.mpr
    intro ξ hl hr
    simp only [mem_Iio,mem_Ioi] at hl hr
    linarith
  rw [hs,setIntegral_union hj measurableSet_Ioi hi.norm.integrableOn hi.norm.integrableOn]
  rw [show 2*C/(3*R^3)=C/(3*R^3)+C/(3*R^3) by ring]
  exact add_le_add (quartic_decay_left_tail F hi C hd hR)
    (quartic_decay_right_tail F hi C hd hR)

lemma fourierCutoff_fourth_error (F : ℝ → ℂ) (hi : Integrable F) (C : ℝ)
    (hd : ∀ ξ : ℝ, ξ^4*‖F ξ‖ ≤ C) {R : ℝ} (hR : 0 < R) (u : ℝ) :
    ‖fourierCutoff F R u - 𝓕⁻ F u‖ ≤ 2*C/(3*R^3) := by
  have hint : Integrable (fun ξ => Real.fourierChar (inner ℝ ξ u) • F ξ) := by
    apply hi.norm.mono'
    · exact (Real.continuous_fourierChar.comp (by fun_prop)).aestronglyMeasurable.smul
        hi.aestronglyMeasurable
    · exact ae_of_all _ (fun ξ => (Circle.norm_smul _ _).le)
  have h := integral_add_compl (s := Icc (-R) R) measurableSet_Icc hint
  have heq : fourierCutoff F R u - 𝓕⁻ F u =
      -(∫ ξ in (Icc (-R) R)ᶜ, Real.fourierChar (inner ℝ ξ u) • F ξ) := by
    rw [fourierCutoff,Real.fourierInv_eq,← h]
    abel
  rw [heq,norm_neg]
  calc
    _ ≤ ∫ ξ in (Icc (-R) R)ᶜ, ‖Real.fourierChar (inner ℝ ξ u) • F ξ‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ ξ in (Icc (-R) R)ᶜ, ‖F ξ‖ := by simp only [Circle.norm_smul]
    _ ≤ _ := quartic_decay_outside F hi C hd hR

lemma logKernelComplex_fourier_fourth_normalized (ξ : ℝ) :
    ξ^4*‖𝓕 logKernelComplex ξ‖ ≤ 40000/(16*Real.pi^4) := by
  have h := logKernelComplex_fourier_fourth_decay ξ
  have hs : |ξ|^4=ξ^4 := by
    calc
      |ξ|^4 = (|ξ|^2)^2 := by ring
      _ = (ξ^2)^2 := by rw [sq_abs]
      _ = ξ^4 := by ring
  have he : (2*Real.pi*|ξ|)^4=(16*Real.pi^4)*ξ^4 := by
    rw [mul_pow,mul_pow,hs]; norm_num
  rw [he] at h
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 16*Real.pi^4)).mpr
  nlinarith

theorem logKernel_fourierCutoff_fourth_error {H : ℝ} (hH : 0 < H) (u : ℝ) :
    ‖fourierCutoff (𝓕 logKernelComplex) (H/(2*Real.pi)) u-logKernelComplex u‖ ≤
      40000/(3*Real.pi*H^3) := by
  have h := fourierCutoff_fourth_error (𝓕 logKernelComplex) logKernelComplex_fourier_integrable
    (40000/(16*Real.pi^4)) logKernelComplex_fourier_fourth_normalized
    (div_pos hH (by positivity : (0 : ℝ) < 2*Real.pi)) u
  rw [logKernelComplex_integrable.fourierInv_fourier_eq logKernelComplex_fourier_integrable
    logKernelComplex_continuous.continuousAt] at h
  have he : 2*(40000/(16*Real.pi^4))/(3*(H/(2*Real.pi))^3) =
      40000/(3*Real.pi*H^3) := by
    field_simp [ne_of_gt hH,Real.pi_ne_zero]
    <;> ring
  rwa [he] at h

end Helfgott

end

section

open MeasureTheory Set
open scoped FourierTransform

set_option backward.isDefEq.respectTransparency false

namespace Helfgott

lemma integral_fourierChar_interval (R v : ℝ) (hR : 0 ≤ R) :
    (∫ ξ in Icc (-R) R, (Real.fourierChar (ξ*v) : ℂ)) =
      ((2*R*Real.sinc (2*Real.pi*R*v) : ℝ) : ℂ) := by
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
  by_cases hv : v=0
  · subst v
    simp [intervalIntegral.integral_const,Complex.real_smul]
    <;> ring
  · have hc : 2*Real.pi*v ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hv
    calc
      _ = ∫ ξ in -R..R, Complex.exp (((ξ*(2*Real.pi*v) : ℝ) : ℂ)*Complex.I) := by
        apply intervalIntegral.integral_congr
        intro ξ _
        dsimp only
        rw [Real.fourierChar_apply]
        congr 2
        push_cast
        ring
      _ = (2*Real.pi*v)⁻¹ • ∫ t in -(R*(2*Real.pi*v))..R*(2*Real.pi*v),
          Complex.exp ((t : ℂ)*Complex.I) := by
        have h := intervalIntegral.integral_comp_mul_right
          (fun t : ℝ => Complex.exp ((t : ℂ)*Complex.I)) (a := -R) (b := R) hc
        simpa only [neg_mul] using h
      _ = (2*Real.pi*v)⁻¹ • (2*(R*(2*Real.pi*v))*Real.sinc (R*(2*Real.pi*v)) : ℂ) := by
        rw [integral_exp_mul_I_eq_sinc]
        push_cast
        rfl
      _ = _ := by
        rw [Complex.real_smul]
        have he : R*(2*Real.pi*v)=2*Real.pi*R*v := by ring
        rw [he]
        push_cast
        have hvC : (v : ℂ) ≠ 0 := by exact_mod_cast hv
        have hpC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
        field_simp [hvC,hpC]
        <;> ring

lemma fourierCutoff_eq_sinc_convolution (f : ℝ → ℂ) (hi : Integrable f)
    (R u : ℝ) (hR : 0 ≤ R) :
    fourierCutoff (𝓕 f) R u = ∫ v : ℝ,
      ((2*R*Real.sinc (2*Real.pi*R*(u-v)) : ℝ) : ℂ)*f v := by
  let g : ℝ → ℝ → ℂ := fun ξ v => Real.fourierChar (inner ℝ ξ (u-v)) • f v
  have hg : Integrable (Function.uncurry g) ((volume.restrict (Icc (-R) R)).prod volume) := by
    apply (hi.norm.comp_snd (volume.restrict (Icc (-R) R))).mono'
    · exact (Real.continuous_fourierChar.comp (by fun_prop)).aestronglyMeasurable.smul
        hi.aestronglyMeasurable.comp_snd
    · exact ae_of_all _ (fun p => (Circle.norm_smul _ _).le)
  have heq : fourierCutoff (𝓕 f) R u = ∫ ξ in Icc (-R) R, ∫ v : ℝ, g ξ v := by
    unfold fourierCutoff
    simp_rw [Real.fourier_eq,Circle.smul_def,smul_eq_mul,← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Icc
    intro ξ _
    apply integral_congr_ae
    exact ae_of_all _ (fun v => by
      dsimp only [g]
      rw [Circle.smul_def,smul_eq_mul,← mul_assoc,← Circle.coe_mul,← Real.fourierChar.map_add_eq_mul]
      congr 2
      simp only [Real.inner_apply]
      ring)
  rw [heq,integral_integral_swap hg]
  apply integral_congr_ae
  exact ae_of_all _ (fun v => by
    dsimp only [g]
    simp only [Real.inner_apply,Circle.smul_def,smul_eq_mul]
    rw [integral_mul_const,integral_fourierChar_interval R (u-v) hR])

lemma bandLimitedMajorKernel_log_eq (H u : ℝ) :
    bandLimitedMajorKernel H (Real.exp u) = ∫ v : ℝ,
      logMajorKernel (u-v)*(H/Real.pi*Real.sinc (H*v)) := by
  unfold bandLimitedMajorKernel mellinConv
  rw [← integral_comp_exp_univ (fun w => majorKernel (Real.exp u/w)*bandKernel H w/w)]
  apply integral_congr_ae
  exact ae_of_all _ (fun v => by
    unfold logMajorKernel bandKernel
    dsimp only
    rw [Real.log_exp,Real.exp_sub]
    field_simp)

theorem bandLimitedMajorKernel_fourierCutoff (H u : ℝ) (hH : 0 ≤ H) :
    (bandLimitedMajorKernel H (Real.exp u) : ℂ) =
      fourierCutoff (𝓕 logKernelComplex) (H/(2*Real.pi)) u := by
  rw [fourierCutoff_eq_sinc_convolution _ logKernelComplex_integrable _ _
    (div_nonneg hH (by positivity)),bandLimitedMajorKernel_log_eq]
  rw [← integral_complex_ofReal]
  conv_rhs => rw [← integral_sub_left_eq_self _ volume u]
  apply integral_congr_ae
  exact ae_of_all _ (fun v => by
    dsimp only [logKernelComplex]
    have he : 2*Real.pi*(H/(2*Real.pi))*(u-(u-v))=H*v := by field_simp; ring
    have hc : 2*(H/(2*Real.pi))=H/Real.pi := by field_simp
    rw [he,hc]
    push_cast
    ring)

end Helfgott

end

section

open MeasureTheory Set

namespace Helfgott

lemma mellin_inverse_weight (F : ℝ → ℝ) (w : ℝ) (hw : 0 < w) :
    w^(-2 : ℝ) * (F ((w^(-1 : ℝ))⁻¹)/(w^(-1 : ℝ))) = F w/w := by
  rw [Real.rpow_neg_one,inv_inv,Real.rpow_neg hw.le,Real.rpow_two]
  field_simp

theorem integral_mellin_inverse (F : ℝ → ℝ) :
    (∫ w in Ioi (0 : ℝ), F w/w) = ∫ w in Ioi (0 : ℝ), F w⁻¹/w := by
  have h := integral_comp_rpow_Ioi (fun w : ℝ => F w⁻¹/w) (p := (-1 : ℝ)) (by norm_num)
  norm_num only [abs_neg,abs_one,neg_sub,one_add_one_eq_two,smul_eq_mul,one_mul] at h
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro w hw
  exact (mellin_inverse_weight F w hw).symm

theorem integrable_mellin_inverse (F : ℝ → ℝ) :
    IntegrableOn (fun w : ℝ => F w/w) (Ioi (0 : ℝ)) ↔
      IntegrableOn (fun w : ℝ => F w⁻¹/w) (Ioi (0 : ℝ)) := by
  have h := integrableOn_Ioi_comp_rpow_iff' (fun w : ℝ => F w⁻¹/w) (p := (-1 : ℝ)) (by norm_num)
  norm_num only [neg_sub,one_add_one_eq_two,smul_eq_mul] at h
  rw [← h]
  apply integrableOn_congr_fun _ measurableSet_Ioi
  intro w hw
  exact (mellin_inverse_weight F w hw).symm

end Helfgott

end

section

open MeasureTheory Set Filter

namespace Helfgott

private noncomputable def weightedMajorKernel (t : ℝ) : ℝ :=
  (Icc (0 : ℝ) 2).indicator (fun t => t*(2-t)^3*Real.exp (t-1/2)) t

private lemma weightedMajorKernel_nonneg (t : ℝ) : 0 ≤ weightedMajorKernel t := by
  by_cases ht : t ∈ Icc (0 : ℝ) 2
  · rw [weightedMajorKernel,indicator_of_mem ht]
    have h : 0 ≤ 2-t := by linarith [ht.2]
    have h0 : 0 ≤ t := ht.1
    positivity
  · simp [weightedMajorKernel,ht]

private lemma weightedMajorKernel_continuous : Continuous weightedMajorKernel := by
  unfold weightedMajorKernel
  apply continuous_indicator
  · intro t ht
    have hb := frontier_subset_closure ht
    rw [isClosed_Icc.closure_eq] at hb
    have hn : t ∉ interior (Icc (0 : ℝ) 2) := ht.2
    rw [interior_Icc] at hn
    have he : t=0 ∨ t=2 := by
      by_contra hh
      apply hn
      have h0 : t ≠ 0 := by tauto
      have h2 : t ≠ 2 := by tauto
      exact ⟨lt_of_le_of_ne hb.1 (Ne.symm h0),lt_of_le_of_ne hb.2 h2⟩
    rcases he with rfl | rfl <;> norm_num
  · exact (by fun_prop : Continuous (fun t : ℝ => t*(2-t)^3*Real.exp (t-1/2))).continuousOn

private lemma weightedMajorKernel_compact : HasCompactSupport weightedMajorKernel := by
  apply HasCompactSupport.intro (K := Icc (0 : ℝ) 2) isCompact_Icc
  intro t ht
  simp [weightedMajorKernel,ht]

private lemma weightedMajorKernel_integrable : Integrable weightedMajorKernel :=
  weightedMajorKernel_continuous.integrable_of_hasCompactSupport weightedMajorKernel_compact

private lemma majorKernel_eq_weighted (t : ℝ) : majorKernel t = t*weightedMajorKernel t := by
  by_cases ht : t ∈ Icc (0 : ℝ) 2
  · simp only [majorKernel,weightedMajorKernel,indicator_of_mem ht]
    ring
  · simp [majorKernel,weightedMajorKernel,ht]

lemma bandKernel_abs_le (H w : ℝ) : |bandKernel H w| ≤ |H|/Real.pi := by
  unfold bandKernel
  rw [abs_mul,abs_div,abs_of_pos Real.pi_pos]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_sinc_le_one _)

private lemma inverse_major_integrand (H t v : ℝ) (hv : 0 < v) :
    majorKernel (t/v⁻¹)*bandKernel H v⁻¹/v =
      t*weightedMajorKernel (t*v)*bandKernel H v⁻¹ := by
  rw [div_inv_eq_mul,majorKernel_eq_weighted]
  field_simp

private lemma inverse_major_integrable (H t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun v : ℝ => t*weightedMajorKernel (t*v)*bandKernel H v⁻¹) (Ioi (0 : ℝ)) := by
  have hk := weightedMajorKernel_continuous
  have hi : IntegrableOn (fun v : ℝ => t*weightedMajorKernel (t*v)) (Ioi (0 : ℝ)) :=
    ((weightedMajorKernel_integrable.comp_mul_left' ht.ne').const_mul t).integrableOn
  apply (hi.mul_const (|H|/Real.pi)).mono'
  · have hm : Measurable (fun v : ℝ => t*weightedMajorKernel (t*v)*bandKernel H v⁻¹) := by
      unfold bandKernel
      fun_prop
    exact hm.aestronglyMeasurable
  · exact Eventually.of_forall (fun v => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg
        (mul_nonneg ht.le (weightedMajorKernel_nonneg _))]
      exact mul_le_mul_of_nonneg_left (bandKernel_abs_le H v⁻¹)
        (mul_nonneg ht.le (weightedMajorKernel_nonneg _)))

lemma bandLimitedMajorKernel_integrable (H t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun w : ℝ => majorKernel (t/w)*bandKernel H w/w) (Ioi (0 : ℝ)) := by
  apply (integrable_mellin_inverse (fun w => majorKernel (t/w)*bandKernel H w)).mpr
  apply (inverse_major_integrable H t ht).congr_fun _ measurableSet_Ioi
  intro v hv
  exact (inverse_major_integrand H t v hv).symm

lemma bandLimitedMajorKernel_inverse (H t : ℝ) :
    bandLimitedMajorKernel H t =
      ∫ v in Ioi (0 : ℝ), t*weightedMajorKernel (t*v)*bandKernel H v⁻¹ := by
  unfold bandLimitedMajorKernel mellinConv
  rw [integral_mellin_inverse (fun w => majorKernel (t/w)*bandKernel H w)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  exact inverse_major_integrand H t v hv

private lemma bandLimitedMajorKernel_abs_le_pos (H t : ℝ) (ht : 0 < t) :
    |bandLimitedMajorKernel H t| ≤ (|H|/Real.pi)*(∫ v in Ioi (0 : ℝ), weightedMajorKernel v) := by
  rw [bandLimitedMajorKernel_inverse]
  have hi : IntegrableOn (fun v : ℝ => t*weightedMajorKernel (t*v)) (Ioi (0 : ℝ)) :=
    ((weightedMajorKernel_integrable.comp_mul_left' ht.ne').const_mul t).integrableOn
  have hn : |∫ v in Ioi (0 : ℝ), t*weightedMajorKernel (t*v)*bandKernel H v⁻¹| ≤
      ∫ v in Ioi (0 : ℝ), (|H|/Real.pi)*(t*weightedMajorKernel (t*v)) := by
    rw [← Real.norm_eq_abs]
    apply (norm_integral_le_integral_norm _).trans
    apply integral_mono (inverse_major_integrable H t ht).norm (hi.const_mul (|H|/Real.pi))
    intro v
    dsimp only
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (mul_nonneg ht.le (weightedMajorKernel_nonneg _))]
    convert! mul_le_mul_of_nonneg_left (bandKernel_abs_le H v⁻¹)
      (mul_nonneg ht.le (weightedMajorKernel_nonneg _)) using 1 <;> ring
  refine hn.trans_eq ?_
  rw [integral_const_mul,integral_const_mul,integral_comp_mul_left_Ioi weightedMajorKernel 0 ht]
  simp only [mul_zero,smul_eq_mul]
  field_simp

lemma majorKernel_zero_of_nonpos (t : ℝ) (ht : t ≤ 0) : majorKernel t = 0 := by
  by_cases hz : t = 0
  · subst t; simp [majorKernel]
  · have hn : t ∉ Icc (0 : ℝ) 2 := by intro h; exact hz (le_antisymm ht h.1)
    simp [majorKernel,hn]

lemma bandLimitedMajorKernel_zero_of_nonpos (H t : ℝ) (ht : t ≤ 0) :
    bandLimitedMajorKernel H t = 0 := by
  unfold bandLimitedMajorKernel mellinConv
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  rw [majorKernel_zero_of_nonpos (t/w) (div_nonpos_of_nonpos_of_nonneg ht hw.le)]
  simp

theorem etaPlus_gaussian_envelope :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |etaPlus t| ≤ C*|t| *Real.exp (-(t^2)/2) := by
  let C : ℝ := ((200 : ℝ)/Real.pi)*(∫ v in Ioi (0 : ℝ), weightedMajorKernel v)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by positivity) (integral_nonneg weightedMajorKernel_nonneg)
  refine ⟨C,hC,?_⟩
  intro t
  have hb : |bandLimitedMajorKernel 200 t| ≤ C := by
    by_cases ht : 0 < t
    · simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 200)] using
        bandLimitedMajorKernel_abs_le_pos 200 t ht
    · rw [bandLimitedMajorKernel_zero_of_nonpos 200 t (le_of_not_gt ht),abs_zero]
      exact hC
  unfold etaPlus
  rw [abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (abs_nonneg t)) (Real.exp_pos _).le

end Helfgott

end

section

open MeasureTheory Set
open scoped FourierTransform

namespace Helfgott

lemma etaCircle_eq_majorKernel (t : ℝ) :
    etaCircle t = majorKernel t*t*Real.exp (-(t^2)/2) := by
  by_cases ht : t ∈ Icc (0 : ℝ) 2
  · simp only [etaCircle,majorKernel,Set.indicator_of_mem ht]
    rw [show -((t-1)^2)/2 = (t-1/2)+(-(t^2)/2) by ring,Real.exp_add]
    ring
  · simp [etaCircle,majorKernel,Set.indicator_of_notMem ht]

lemma etaCircle_abs_le_one (t : ℝ) : |etaCircle t| ≤ 1 := by
  by_cases ht : t ∈ Icc (0 : ℝ) 2
  · have htn : 0 ≤ t*(2-t) := mul_nonneg ht.1 (by linarith [ht.2])
    have htl : t*(2-t) ≤ 1 := by nlinarith [sq_nonneg (t-1)]
    have hp : (t*(2-t))^3 ≤ 1 := by simpa using pow_le_pow_left₀ htn htl 3
    have he : Real.exp (-((t-1)^2)/2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (t-1)])
    rw [etaCircle,Set.indicator_of_mem ht,
      show t^3*(2-t)^3=(t*(2-t))^3 by ring,abs_of_nonneg (by positivity)]
    exact mul_le_one₀ hp (by positivity) he
  · simp [etaCircle,Set.indicator_of_notMem ht]

lemma gaussian_factor_abs_le (t : ℝ) : |t| *Real.exp (-(t^2)/2) ≤ 5/8 := by
  have hs : (Real.exp (-(t^2)/2))^2 = Real.exp (-(t^2)) := by
    rw [sq,← Real.exp_add]
    congr 1
    ring
  have hn : Real.exp (-1 : ℝ) ≤ 25/64 := by
    rw [Real.exp_neg,← one_div]
    apply (div_le_iff₀ (Real.exp_pos (1 : ℝ))).mpr
    nlinarith [Real.exp_one_gt_d9]
  have h := Real.mul_exp_neg_le_exp_neg_one (t^2)
  have he : (|t| *Real.exp (-(t^2)/2))^2 = t^2*Real.exp (-(t^2)) := by
    rw [mul_pow,sq_abs,hs]
  have hpos : 0 ≤ |t| *Real.exp (-(t^2)/2) := by positivity
  nlinarith

lemma bandLimitedMajorKernel_error {H t : ℝ} (hH : 0 < H) (ht : 0 < t) :
    |bandLimitedMajorKernel H t-majorKernel t| ≤ 80/(Real.pi*H) := by
  have h := logKernel_fourierCutoff_error hH (Real.log t)
  rw [← bandLimitedMajorKernel_fourierCutoff H (Real.log t) hH.le] at h
  simpa only [logKernelComplex,logMajorKernel,Real.exp_log ht,← Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs] using h

theorem etaPlus_abs_le (t : ℝ) : |etaPlus t| ≤ (1079955/1000000 : ℝ) := by
  by_cases ht : 0 < t
  · have hb := bandLimitedMajorKernel_error (by norm_num : (0 : ℝ) < 200) ht
    have hdiff : etaPlus t-etaCircle t =
        (bandLimitedMajorKernel 200 t-majorKernel t)*t*Real.exp (-(t^2)/2) := by
      rw [etaCircle_eq_majorKernel]
      unfold etaPlus
      ring
    have hd : |etaPlus t-etaCircle t| ≤ (80/(Real.pi*200))*(5/8) := by
      rw [hdiff,abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
      calc
        _ = |bandLimitedMajorKernel 200 t-majorKernel t| *(|t| *Real.exp (-(t^2)/2)) := by ring
        _ ≤ (80/(Real.pi*200))*(5/8) := by
          gcongr
          exact gaussian_factor_abs_le t
    have hnum : (80/(Real.pi*200))*(5/8) ≤ (79955/1000000 : ℝ) := by
      have he : (80/(Real.pi*200))*(5/8)=1/(4*Real.pi) := by field_simp; norm_num
      rw [he]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4*Real.pi)).mpr
      nlinarith [Real.pi_gt_d2]
    have htri : |etaPlus t| ≤ |etaPlus t-etaCircle t|+|etaCircle t| := by
      simpa only [sub_add_cancel] using abs_add_le (etaPlus t-etaCircle t) (etaCircle t)
    linarith [etaCircle_abs_le_one t]
  · rw [etaPlus,bandLimitedMajorKernel_zero_of_nonpos 200 t (le_of_not_gt ht)]
    norm_num

end Helfgott
end

section

open MeasureTheory Filter Set
open scoped Topology

namespace Helfgott

private lemma body_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => s^3 * (2-s)^3 * Real.exp (-((s-1)^2)/2))
      (-(t-1) * (1-(t-1)^2)^2 * (7-(t-1)^2) * Real.exp (-((t-1)^2)/2)) t := by
  convert! ((((hasDerivAt_id t).pow 3).mul
    (((hasDerivAt_const t (2 : ℝ)).sub (hasDerivAt_id t)).pow 3)).mul
    (((((hasDerivAt_id t).sub_const 1).pow 2).neg.div_const 2).exp)) using 1 <;>
    simp <;> ring

theorem etaCircle_hasDerivAt (t : ℝ) :
    HasDerivAt etaCircle
      ((Set.Icc (0 : ℝ) 2).indicator (fun t =>
        -(t-1) * (1-(t-1)^2)^2 * (7-(t-1)^2) * Real.exp (-((t-1)^2)/2)) t) t := by
  by_cases ht : t ∈ Set.Icc (0 : ℝ) 2
  · rw [Set.indicator_of_mem ht]
    by_cases hboundary : t = 0 ∨ t = 2
    · have hval : etaCircle t = 0 := by
        rcases hboundary with rfl | rfl <;> norm_num [etaCircle]
      have hd : -(t-1) * (1-(t-1)^2)^2 * (7-(t-1)^2) * Real.exp (-((t-1)^2)/2) = 0 := by
        rcases hboundary with rfl | rfl <;> norm_num
      rw [hd]
      have hinside : HasDerivWithinAt etaCircle 0 (Set.Icc (0 : ℝ) 2) t := by
        have h := (body_hasDerivAt t).hasDerivWithinAt (s := Set.Icc (0 : ℝ) 2)
        rw [hd] at h
        apply h.congr
        · intro x hx; simp only [etaCircle, Set.indicator_of_mem hx]
        · simp only [etaCircle, Set.indicator_of_mem ht]
      have houtside : HasDerivWithinAt etaCircle 0 (Set.Icc (0 : ℝ) 2)ᶜ t := by
        apply (hasDerivAt_const t (0 : ℝ)).hasDerivWithinAt.congr
        · intro x hx; simp only [etaCircle, Set.indicator_of_notMem hx]
        · exact hval
      simpa only [Set.union_compl_self, hasDerivWithinAt_univ] using hinside.union houtside
    · have h0 : 0 < t := lt_of_le_of_ne ht.1 (by tauto)
      have h2 : t < 2 := lt_of_le_of_ne ht.2 (by tauto)
      apply (body_hasDerivAt t).congr_of_eventuallyEq
      filter_upwards [Icc_mem_nhds h0 h2] with x hx
      simp only [etaCircle, Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem ht]
    apply (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds ht] with x hx
    simp only [etaCircle, Set.indicator_of_notMem hx]

lemma etaCircle_continuous : Continuous etaCircle :=
  continuous_iff_continuousAt.mpr (fun t => (etaCircle_hasDerivAt t).continuousAt)

lemma etaCircle_nonneg (t : ℝ) : 0 ≤ etaCircle t := by
  by_cases ht : t ∈ Set.Icc (0 : ℝ) 2
  · simp only [etaCircle, Set.indicator_of_mem ht]
    have h2 : 0 ≤ 2-t := sub_nonneg.mpr ht.2
    have h0 : 0 ≤ t := ht.1
    positivity
  · simp only [etaCircle, Set.indicator_of_notMem ht, le_refl]

lemma etaCircle_symmetric (t : ℝ) : etaCircle (2-t) = etaCircle t := by
  by_cases ht : t ∈ Set.Icc (0 : ℝ) 2
  · have ht' : 2-t ∈ Set.Icc (0 : ℝ) 2 := by constructor <;> linarith [ht.1,ht.2]
    simp only [etaCircle, Set.indicator_of_mem ht, Set.indicator_of_mem ht']
    have he : -((2-t-1)^2)/2 = -((t-1)^2)/2 := by ring
    rw [he]
    ring
  · have ht' : 2-t ∉ Set.Icc (0 : ℝ) 2 := by
      intro h; apply ht; constructor <;> linarith [h.1,h.2]
    simp only [etaCircle, Set.indicator_of_notMem ht, Set.indicator_of_notMem ht']

lemma etaCircle_hasCompactSupport : HasCompactSupport etaCircle := by
  apply HasCompactSupport.intro (K := Set.Icc (0 : ℝ) 2) isCompact_Icc
  intro t ht
  simp only [etaCircle,Set.indicator_of_notMem ht]

lemma etaCircle_integrable : Integrable etaCircle :=
  etaCircle_continuous.integrable_of_hasCompactSupport etaCircle_hasCompactSupport

lemma etaCircle_square_integrable : Integrable (fun t => etaCircle t ^ 2) := by
  apply (etaCircle_continuous.pow 2).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (K := Set.Icc (0 : ℝ) 2) isCompact_Icc
  intro t ht
  change etaCircle t ^ 2 = 0
  simp only [etaCircle,Set.indicator_of_notMem ht,zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

lemma etaCircle_deriv_continuous : Continuous (fun t =>
    ((Set.Icc (0 : ℝ) 2).indicator (fun t =>
      -(t-1) * (1-(t-1)^2)^2 * (7-(t-1)^2) * Real.exp (-((t-1)^2)/2)) t)) := by
  apply continuous_indicator
  · intro t ht
    have hb := frontier_subset_closure ht
    rw [isClosed_Icc.closure_eq] at hb
    have hn : t ∉ interior (Set.Icc (0 : ℝ) 2) := ht.2
    rw [interior_Icc] at hn
    have he : t=0 ∨ t=2 := by
      by_contra hh
      apply hn
      have hne0 : t ≠ 0 := by tauto
      have hne2 : t ≠ 2 := by tauto
      exact ⟨lt_of_le_of_ne hb.1 (Ne.symm hne0),lt_of_le_of_ne hb.2 hne2⟩
    rcases he with rfl | rfl <;> norm_num
  · apply Continuous.continuousOn
    fun_prop

lemma etaCircle_deriv_square_integrable : Integrable (fun t =>
    (((Set.Icc (0 : ℝ) 2).indicator (fun t =>
      -(t-1) * (1-(t-1)^2)^2 * (7-(t-1)^2) * Real.exp (-((t-1)^2)/2)) t))^2) := by
  apply (etaCircle_deriv_continuous.pow 2).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (K := Set.Icc (0 : ℝ) 2) isCompact_Icc
  intro t ht
  change (((Set.Icc (0 : ℝ) 2).indicator (fun t =>
    -(t-1) * (1-(t-1)^2)^2 * (7-(t-1)^2) * Real.exp (-((t-1)^2)/2)) t))^2 = 0
  simp only [Set.indicator_of_notMem ht,zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

end Helfgott


end

section

open MeasureTheory Set
open scoped FourierTransform

set_option backward.isDefEq.respectTransparency false

namespace Helfgott

lemma fourierCutoff_continuous (F : ℝ → ℂ) (hi : Integrable F) (R : ℝ) :
    Continuous (fourierCutoff F R) := by
  unfold fourierCutoff
  apply continuous_of_dominated (bound := fun ξ => ‖F ξ‖)
  · intro u
    exact (Real.continuous_fourierChar.comp (by fun_prop)).aestronglyMeasurable.smul
      hi.integrableOn.aestronglyMeasurable
  · intro u
    exact ae_of_all _ (fun ξ => (Circle.norm_smul _ _).le)
  · exact hi.norm.integrableOn
  · exact ae_of_all _ (fun ξ => by
      have hc : Continuous (fun u : ℝ => Real.fourierChar (inner ℝ ξ u)) :=
        Real.continuous_fourierChar.comp (by fun_prop)
      exact hc.smul continuous_const)

lemma etaPlus_measurable : Measurable etaPlus := by
  let g : ℝ → ℝ := fun t =>
    (fourierCutoff (𝓕 logKernelComplex) (200/(2*Real.pi)) (Real.log t)).re*
      t*Real.exp (-(t^2)/2)
  have hg : Measurable g := by
    have hc := Complex.continuous_re.comp (fourierCutoff_continuous (𝓕 logKernelComplex)
      logKernelComplex_fourier_integrable (200/(2*Real.pi)))
    exact ((hc.measurable.comp Real.measurable_log).mul measurable_id).mul (by fun_prop)
  have he : etaPlus = fun t => if 0 < t then g t else 0 := by
    funext t
    by_cases ht : 0 < t
    · rw [if_pos ht]
      have h := bandLimitedMajorKernel_fourierCutoff 200 (Real.log t) (by norm_num)
      rw [Real.exp_log ht] at h
      have hr := congrArg Complex.re h
      dsimp only [etaPlus,g]
      rw [← hr,Complex.ofReal_re]
    · rw [if_neg ht,etaPlus,bandLimitedMajorKernel_zero_of_nonpos 200 t (le_of_not_gt ht)]
      ring
  rw [he]
  exact hg.ite (measurableSet_lt measurable_const measurable_id) measurable_const

lemma bandLimitedMajorKernel_fourth_error {H t : ℝ} (hH : 0 < H) (ht : 0 < t) :
    |bandLimitedMajorKernel H t-majorKernel t| ≤ 40000/(3*Real.pi*H^3) := by
  have h := logKernel_fourierCutoff_fourth_error hH (Real.log t)
  rw [← bandLimitedMajorKernel_fourierCutoff H (Real.log t) hH.le] at h
  simpa only [logKernelComplex,logMajorKernel,Real.exp_log ht,← Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs] using h

lemma etaCircle_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) : etaCircle t = 0 := by
  by_cases hz : t = 0
  · simp [hz,etaCircle]
  · have hn : t ∉ Icc (0 : ℝ) 2 := by intro h; exact hz (le_antisymm ht h.1)
    simp [etaCircle,Set.indicator_of_notMem hn]

lemma etaPlus_approx_pointwise (t : ℝ) :
    |etaPlus t-etaCircle t| ≤
      (1/1800 : ℝ)*(Ioi (0 : ℝ)).indicator (fun t => t*Real.exp (-(t^2)/2)) t := by
  by_cases ht : 0 < t
  · rw [Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
    have hb := bandLimitedMajorKernel_fourth_error (by norm_num : (0 : ℝ) < 200) ht
    have hnum : 40000/(3*Real.pi*(200 : ℝ)^3) ≤ (1/1800 : ℝ) := by
      have he : 40000/(3*Real.pi*(200 : ℝ)^3)=1/(600*Real.pi) := by field_simp; norm_num
      rw [he]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 600*Real.pi)).mpr
      nlinarith [Real.pi_gt_three]
    have he : etaPlus t-etaCircle t =
        (bandLimitedMajorKernel 200 t-majorKernel t)*t*Real.exp (-(t^2)/2) := by
      rw [etaCircle_eq_majorKernel]
      unfold etaPlus
      ring
    rw [he,abs_mul,abs_mul,abs_of_pos ht,abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (1/1800)*t*Real.exp (-(t^2)/2) := by gcongr; exact hb.trans hnum
      _ = _ := by ring
  · rw [etaCircle_zero_of_nonpos (le_of_not_gt ht),etaPlus,
      bandLimitedMajorKernel_zero_of_nonpos 200 t (le_of_not_gt ht),
      Set.indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht)]
    norm_num

end Helfgott

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 5000
open MeasureTheory Set Finset

namespace Helfgott

noncomputable def kernelMassPolynomial (t : ℝ) : ℝ := t*(2-t)^3
noncomputable def kernelVariationPolynomial (t : ℝ) : ℝ := t*(2-t)*(16-26*t-3*t^2+7*t^3+t^4)

lemma exp_sixteenth_rational_upper : Real.exp (1/16 : ℝ)≤16/15 := by
  have hh := Real.exp_le_two_add_div_two_sub (by norm_num : (0 : ℝ)≤1/16)
    (by norm_num : (1/16 : ℝ)<2)
  norm_num at hh
  linarith

lemma exp_mesh_rational_upper (t : ℝ) (m : ℕ) (ht : t≤(m : ℝ)/16) :
    Real.exp t≤(16/15 : ℝ)^m := by
  calc
    _≤Real.exp ((m : ℝ)/16) := Real.exp_le_exp.mpr ht
    _=(Real.exp (1/16 : ℝ))^m := by rw [← Real.exp_nat_mul]; congr 1; ring
    _≤_ := pow_le_pow_left₀ (Real.exp_nonneg _) exp_sixteenth_rational_upper m

lemma interval_mass_of_mesh_bound (p : ℝ → ℝ) (hp : Continuous p) (a b M E : ℝ)
    (hab : a≤b) (hM : 0≤M) (hb : ∀ t ∈ Icc a b,|p t|≤M)
    (he : ∀ t ∈ Icc a b,Real.exp (t-1/2)≤E) :
    (∫ t in a..b,|p t| * Real.exp (t-1/2))≤(b-a)*M*E := by
  have hf : Continuous (fun t => |p t| * Real.exp (t-1/2)) := by fun_prop
  have hh := intervalIntegral.integral_mono_on (μ := volume) hab (hf.intervalIntegrable a b)
    (intervalIntegrable_const (b := b) (a := a) (c := M*E))
    (fun t ht => mul_le_mul (hb t ht) (he t ht) (Real.exp_nonneg _) hM)
  simpa only [intervalIntegral.integral_const,smul_eq_mul,mul_assoc] using hh


end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 6000
open MeasureTheory Set Finset
namespace Helfgott
noncomputable def kernelFourthDensityPolynomial (t : ℝ) : ℝ := t*logRawPoly4 t
lemma kernel_fourth_mesh_0 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (1/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(26681691583/4294967296 : ℝ) := by
  have hta : 0≤t-(0 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(1/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(26681691583/4294967296 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(26681691583/4294967296 : ℝ)=(26681691583 : ℝ)*(t-(0 : ℝ))^0*((1/16 : ℝ)-t)^8 + (247813271032 : ℝ)*(t-(0 : ℝ))^1*((1/16 : ℝ)-t)^7 + (980022231268 : ℝ)*(t-(0 : ℝ))^2*((1/16 : ℝ)-t)^6 + (2170099401160 : ℝ)*(t-(0 : ℝ))^3*((1/16 : ℝ)-t)^5 + (2955944804922 : ℝ)*(t-(0 : ℝ))^4*((1/16 : ℝ)-t)^4 + (2543940186568 : ℝ)*(t-(0 : ℝ))^5*((1/16 : ℝ)-t)^3 + (1353803575268 : ℝ)*(t-(0 : ℝ))^6*((1/16 : ℝ)-t)^2 + (407962827448 : ℝ)*(t-(0 : ℝ))^7*((1/16 : ℝ)-t)^1 + (53363383166 : ℝ)*(t-(0 : ℝ))^8*((1/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(26681691583/4294967296 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (26681691583/4294967296 : ℝ)-kernelFourthDensityPolynomial t=(26681691583 : ℝ)*(t-(0 : ℝ))^0*((1/16 : ℝ)-t)^8 + (179093794296 : ℝ)*(t-(0 : ℝ))^1*((1/16 : ℝ)-t)^7 + (514152497380 : ℝ)*(t-(0 : ℝ))^2*((1/16 : ℝ)-t)^6 + (818250056136 : ℝ)*(t-(0 : ℝ))^3*((1/16 : ℝ)-t)^5 + (779492016698 : ℝ)*(t-(0 : ℝ))^4*((1/16 : ℝ)-t)^4 + (444409270728 : ℝ)*(t-(0 : ℝ))^5*((1/16 : ℝ)-t)^3 + (140371153380 : ℝ)*(t-(0 : ℝ))^6*((1/16 : ℝ)-t)^2 + (18944237880 : ℝ)*(t-(0 : ℝ))^7*((1/16 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_0 :
    (∫ t in (0 : ℝ)..(1/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(26681691583/68719476736 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (0 : ℝ) (1/16 : ℝ) (26681691583/4294967296 : ℝ) (1 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_0 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 0 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_1 (t : ℝ) (ht : t ∈ Icc (1/16 : ℝ) (1/8 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(148090143/16777216 : ℝ) := by
  have hta : 0≤t-(1/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(1/8 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(148090143/16777216 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(148090143/16777216 : ℝ)=(64592768191 : ℝ)*(t-(1/16 : ℝ))^0*((1/8 : ℝ)-t)^8 + (535686383408 : ℝ)*(t-(1/16 : ℝ))^1*((1/8 : ℝ)-t)^7 + (1933445686288 : ℝ)*(t-(1/16 : ℝ))^2*((1/8 : ℝ)-t)^6 + (3968466430784 : ℝ)*(t-(1/16 : ℝ))^3*((1/8 : ℝ)-t)^5 + (5068211867552 : ℝ)*(t-(1/16 : ℝ))^4*((1/8 : ℝ)-t)^4 + (4125268442368 : ℝ)*(t-(1/16 : ℝ))^5*((1/8 : ℝ)-t)^3 + (2090329650432 : ℝ)*(t-(1/16 : ℝ))^6*((1/8 : ℝ)-t)^2 + (602980869120 : ℝ)*(t-(1/16 : ℝ))^7*((1/8 : ℝ)-t)^1 + (75822153216 : ℝ)*(t-(1/16 : ℝ))^8*((1/8 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(148090143/16777216 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (148090143/16777216 : ℝ)-kernelFourthDensityPolynomial t=(11229385025 : ℝ)*(t-(1/16 : ℝ))^0*((1/8 : ℝ)-t)^8 + (70890842320 : ℝ)*(t-(1/16 : ℝ))^1*((1/8 : ℝ)-t)^7 + (189574603760 : ℝ)*(t-(1/16 : ℝ))^2*((1/8 : ℝ)-t)^6 + (277574149312 : ℝ)*(t-(1/16 : ℝ))^3*((1/8 : ℝ)-t)^5 + (239338857568 : ℝ)*(t-(1/16 : ℝ))^4*((1/8 : ℝ)-t)^4 + (120772137728 : ℝ)*(t-(1/16 : ℝ))^5*((1/8 : ℝ)-t)^3 + (32690639616 : ℝ)*(t-(1/16 : ℝ))^6*((1/8 : ℝ)-t)^2 + (3596356608 : ℝ)*(t-(1/16 : ℝ))^7*((1/8 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_1 :
    (∫ t in (1/16 : ℝ)..(1/8 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(148090143/268435456 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (1/16 : ℝ) (1/8 : ℝ) (148090143/16777216 : ℝ) (1 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_1 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 0 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_2 (t : ℝ) (ht : t ∈ Icc (1/8 : ℝ) (3/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(4215501945/469762048 : ℝ) := by
  have hta : 0≤t-(1/8 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(3/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(4215501945/469762048 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(4215501945/469762048 : ℝ)=(535169660736/7 : ℝ)*(t-(1/8 : ℝ))^0*((3/16 : ℝ)-t)^8 + (4306531782144/7 : ℝ)*(t-(1/8 : ℝ))^1*((3/16 : ℝ)-t)^7 + (2158336995840 : ℝ)*(t-(1/8 : ℝ))^2*((3/16 : ℝ)-t)^6 + (4311935703296 : ℝ)*(t-(1/8 : ℝ))^3*((3/16 : ℝ)-t)^5 + (5365620600352 : ℝ)*(t-(1/8 : ℝ))^4*((3/16 : ℝ)-t)^4 + (4258563445696 : ℝ)*(t-(1/8 : ℝ))^5*((3/16 : ℝ)-t)^3 + (2105185504400 : ℝ)*(t-(1/8 : ℝ))^6*((3/16 : ℝ)-t)^2 + (4148180530288/7 : ℝ)*(t-(1/8 : ℝ))^7*((3/16 : ℝ)-t)^1 + (509034990489/7 : ℝ)*(t-(1/8 : ℝ))^8*((3/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(4215501945/469762048 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (4215501945/469762048 : ℝ)-kernelFourthDensityPolynomial t=(4414588224/7 : ℝ)*(t-(1/8 : ℝ))^0*((3/16 : ℝ)-t)^8 + (10142209536/7 : ℝ)*(t-(1/8 : ℝ))^1*((3/16 : ℝ)-t)^7 + (4738288384 : ℝ)*(t-(1/8 : ℝ))^3*((3/16 : ℝ)-t)^5 + (30221889248 : ℝ)*(t-(1/8 : ℝ))^4*((3/16 : ℝ)-t)^4 + (58110545984 : ℝ)*(t-(1/8 : ℝ))^5*((3/16 : ℝ)-t)^3 + (53151491440 : ℝ)*(t-(1/8 : ℝ))^6*((3/16 : ℝ)-t)^2 + (168493461392/7 : ℝ)*(t-(1/8 : ℝ))^7*((3/16 : ℝ)-t)^1 + (30549258471/7 : ℝ)*(t-(1/8 : ℝ))^8*((3/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_2 :
    (∫ t in (1/8 : ℝ)..(3/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(4215501945/7516192768 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (1/8 : ℝ) (3/16 : ℝ) (4215501945/469762048 : ℝ) (1 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_2 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 0 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_3 (t : ℝ) (ht : t ∈ Icc (3/16 : ℝ) (1/4 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(34177552287/4294967296 : ℝ) := by
  have hta : 0≤t-(3/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(1/4 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(34177552287/4294967296 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(34177552287/4294967296 : ℝ)=(68355104574 : ℝ)*(t-(3/16 : ℝ))^0*((1/4 : ℝ)-t)^8 + (535997892824 : ℝ)*(t-(3/16 : ℝ))^1*((1/4 : ℝ)-t)^7 + (1831187257764 : ℝ)*(t-(3/16 : ℝ))^2*((1/4 : ℝ)-t)^6 + (3559341567176 : ℝ)*(t-(3/16 : ℝ))^3*((1/4 : ℝ)-t)^5 + (4304001089402 : ℝ)*(t-(3/16 : ℝ))^4*((1/4 : ℝ)-t)^4 + (3314293050056 : ℝ)*(t-(3/16 : ℝ))^5*((1/4 : ℝ)-t)^3 + (1586492208484 : ℝ)*(t-(3/16 : ℝ))^6*((1/4 : ℝ)-t)^2 + (431380921592 : ℝ)*(t-(3/16 : ℝ))^7*((1/4 : ℝ)-t)^1 + (50977771423 : ℝ)*(t-(3/16 : ℝ))^8*((1/4 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(34177552287/4294967296 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (34177552287/4294967296 : ℝ)-kernelFourthDensityPolynomial t=(10842943768 : ℝ)*(t-(3/16 : ℝ))^1*((1/4 : ℝ)-t)^7 + (82755670308 : ℝ)*(t-(3/16 : ℝ))^2*((1/4 : ℝ)-t)^6 + (268544288968 : ℝ)*(t-(3/16 : ℝ))^3*((1/4 : ℝ)-t)^5 + (480856230778 : ℝ)*(t-(3/16 : ℝ))^4*((1/4 : ℝ)-t)^4 + (513592806088 : ℝ)*(t-(3/16 : ℝ))^5*((1/4 : ℝ)-t)^3 + (327450719588 : ℝ)*(t-(3/16 : ℝ))^6*((1/4 : ℝ)-t)^2 + (115459915000 : ℝ)*(t-(3/16 : ℝ))^7*((1/4 : ℝ)-t)^1 + (17377333151 : ℝ)*(t-(3/16 : ℝ))^8*((1/4 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_3 :
    (∫ t in (3/16 : ℝ)..(1/4 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(34177552287/68719476736 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (3/16 : ℝ) (1/4 : ℝ) (34177552287/4294967296 : ℝ) (1 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_3 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 0 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_4 (t : ℝ) (ht : t ∈ Icc (1/4 : ℝ) (5/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(256351/65536 : ℝ) := by
  have hta : 0≤t-(1/4 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(5/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(256351/65536 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(256351/65536 : ℝ)=(33600438272 : ℝ)*(t-(1/4 : ℝ))^0*((5/16 : ℝ)-t)^8 + (245244755968 : ℝ)*(t-(1/4 : ℝ))^1*((5/16 : ℝ)-t)^7 + (770104377344 : ℝ)*(t-(1/4 : ℝ))^2*((5/16 : ℝ)-t)^6 + (1352526979072 : ℝ)*(t-(1/4 : ℝ))^3*((5/16 : ℝ)-t)^5 + (1442635725312 : ℝ)*(t-(1/4 : ℝ))^4*((5/16 : ℝ)-t)^4 + (945418145280 : ℝ)*(t-(1/4 : ℝ))^5*((5/16 : ℝ)-t)^3 + (363471784000 : ℝ)*(t-(1/4 : ℝ))^6*((5/16 : ℝ)-t)^2 + (71313616160 : ℝ)*(t-(1/4 : ℝ))^7*((5/16 : ℝ)-t)^1 + (4691171551 : ℝ)*(t-(1/4 : ℝ))^8*((5/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(256351/65536 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (256351/65536 : ℝ)-kernelFourthDensityPolynomial t=(23558750208 : ℝ)*(t-(1/4 : ℝ))^1*((5/16 : ℝ)-t)^7 + (170707894272 : ℝ)*(t-(1/4 : ℝ))^2*((5/16 : ℝ)-t)^6 + (529097564160 : ℝ)*(t-(1/4 : ℝ))^3*((5/16 : ℝ)-t)^5 + (909394953728 : ℝ)*(t-(1/4 : ℝ))^4*((5/16 : ℝ)-t)^4 + (936206397952 : ℝ)*(t-(1/4 : ℝ))^5*((5/16 : ℝ)-t)^3 + (577340487616 : ℝ)*(t-(1/4 : ℝ))^6*((5/16 : ℝ)-t)^2 + (197489890016 : ℝ)*(t-(1/4 : ℝ))^7*((5/16 : ℝ)-t)^1 + (28909266721 : ℝ)*(t-(1/4 : ℝ))^8*((5/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_4 :
    (∫ t in (1/4 : ℝ)..(5/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(256351/1048576 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (1/4 : ℝ) (5/16 : ℝ) (256351/65536 : ℝ) (1 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_4 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 0 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_5 (t : ℝ) (ht : t ∈ Icc (5/16 : ℝ) (3/8 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(194161857/16777216 : ℝ) := by
  have hta : 0≤t-(5/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(3/8 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(194161857/16777216 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(194161857/16777216 : ℝ)=(37596387807 : ℝ)*(t-(5/16 : ℝ))^0*((3/8 : ℝ)-t)^8 + (266986858704 : ℝ)*(t-(5/16 : ℝ))^1*((3/8 : ℝ)-t)^7 + (811838426640 : ℝ)*(t-(5/16 : ℝ))^2*((3/8 : ℝ)-t)^6 + (1370236470464 : ℝ)*(t-(5/16 : ℝ))^3*((3/8 : ℝ)-t)^5 + (1386426062752 : ℝ)*(t-(5/16 : ℝ))^4*((3/8 : ℝ)-t)^4 + (840964932352 : ℝ)*(t-(5/16 : ℝ))^5*((3/8 : ℝ)-t)^3 + (283151863040 : ℝ)*(t-(5/16 : ℝ))^6*((3/8 : ℝ)-t)^2 + (40824478720 : ℝ)*(t-(5/16 : ℝ))^7*((3/8 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(194161857/16777216 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (194161857/16777216 : ℝ)-kernelFourthDensityPolynomial t=(61814482977 : ℝ)*(t-(5/16 : ℝ))^0*((3/8 : ℝ)-t)^8 + (528300107568 : ℝ)*(t-(5/16 : ℝ))^1*((3/8 : ℝ)-t)^7 + (1971665955312 : ℝ)*(t-(5/16 : ℝ))^2*((3/8 : ℝ)-t)^6 + (4196772293440 : ℝ)*(t-(5/16 : ℝ))^3*((3/8 : ℝ)-t)^5 + (5572334892128 : ℝ)*(t-(5/16 : ℝ))^4*((3/8 : ℝ)-t)^4 + (4726043831552 : ℝ)*(t-(5/16 : ℝ))^5*((3/8 : ℝ)-t)^3 + (2500352518912 : ℝ)*(t-(5/16 : ℝ))^6*((3/8 : ℝ)-t)^2 + (754462487552 : ℝ)*(t-(5/16 : ℝ))^7*((3/8 : ℝ)-t)^1 + (99410870784 : ℝ)*(t-(5/16 : ℝ))^8*((3/8 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_5 :
    (∫ t in (5/16 : ℝ)..(3/8 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(194161857/268435456 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (5/16 : ℝ) (3/8 : ℝ) (194161857/16777216 : ℝ) (1 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_5 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 0 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_6 (t : ℝ) (ht : t ∈ Icc (3/8 : ℝ) (7/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(92495694977/4294967296 : ℝ) := by
  have hta : 0≤t-(3/8 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(7/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(92495694977/4294967296 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(92495694977/4294967296 : ℝ)=(42790259585 : ℝ)*(t-(3/8 : ℝ))^0*((7/16 : ℝ)-t)^8 + (301497597960 : ℝ)*(t-(3/8 : ℝ))^1*((7/16 : ℝ)-t)^7 + (909736429340 : ℝ)*(t-(3/8 : ℝ))^2*((7/16 : ℝ)-t)^6 + (1523855748408 : ℝ)*(t-(3/8 : ℝ))^3*((7/16 : ℝ)-t)^5 + (1530352650982 : ℝ)*(t-(3/8 : ℝ))^4*((7/16 : ℝ)-t)^4 + (921419277432 : ℝ)*(t-(3/8 : ℝ))^5*((7/16 : ℝ)-t)^3 + (307975219884 : ℝ)*(t-(3/8 : ℝ))^6*((7/16 : ℝ)-t)^2 + (44081935992 : ℝ)*(t-(3/8 : ℝ))^7*((7/16 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(92495694977/4294967296 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (92495694977/4294967296 : ℝ)-kernelFourthDensityPolynomial t=(142201130369 : ℝ)*(t-(3/8 : ℝ))^0*((7/16 : ℝ)-t)^8 + (1178433521672 : ℝ)*(t-(3/8 : ℝ))^1*((7/16 : ℝ)-t)^7 + (4270022489372 : ℝ)*(t-(3/8 : ℝ))^2*((7/16 : ℝ)-t)^6 + (8835662089016 : ℝ)*(t-(3/8 : ℝ))^3*((7/16 : ℝ)-t)^5 + (11419044645798 : ℝ)*(t-(3/8 : ℝ))^4*((7/16 : ℝ)-t)^4 + (9438098559992 : ℝ)*(t-(3/8 : ℝ))^5*((7/16 : ℝ)-t)^3 + (4871783698828 : ℝ)*(t-(3/8 : ℝ))^6*((7/16 : ℝ)-t)^2 + (1435849183640 : ℝ)*(t-(3/8 : ℝ))^7*((7/16 : ℝ)-t)^1 + (184991389954 : ℝ)*(t-(3/8 : ℝ))^8*((7/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_6 :
    (∫ t in (3/8 : ℝ)..(7/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(92495694977/68719476736 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (3/8 : ℝ) (7/16 : ℝ) (92495694977/4294967296 : ℝ) (1 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_6 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 0 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_7 (t : ℝ) (ht : t ∈ Icc (7/16 : ℝ) (1/2 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(8133/256 : ℝ) := by
  have hta : 0≤t-(7/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(1/2 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(8133/256 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(8133/256 : ℝ)=(43953402751 : ℝ)*(t-(7/16 : ℝ))^0*((1/2 : ℝ)-t)^8 + (307545286016 : ℝ)*(t-(7/16 : ℝ))^1*((1/2 : ℝ)-t)^7 + (921523393024 : ℝ)*(t-(7/16 : ℝ))^2*((1/2 : ℝ)-t)^6 + (1532791291904 : ℝ)*(t-(7/16 : ℝ))^3*((1/2 : ℝ)-t)^5 + (1528469184512 : ℝ)*(t-(7/16 : ℝ))^4*((1/2 : ℝ)-t)^4 + (913735942144 : ℝ)*(t-(7/16 : ℝ))^5*((1/2 : ℝ)-t)^3 + (303210430464 : ℝ)*(t-(7/16 : ℝ))^6*((1/2 : ℝ)-t)^2 + (43083890688 : ℝ)*(t-(7/16 : ℝ))^7*((1/2 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(8133/256 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (8133/256 : ℝ)-kernelFourthDensityPolynomial t=(228944792705 : ℝ)*(t-(7/16 : ℝ))^0*((1/2 : ℝ)-t)^8 + (1875640277632 : ℝ)*(t-(7/16 : ℝ))^1*((1/2 : ℝ)-t)^7 + (6719626079744 : ℝ)*(t-(7/16 : ℝ))^2*((1/2 : ℝ)-t)^6 + (13749507653632 : ℝ)*(t-(7/16 : ℝ))^3*((1/2 : ℝ)-t)^5 + (17574404497408 : ℝ)*(t-(7/16 : ℝ))^4*((1/2 : ℝ)-t)^4 + (14368563003392 : ℝ)*(t-(7/16 : ℝ))^5*((1/2 : ℝ)-t)^3 + (7337939042304 : ℝ)*(t-(7/16 : ℝ))^6*((1/2 : ℝ)-t)^2 + (2140101672960 : ℝ)*(t-(7/16 : ℝ))^7*((1/2 : ℝ)-t)^1 + (272898195456 : ℝ)*(t-(7/16 : ℝ))^8*((1/2 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_7 :
    (∫ t in (7/16 : ℝ)..(1/2 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(8133/4096 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (7/16 : ℝ) (1/2 : ℝ) (8133/256 : ℝ) (1 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_7 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 0 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_8 (t : ℝ) (ht : t ∈ Icc (1/2 : ℝ) (9/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(177136684929/4294967296 : ℝ) := by
  have hta : 0≤t-(1/2 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(9/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(177136684929/4294967296 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(177136684929/4294967296 : ℝ)=(40687587201 : ℝ)*(t-(1/2 : ℝ))^0*((9/16 : ℝ)-t)^8 + (282416806920 : ℝ)*(t-(1/2 : ℝ))^1*((9/16 : ℝ)-t)^7 + (839288402460 : ℝ)*(t-(1/2 : ℝ))^2*((9/16 : ℝ)-t)^6 + (1384247288888 : ℝ)*(t-(1/2 : ℝ))^3*((9/16 : ℝ)-t)^5 + (1368377302342 : ℝ)*(t-(1/2 : ℝ))^4*((9/16 : ℝ)-t)^4 + (810719470648 : ℝ)*(t-(1/2 : ℝ))^5*((9/16 : ℝ)-t)^3 + (266541909020 : ℝ)*(t-(1/2 : ℝ))^6*((9/16 : ℝ)-t)^2 + (37511634568 : ℝ)*(t-(1/2 : ℝ))^7*((9/16 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(177136684929/4294967296 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (177136684929/4294967296 : ℝ)-kernelFourthDensityPolynomial t=(313585782657 : ℝ)*(t-(1/2 : ℝ))^0*((9/16 : ℝ)-t)^8 + (2551770151944 : ℝ)*(t-(1/2 : ℝ))^1*((9/16 : ℝ)-t)^7 + (9080365953564 : ℝ)*(t-(1/2 : ℝ))^2*((9/16 : ℝ)-t)^6 + (18455061423160 : ℝ)*(t-(1/2 : ℝ))^3*((9/16 : ℝ)-t)^5 + (23430758587718 : ℝ)*(t-(1/2 : ℝ))^4*((9/16 : ℝ)-t)^4 + (19028589241400 : ℝ)*(t-(1/2 : ℝ))^5*((9/16 : ℝ)-t)^3 + (9653112447004 : ℝ)*(t-(1/2 : ℝ))^6*((9/16 : ℝ)-t)^2 + (2796675324296 : ℝ)*(t-(1/2 : ℝ))^7*((9/16 : ℝ)-t)^1 + (354273369858 : ℝ)*(t-(1/2 : ℝ))^8*((9/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_8 :
    (∫ t in (1/2 : ℝ)..(9/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(59045561643/21474836480 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (1/2 : ℝ) (9/16 : ℝ) (177136684929/4294967296 : ℝ) (16/15 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_8 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 1 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_9 (t : ℝ) (ht : t ∈ Icc (9/16 : ℝ) (5/8 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(819924545/16777216 : ℝ) := by
  have hta : 0≤t-(9/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(5/8 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(819924545/16777216 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(819924545/16777216 : ℝ)=(32763998591 : ℝ)*(t-(9/16 : ℝ))^0*((5/8 : ℝ)-t)^8 + (224600354160 : ℝ)*(t-(9/16 : ℝ))^1*((5/8 : ℝ)-t)^7 + (658770985616 : ℝ)*(t-(9/16 : ℝ))^2*((5/8 : ℝ)-t)^6 + (1071590054976 : ℝ)*(t-(9/16 : ℝ))^3*((5/8 : ℝ)-t)^5 + (1043919359392 : ℝ)*(t-(9/16 : ℝ))^4*((5/8 : ℝ)-t)^4 + (608966310144 : ℝ)*(t-(9/16 : ℝ))^5*((5/8 : ℝ)-t)^3 + (196933969152 : ℝ)*(t-(9/16 : ℝ))^6*((5/8 : ℝ)-t)^2 + (27231593472 : ℝ)*(t-(9/16 : ℝ))^7*((5/8 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(819924545/16777216 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (819924545/16777216 : ℝ)-kernelFourthDensityPolynomial t=(387037368449 : ℝ)*(t-(9/16 : ℝ))^0*((5/8 : ℝ)-t)^8 + (3133810582160 : ℝ)*(t-(9/16 : ℝ))^1*((5/8 : ℝ)-t)^7 + (11095667291504 : ℝ)*(t-(9/16 : ℝ))^2*((5/8 : ℝ)-t)^6 + (22437286499264 : ℝ)*(t-(9/16 : ℝ))^3*((5/8 : ℝ)-t)^5 + (28342176333408 : ℝ)*(t-(9/16 : ℝ))^4*((5/8 : ℝ)-t)^4 + (22899910244096 : ℝ)*(t-(9/16 : ℝ))^5*((5/8 : ℝ)-t)^3 + (11557504307968 : ℝ)*(t-(9/16 : ℝ))^6*((5/8 : ℝ)-t)^2 + (3331179342848 : ℝ)*(t-(9/16 : ℝ))^7*((5/8 : ℝ)-t)^1 + (419801367040 : ℝ)*(t-(9/16 : ℝ))^8*((5/8 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_9 :
    (∫ t in (9/16 : ℝ)..(5/8 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(163984909/47185920 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (9/16 : ℝ) (5/8 : ℝ) (819924545/16777216 : ℝ) (256/225 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_9 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 2 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_10 (t : ℝ) (ht : t ∈ Icc (5/8 : ℝ) (11/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(230056003617/4294967296 : ℝ) := by
  have hta : 0≤t-(5/8 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(11/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(230056003617/4294967296 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(230056003617/4294967296 : ℝ)=(20155320097 : ℝ)*(t-(5/8 : ℝ))^0*((11/16 : ℝ)-t)^8 + (134010967304 : ℝ)*(t-(5/8 : ℝ))^1*((11/16 : ℝ)-t)^7 + (380040623260 : ℝ)*(t-(5/8 : ℝ))^2*((11/16 : ℝ)-t)^6 + (595485393464 : ℝ)*(t-(5/8 : ℝ))^3*((11/16 : ℝ)-t)^5 + (556320641702 : ℝ)*(t-(5/8 : ℝ))^4*((11/16 : ℝ)-t)^4 + (309553059832 : ℝ)*(t-(5/8 : ℝ))^5*((11/16 : ℝ)-t)^3 + (94861215660 : ℝ)*(t-(5/8 : ℝ))^6*((11/16 : ℝ)-t)^2 + (12328380120 : ℝ)*(t-(5/8 : ℝ))^7*((11/16 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(230056003617/4294967296 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (230056003617/4294967296 : ℝ)-kernelFourthDensityPolynomial t=(439956687137 : ℝ)*(t-(5/8 : ℝ))^0*((11/16 : ℝ)-t)^8 + (3546885090568 : ℝ)*(t-(5/8 : ℝ))^1*((11/16 : ℝ)-t)^7 + (12503095579292 : ℝ)*(t-(5/8 : ℝ))^2*((11/16 : ℝ)-t)^6 + (25170787011640 : ℝ)*(t-(5/8 : ℝ))^3*((11/16 : ℝ)-t)^5 + (31651519864678 : ℝ)*(t-(5/8 : ℝ))^4*((11/16 : ℝ)-t)^4 + (25456719345272 : ℝ)*(t-(5/8 : ℝ))^5*((11/16 : ℝ)-t)^3 + (12788274986892 : ℝ)*(t-(5/8 : ℝ))^6*((11/16 : ℝ)-t)^2 + (3668567677752 : ℝ)*(t-(5/8 : ℝ))^7*((11/16 : ℝ)-t)^1 + (460112007234 : ℝ)*(t-(5/8 : ℝ))^8*((11/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_10 :
    (∫ t in (5/8 : ℝ)..(11/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(76685334539/18874368000 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (5/8 : ℝ) (11/16 : ℝ) (230056003617/4294967296 : ℝ) (4096/3375 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_10 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 3 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_11 (t : ℝ) (ht : t ∈ Icc (11/16 : ℝ) (3/4 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(229078495/4194304 : ℝ) := by
  have hta : 0≤t-(11/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(3/4 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(229078495/4194304 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(229078495/4194304 : ℝ)=(4520375263 : ℝ)*(t-(11/16 : ℝ))^0*((3/4 : ℝ)-t)^8 + (23834621984 : ℝ)*(t-(11/16 : ℝ))^1*((3/4 : ℝ)-t)^7 + (48834401344 : ℝ)*(t-(11/16 : ℝ))^2*((3/4 : ℝ)-t)^6 + (46338612736 : ℝ)*(t-(11/16 : ℝ))^3*((3/4 : ℝ)-t)^5 + (16942817792 : ℝ)*(t-(11/16 : ℝ))^4*((3/4 : ℝ)-t)^4 + (3169701888 : ℝ)*(t-(11/16 : ℝ))^6*((3/4 : ℝ)-t)^2 + (4744667136 : ℝ)*(t-(11/16 : ℝ))^7*((3/4 : ℝ)-t)^1 + (1450605568 : ℝ)*(t-(11/16 : ℝ))^8*((3/4 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(229078495/4194304 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (229078495/4194304 : ℝ)-kernelFourthDensityPolynomial t=(464632382497 : ℝ)*(t-(11/16 : ℝ))^0*((3/4 : ℝ)-t)^8 + (3729387440096 : ℝ)*(t-(11/16 : ℝ))^1*((3/4 : ℝ)-t)^7 + (13087442815936 : ℝ)*(t-(11/16 : ℝ))^2*((3/4 : ℝ)-t)^6 + (26226215821824 : ℝ)*(t-(11/16 : ℝ))^3*((3/4 : ℝ)-t)^5 + (32823750225408 : ℝ)*(t-(11/16 : ℝ))^4*((3/4 : ℝ)-t)^4 + (26272554434560 : ℝ)*(t-(11/16 : ℝ))^5*((3/4 : ℝ)-t)^3 + (13133107515392 : ℝ)*(t-(11/16 : ℝ))^6*((3/4 : ℝ)-t)^2 + (3748477394944 : ℝ)*(t-(11/16 : ℝ))^7*((3/4 : ℝ)-t)^1 + (467702152192 : ℝ)*(t-(11/16 : ℝ))^8*((3/4 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_11 :
    (∫ t in (11/16 : ℝ)..(3/4 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(45815699/10368000 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (11/16 : ℝ) (3/4 : ℝ) (229078495/4194304 : ℝ) (65536/50625 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_11 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 4 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_12 (t : ℝ) (ht : t ∈ Icc (3/4 : ℝ) (13/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(3557217/65536 : ℝ) := by
  have hta : 0≤t-(3/4 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(13/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(3557217/65536 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(3557217/65536 : ℝ)=(6860177408 : ℝ)*(t-(3/4 : ℝ))^1*((13/16 : ℝ)-t)^7 + (58595229696 : ℝ)*(t-(3/4 : ℝ))^2*((13/16 : ℝ)-t)^6 + (208121765888 : ℝ)*(t-(3/4 : ℝ))^3*((13/16 : ℝ)-t)^5 + (401753979392 : ℝ)*(t-(3/4 : ℝ))^4*((13/16 : ℝ)-t)^4 + (457593901568 : ℝ)*(t-(3/4 : ℝ))^5*((13/16 : ℝ)-t)^3 + (308610711616 : ℝ)*(t-(3/4 : ℝ))^6*((13/16 : ℝ)-t)^2 + (114396942560 : ℝ)*(t-(3/4 : ℝ))^7*((13/16 : ℝ)-t)^1 + (18012866719 : ℝ)*(t-(3/4 : ℝ))^8*((13/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(3557217/65536 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (3557217/65536 : ℝ)-kernelFourthDensityPolynomial t=(466251546624 : ℝ)*(t-(3/4 : ℝ))^0*((13/16 : ℝ)-t)^8 + (3723152195584 : ℝ)*(t-(3/4 : ℝ))^1*((13/16 : ℝ)-t)^7 + (12996448075776 : ℝ)*(t-(3/4 : ℝ))^2*((13/16 : ℝ)-t)^6 + (25901964845056 : ℝ)*(t-(3/4 : ℝ))^3*((13/16 : ℝ)-t)^5 + (32235854284288 : ℝ)*(t-(3/4 : ℝ))^4*((13/16 : ℝ)-t)^4 + (25652492709376 : ℝ)*(t-(3/4 : ℝ))^5*((13/16 : ℝ)-t)^3 + (12746432593856 : ℝ)*(t-(3/4 : ℝ))^6*((13/16 : ℝ)-t)^2 + (3615615430432 : ℝ)*(t-(3/4 : ℝ))^7*((13/16 : ℝ)-t)^1 + (448238679905 : ℝ)*(t-(3/4 : ℝ))^8*((13/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_12 :
    (∫ t in (3/4 : ℝ)..(13/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(1185739/253125 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (3/4 : ℝ) (13/16 : ℝ) (3557217/65536 : ℝ) (1048576/759375 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_12 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 5 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_13 (t : ℝ) (ht : t ∈ Icc (13/16 : ℝ) (7/8 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(215112906593/4294967296 : ℝ) := by
  have hta : 0≤t-(13/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(7/8 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(215112906593/4294967296 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(215112906593/4294967296 : ℝ)=(29705991192 : ℝ)*(t-(13/16 : ℝ))^1*((7/8 : ℝ)-t)^7 + (220134320172 : ℝ)*(t-(13/16 : ℝ))^2*((7/8 : ℝ)-t)^6 + (697435216632 : ℝ)*(t-(13/16 : ℝ))^3*((7/8 : ℝ)-t)^5 + (1224823798822 : ℝ)*(t-(13/16 : ℝ))^4*((7/8 : ℝ)-t)^4 + (1287916655672 : ℝ)*(t-(13/16 : ℝ))^5*((7/8 : ℝ)-t)^3 + (810970294172 : ℝ)*(t-(13/16 : ℝ))^6*((7/8 : ℝ)-t)^2 + (283173715720 : ℝ)*(t-(13/16 : ℝ))^7*((7/8 : ℝ)-t)^1 + (42303166049 : ℝ)*(t-(13/16 : ℝ))^8*((7/8 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(215112906593/4294967296 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (215112906593/4294967296 : ℝ)-kernelFourthDensityPolynomial t=(430225813186 : ℝ)*(t-(13/16 : ℝ))^0*((7/8 : ℝ)-t)^8 + (3412100514296 : ℝ)*(t-(13/16 : ℝ))^1*((7/8 : ℝ)-t)^7 + (11826188449036 : ℝ)*(t-(13/16 : ℝ))^2*((7/8 : ℝ)-t)^6 + (23395210321784 : ℝ)*(t-(13/16 : ℝ))^3*((7/8 : ℝ)-t)^5 + (28890983124198 : ℝ)*(t-(13/16 : ℝ))^4*((7/8 : ℝ)-t)^4 + (22804728882744 : ℝ)*(t-(13/16 : ℝ))^5*((7/8 : ℝ)-t)^3 + (11235352475036 : ℝ)*(t-(13/16 : ℝ))^6*((7/8 : ℝ)-t)^2 + (3158632789768 : ℝ)*(t-(13/16 : ℝ))^7*((7/8 : ℝ)-t)^1 + (387922647137 : ℝ)*(t-(13/16 : ℝ))^8*((7/8 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_13 :
    (∫ t in (13/16 : ℝ)..(7/8 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(215112906593/46656000000 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (13/16 : ℝ) (7/8 : ℝ) (215112906593/4294967296 : ℝ) (16777216/11390625 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_13 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 6 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_14 (t : ℝ) (ht : t ∈ Icc (7/8 : ℝ) (15/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(675038049/16777216 : ℝ) := by
  have hta : 0≤t-(7/8 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(15/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(675038049/16777216 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(675038049/16777216 : ℝ)=(55251612672 : ℝ)*(t-(7/8 : ℝ))^1*((15/16 : ℝ)-t)^7 + (400004222208 : ℝ)*(t-(7/8 : ℝ))^2*((15/16 : ℝ)-t)^6 + (1239975845120 : ℝ)*(t-(7/8 : ℝ))^3*((15/16 : ℝ)-t)^5 + (2133558842272 : ℝ)*(t-(7/8 : ℝ))^4*((15/16 : ℝ)-t)^4 + (2200751472448 : ℝ)*(t-(7/8 : ℝ))^5*((15/16 : ℝ)-t)^3 + (1360880286224 : ℝ)*(t-(7/8 : ℝ))^6*((15/16 : ℝ)-t)^2 + (467126342704 : ℝ)*(t-(7/8 : ℝ))^7*((15/16 : ℝ)-t)^1 + (68661922239 : ℝ)*(t-(7/8 : ℝ))^8*((15/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(675038049/16777216 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (675038049/16777216 : ℝ)-kernelFourthDensityPolynomial t=(345619481088 : ℝ)*(t-(7/8 : ℝ))^0*((15/16 : ℝ)-t)^8 + (2709704236032 : ℝ)*(t-(7/8 : ℝ))^1*((15/16 : ℝ)-t)^7 + (9277341248256 : ℝ)*(t-(7/8 : ℝ))^2*((15/16 : ℝ)-t)^6 + (18114715095808 : ℝ)*(t-(7/8 : ℝ))^3*((15/16 : ℝ)-t)^5 + (22059804833888 : ℝ)*(t-(7/8 : ℝ))^4*((15/16 : ℝ)-t)^4 + (17153939468480 : ℝ)*(t-(7/8 : ℝ))^5*((15/16 : ℝ)-t)^3 + (8316465184240 : ℝ)*(t-(7/8 : ℝ))^6*((15/16 : ℝ)-t)^2 + (2297829506000 : ℝ)*(t-(7/8 : ℝ))^7*((15/16 : ℝ)-t)^1 + (276957558849 : ℝ)*(t-(7/8 : ℝ))^8*((15/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_14 :
    (∫ t in (7/8 : ℝ)..(15/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(225012683/56953125 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (7/8 : ℝ) (15/16 : ℝ) (675038049/16777216 : ℝ) (268435456/170859375 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_14 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 7 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_15 (t : ℝ) (ht : t ∈ Icc (15/16 : ℝ) (1 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(104147818305/4294967296 : ℝ) := by
  have hta : 0≤t-(15/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(1 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(104147818305/4294967296 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(104147818305/4294967296 : ℝ)=(82169035208 : ℝ)*(t-(15/16 : ℝ))^1*((1 : ℝ)-t)^7 + (588712956444 : ℝ)*(t-(15/16 : ℝ))^2*((1 : ℝ)-t)^6 + (1806672692792 : ℝ)*(t-(15/16 : ℝ))^3*((1 : ℝ)-t)^5 + (3078503685062 : ℝ)*(t-(15/16 : ℝ))^4*((1 : ℝ)-t)^4 + (3145626883640 : ℝ)*(t-(15/16 : ℝ))^5*((1 : ℝ)-t)^3 + (1927440796444 : ℝ)*(t-(15/16 : ℝ))^6*((1 : ℝ)-t)^2 + (655746710024 : ℝ)*(t-(15/16 : ℝ))^7*((1 : ℝ)-t)^1 + (95557883713 : ℝ)*(t-(15/16 : ℝ))^8*((1 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(104147818305/4294967296 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (104147818305/4294967296 : ℝ)-kernelFourthDensityPolynomial t=(208295636610 : ℝ)*(t-(15/16 : ℝ))^0*((1 : ℝ)-t)^8 + (1584196057672 : ℝ)*(t-(15/16 : ℝ))^1*((1 : ℝ)-t)^7 + (5243564868636 : ℝ)*(t-(15/16 : ℝ))^2*((1 : ℝ)-t)^6 + (9857882957368 : ℝ)*(t-(15/16 : ℝ))^3*((1 : ℝ)-t)^5 + (11502190877638 : ℝ)*(t-(15/16 : ℝ))^4*((1 : ℝ)-t)^4 + (8518928766520 : ℝ)*(t-(15/16 : ℝ))^5*((1 : ℝ)-t)^3 + (3904837028636 : ℝ)*(t-(15/16 : ℝ))^6*((1 : ℝ)-t)^2 + (1010618382856 : ℝ)*(t-(15/16 : ℝ))^7*((1 : ℝ)-t)^1 + (112737752897 : ℝ)*(t-(15/16 : ℝ))^8*((1 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_15 :
    (∫ t in (15/16 : ℝ)..(1 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(6943187887/2733750000 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (15/16 : ℝ) (1 : ℝ) (104147818305/4294967296 : ℝ) (4294967296/2562890625 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_15 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 8 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_16 (t : ℝ) (ht : t ∈ Icc (1 : ℝ) (17/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(112433399103/4294967296 : ℝ) := by
  have hta : 0≤t-(1 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(17/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(112433399103/4294967296 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(112433399103/4294967296 : ℝ)=(103843464511 : ℝ)*(t-(1 : ℝ))^0*((17/16 : ℝ)-t)^8 + (939464075768 : ℝ)*(t-(1 : ℝ))^1*((17/16 : ℝ)-t)^7 + (3681466094308 : ℝ)*(t-(1 : ℝ))^2*((17/16 : ℝ)-t)^6 + (8174863459784 : ℝ)*(t-(1 : ℝ))^3*((17/16 : ℝ)-t)^5 + (11264424243002 : ℝ)*(t-(1 : ℝ))^4*((17/16 : ℝ)-t)^4 + (9872371398088 : ℝ)*(t-(1 : ℝ))^5*((17/16 : ℝ)-t)^3 + (5378340436452 : ℝ)*(t-(1 : ℝ))^6*((17/16 : ℝ)-t)^2 + (1666242102840 : ℝ)*(t-(1 : ℝ))^7*((17/16 : ℝ)-t)^1 + (224866798206 : ℝ)*(t-(1 : ℝ))^8*((17/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(112433399103/4294967296 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (112433399103/4294967296 : ℝ)-kernelFourthDensityPolynomial t=(121023333695 : ℝ)*(t-(1 : ℝ))^0*((17/16 : ℝ)-t)^8 + (859470309880 : ℝ)*(t-(1 : ℝ))^1*((17/16 : ℝ)-t)^7 + (2614804255460 : ℝ)*(t-(1 : ℝ))^2*((17/16 : ℝ)-t)^6 + (4417677239752 : ℝ)*(t-(1 : ℝ))^3*((17/16 : ℝ)-t)^5 + (4476251631418 : ℝ)*(t-(1 : ℝ))^4*((17/16 : ℝ)-t)^4 + (2720169301448 : ℝ)*(t-(1 : ℝ))^5*((17/16 : ℝ)-t)^3 + (917929913316 : ℝ)*(t-(1 : ℝ))^6*((17/16 : ℝ)-t)^2 + (132692282808 : ℝ)*(t-(1 : ℝ))^7*((17/16 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_16 :
    (∫ t in (1 : ℝ)..(17/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(37477799701/12814453125 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (1 : ℝ) (17/16 : ℝ) (112433399103/4294967296 : ℝ) (68719476736/38443359375 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_16 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 9 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_17 (t : ℝ) (ht : t ∈ Icc (17/16 : ℝ) (9/8 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(996253407/16777216 : ℝ) := by
  have hta : 0≤t-(17/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(9/8 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(996253407/16777216 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(996253407/16777216 : ℝ)=(367474271295 : ℝ)*(t-(17/16 : ℝ))^0*((9/8 : ℝ)-t)^8 + (3072486453168 : ℝ)*(t-(17/16 : ℝ))^1*((9/8 : ℝ)-t)^7 + (11229041642256 : ℝ)*(t-(17/16 : ℝ))^2*((9/8 : ℝ)-t)^6 + (23429721290048 : ℝ)*(t-(17/16 : ℝ))^3*((9/8 : ℝ)-t)^5 + (30526684760992 : ℝ)*(t-(17/16 : ℝ))^4*((9/8 : ℝ)-t)^4 + (25431887680768 : ℝ)*(t-(17/16 : ℝ))^5*((9/8 : ℝ)-t)^3 + (13230078592256 : ℝ)*(t-(17/16 : ℝ))^6*((9/8 : ℝ)-t)^2 + (3929265587200 : ℝ)*(t-(17/16 : ℝ))^7*((9/8 : ℝ)-t)^1 + (510081744384 : ℝ)*(t-(17/16 : ℝ))^8*((9/8 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(996253407/16777216 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (996253407/16777216 : ℝ)-kernelFourthDensityPolynomial t=(142607473089 : ℝ)*(t-(17/16 : ℝ))^0*((9/8 : ℝ)-t)^8 + (1008167501904 : ℝ)*(t-(17/16 : ℝ))^1*((9/8 : ℝ)-t)^7 + (3053247200496 : ℝ)*(t-(17/16 : ℝ))^2*((9/8 : ℝ)-t)^6 + (5134856395456 : ℝ)*(t-(17/16 : ℝ))^3*((9/8 : ℝ)-t)^5 + (5179037345888 : ℝ)*(t-(17/16 : ℝ))^4*((9/8 : ℝ)-t)^4 + (3132690004736 : ℝ)*(t-(17/16 : ℝ))^5*((9/8 : ℝ)-t)^3 + (1052210250496 : ℝ)*(t-(17/16 : ℝ))^6*((9/8 : ℝ)-t)^2 + (151388367872 : ℝ)*(t-(17/16 : ℝ))^7*((9/8 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_17 :
    (∫ t in (17/16 : ℝ)..(9/8 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(453405995008/64072265625 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (17/16 : ℝ) (9/8 : ℝ) (996253407/16777216 : ℝ) (1099511627776/576650390625 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_17 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 10 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_18 (t : ℝ) (ht : t ∈ Icc (9/8 : ℝ) (19/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(412368437791/4294967296 : ℝ) := by
  have hta : 0≤t-(9/8 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(19/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(412368437791/4294967296 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(412368437791/4294967296 : ℝ)=(667409309983 : ℝ)*(t-(9/8 : ℝ))^0*((19/16 : ℝ)-t)^8 + (5490662847736 : ℝ)*(t-(9/8 : ℝ))^1*((19/16 : ℝ)-t)^7 + (19754687579236 : ℝ)*(t-(9/8 : ℝ))^2*((19/16 : ℝ)-t)^6 + (40597711259080 : ℝ)*(t-(9/8 : ℝ))^3*((19/16 : ℝ)-t)^5 + (52122642374682 : ℝ)*(t-(9/8 : ℝ))^4*((19/16 : ℝ)-t)^4 + (42808925105800 : ℝ)*(t-(9/8 : ℝ))^5*((19/16 : ℝ)-t)^3 + (21964179020276 : ℝ)*(t-(9/8 : ℝ))^6*((19/16 : ℝ)-t)^2 + (6436355947144 : ℝ)*(t-(9/8 : ℝ))^7*((19/16 : ℝ)-t)^1 + (824736875582 : ℝ)*(t-(9/8 : ℝ))^8*((19/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(412368437791/4294967296 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (412368437791/4294967296 : ℝ)-kernelFourthDensityPolynomial t=(157327565599 : ℝ)*(t-(9/8 : ℝ))^0*((19/16 : ℝ)-t)^8 + (1107232156920 : ℝ)*(t-(9/8 : ℝ))^1*((19/16 : ℝ)-t)^7 + (3337944937060 : ℝ)*(t-(9/8 : ℝ))^2*((19/16 : ℝ)-t)^6 + (5587553773512 : ℝ)*(t-(9/8 : ℝ))^3*((19/16 : ℝ)-t)^5 + (5608938916058 : ℝ)*(t-(9/8 : ℝ))^4*((19/16 : ℝ)-t)^4 + (3376339926792 : ℝ)*(t-(9/8 : ℝ))^5*((19/16 : ℝ)-t)^3 + (1128453496020 : ℝ)*(t-(9/8 : ℝ))^6*((19/16 : ℝ)-t)^2 + (161539057512 : ℝ)*(t-(9/8 : ℝ))^7*((19/16 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_18 :
    (∫ t in (9/8 : ℝ)..(19/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(105566320074496/8649755859375 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (9/8 : ℝ) (19/16 : ℝ) (412368437791/4294967296 : ℝ) (17592186044416/8649755859375 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_18 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 11 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_19 (t : ℝ) (ht : t ∈ Icc (19/16 : ℝ) (5/4 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(8758335/65536 : ℝ) := by
  have hta : 0≤t-(19/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(5/4 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(8758335/65536 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(8758335/65536 : ℝ)=(986354680351 : ℝ)*(t-(19/16 : ℝ))^0*((5/4 : ℝ)-t)^8 + (8052376500320 : ℝ)*(t-(19/16 : ℝ))^1*((5/4 : ℝ)-t)^7 + (28751024358976 : ℝ)*(t-(19/16 : ℝ))^2*((5/4 : ℝ)-t)^6 + (58640040905216 : ℝ)*(t-(19/16 : ℝ))^3*((5/4 : ℝ)-t)^5 + (74723014318592 : ℝ)*(t-(19/16 : ℝ))^4*((5/4 : ℝ)-t)^4 + (60914814459904 : ℝ)*(t-(19/16 : ℝ))^5*((5/4 : ℝ)-t)^3 + (31023376515072 : ℝ)*(t-(19/16 : ℝ))^6*((5/4 : ℝ)-t)^2 + (9024510492672 : ℝ)*(t-(19/16 : ℝ))^7*((5/4 : ℝ)-t)^1 + (1147972485120 : ℝ)*(t-(19/16 : ℝ))^8*((5/4 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(8758335/65536 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (8758335/65536 : ℝ)-kernelFourthDensityPolynomial t=(161617804769 : ℝ)*(t-(19/16 : ℝ))^0*((5/4 : ℝ)-t)^8 + (1131403380640 : ℝ)*(t-(19/16 : ℝ))^1*((5/4 : ℝ)-t)^7 + (3392205224384 : ℝ)*(t-(19/16 : ℝ))^2*((5/4 : ℝ)-t)^6 + (5646418261504 : ℝ)*(t-(19/16 : ℝ))^3*((5/4 : ℝ)-t)^5 + (5635059639808 : ℝ)*(t-(19/16 : ℝ))^4*((5/4 : ℝ)-t)^4 + (3371644706816 : ℝ)*(t-(19/16 : ℝ))^5*((5/4 : ℝ)-t)^3 + (1119853068288 : ℝ)*(t-(19/16 : ℝ))^6*((5/4 : ℝ)-t)^2 + (159269388288 : ℝ)*(t-(19/16 : ℝ))^7*((5/4 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_19 :
    (∫ t in (19/16 : ℝ)..(5/4 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(156736509968384/8649755859375 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (19/16 : ℝ) (5/4 : ℝ) (8758335/65536 : ℝ) (281474976710656/129746337890625 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_19 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 12 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_20 (t : ℝ) (ht : t ∈ Icc (5/4 : ℝ) (21/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(725262105183/4294967296 : ℝ) := by
  have hta : 0≤t-(5/4 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(21/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(725262105183/4294967296 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(725262105183/4294967296 : ℝ)=(1299248347743 : ℝ)*(t-(5/4 : ℝ))^0*((21/16 : ℝ)-t)^8 + (10553256170232 : ℝ)*(t-(5/4 : ℝ))^1*((21/16 : ℝ)-t)^7 + (37488872104548 : ℝ)*(t-(5/4 : ℝ))^2*((21/16 : ℝ)-t)^6 + (76069943977160 : ℝ)*(t-(5/4 : ℝ))^3*((21/16 : ℝ)-t)^5 + (96433016393722 : ℝ)*(t-(5/4 : ℝ))^4*((21/16 : ℝ)-t)^4 + (78204003404488 : ℝ)*(t-(5/4 : ℝ))^5*((21/16 : ℝ)-t)^3 + (39619695811748 : ℝ)*(t-(5/4 : ℝ))^6*((21/16 : ℝ)-t)^2 + (11464153316248 : ℝ)*(t-(5/4 : ℝ))^7*((21/16 : ℝ)-t)^1 + (1450524210366 : ℝ)*(t-(5/4 : ℝ))^8*((21/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(725262105183/4294967296 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (725262105183/4294967296 : ℝ)-kernelFourthDensityPolynomial t=(151275862623 : ℝ)*(t-(5/4 : ℝ))^0*((21/16 : ℝ)-t)^8 + (1050937512696 : ℝ)*(t-(5/4 : ℝ))^1*((21/16 : ℝ)-t)^7 + (3125805785700 : ℝ)*(t-(5/4 : ℝ))^2*((21/16 : ℝ)-t)^6 + (5159411803336 : ℝ)*(t-(5/4 : ℝ))^3*((21/16 : ℝ)-t)^5 + (5103678331898 : ℝ)*(t-(5/4 : ℝ))^4*((21/16 : ℝ)-t)^4 + (3025352376008 : ℝ)*(t-(5/4 : ℝ))^5*((21/16 : ℝ)-t)^3 + (994982078500 : ℝ)*(t-(5/4 : ℝ))^6*((21/16 : ℝ)-t)^2 + (140040366680 : ℝ)*(t-(5/4 : ℝ))^7*((21/16 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_20 :
    (∫ t in (5/4 : ℝ)..(21/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(15843592441757696/648731689453125 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (5/4 : ℝ) (21/16 : ℝ) (725262105183/4294967296 : ℝ) (4503599627370496/1946195068359375 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_20 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 13 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_21 (t : ℝ) (ht : t ∈ Icc (21/16 : ℝ) (11/8 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(3307301503/16777216 : ℝ) := by
  have hta : 0≤t-(21/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(11/8 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(3307301503/16777216 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(3307301503/16777216 : ℝ)=(1571931289951 : ℝ)*(t-(21/16 : ℝ))^0*((11/8 : ℝ)-t)^8 + (12715490686288 : ℝ)*(t-(21/16 : ℝ))^1*((11/8 : ℝ)-t)^7 + (44979659173648 : ℝ)*(t-(21/16 : ℝ))^2*((11/8 : ℝ)-t)^6 + (90877110472384 : ℝ)*(t-(21/16 : ℝ))^3*((11/8 : ℝ)-t)^5 + (114697413685152 : ℝ)*(t-(21/16 : ℝ))^4*((11/8 : ℝ)-t)^4 + (92597705206528 : ℝ)*(t-(21/16 : ℝ))^5*((11/8 : ℝ)-t)^3 + (46696078836992 : ℝ)*(t-(21/16 : ℝ))^6*((11/8 : ℝ)-t)^2 + (13448114990080 : ℝ)*(t-(21/16 : ℝ))^7*((11/8 : ℝ)-t)^1 + (1693338369536 : ℝ)*(t-(21/16 : ℝ))^8*((11/8 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(3307301503/16777216 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (3307301503/16777216 : ℝ)-kernelFourthDensityPolynomial t=(121407079585 : ℝ)*(t-(21/16 : ℝ))^0*((11/8 : ℝ)-t)^8 + (831216270000 : ℝ)*(t-(21/16 : ℝ))^1*((11/8 : ℝ)-t)^7 + (2433815173360 : ℝ)*(t-(21/16 : ℝ))^2*((11/8 : ℝ)-t)^6 + (3949838221632 : ℝ)*(t-(21/16 : ℝ))^3*((11/8 : ℝ)-t)^5 + (3836272182368 : ℝ)*(t-(21/16 : ℝ))^4*((11/8 : ℝ)-t)^4 + (2229243487488 : ℝ)*(t-(21/16 : ℝ))^5*((11/8 : ℝ)-t)^3 + (717395510016 : ℝ)*(t-(21/16 : ℝ))^6*((11/8 : ℝ)-t)^2 + (98591966208 : ℝ)*(t-(21/16 : ℝ))^7*((11/8 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_21 :
    (∫ t in (21/16 : ℝ)..(11/8 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(887796987087290368/29192926025390625 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (21/16 : ℝ) (11/8 : ℝ) (3307301503/16777216 : ℝ) (72057594037927936/29192926025390625 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_21 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 14 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_22 (t : ℝ) (ht : t ∈ Icc (11/8 : ℝ) (23/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(913035440127/4294967296 : ℝ) := by
  have hta : 0≤t-(11/8 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(23/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(913035440127/4294967296 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(913035440127/4294967296 : ℝ)=(1759704624895 : ℝ)*(t-(11/8 : ℝ))^0*((23/16 : ℝ)-t)^8 + (14176228965368 : ℝ)*(t-(11/8 : ℝ))^1*((23/16 : ℝ)-t)^7 + (49934621513956 : ℝ)*(t-(11/8 : ℝ))^2*((23/16 : ℝ)-t)^6 + (100445681522888 : ℝ)*(t-(11/8 : ℝ))^3*((23/16 : ℝ)-t)^5 + (126197506372442 : ℝ)*(t-(11/8 : ℝ))^4*((23/16 : ℝ)-t)^4 + (101401078730248 : ℝ)*(t-(11/8 : ℝ))^5*((23/16 : ℝ)-t)^3 + (50884769163636 : ℝ)*(t-(11/8 : ℝ))^6*((23/16 : ℝ)-t)^2 + (14579683336680 : ℝ)*(t-(11/8 : ℝ))^7*((23/16 : ℝ)-t)^1 + (1826070880254 : ℝ)*(t-(11/8 : ℝ))^8*((23/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(913035440127/4294967296 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (913035440127/4294967296 : ℝ)-kernelFourthDensityPolynomial t=(66366255359 : ℝ)*(t-(11/8 : ℝ))^0*((23/16 : ℝ)-t)^8 + (432338076664 : ℝ)*(t-(11/8 : ℝ))^1*((23/16 : ℝ)-t)^7 + (1195363133156 : ℝ)*(t-(11/8 : ℝ))^2*((23/16 : ℝ)-t)^6 + (1814287771336 : ℝ)*(t-(11/8 : ℝ))^3*((23/16 : ℝ)-t)^5 + (1627455245338 : ℝ)*(t-(11/8 : ℝ))^4*((23/16 : ℝ)-t)^4 + (858890563976 : ℝ)*(t-(11/8 : ℝ))^5*((23/16 : ℝ)-t)^3 + (245215483476 : ℝ)*(t-(11/8 : ℝ))^6*((23/16 : ℝ)-t)^2 + (28883705352 : ℝ)*(t-(11/8 : ℝ))^7*((23/16 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_22 :
    (∫ t in (11/8 : ℝ)..(23/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(5106064264888582144/145964630126953125 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (11/8 : ℝ) (23/16 : ℝ) (913035440127/4294967296 : ℝ) (1152921504606846976/437893890380859375 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_22 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 15 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_23 (t : ℝ) (ht : t ∈ Icc (23/16 : ℝ) (3/2 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(448804763/2097152 : ℝ) := by
  have hta : 0≤t-(23/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(3/2 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(448804763/2097152 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(448804763/2097152 : ℝ)=(1832187594751 : ℝ)*(t-(23/16 : ℝ))^0*((3/2 : ℝ)-t)^8 + (14686384463360 : ℝ)*(t-(23/16 : ℝ))^1*((3/2 : ℝ)-t)^7 + (51460409044480 : ℝ)*(t-(23/16 : ℝ))^2*((3/2 : ℝ)-t)^6 + (102945041317888 : ℝ)*(t-(23/16 : ℝ))^3*((3/2 : ℝ)-t)^5 + (128589090516992 : ℝ)*(t-(23/16 : ℝ))^4*((3/2 : ℝ)-t)^4 + (102693171314688 : ℝ)*(t-(23/16 : ℝ))^5*((3/2 : ℝ)-t)^3 + (51202069340160 : ℝ)*(t-(23/16 : ℝ))^6*((3/2 : ℝ)-t)^2 + (14571043995648 : ℝ)*(t-(23/16 : ℝ))^7*((3/2 : ℝ)-t)^1 + (1811884595200 : ℝ)*(t-(23/16 : ℝ))^8*((3/2 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(448804763/2097152 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (448804763/2097152 : ℝ)-kernelFourthDensityPolynomial t=(6116714497 : ℝ)*(t-(23/16 : ℝ))^0*((3/2 : ℝ)-t)^8 + (20050010624 : ℝ)*(t-(23/16 : ℝ))^1*((3/2 : ℝ)-t)^7 + (12111614464 : ℝ)*(t-(23/16 : ℝ))^2*((3/2 : ℝ)-t)^6 + (92211130368 : ℝ)*(t-(23/16 : ℝ))^4*((3/2 : ℝ)-t)^4 + (251870003200 : ℝ)*(t-(23/16 : ℝ))^5*((3/2 : ℝ)-t)^3 + (270451318784 : ℝ)*(t-(23/16 : ℝ))^6*((3/2 : ℝ)-t)^2 + (135390478336 : ℝ)*(t-(23/16 : ℝ))^7*((3/2 : ℝ)-t)^1 + (26419714048 : ℝ)*(t-(23/16 : ℝ))^8*((3/2 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_23 :
    (∫ t in (23/16 : ℝ)..(3/2 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(246733027759875948544/6568408355712890625 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (23/16 : ℝ) (3/2 : ℝ) (448804763/2097152 : ℝ) (18446744073709551616/6568408355712890625 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_23 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 16 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_24 (t : ℝ) (ht : t ∈ Icc (3/2 : ℝ) (25/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(53211/256 : ℝ) := by
  have hta : 0≤t-(3/2 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(25/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(53211/256 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(53211/256 : ℝ)=(1785464881152 : ℝ)*(t-(3/2 : ℝ))^0*((25/16 : ℝ)-t)^8 + (14207751815168 : ℝ)*(t-(3/2 : ℝ))^1*((25/16 : ℝ)-t)^7 + (49398776070144 : ℝ)*(t-(3/2 : ℝ))^2*((25/16 : ℝ)-t)^6 + (98008759795712 : ℝ)*(t-(3/2 : ℝ))^3*((25/16 : ℝ)-t)^5 + (121350585638912 : ℝ)*(t-(3/2 : ℝ))^4*((25/16 : ℝ)-t)^4 + (96004977704960 : ℝ)*(t-(3/2 : ℝ))^5*((25/16 : ℝ)-t)^3 + (47387147537920 : ℝ)*(t-(3/2 : ℝ))^6*((25/16 : ℝ)-t)^2 + (13340018301440 : ℝ)*(t-(3/2 : ℝ))^7*((25/16 : ℝ)-t)^1 + (1639533489151 : ℝ)*(t-(3/2 : ℝ))^8*((25/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(53211/256 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (53211/256 : ℝ)-kernelFourthDensityPolynomial t=(75967234048 : ℝ)*(t-(3/2 : ℝ))^1*((25/16 : ℝ)-t)^7 + (594240602112 : ℝ)*(t-(3/2 : ℝ))^2*((25/16 : ℝ)-t)^6 + (1977273548800 : ℝ)*(t-(3/2 : ℝ))^3*((25/16 : ℝ)-t)^5 + (3631956041728 : ℝ)*(t-(3/2 : ℝ))^4*((25/16 : ℝ)-t)^4 + (3981055639552 : ℝ)*(t-(3/2 : ℝ))^5*((25/16 : ℝ)-t)^3 + (2605869134336 : ℝ)*(t-(3/2 : ℝ))^6*((25/16 : ℝ)-t)^2 + (943700747776 : ℝ)*(t-(3/2 : ℝ))^7*((25/16 : ℝ)-t)^1 + (145931392001 : ℝ)*(t-(3/2 : ℝ))^8*((25/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_24 :
    (∫ t in (3/2 : ℝ)..(25/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(1278085545450727800832/32842041778564453125 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (3/2 : ℝ) (25/16 : ℝ) (53211/256 : ℝ) (295147905179352825856/98526125335693359375 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_24 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 17 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_25 (t : ℝ) (ht : t ∈ Icc (25/16 : ℝ) (13/8 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(746801048575/4294967296 : ℝ) := by
  have hta : 0≤t-(25/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(13/8 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(746801048575/4294967296 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(746801048575/4294967296 : ℝ)=(1493602097150 : ℝ)*(t-(25/16 : ℝ))^0*((13/8 : ℝ)-t)^8 + (11725066388968 : ℝ)*(t-(25/16 : ℝ))^1*((13/8 : ℝ)-t)^7 + (40168563126644 : ℝ)*(t-(25/16 : ℝ))^2*((13/8 : ℝ)-t)^6 + (78418100616712 : ℝ)*(t-(25/16 : ℝ))^3*((13/8 : ℝ)-t)^5 + (95386846870362 : ℝ)*(t-(25/16 : ℝ))^4*((13/8 : ℝ)-t)^4 + (74002028984520 : ℝ)*(t-(25/16 : ℝ))^5*((13/8 : ℝ)-t)^3 + (35743100348644 : ℝ)*(t-(25/16 : ℝ))^6*((13/8 : ℝ)-t)^2 + (9821728955384 : ℝ)*(t-(25/16 : ℝ))^7*((13/8 : ℝ)-t)^1 + (1174812502783 : ℝ)*(t-(25/16 : ℝ))^8*((13/8 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(746801048575/4294967296 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (746801048575/4294967296 : ℝ)-kernelFourthDensityPolynomial t=(223750388232 : ℝ)*(t-(25/16 : ℝ))^1*((13/8 : ℝ)-t)^7 + (1652295593556 : ℝ)*(t-(25/16 : ℝ))^2*((13/8 : ℝ)-t)^6 + (5223616823688 : ℝ)*(t-(25/16 : ℝ))^3*((13/8 : ℝ)-t)^5 + (9165299930138 : ℝ)*(t-(25/16 : ℝ))^4*((13/8 : ℝ)-t)^4 + (9639688455880 : ℝ)*(t-(25/16 : ℝ))^5*((13/8 : ℝ)-t)^3 + (6077758371556 : ℝ)*(t-(25/16 : ℝ))^6*((13/8 : ℝ)-t)^2 + (2127087821816 : ℝ)*(t-(25/16 : ℝ))^7*((13/8 : ℝ)-t)^1 + (318789594367 : ℝ)*(t-(25/16 : ℝ))^8*((13/8 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_25 :
    (∫ t in (25/16 : ℝ)..(13/8 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(2052791091358804738048/59115675201416015625 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (25/16 : ℝ) (13/8 : ℝ) (746801048575/4294967296 : ℝ) (4722366482869645213696/1477891880035400390625 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_25 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 18 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_26 (t : ℝ) (ht : t ∈ Icc (13/8 : ℝ) (27/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(1671919743/16777216 : ℝ) := by
  have hta : 0≤t-(13/8 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(27/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(1671919743/16777216 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(1671919743/16777216 : ℝ)=(856022908416 : ℝ)*(t-(13/8 : ℝ))^0*((27/16 : ℝ)-t)^8 + (6424954334208 : ℝ)*(t-(13/8 : ℝ))^1*((27/16 : ℝ)-t)^7 + (20891786642688 : ℝ)*(t-(13/8 : ℝ))^2*((27/16 : ℝ)-t)^6 + (38353726909184 : ℝ)*(t-(13/8 : ℝ))^3*((27/16 : ℝ)-t)^5 + (43343201947552 : ℝ)*(t-(13/8 : ℝ))^4*((27/16 : ℝ)-t)^4 + (30735143435968 : ℝ)*(t-(13/8 : ℝ))^5*((27/16 : ℝ)-t)^3 + (13262087554832 : ℝ)*(t-(13/8 : ℝ))^6*((27/16 : ℝ)-t)^2 + (3147140829520 : ℝ)*(t-(13/8 : ℝ))^7*((27/16 : ℝ)-t)^1 + (307866455391 : ℝ)*(t-(13/8 : ℝ))^8*((27/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(1671919743/16777216 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (1671919743/16777216 : ℝ)-kernelFourthDensityPolynomial t=(423228933120 : ℝ)*(t-(13/8 : ℝ))^1*((27/16 : ℝ)-t)^7 + (3076854792960 : ℝ)*(t-(13/8 : ℝ))^2*((27/16 : ℝ)-t)^6 + (9583555962112 : ℝ)*(t-(13/8 : ℝ))^3*((27/16 : ℝ)-t)^5 + (16578401641568 : ℝ)*(t-(13/8 : ℝ))^4*((27/16 : ℝ)-t)^4 + (17202139435328 : ℝ)*(t-(13/8 : ℝ))^5*((27/16 : ℝ)-t)^3 + (10706553880816 : ℝ)*(t-(13/8 : ℝ))^6*((27/16 : ℝ)-t)^2 + (3701042437808 : ℝ)*(t-(13/8 : ℝ))^7*((27/16 : ℝ)-t)^1 + (548156453025 : ℝ)*(t-(13/8 : ℝ))^8*((27/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_26 :
    (∫ t in (13/8 : ℝ)..(27/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(156867856907670321627136/7389459400177001953125 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (13/8 : ℝ) (27/16 : ℝ) (1671919743/16777216 : ℝ) (75557863725914323419136/22168378200531005859375 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_26 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 19 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_27 (t : ℝ) (ht : t ∈ Icc (27/16 : ℝ) (7/4 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(14717633/65536 : ℝ) := by
  have hta : 0≤t-(27/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(7/4 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(14717633/65536 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(14717633/65536 : ℝ)=(844389797471 : ℝ)*(t-(27/16 : ℝ))^0*((7/4 : ℝ)-t)^8 + (6070909193376 : ℝ)*(t-(27/16 : ℝ))^1*((7/4 : ℝ)-t)^7 + (18705812523584 : ℝ)*(t-(27/16 : ℝ))^2*((7/4 : ℝ)-t)^6 + (32019556713984 : ℝ)*(t-(27/16 : ℝ))^3*((7/4 : ℝ)-t)^5 + (32884652595712 : ℝ)*(t-(27/16 : ℝ))^4*((7/4 : ℝ)-t)^4 + (20263290691584 : ℝ)*(t-(27/16 : ℝ))^5*((7/4 : ℝ)-t)^3 + (6936514412544 : ℝ)*(t-(27/16 : ℝ))^6*((7/4 : ℝ)-t)^2 + (1017612730368 : ℝ)*(t-(27/16 : ℝ))^7*((7/4 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(14717633/65536 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (14717633/65536 : ℝ)-kernelFourthDensityPolynomial t=(1084679795105 : ℝ)*(t-(27/16 : ℝ))^0*((7/4 : ℝ)-t)^8 + (9361647547232 : ℝ)*(t-(27/16 : ℝ))^1*((7/4 : ℝ)-t)^7 + (35308136068544 : ℝ)*(t-(27/16 : ℝ))^2*((7/4 : ℝ)-t)^6 + (76008340470272 : ℝ)*(t-(27/16 : ℝ))^3*((7/4 : ℝ)-t)^5 + (102150218884608 : ℝ)*(t-(27/16 : ℝ))^4*((7/4 : ℝ)-t)^4 + (87764606492672 : ℝ)*(t-(27/16 : ℝ))^5*((7/4 : ℝ)-t)^3 + (47077434179584 : ℝ)*(t-(27/16 : ℝ))^6*((7/4 : ℝ)-t)^2 + (14414944010240 : ℝ)*(t-(27/16 : ℝ))^7*((7/4 : ℝ)-t)^1 + (1929069592576 : ℝ)*(t-(27/16 : ℝ))^8*((7/4 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_27 :
    (∫ t in (27/16 : ℝ)..(7/4 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(16968275582611383079927808/332525673007965087890625 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (27/16 : ℝ) (7/4 : ℝ) (14717633/65536 : ℝ) (1208925819614629174706176/332525673007965087890625 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_27 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 20 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_28 (t : ℝ) (ht : t ∈ Icc (7/4 : ℝ) (29/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(2183534686689/4294967296 : ℝ) := by
  have hta : 0≤t-(7/4 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(29/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(2183534686689/4294967296 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(2183534686689/4294967296 : ℝ)=(1218999890401 : ℝ)*(t-(7/4 : ℝ))^0*((29/16 : ℝ)-t)^8 + (8734386392840 : ℝ)*(t-(7/4 : ℝ))^1*((29/16 : ℝ)-t)^7 + (26821933118620 : ℝ)*(t-(7/4 : ℝ))^2*((29/16 : ℝ)-t)^6 + (45759406770488 : ℝ)*(t-(7/4 : ℝ))^3*((29/16 : ℝ)-t)^5 + (46841038257542 : ℝ)*(t-(7/4 : ℝ))^4*((29/16 : ℝ)-t)^4 + (28769207251768 : ℝ)*(t-(7/4 : ℝ))^5*((29/16 : ℝ)-t)^3 + (9816580344540 : ℝ)*(t-(7/4 : ℝ))^6*((29/16 : ℝ)-t)^2 + (1435551196008 : ℝ)*(t-(7/4 : ℝ))^7*((29/16 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(2183534686689/4294967296 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (2183534686689/4294967296 : ℝ)-kernelFourthDensityPolynomial t=(3148069482977 : ℝ)*(t-(7/4 : ℝ))^0*((29/16 : ℝ)-t)^8 + (26202168594184 : ℝ)*(t-(7/4 : ℝ))^1*((29/16 : ℝ)-t)^7 + (95456009335964 : ℝ)*(t-(7/4 : ℝ))^2*((29/16 : ℝ)-t)^6 + (198796478138680 : ℝ)*(t-(7/4 : ℝ))^3*((29/16 : ℝ)-t)^5 + (258853817878918 : ℝ)*(t-(7/4 : ℝ))^4*((29/16 : ℝ)-t)^4 + (215786677657400 : ℝ)*(t-(7/4 : ℝ))^5*((29/16 : ℝ)-t)^3 + (112461362110044 : ℝ)*(t-(7/4 : ℝ))^6*((29/16 : ℝ)-t)^2 + (33501003791016 : ℝ)*(t-(7/4 : ℝ))^7*((29/16 : ℝ)-t)^1 + (4367069373378 : ℝ)*(t-(7/4 : ℝ))^8*((29/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_28 :
    (∫ t in (7/4 : ℝ)..(29/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(204870125027565273589219328/1662628365039825439453125 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (7/4 : ℝ) (29/16 : ℝ) (2183534686689/4294967296 : ℝ) (19342813113834066795298816/4987885095119476318359375 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_28 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 21 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_29 (t : ℝ) (ht : t ∈ Icc (29/16 : ℝ) (15/8 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(15110391585/16777216 : ℝ) := by
  have hta : 0≤t-(29/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(15/8 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(15110391585/16777216 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(15110391585/16777216 : ℝ)=(1684725559071 : ℝ)*(t-(29/16 : ℝ))^0*((15/8 : ℝ)-t)^8 + (12042253276560 : ℝ)*(t-(29/16 : ℝ))^1*((15/8 : ℝ)-t)^7 + (36891179254416 : ℝ)*(t-(29/16 : ℝ))^2*((15/8 : ℝ)-t)^6 + (62788087726016 : ℝ)*(t-(29/16 : ℝ))^3*((15/8 : ℝ)-t)^5 + (64120240664992 : ℝ)*(t-(29/16 : ℝ))^4*((15/8 : ℝ)-t)^4 + (39289425889024 : ℝ)*(t-(29/16 : ℝ))^5*((15/8 : ℝ)-t)^3 + (13375025161472 : ℝ)*(t-(29/16 : ℝ))^6*((15/8 : ℝ)-t)^2 + (1951403748352 : ℝ)*(t-(29/16 : ℝ))^7*((15/8 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(15110391585/16777216 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (15110391585/16777216 : ℝ)-kernelFourthDensityPolynomial t=(6051794932449 : ℝ)*(t-(29/16 : ℝ))^0*((15/8 : ℝ)-t)^8 + (49849910655600 : ℝ)*(t-(29/16 : ℝ))^1*((15/8 : ℝ)-t)^7 + (179731394508144 : ℝ)*(t-(29/16 : ℝ))^2*((15/8 : ℝ)-t)^6 + (370457059799104 : ℝ)*(t-(29/16 : ℝ))^3*((15/8 : ℝ)-t)^5 + (477436193741408 : ℝ)*(t-(29/16 : ℝ))^4*((15/8 : ℝ)-t)^4 + (393955721636096 : ℝ)*(t-(29/16 : ℝ))^5*((15/8 : ℝ)-t)^3 + (203247548601088 : ℝ)*(t-(29/16 : ℝ))^6*((15/8 : ℝ)-t)^2 + (59940760183808 : ℝ)*(t-(29/16 : ℝ))^7*((15/8 : ℝ)-t)^1 + (7736520491520 : ℝ)*(t-(29/16 : ℝ))^8*((15/8 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_29 :
    (∫ t in (29/16 : ℝ)..(15/8 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(1161406360091789285302206464/4987885095119476318359375 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (29/16 : ℝ) (15/8 : ℝ) (15110391585/16777216 : ℝ) (309485009821345068724781056/74818276426792144775390625 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_29 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 22 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_30 (t : ℝ) (ht : t ∈ Icc (15/8 : ℝ) (31/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(6123873294017/4294967296 : ℝ) := by
  have hta : 0≤t-(15/8 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(31/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(6123873294017/4294967296 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(6123873294017/4294967296 : ℝ)=(2255613048257 : ℝ)*(t-(15/8 : ℝ))^0*((31/16 : ℝ)-t)^8 + (16093500637704 : ℝ)*(t-(15/8 : ℝ))^1*((31/16 : ℝ)-t)^7 + (49212538035740 : ℝ)*(t-(15/8 : ℝ))^2*((31/16 : ℝ)-t)^6 + (83607291889464 : ℝ)*(t-(15/8 : ℝ))^3*((31/16 : ℝ)-t)^5 + (85227355302502 : ℝ)*(t-(15/8 : ℝ))^4*((31/16 : ℝ)-t)^4 + (52129059493752 : ℝ)*(t-(15/8 : ℝ))^5*((31/16 : ℝ)-t)^3 + (17714242948140 : ℝ)*(t-(15/8 : ℝ))^6*((31/16 : ℝ)-t)^2 + (2579897313720 : ℝ)*(t-(15/8 : ℝ))^7*((31/16 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(6123873294017/4294967296 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (6123873294017/4294967296 : ℝ)-kernelFourthDensityPolynomial t=(9992133539777 : ℝ)*(t-(15/8 : ℝ))^0*((31/16 : ℝ)-t)^8 + (81888472066568 : ℝ)*(t-(15/8 : ℝ))^1*((31/16 : ℝ)-t)^7 + (293724366429212 : ℝ)*(t-(15/8 : ℝ))^2*((31/16 : ℝ)-t)^6 + (602266517040440 : ℝ)*(t-(15/8 : ℝ))^3*((31/16 : ℝ)-t)^5 + (772114905859878 : ℝ)*(t-(15/8 : ℝ))^4*((31/16 : ℝ)-t)^4 + (633744749436152 : ℝ)*(t-(15/8 : ℝ))^5*((31/16 : ℝ)-t)^3 + (325222661516812 : ℝ)*(t-(15/8 : ℝ))^6*((31/16 : ℝ)-t)^2 + (95402075390552 : ℝ)*(t-(15/8 : ℝ))^7*((31/16 : ℝ)-t)^1 + (12247746588034 : ℝ)*(t-(15/8 : ℝ))^8*((31/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_30 :
    (∫ t in (15/8 : ℝ)..(31/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(441271575759985489465585958912/1122274146401882171630859375 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (15/8 : ℝ) (31/16 : ℝ) (6123873294017/4294967296 : ℝ) (4951760157141521099596496896/1122274146401882171630859375 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_30 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 23 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_31 (t : ℝ) (ht : t ∈ Icc (31/16 : ℝ) (2 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(2112 : ℝ) := by
  have hta : 0≤t-(31/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(2 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(2112 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(2112 : ℝ)=(2947097635135 : ℝ)*(t-(31/16 : ℝ))^0*((2 : ℝ)-t)^8 + (20996883767360 : ℝ)*(t-(31/16 : ℝ))^1*((2 : ℝ)-t)^7 + (64114414339840 : ℝ)*(t-(31/16 : ℝ))^2*((2 : ℝ)-t)^6 + (108767949099008 : ℝ)*(t-(31/16 : ℝ))^3*((2 : ℝ)-t)^5 + (110716923871232 : ℝ)*(t-(31/16 : ℝ))^4*((2 : ℝ)-t)^4 + (67623014367232 : ℝ)*(t-(31/16 : ℝ))^5*((2 : ℝ)-t)^3 + (22946600976384 : ℝ)*(t-(31/16 : ℝ))^6*((2 : ℝ)-t)^2 + (3337189588992 : ℝ)*(t-(31/16 : ℝ))^7*((2 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(2112 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (2112 : ℝ)-kernelFourthDensityPolynomial t=(15194844223169 : ℝ)*(t-(31/16 : ℝ))^0*((2 : ℝ)-t)^8 + (124138651099072 : ℝ)*(t-(31/16 : ℝ))^1*((2 : ℝ)-t)^7 + (443859957692672 : ℝ)*(t-(31/16 : ℝ))^2*((2 : ℝ)-t)^6 + (907180794966016 : ℝ)*(t-(31/16 : ℝ))^3*((2 : ℝ)-t)^5 + (1159219006210048 : ℝ)*(t-(31/16 : ℝ))^4*((2 : ℝ)-t)^4 + (948325729697792 : ℝ)*(t-(31/16 : ℝ))^5*((2 : ℝ)-t)^3 + (485027771056128 : ℝ)*(t-(31/16 : ℝ))^6*((2 : ℝ)-t)^2 + (141798345277440 : ℝ)*(t-(31/16 : ℝ))^7*((2 : ℝ)-t)^1 + (18141941858304 : ℝ)*(t-(31/16 : ℝ))^8*((2 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_31 :
    (∫ t in (31/16 : ℝ)..(2 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(3486039150627630854115933814784/5611370732009410858154296875 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (31/16 : ℝ) (2 : ℝ) (2112 : ℝ) (79228162514264337593543950336/16834112196028232574462890625 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_31 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 24 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_whole_interval :
    (∫ t in (0 : ℝ)..2,|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(1730 : ℝ) := by
  have hc : Continuous (fun t => |kernelFourthDensityPolynomial t| * Real.exp (t-1/2)) := by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (μ := volume) (a := fun j : ℕ => (j : ℝ)/16) (n := 32)
    (fun k hk => hc.intervalIntegrable ((k : ℝ)/16) ((k+1 : ℕ)/16 : ℝ))
  norm_num only [Nat.cast_zero,zero_div,Nat.cast_ofNat] at hsum
  rw [← hsum]
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.cast_add,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
  have h0 := kernel_fourth_interval_0
  have h1 := kernel_fourth_interval_1
  have h2 := kernel_fourth_interval_2
  have h3 := kernel_fourth_interval_3
  have h4 := kernel_fourth_interval_4
  have h5 := kernel_fourth_interval_5
  have h6 := kernel_fourth_interval_6
  have h7 := kernel_fourth_interval_7
  have h8 := kernel_fourth_interval_8
  have h9 := kernel_fourth_interval_9
  have h10 := kernel_fourth_interval_10
  have h11 := kernel_fourth_interval_11
  have h12 := kernel_fourth_interval_12
  have h13 := kernel_fourth_interval_13
  have h14 := kernel_fourth_interval_14
  have h15 := kernel_fourth_interval_15
  have h16 := kernel_fourth_interval_16
  have h17 := kernel_fourth_interval_17
  have h18 := kernel_fourth_interval_18
  have h19 := kernel_fourth_interval_19
  have h20 := kernel_fourth_interval_20
  have h21 := kernel_fourth_interval_21
  have h22 := kernel_fourth_interval_22
  have h23 := kernel_fourth_interval_23
  have h24 := kernel_fourth_interval_24
  have h25 := kernel_fourth_interval_25
  have h26 := kernel_fourth_interval_26
  have h27 := kernel_fourth_interval_27
  have h28 := kernel_fourth_interval_28
  have h29 := kernel_fourth_interval_29
  have h30 := kernel_fourth_interval_30
  have h31 := kernel_fourth_interval_31
  norm_num at *
  linarith

end Helfgott

end

section
open MeasureTheory Set
namespace Helfgott
lemma etaPlus_approx_integrable : Integrable (fun t : ℝ => etaPlus t-etaCircle t) := etaPlus_approximation_l1_l2.1
lemma etaPlus_approx_square_integrable : Integrable (fun t : ℝ => (etaPlus t-etaCircle t)^2) := etaPlus_approximation_l1_l2.2.1
lemma etaPlus_approx_l1_le : (∫ t : ℝ,|etaPlus t-etaCircle t|)≤1/1800 := etaPlus_approximation_l1_l2.2.2.1
lemma etaPlus_approx_l2_square_le : (∫ t : ℝ,(etaPlus t-etaCircle t)^2)≤1/6250000 := etaPlus_approximation_l1_l2.2.2.2
end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped FourierTransform Topology
namespace Helfgott
lemma logRawPoly4_abs_integral_le_tight :
    (∫ u in Iic (Real.log 2),|logRawFn logRawPoly4 u|)≤1730 := by
  rw [logRawFn_abs_integral,←intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤2)]
  simpa only [kernelFourthDensityPolynomial,abs_mul,abs_of_pos (Real.exp_pos _)]
    using kernel_fourth_whole_interval
lemma logKernelComplex_fourier_fourth_decay_tight (ξ : ℝ) :
    (2*Real.pi*|ξ|)^4*‖𝓕 logKernelComplex ξ‖ ≤ 2600 := by
  have hn : ‖fourierCoefficient ξ‖ = 2*Real.pi*|ξ| := by
    dsimp [fourierCoefficient]
    simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,Complex.norm_I,mul_one]
  have hi : ‖∫ u in Iic (Real.log 2), fourierPhase ξ u*(logRawFn logRawPoly4 u : ℂ)‖ ≤
      ∫ u in Iic (Real.log 2), |logRawFn logRawPoly4 u| := by
    calc
      _ ≤ ∫ u in Iic (Real.log 2), ‖fourierPhase ξ u*(logRawFn logRawPoly4 u : ℂ)‖ :=
        norm_integral_le_integral_norm _
      _ = _ := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro u _
        simp only [norm_mul,fourierPhase_norm,one_mul,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ = ‖(fourierCoefficient ξ)^4*𝓕 logKernelComplex ξ‖ := by rw [norm_mul,norm_pow,hn]
    _ = ‖(∫ u in Iic (Real.log 2), fourierPhase ξ u*(logRawFn logRawPoly4 u : ℂ))-
        fourierPhase ξ (Real.log 2)*(logRawFn logRawPoly3 (Real.log 2) : ℂ)‖ := by
      rw [logKernelComplex_fourier_fourth_identity]
    _ ≤ ‖∫ u in Iic (Real.log 2), fourierPhase ξ u*(logRawFn logRawPoly4 u : ℂ)‖+
        ‖fourierPhase ξ (Real.log 2)*(logRawFn logRawPoly3 (Real.log 2) : ℂ)‖ := norm_sub_le _ _
    _ ≤ 2600 := by
      simp only [norm_mul,fourierPhase_norm,one_mul,Complex.norm_real,Real.norm_eq_abs]
      linarith [logRawPoly4_abs_integral_le_tight,logRawPoly3_endpoint_abs_le]

lemma logKernelComplex_fourier_fourth_normalized_tight (ξ : ℝ) :
    ξ^4*‖𝓕 logKernelComplex ξ‖ ≤ 2600/(16*Real.pi^4) := by
  have h := logKernelComplex_fourier_fourth_decay_tight ξ
  have hs : |ξ|^4=ξ^4 := by
    calc
      |ξ|^4 = (|ξ|^2)^2 := by ring
      _ = (ξ^2)^2 := by rw [sq_abs]
      _ = ξ^4 := by ring
  have he : (2*Real.pi*|ξ|)^4=(16*Real.pi^4)*ξ^4 := by
    rw [mul_pow,mul_pow,hs]; norm_num
  rw [he] at h
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 16*Real.pi^4)).mpr
  nlinarith

theorem logKernel_fourierCutoff_fourth_error_tight {H : ℝ} (hH : 0 < H) (u : ℝ) :
    ‖fourierCutoff (𝓕 logKernelComplex) (H/(2*Real.pi)) u-logKernelComplex u‖ ≤
      2600/(3*Real.pi*H^3) := by
  have h := fourierCutoff_fourth_error (𝓕 logKernelComplex) logKernelComplex_fourier_integrable
    (2600/(16*Real.pi^4)) logKernelComplex_fourier_fourth_normalized_tight
    (div_pos hH (by positivity : (0 : ℝ) < 2*Real.pi)) u
  rw [logKernelComplex_integrable.fourierInv_fourier_eq logKernelComplex_fourier_integrable
    logKernelComplex_continuous.continuousAt] at h
  have he : 2*(2600/(16*Real.pi^4))/(3*(H/(2*Real.pi))^3) =
      2600/(3*Real.pi*H^3) := by
    field_simp [ne_of_gt hH,Real.pi_ne_zero]
    <;> ring
  rwa [he] at h

lemma bandLimitedMajorKernel_fourth_error_tight {H t : ℝ} (hH : 0 < H) (ht : 0 < t) :
    |bandLimitedMajorKernel H t-majorKernel t| ≤ 2600/(3*Real.pi*H^3) := by
  have h := logKernel_fourierCutoff_fourth_error_tight hH (Real.log t)
  rw [← bandLimitedMajorKernel_fourierCutoff H (Real.log t) hH.le] at h
  simpa only [logKernelComplex,logMajorKernel,Real.exp_log ht,← Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs] using h

lemma etaPlus_approx_pointwise_tight (t : ℝ) :
    |etaPlus t-etaCircle t| ≤
      (1/28000 : ℝ)*(Ioi (0 : ℝ)).indicator (fun t => t*Real.exp (-(t^2)/2)) t := by
  by_cases ht : 0 < t
  · rw [Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
    have hb := bandLimitedMajorKernel_fourth_error_tight (by norm_num : (0 : ℝ) < 200) ht
    have hnum : 2600/(3*Real.pi*(200 : ℝ)^3)≤(1/28000 : ℝ) := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ)<3*Real.pi*200^3)).mpr
      nlinarith [Real.pi_gt_d2]
    have he : etaPlus t-etaCircle t =
        (bandLimitedMajorKernel 200 t-majorKernel t)*t*Real.exp (-(t^2)/2) := by
      rw [etaCircle_eq_majorKernel]
      unfold etaPlus
      ring
    rw [he,abs_mul,abs_mul,abs_of_pos ht,abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (1/28000)*t*Real.exp (-(t^2)/2) := by gcongr; exact hb.trans hnum
      _ = _ := by ring
  · rw [etaCircle_zero_of_nonpos (le_of_not_gt ht),etaPlus,
      bandLimitedMajorKernel_zero_of_nonpos 200 t (le_of_not_gt ht),
      Set.indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht)]
    norm_num

lemma etaPlus_approx_square_pointwise_tight (t : ℝ) :
    (etaPlus t-etaCircle t)^2 ≤ (1/28000 : ℝ)^2*gaussianApproxSquareFactor t := by
  have h := pow_le_pow_left₀ (abs_nonneg (etaPlus t-etaCircle t)) (etaPlus_approx_pointwise_tight t) 2
  change |etaPlus t-etaCircle t|^2 ≤ ((1/28000 : ℝ)*gaussianApproxFactor t)^2 at h
  simpa only [sq_abs,mul_pow,gaussianApproxFactor_square] using h

lemma etaPlus_approx_l2_square_le_tight : (∫ t : ℝ, (etaPlus t-etaCircle t)^2) ≤ 1/1568000000 := by
  calc
    _ ≤ ∫ t : ℝ, (1/28000 : ℝ)^2*gaussianApproxSquareFactor t :=
      integral_mono etaPlus_approx_square_integrable
        (gaussianApproxSquareFactor_integrable.const_mul ((1/28000 : ℝ)^2))
        etaPlus_approx_square_pointwise_tight
    _ = (1/28000 : ℝ)^2*(∫ t : ℝ, gaussianApproxSquareFactor t) := integral_const_mul _ _
    _ ≤ (1/28000 : ℝ)^2*(1/2) := by
      gcongr
      exact gaussianApproxSquareFactor_integral_le
    _ ≤ _ := by norm_num

end Helfgott
end
open MeasureTheory Helfgott
theorem solution :
    Integrable (fun t : ℝ => (etaPlus t-etaCircle t)^2) ∧
    (∫ t : ℝ,(etaPlus t-etaCircle t)^2)≤1/1568000000 := ⟨etaPlus_approx_square_integrable,etaPlus_approx_l2_square_le_tight⟩
#print axioms solution
