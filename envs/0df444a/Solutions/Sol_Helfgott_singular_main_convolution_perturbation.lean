-- Prove2me | solution 1 for Helfgott.singular_main_convolution_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-05T02:43:50.951652+00:00
-- url     : https://prove2.me/submissions/7fd0d67d-d746-42ce-8473-8e5ae7a4fac2

import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Convolution
import Definitions.Def_Helfgott_SingularSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! Full actual/compact ternary main-term perturbation. All smoothing approximation and Euler upper/convergence proofs included. Written by Codex. -/

section
/-! Full direct actual main-convolution bound. Written by Codex. -/

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

open MeasureTheory Set

namespace Helfgott

lemma etaPlus_approx_square_pointwise (t : ℝ) :
    (etaPlus t-etaCircle t)^2 ≤ (1/1800 : ℝ)^2*gaussianApproxSquareFactor t := by
  have h := pow_le_pow_left₀ (abs_nonneg (etaPlus t-etaCircle t)) (etaPlus_approx_pointwise t) 2
  change |etaPlus t-etaCircle t|^2 ≤ ((1/1800 : ℝ)*gaussianApproxFactor t)^2 at h
  simpa only [sq_abs,mul_pow,gaussianApproxFactor_square] using h

lemma etaPlus_approx_integrable : Integrable (fun t => etaPlus t-etaCircle t) := by
  apply (gaussianApproxFactor_integrable.const_mul (1/1800 : ℝ)).mono'
    (etaPlus_measurable.sub etaCircle_continuous.measurable).aestronglyMeasurable
  exact ae_of_all _ (fun t => by
    simpa only [Real.norm_eq_abs,Pi.sub_apply,gaussianApproxFactor] using etaPlus_approx_pointwise t)

lemma etaPlus_approx_square_integrable : Integrable (fun t => (etaPlus t-etaCircle t)^2) := by
  apply (gaussianApproxSquareFactor_integrable.const_mul ((1/1800 : ℝ)^2)).mono'
    ((etaPlus_measurable.sub etaCircle_continuous.measurable).pow_const 2).aestronglyMeasurable
  exact ae_of_all _ (fun t => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact etaPlus_approx_square_pointwise t)

lemma etaPlus_approx_l1_le : (∫ t : ℝ, |etaPlus t-etaCircle t|) ≤ 1/1800 := by
  calc
    _ ≤ ∫ t : ℝ, (1/1800 : ℝ)*gaussianApproxFactor t :=
      integral_mono etaPlus_approx_integrable.abs
        (gaussianApproxFactor_integrable.const_mul (1/1800 : ℝ)) etaPlus_approx_pointwise
    _ = _ := by rw [integral_const_mul,gaussianApproxFactor_integral,mul_one]

lemma etaPlus_approx_l2_square_le : (∫ t : ℝ, (etaPlus t-etaCircle t)^2) ≤ 1/6250000 := by
  calc
    _ ≤ ∫ t : ℝ, (1/1800 : ℝ)^2*gaussianApproxSquareFactor t :=
      integral_mono etaPlus_approx_square_integrable
        (gaussianApproxSquareFactor_integrable.const_mul ((1/1800 : ℝ)^2))
        etaPlus_approx_square_pointwise
    _ = (1/1800 : ℝ)^2*(∫ t : ℝ, gaussianApproxSquareFactor t) := integral_const_mul _ _
    _ ≤ (1/1800 : ℝ)^2*(1/2) := by
      gcongr
      exact gaussianApproxSquareFactor_integral_le
    _ ≤ _ := by norm_num

theorem etaPlus_approximation :
    Integrable (fun t : ℝ => etaPlus t-etaCircle t) ∧
    Integrable (fun t : ℝ => (etaPlus t-etaCircle t)^2) ∧
    (∫ t : ℝ, |etaPlus t-etaCircle t|) ≤ 1/1800 ∧
    (∫ t : ℝ, (etaPlus t-etaCircle t)^2) ≤ 1/6250000 :=
  ⟨etaPlus_approx_integrable,etaPlus_approx_square_integrable,
    etaPlus_approx_l1_le,etaPlus_approx_l2_square_le⟩

end Helfgott

open MeasureTheory Set Filter
open scoped Interval

namespace Helfgott

lemma exp_neg_upper_quadratic (u : ℝ) (hu : 0 ≤ u) :
    Real.exp (-u) ≤ 1-u+u^2/2 := by
  let g : ℝ → ℝ := fun t => 1-t+t^2/2-Real.exp (-t)
  have hd (t : ℝ) : HasDerivAt g (-1+t+Real.exp (-t)) t := by
    dsimp [g]
    convert! (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).add
      (((hasDerivAt_id t).pow 2).div_const 2)).sub
      (((hasDerivAt_id t).neg).exp) using 1 <;> simp <;> ring
  have hm : Monotone g := monotone_of_hasDerivAt_nonneg hd (by
    intro t
    have ht := Real.add_one_le_exp (-t)
    change 0 ≤ -1+t+Real.exp (-t)
    linarith)
  have h := hm hu
  dsimp [g] at h
  norm_num at h
  linarith

lemma symmetric_smoothing_l2_upper :
    (∫ t in (-1 : ℝ)..1, ((1-t^2)^3*Real.exp (-(t^2)/2))^2) ≤ 641/1000 := by
  let P : ℝ → ℝ := fun t => (1-t^2)^6*(1-t^2+t^4/2)
  have hp (t : ℝ) : ((1-t^2)^3*Real.exp (-(t^2)/2))^2 ≤ P t := by
    have he := exp_neg_upper_quadratic (t^2) (sq_nonneg t)
    have hexp : Real.exp (-(t^2)/2)^2=Real.exp (-(t^2)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [mul_pow,← pow_mul,hexp]
    dsimp [P]
    convert! mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ (1-t^2)^6) using 1 <;>
      (first | rfl | ring | (ext x; ring))
  let Q : ℝ → ℝ := fun t => (1/1 : ℝ)*t^1/1 + (-7/1 : ℝ)*t^3/3 + (43/2 : ℝ)*t^5/5 + (-38/1 : ℝ)*t^7/7 + (85/2 : ℝ)*t^9/9 + (-31/1 : ℝ)*t^11/11 + (29/2 : ℝ)*t^13/13 + (-4/1 : ℝ)*t^15/15 + (1/2 : ℝ)*t^17/17
  have hd (t : ℝ) : HasDerivAt Q (P t) t := by
    dsimp [Q,P]
    convert! ((((((((((hasDerivAt_const t (0 : ℝ)).add ((((hasDerivAt_id t).pow 1).const_mul (1/1 : ℝ)).div_const 1)).add ((((hasDerivAt_id t).pow 3).const_mul (-7/1 : ℝ)).div_const 3)).add ((((hasDerivAt_id t).pow 5).const_mul (43/2 : ℝ)).div_const 5)).add ((((hasDerivAt_id t).pow 7).const_mul (-38/1 : ℝ)).div_const 7)).add ((((hasDerivAt_id t).pow 9).const_mul (85/2 : ℝ)).div_const 9)).add ((((hasDerivAt_id t).pow 11).const_mul (-31/1 : ℝ)).div_const 11)).add ((((hasDerivAt_id t).pow 13).const_mul (29/2 : ℝ)).div_const 13)).add ((((hasDerivAt_id t).pow 15).const_mul (-4/1 : ℝ)).div_const 15)).add ((((hasDerivAt_id t).pow 17).const_mul (1/2 : ℝ)).div_const 17)) using 1
    all_goals try funext x
    all_goals simp
    all_goals ring
  have hi : (∫ t in (-1 : ℝ)..1, P t)=490496/765765 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      ((by dsimp [P]; fun_prop : Continuous P).intervalIntegrable _ _)]
    norm_num [Q]
  have hm : (∫ t in (-1 : ℝ)..1, ((1-t^2)^3*Real.exp (-(t^2)/2))^2) ≤
      ∫ t in (-1 : ℝ)..1, P t := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact (by fun_prop : Continuous (fun t : ℝ =>
        ((1-t^2)^3*Real.exp (-(t^2)/2))^2)).intervalIntegrable _ _
    · exact (by dsimp [P]; fun_prop : Continuous P).intervalIntegrable _ _
    · exact fun t _ => hp t
  rw [hi] at hm
  exact hm.trans (by norm_num)

lemma etaCircle_square_integral_eq_symmetric :
    (∫ t : ℝ, (etaCircle t)^2) =
      ∫ t in (-1 : ℝ)..1, ((1-t^2)^3*Real.exp (-(t^2)/2))^2 := by
  have heq : (∫ t : ℝ, (etaCircle t)^2) =
      ∫ t in (-1 : ℝ)..1, ((1-t^2)^3 * Real.exp (-(t^2)/2))^2 := by
    calc
      (∫ t : ℝ, (etaCircle t)^2) =
          ∫ t : ℝ, (Set.Icc (0 : ℝ) 2).indicator
            (fun t => (t^3*(2-t)^3*Real.exp (-((t-1)^2)/2))^2) t := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun t => by
          by_cases ht : t ∈ Set.Icc (0 : ℝ) 2 <;> simp [etaCircle,ht])
      _ = ∫ t in (0 : ℝ)..2, (t^3*(2-t)^3*Real.exp (-((t-1)^2)/2))^2 := by
        rw [integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
          intervalIntegral.integral_of_le (by norm_num)]
      _ = ∫ t in (-1 : ℝ)..1,
          ((t+1)^3*(2-(t+1))^3*Real.exp (-(((t+1)-1)^2)/2))^2 := by
        simpa only [neg_add_cancel,one_add_one_eq_two] using
          (intervalIntegral.integral_comp_add_right
            (fun t : ℝ => (t^3*(2-t)^3*Real.exp (-((t-1)^2)/2))^2) 1
            (a := (-1 : ℝ)) (b := 1)).symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro t _
        simp only [add_sub_cancel_right]
        ring
  exact heq

lemma etaCircle_square_integral_upper : (∫ t : ℝ, (etaCircle t)^2) ≤ 641/1000 := by
  rw [etaCircle_square_integral_eq_symmetric]
  exact symmetric_smoothing_l2_upper

end Helfgott

open MeasureTheory Set

set_option backward.isDefEq.respectTransparency false

namespace Helfgott

lemma abs_mul_le_half_squares (x y : ℝ) : |x*y| ≤ (x^2+y^2)/2 := by
  apply abs_le.mpr
  constructor
  · nlinarith [sq_nonneg (x+y)]
  · nlinarith [sq_nonneg (x-y)]

lemma abs_mul_le_unequal_squares (x y : ℝ) : |x*y| ≤ x^2/4000+1000*y^2 := by
  apply abs_le.mpr
  constructor
  · nlinarith [sq_nonneg (x+2000*y)]
  · nlinarith [sq_nonneg (x-2000*y)]

lemma integrable_mul_of_square_integrable (f g : ℝ → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hf2 : Integrable (fun u => (f u)^2)) (hg2 : Integrable (fun u => (g u)^2)) :
    Integrable (fun u => f u*g u) := by
  apply (hf2.add hg2).mono' (hf.mul hg).aestronglyMeasurable
  exact ae_of_all _ (fun u => by
    simp only [Real.norm_eq_abs,Pi.add_apply,Pi.mul_apply]
    nlinarith [abs_mul_le_half_squares (f u) (g u),sq_nonneg (f u),sq_nonneg (g u)])

theorem convolution_difference_error_bound (f g : ℝ → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hg2 : Integrable (fun u => (g u)^2))
    (hd2 : Integrable (fun u => (f u-g u)^2))
    (hgb : (∫ u : ℝ, (g u)^2) ≤ 641/1000)
    (hdb : (∫ u : ℝ, (f u-g u)^2) ≤ 1/6250000)
    (ρ : ℝ) :
    Integrable (fun u => f u*f (ρ-u)) ∧
    |(∫ u : ℝ, f u*f (ρ-u))-(∫ u : ℝ, g u*g (ρ-u))| ≤ 32033/50000000 := by
  let d : ℝ → ℝ := fun u => f u-g u
  have hd : Measurable d := hf.sub hg
  have hd2' : Integrable (fun u => (d u)^2) := hd2
  have hdb' : (∫ u : ℝ, (d u)^2) ≤ 1/6250000 := hdb
  have hgm : Measurable (fun u => g (ρ-u)) := hg.comp (measurable_const.sub measurable_id)
  have hdm : Measurable (fun u => d (ρ-u)) := hd.comp (measurable_const.sub measurable_id)
  have hgsq := hg2.comp_sub_left ρ
  have hdsq := hd2'.comp_sub_left ρ
  have hiA := integrable_mul_of_square_integrable g (fun u => g (ρ-u)) hg hgm hg2 hgsq
  have hiB := integrable_mul_of_square_integrable d (fun u => g (ρ-u)) hd hgm hd2' hgsq
  have hiC := integrable_mul_of_square_integrable g (fun u => d (ρ-u)) hg hdm hg2 hdsq
  have hiD := integrable_mul_of_square_integrable d (fun u => d (ρ-u)) hd hdm hd2' hdsq
  have hBM : (∫ u : ℝ, |d u*g (ρ-u)|) ≤ 1281/4000000 := by
    calc
      _ ≤ ∫ u : ℝ, (g (ρ-u))^2/4000+1000*(d u)^2 := by
        apply integral_mono hiB.abs ((hgsq.div_const 4000).add (hd2'.const_mul 1000))
        intro u
        simpa only [mul_comm,Pi.add_apply] using abs_mul_le_unequal_squares (g (ρ-u)) (d u)
      _ = (∫ u : ℝ, (g u)^2)/4000+1000*(∫ u : ℝ, (d u)^2) := by
        rw [integral_add (hgsq.div_const 4000) (hd2'.const_mul 1000),integral_div,
          integral_const_mul,integral_sub_left_eq_self (fun u => (g u)^2) volume ρ]
      _ ≤ _ := by linarith
  have hCM : (∫ u : ℝ, |g u*d (ρ-u)|) ≤ 1281/4000000 := by
    calc
      _ ≤ ∫ u : ℝ, (g u)^2/4000+1000*(d (ρ-u))^2 :=
        integral_mono hiC.abs ((hg2.div_const 4000).add (hdsq.const_mul 1000))
          (fun u => abs_mul_le_unequal_squares (g u) (d (ρ-u)))
      _ = (∫ u : ℝ, (g u)^2)/4000+1000*(∫ u : ℝ, (d u)^2) := by
        rw [integral_add (hg2.div_const 4000) (hdsq.const_mul 1000),integral_div,
          integral_const_mul,integral_sub_left_eq_self (fun u => (d u)^2) volume ρ]
      _ ≤ _ := by linarith
  have hDM : (∫ u : ℝ, |d u*d (ρ-u)|) ≤ 1/6250000 := by
    calc
      _ ≤ ∫ u : ℝ, ((d u)^2+(d (ρ-u))^2)/2 :=
        integral_mono hiD.abs ((hd2'.add hdsq).div_const 2)
          (fun u => abs_mul_le_half_squares (d u) (d (ρ-u)))
      _ = (∫ u : ℝ, (d u)^2) := by
        rw [integral_div,integral_add hd2' hdsq,
          integral_sub_left_eq_self (fun u => (d u)^2) volume ρ]
        ring
      _ ≤ _ := hdb'
  have heq : (fun u => f u*f (ρ-u)) =
      (fun u => g u*g (ρ-u)+d u*g (ρ-u)+g u*d (ρ-u)+d u*d (ρ-u)) := by
    funext u
    dsimp only [d]
    ring
  have hiF : Integrable (fun u => f u*f (ρ-u)) := by
    rw [heq]
    exact ((hiA.add hiB).add hiC).add hiD
  refine ⟨hiF,?_⟩
  have hEA : (∫ u : ℝ, f u*f (ρ-u))-(∫ u : ℝ, g u*g (ρ-u)) =
      (∫ u : ℝ, d u*g (ρ-u))+(∫ u : ℝ, g u*d (ρ-u))+(∫ u : ℝ, d u*d (ρ-u)) := by
    have e1 := integral_add hiA hiB
    have e2 := integral_add (hiA.add hiB) hiC
    have e3 := integral_add ((hiA.add hiB).add hiC) hiD
    simp only [Pi.add_apply] at e1 e2 e3
    rw [heq,e3,e2,e1]
    ring
  rw [hEA]
  have hnB := norm_integral_le_integral_norm (μ := volume) (fun u => d u*g (ρ-u))
  have hnC := norm_integral_le_integral_norm (μ := volume) (fun u => g u*d (ρ-u))
  have hnD := norm_integral_le_integral_norm (μ := volume) (fun u => d u*d (ρ-u))
  simp only [Real.norm_eq_abs] at hnB hnC hnD
  have ht1 := abs_add_le (∫ u : ℝ, d u*g (ρ-u)) (∫ u : ℝ, g u*d (ρ-u))
  have ht2 := abs_add_le ((∫ u : ℝ, d u*g (ρ-u))+(∫ u : ℝ, g u*d (ρ-u)))
    (∫ u : ℝ, d u*d (ρ-u))
  linarith

theorem etaPlus_convolution_approximation (ρ : ℝ) :
    Integrable (fun u : ℝ => etaPlus u*etaPlus (ρ-u)) ∧
    |(∫ u : ℝ, etaPlus u*etaPlus (ρ-u))-
      (∫ u : ℝ, etaCircle u*etaCircle (ρ-u))| ≤ 32033/50000000 :=
  convolution_difference_error_bound etaPlus etaCircle etaPlus_measurable
    etaCircle_continuous.measurable etaCircle_square_integrable etaPlus_approx_square_integrable
    etaCircle_square_integral_upper etaPlus_approx_l2_square_le ρ

end Helfgott

/-!
A rigorous elementary lower bound for the L² mass of the compact symmetric
smoothing in Helfgott, arXiv:1312.7748v2, (4.3), used in §7.2. The variable
is translated by one: η_circle(t+1) = (1-t²)^3 exp(-t²/2) on [-1,1].
The lower bound 16/25 is derived here using a cubic lower Taylor polynomial
for exp(-u), then exact polynomial integration. Written by Codex.
-/

open MeasureTheory
open scoped Interval

namespace Helfgott

lemma exp_neg_lower_cubic (u : ℝ) (hu : 0 ≤ u) :
    1 - u + u ^ 2 / 2 - u ^ 3 / 6 ≤ Real.exp (-u) := by
  let g₂ : ℝ → ℝ := fun t => 1 - t + t ^ 2 / 2 - Real.exp (-t)
  have hg₂ (t : ℝ) : HasDerivAt g₂ (-1 + t + Real.exp (-t)) t := by
    dsimp [g₂]
    convert! (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).add
      (((hasDerivAt_id t).pow 2).div_const 2)).sub
      (((hasDerivAt_id t).neg).exp) using 1 <;> simp <;> ring
  have hm₂ : Monotone g₂ := monotone_of_hasDerivAt_nonneg hg₂ (by
    intro t
    have ht := Real.add_one_le_exp (-t)
    change 0 ≤ -1 + t + Real.exp (-t)
    linarith)
  have h₂ (t : ℝ) (ht : 0 ≤ t) : 0 ≤ g₂ t := by
    have h := hm₂ ht
    simpa [g₂] using h
  let g₃ : ℝ → ℝ := fun t => Real.exp (-t) - 1 + t - t ^ 2 / 2 + t ^ 3 / 6
  have hg₃ (t : ℝ) : HasDerivAt g₃ (g₂ t) t := by
    dsimp [g₃, g₂]
    convert! (((((((hasDerivAt_id t).neg).exp).sub (hasDerivAt_const t (1 : ℝ))).add
      (hasDerivAt_id t)).sub (((hasDerivAt_id t).pow 2).div_const 2)).add
      (((hasDerivAt_id t).pow 3).div_const 6)) using 1 <;> simp <;> ring
  have hm₃ : MonotoneOn g₃ (Set.Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (by dsimp [g₃]; fun_prop)
      (fun t _ => (hg₃ t).hasDerivWithinAt)
      (fun t ht => h₂ t (Set.mem_Ici.mp (interior_subset ht)))
  have h := hm₃ (by simp : (0 : ℝ) ∈ Set.Ici 0) hu hu
  dsimp [g₃] at h
  norm_num at h
  linarith

theorem symmetric_smoothing_l2_lower :
    (16 / 25 : ℝ) ≤ ∫ t in (-1 : ℝ)..1,
      ((1 - t ^ 2) ^ 3 * Real.exp (-(t ^ 2) / 2)) ^ 2 := by
  let P : ℝ → ℝ := fun t =>
    (1 - t ^ 2) ^ 6 * (1 - t ^ 2 + t ^ 4 / 2 - t ^ 6 / 6)
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
      P t ≤ ((1 - t ^ 2) ^ 3 * Real.exp (-(t ^ 2) / 2)) ^ 2 := by
    have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
    have he := exp_neg_lower_cubic (t ^ 2) ht2
    have hexp : Real.exp (-(t ^ 2) / 2) ^ 2 = Real.exp (-(t ^ 2)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [mul_pow, ← pow_mul, hexp]
    dsimp [P]
    convert! mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ (1 - t ^ 2) ^ 6) using 1 <;>
      (first | rfl | ring | (ext x; ring))
  let Q : ℝ → ℝ := fun t => (1 / 1 : ℝ) * t ^ 1 / 1 + (-7 / 1 : ℝ) * t ^ 3 / 3 + (43 / 2 : ℝ) * t ^ 5 / 5 + (-229 / 6 : ℝ) * t ^ 7 / 7 + (87 / 2 : ℝ) * t ^ 9 / 9 + (-67 / 2 : ℝ) * t ^ 11 / 11 + (107 / 6 : ℝ) * t ^ 13 / 13 + (-13 / 2 : ℝ) * t ^ 15 / 15 + (3 / 2 : ℝ) * t ^ 17 / 17 + (-1 / 6 : ℝ) * t ^ 19 / 19
  have hQ (t : ℝ) : HasDerivAt Q (P t) t := by
    dsimp [Q, P]
    convert! (((((((((((hasDerivAt_const t (0 : ℝ)).add ((((hasDerivAt_id t).pow 1).const_mul (1 / 1 : ℝ)).div_const 1)).add ((((hasDerivAt_id t).pow 3).const_mul (-7 / 1 : ℝ)).div_const 3)).add ((((hasDerivAt_id t).pow 5).const_mul (43 / 2 : ℝ)).div_const 5)).add ((((hasDerivAt_id t).pow 7).const_mul (-229 / 6 : ℝ)).div_const 7)).add ((((hasDerivAt_id t).pow 9).const_mul (87 / 2 : ℝ)).div_const 9)).add ((((hasDerivAt_id t).pow 11).const_mul (-67 / 2 : ℝ)).div_const 11)).add ((((hasDerivAt_id t).pow 13).const_mul (107 / 6 : ℝ)).div_const 13)).add ((((hasDerivAt_id t).pow 15).const_mul (-13 / 2 : ℝ)).div_const 15)).add ((((hasDerivAt_id t).pow 17).const_mul (3 / 2 : ℝ)).div_const 17)).add ((((hasDerivAt_id t).pow 19).const_mul (-1 / 6 : ℝ)).div_const 19)) using 1
    all_goals try funext x
    all_goals simp
    all_goals ring
  have hpint : (∫ t in (-1 : ℝ)..1, P t) = 3104768 / 4849845 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hQ t)
      ((by dsimp [P]; fun_prop : Continuous P).intervalIntegrable _ _)]
    norm_num [Q]
  have hmono : (∫ t in (-1 : ℝ)..1, P t) ≤
      ∫ t in (-1 : ℝ)..1, ((1 - t ^ 2) ^ 3 * Real.exp (-(t ^ 2) / 2)) ^ 2 := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact (by dsimp [P]; fun_prop : Continuous P).intervalIntegrable _ _
    · exact (by fun_prop : Continuous (fun t : ℝ =>
        ((1 - t ^ 2) ^ 3 * Real.exp (-(t ^ 2) / 2)) ^ 2)).intervalIntegrable _ _
    · exact hpoint
  rw [hpint] at hmono
  exact le_trans (by norm_num) hmono

end Helfgott

/-! An elementary upper bound for the derivative energy of the centered form
of Helfgott's symmetric smoothing (arXiv:1312.7748v2, (4.3), (4.5), (7.6)).
The paper's value is about 2.73753; the bound 17/5 derived here is sufficient
with the sharp polarization constant 1/2. Written by Codex. -/

open MeasureTheory
open scoped Interval

namespace Helfgott

lemma symmetric_smoothing_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => (1-s^2)^3 * Real.exp (-(s^2)/2))
      (-t * (1-t^2)^2 * (7-t^2) * Real.exp (-(t^2)/2)) t := by
  convert! (((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).pow 2)).pow 3).mul
    ((((hasDerivAt_id t).pow 2).neg.div_const 2).exp) using 1 <;> simp <;> ring

theorem symmetric_smoothing_derivative_l2_upper :
    (∫ t in (-1 : ℝ)..1,
      (-t * (1-t^2)^2 * (7-t^2) * Real.exp (-(t^2)/2))^2) ≤ (17/5 : ℝ) := by
  let P : ℝ → ℝ := fun t => t^2 * (1-t^2)^4 * (7-t^2)^2
  have hpoint (t : ℝ) :
      (-t * (1-t^2)^2 * (7-t^2) * Real.exp (-(t^2)/2))^2 ≤ P t := by
    have hexp : Real.exp (-(t^2)/2)^2 = Real.exp (-(t^2)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have he : Real.exp (-(t^2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sq_nonneg t]
    have h := mul_le_mul_of_nonneg_left he (show 0 ≤ P t by dsimp [P]; positivity)
    convert! h using 1 <;> dsimp [P] <;> simp only [mul_pow, pow_mul, neg_sq, hexp, mul_one] <;> ring
  let Q : ℝ → ℝ := fun t => (49 / 1 : ℝ) * t ^ 3 / 3 + (-210 / 1 : ℝ) * t ^ 5 / 5 + (351 / 1 : ℝ) * t ^ 7 / 7 + (-284 / 1 : ℝ) * t ^ 9 / 9 + (111 / 1 : ℝ) * t ^ 11 / 11 + (-18 / 1 : ℝ) * t ^ 13 / 13 + (1 / 1 : ℝ) * t ^ 15 / 15
  have hQ (t : ℝ) : HasDerivAt Q (P t) t := by
    dsimp [Q,P]
    convert! ((((((((hasDerivAt_const t (0 : ℝ)).add ((((hasDerivAt_id t).pow 3).const_mul (49 / 1 : ℝ)).div_const 3)).add ((((hasDerivAt_id t).pow 5).const_mul (-210 / 1 : ℝ)).div_const 5)).add ((((hasDerivAt_id t).pow 7).const_mul (351 / 1 : ℝ)).div_const 7)).add ((((hasDerivAt_id t).pow 9).const_mul (-284 / 1 : ℝ)).div_const 9)).add ((((hasDerivAt_id t).pow 11).const_mul (111 / 1 : ℝ)).div_const 11)).add ((((hasDerivAt_id t).pow 13).const_mul (-18 / 1 : ℝ)).div_const 13)).add ((((hasDerivAt_id t).pow 15).const_mul (1 / 1 : ℝ)).div_const 15)) using 1
    all_goals try funext x
    all_goals simp
    all_goals ring
  have hpint : (∫ t in (-1 : ℝ)..1, P t) = 152576 / 45045 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hQ t)
      ((by dsimp [P]; fun_prop : Continuous P).intervalIntegrable _ _)]
    norm_num [Q]
  have hmono : (∫ t in (-1 : ℝ)..1,
      (-t * (1-t^2)^2 * (7-t^2) * Real.exp (-(t^2)/2))^2) ≤
      ∫ t in (-1 : ℝ)..1, P t := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact (by fun_prop : Continuous (fun t : ℝ =>
        (-t * (1-t^2)^2 * (7-t^2) * Real.exp (-(t^2)/2))^2)).intervalIntegrable _ _
    · exact (by dsimp [P]; fun_prop : Continuous P).intervalIntegrable _ _
    · intro t _; exact hpoint t
  rw [hpint] at hmono
  exact le_trans hmono (by norm_num)

end Helfgott

open MeasureTheory Set Filter
open scoped Interval

namespace Helfgott

lemma integral_square_le_length_mul (g : ℝ → ℝ) (hg : Continuous g)
    (h : ℝ) (hh : 0 ≤ h) :
    (∫ t in (0 : ℝ)..h, g t)^2 ≤ h * (∫ t in (0 : ℝ)..h, (g t)^2) := by
  by_cases hz : h=0
  · subst h; simp
  have hp : 0 < h := lt_of_le_of_ne hh (Ne.symm hz)
  let I : ℝ := ∫ t in (0 : ℝ)..h, g t
  let J : ℝ := ∫ t in (0 : ℝ)..h, (g t)^2
  have hn : 0 ≤ ∫ t in (0 : ℝ)..h, (h*g t-I)^2 :=
    intervalIntegral.integral_nonneg hh (fun t _ => sq_nonneg _)
  have heq : (∫ t in (0 : ℝ)..h, (h*g t-I)^2) = h^2*J - (2*h*I)*I + I^2*h := by
    have he (t : ℝ) : (h*g t-I)^2 = h^2*(g t)^2 - (2*h*I)*g t + I^2 := by ring
    simp_rw [he]
    have hi1 : IntervalIntegrable (fun t => h^2*(g t)^2) volume 0 h :=
      (by fun_prop : Continuous (fun t => h^2*(g t)^2)).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun t => (2*h*I)*g t) volume 0 h :=
      (by fun_prop : Continuous (fun t => (2*h*I)*g t)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add (hi1.sub hi2) intervalIntegrable_const,
      intervalIntegral.integral_sub hi1 hi2,
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    dsimp [I,J]
    simp
    ring
  rw [heq] at hn
  have hfac : h^2*J - (2*h*I)*I + I^2*h = h * (h*J-I^2) := by ring
  rw [hfac] at hn
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hn hp)

theorem translation_l2_bound (f g : ℝ → ℝ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g)
    (hg2 : Integrable (fun t => (g t)^2))
    (hder : ∀ t, HasDerivAt f (g t) t) (h : ℝ) (hh : 0 ≤ h) :
    (∫ t : ℝ, (f (t+h)-f t)^2) ≤ h^2 * (∫ t : ℝ, (g t)^2) := by
  have hpoint (t : ℝ) : (f (t+h)-f t)^2 ≤ h * (∫ r in (0 : ℝ)..h, (g (t+r))^2) := by
    have hcon : Continuous (fun r : ℝ => g (t+r)) := by fun_prop
    have hFTC : (∫ r in (0 : ℝ)..h, g (t+r)) = f (t+h)-f t := by
      have hd (r : ℝ) : HasDerivAt (fun r => f (t+r)) (g (t+r)) r := by
        convert! (hder (t+r)).comp r ((hasDerivAt_id r).const_add t) using 1 <;> simp [Function.comp_def]
      simpa only [add_zero] using intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := (0 : ℝ)) (b := h) (fun r _ => hd r) (hcon.intervalIntegrable _ _)
    rw [← hFTC]
    exact integral_square_le_length_mul _ hcon h hh
  have hpair : Integrable (fun z : ℝ × ℝ => (g (z.2+z.1))^2)
      ((volume.restrict (Set.Ioc (0 : ℝ) h)).prod volume) := by
    apply (integrable_prod_iff (by fun_prop : Continuous (fun z : ℝ × ℝ =>
      (g (z.2+z.1))^2)).aestronglyMeasurable).mpr
    constructor
    · exact Eventually.of_forall (fun r => hg2.comp_add_right r)
    · have heq : (fun r : ℝ => ∫ t : ℝ, ‖(g (t+r))^2‖) =
          fun _ => ∫ t : ℝ, (g t)^2 := by
        funext r
        simp_rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact integral_add_right_eq_self (fun t => (g t)^2) r
      rw [heq]
      exact integrable_const _
  have hdiffc : HasCompactSupport (fun t : ℝ => f (t+h)-f t) := by
    convert! (hfc.comp_isClosedEmbedding (Homeomorph.addRight h).isClosedEmbedding).sub hfc using 1
  have hdiff2 : Integrable (fun t : ℝ => (f (t+h)-f t)^2) := by
    apply (by fun_prop : Continuous (fun t : ℝ => (f (t+h)-f t)^2)).integrable_of_hasCompactSupport
    convert! hdiffc.mul_left (f := fun t => f (t+h)-f t) using 1
    funext t
    simp only [pow_two,Pi.mul_apply]
  have hrhs : Integrable (fun t : ℝ => h * (∫ r in Set.Ioc (0 : ℝ) h, (g (t+r))^2)) :=
    hpair.integral_prod_right.const_mul h
  have hbound : (∫ t : ℝ, (f (t+h)-f t)^2) ≤
      ∫ t : ℝ, h * (∫ r in Set.Ioc (0 : ℝ) h, (g (t+r))^2) := by
    apply integral_mono hdiff2 hrhs
    intro t
    simpa only [intervalIntegral.integral_of_le hh] using hpoint t
  have htotal : (∫ t : ℝ, h * (∫ r in Set.Ioc (0 : ℝ) h, (g (t+r))^2)) =
      h^2 * (∫ t : ℝ, (g t)^2) := by
    rw [integral_const_mul,← integral_integral_swap hpair]
    simp_rw [integral_add_right_eq_self (fun t => (g t)^2)]
    rw [setIntegral_const]
    simp [measureReal_def,Real.volume_Ioc,ENNReal.toReal_ofReal hh]
    ring
  exact hbound.trans_eq htotal

theorem translation_l2_bound_all (f g : ℝ → ℝ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g)
    (hg2 : Integrable (fun t => (g t)^2))
    (hder : ∀ t, HasDerivAt f (g t) t) (h : ℝ) :
    (∫ t : ℝ, (f (t+h)-f t)^2) ≤ h^2 * (∫ t : ℝ, (g t)^2) := by
  by_cases hh : 0 ≤ h
  · exact translation_l2_bound f g hf hfc hg hg2 hder h hh
  · have hh' : 0 ≤ -h := by linarith
    have hb := translation_l2_bound f g hf hfc hg hg2 hder (-h) hh'
    have hi : (∫ t : ℝ, (f (t+h)-f t)^2) = (∫ t : ℝ, (f (t+(-h))-f t)^2) := by
      calc
        (∫ t : ℝ, (f (t+h)-f t)^2) =
            ∫ t : ℝ, (f ((t+h)+(-h))-f (t+h))^2 := by
          apply integral_congr_ae
          exact Eventually.of_forall (fun t => by simp only [add_neg_cancel_right]; ring)
        _ = _ := integral_add_right_eq_self (fun t => (f (t+(-h))-f t)^2) h
    rw [← hi] at hb
    simpa only [neg_sq] using hb

theorem translated_product_lower (f g : ℝ → ℝ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g)
    (hg2 : Integrable (fun t => (g t)^2))
    (hder : ∀ t, HasDerivAt f (g t) t) (h : ℝ) :
    (∫ t : ℝ, (f t)^2) - (h^2/2) * (∫ t : ℝ, (g t)^2) ≤
      ∫ t : ℝ, f t * f (t+h) := by
  have hb := translation_l2_bound_all f g hf hfc hg hg2 hder h
  have hsq : Integrable (fun t : ℝ => (f t)^2) := by
    apply (hf.pow 2).integrable_of_hasCompactSupport
    convert! hfc.mul_left (f := f) using 1
    funext t; simp only [pow_two,Pi.mul_apply]
  have hshift : Integrable (fun t : ℝ => (f (t+h))^2) := hsq.comp_add_right h
  have hp : Integrable (fun t : ℝ => f t * f (t+h)) := by
    apply (by fun_prop : Continuous (fun t : ℝ => f t * f (t+h))).integrable_of_hasCompactSupport
    convert! hfc.mul_right (f' := fun t => f (t+h)) using 1
  have hi : (∫ t : ℝ, (f (t+h)-f t)^2) =
      2*(∫ t : ℝ, (f t)^2) - 2*(∫ t : ℝ, f t * f (t+h)) := by
    calc
      (∫ t : ℝ, (f (t+h)-f t)^2) =
          ∫ t : ℝ, (f (t+h))^2 + (f t)^2 - 2*(f t * f (t+h)) := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun t => by ring)
      _ = _ := by
        rw [integral_sub (f := fun t => (f (t+h))^2 + (f t)^2)
          (g := fun t => 2*(f t * f (t+h))) (hshift.add hsq) (hp.const_mul 2),
          integral_add (f := fun t => (f (t+h))^2) (g := fun t => (f t)^2) hshift hsq,
          integral_const_mul,integral_add_right_eq_self (fun t => (f t)^2)]
        ring
  rw [hi] at hb
  linarith

end Helfgott

open MeasureTheory Set Filter
open scoped Interval

namespace Helfgott

private noncomputable def circleDeriv (t : ℝ) : ℝ :=
  ((Set.Icc (0 : ℝ) 2).indicator (fun t =>
    -(t-1) * (1-(t-1)^2)^2 * (7-(t-1)^2) * Real.exp (-((t-1)^2)/2)) t)

lemma etaCircle_mass_lower : (16/25 : ℝ) ≤ ∫ t : ℝ, (etaCircle t)^2 := by
  have heq : (∫ t : ℝ, (etaCircle t)^2) =
      ∫ t in (-1 : ℝ)..1, ((1-t^2)^3 * Real.exp (-(t^2)/2))^2 := by
    calc
      (∫ t : ℝ, (etaCircle t)^2) =
          ∫ t : ℝ, (Set.Icc (0 : ℝ) 2).indicator
            (fun t => (t^3*(2-t)^3*Real.exp (-((t-1)^2)/2))^2) t := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun t => by
          by_cases ht : t ∈ Set.Icc (0 : ℝ) 2 <;> simp [etaCircle,ht])
      _ = ∫ t in (0 : ℝ)..2, (t^3*(2-t)^3*Real.exp (-((t-1)^2)/2))^2 := by
        rw [integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
          intervalIntegral.integral_of_le (by norm_num)]
      _ = ∫ t in (-1 : ℝ)..1,
          ((t+1)^3*(2-(t+1))^3*Real.exp (-(((t+1)-1)^2)/2))^2 := by
        simpa only [neg_add_cancel,one_add_one_eq_two] using
          (intervalIntegral.integral_comp_add_right
            (fun t : ℝ => (t^3*(2-t)^3*Real.exp (-((t-1)^2)/2))^2) 1
            (a := (-1 : ℝ)) (b := 1)).symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro t _
        simp only [add_sub_cancel_right]
        ring
  rw [heq]
  exact symmetric_smoothing_l2_lower

private lemma circleDeriv_energy_upper : (∫ t : ℝ, (circleDeriv t)^2) ≤ (17/5 : ℝ) := by
  have heq : (∫ t : ℝ, (circleDeriv t)^2) =
      ∫ t in (-1 : ℝ)..1,
        (-t*(1-t^2)^2*(7-t^2)*Real.exp (-(t^2)/2))^2 := by
    calc
      (∫ t : ℝ, (circleDeriv t)^2) =
          ∫ t : ℝ, (Set.Icc (0 : ℝ) 2).indicator
            (fun t => (-(t-1)*(1-(t-1)^2)^2*(7-(t-1)^2)*Real.exp (-((t-1)^2)/2))^2) t := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun t => by
          by_cases ht : t ∈ Set.Icc (0 : ℝ) 2 <;> simp [circleDeriv,ht])
      _ = ∫ t in (0 : ℝ)..2,
          (-(t-1)*(1-(t-1)^2)^2*(7-(t-1)^2)*Real.exp (-((t-1)^2)/2))^2 := by
        rw [integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
          intervalIntegral.integral_of_le (by norm_num)]
      _ = _ := by
        simpa only [neg_add_cancel,one_add_one_eq_two,add_sub_cancel_right] using
          (intervalIntegral.integral_comp_add_right
            (fun t : ℝ => (-(t-1)*(1-(t-1)^2)^2*(7-(t-1)^2)*Real.exp (-((t-1)^2)/2))^2) 1
            (a := (-1 : ℝ)) (b := 1)).symm
  rw [heq]
  exact symmetric_smoothing_derivative_l2_upper

theorem etaCircle_convolution_lower (ρ : ℝ) :
    (16/25 : ℝ) - (17/10 : ℝ)*(ρ-2)^2 ≤
      ∫ t : ℝ, etaCircle t * etaCircle (ρ-t) := by
  have hg : Continuous circleDeriv := etaCircle_deriv_continuous
  have hg2 : Integrable (fun t => (circleDeriv t)^2) := etaCircle_deriv_square_integrable
  have hder (t : ℝ) : HasDerivAt etaCircle (circleDeriv t) t := etaCircle_hasDerivAt t
  have hb := translated_product_lower etaCircle circleDeriv etaCircle_continuous
    etaCircle_hasCompactSupport hg hg2 hder (2-ρ)
  have heq : (∫ t : ℝ, etaCircle t * etaCircle (t+(2-ρ))) =
      ∫ t : ℝ, etaCircle t * etaCircle (ρ-t) := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun t => by
      change etaCircle t * etaCircle (t+(2-ρ)) = etaCircle t * etaCircle (ρ-t)
      rw [← etaCircle_symmetric (ρ-t)]
      congr 2
      ring)
  rw [heq] at hb
  have henergy := circleDeriv_energy_upper
  have hmass := etaCircle_mass_lower
  have hcoef : 0 ≤ (2-ρ)^2/2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left henergy hcoef
  have hs : (2-ρ)^2 = (ρ-2)^2 := by ring
  rw [hs] at hb hmul
  linarith

end Helfgott

open MeasureTheory Set
open scoped Interval

namespace Helfgott

lemma etaTwo_nonneg (t : ℝ) : 0 ≤ etaTwo t := by
  unfold etaTwo
  split_ifs <;> positivity

lemma etaTwo_le (t : ℝ) : etaTwo t ≤ 4 * Real.log 2 := by
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  unfold etaTwo
  split_ifs
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact max_le (sub_le_self _ (abs_nonneg _)) hlog
  · positivity

lemma etaTwo_eq_zero_of_not_mem (t : ℝ) (ht : t ∉ Set.Icc (1/4 : ℝ) 1) :
    etaTwo t = 0 := by
  by_cases hpos : 0 < t
  · unfold etaTwo
    rw [if_pos hpos]
    have htwopos : 0 < 2*t := by positivity
    have hm : Real.log 2 - |Real.log (2*t)| ≤ 0 := by
      rcases (not_and_or.mp ht) with hlo | hhi
      · have hlt : 2*t ≤ (1/2 : ℝ) := by push_neg at hlo; linarith
        have hlog := Real.log_le_log htwopos hlt
        have hhalf : Real.log (1/2 : ℝ) = -Real.log 2 := by
          rw [one_div, Real.log_inv]
        rw [hhalf] at hlog
        linarith [neg_le_abs (Real.log (2*t))]
      · have hlt : (2 : ℝ) ≤ 2*t := by push_neg at hhi; linarith
        have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hlt
        linarith [le_abs_self (Real.log (2*t))]
    rw [max_eq_right hm, mul_zero]
  · simp [etaTwo,hpos]

lemma etaTwo_eq_lower (t : ℝ) (ht : t ∈ Set.Icc (1/4 : ℝ) (1/2)) :
    etaTwo t = 4 * Real.log (4*t) := by
  have hpos : 0 < t := by linarith [ht.1]
  have hprod : 0 < 2*t := by positivity
  have hlogneg : Real.log (2*t) ≤ 0 := Real.log_nonpos (le_of_lt hprod) (by linarith [ht.2])
  have hsum : Real.log 2 + Real.log (2*t) = Real.log (4*t) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hprod)]
    congr 1; ring
  have hn : 0 ≤ Real.log (4*t) := Real.log_nonneg (by linarith [ht.1])
  unfold etaTwo
  rw [if_pos hpos, abs_of_nonpos hlogneg, sub_neg_eq_add, hsum, max_eq_left hn]

lemma etaTwo_eq_upper (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1) :
    etaTwo t = -4 * Real.log t := by
  have hpos : 0 < t := by linarith [ht.1]
  have hlogpos : 0 ≤ Real.log (2*t) := Real.log_nonneg (by linarith [ht.1])
  have hlogneg : Real.log t ≤ 0 := Real.log_nonpos (le_of_lt hpos) ht.2
  have hlog : Real.log (2*t) = Real.log 2 + Real.log t :=
    Real.log_mul (by norm_num) (ne_of_gt hpos)
  unfold etaTwo
  rw [if_pos hpos, abs_of_nonneg hlogpos, hlog]
  have hm : Real.log 2 - (Real.log 2 + Real.log t) = -Real.log t := by ring
  rw [hm, max_eq_left (neg_nonneg.mpr hlogneg)]
  ring

lemma etaTwo_continuousOn_pos : ContinuousOn etaTwo (Set.Ioi (0 : ℝ)) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  have hg : ContinuousAt (fun s : ℝ => 4 * max (Real.log 2 - |Real.log (2*s)|) 0) t := by
    have hpos : 0 < t := ht
    have hn : 2*t ≠ 0 := by positivity
    fun_prop
  apply hg.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with x hx
  simp only [etaTwo, if_pos (show 0 < x from hx)]

theorem etaTwo_mass_interval : (∫ t in (1/4 : ℝ)..1, etaTwo t) = 1 := by
  have hint (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : IntervalIntegrable etaTwo volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply etaTwo_continuousOn_pos.mono
    intro t ht
    exact lt_of_lt_of_le (lt_min ha hb) ht.1
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hint (1/4) (1/2) (by norm_num) (by norm_num))
    (hint (1/2) 1 (by norm_num) (by norm_num))]
  have hlo : (∫ t in (1/4 : ℝ)..(1/2), etaTwo t) =
      ∫ t in (1/4 : ℝ)..(1/2), 4 * (Real.log 4 + Real.log t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hmem : t ∈ Set.Icc (1/4 : ℝ) (1/2) := by
      have h := Set.uIcc_of_le (by norm_num : (1/4 : ℝ) ≤ 1/2)
      rw [h] at ht
      exact ht
    rw [etaTwo_eq_lower t hmem, Real.log_mul (by norm_num) (by linarith [hmem.1] : t ≠ 0)]
  have hhi : (∫ t in (1/2 : ℝ)..1, etaTwo t) = ∫ t in (1/2 : ℝ)..1, -4 * Real.log t := by
    apply intervalIntegral.integral_congr
    intro t ht
    apply etaTwo_eq_upper
    rw [Set.uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 1)] at ht
    exact ht
  rw [hlo,hhi,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (intervalIntegrable_const) (intervalIntegral.intervalIntegrable_log'),
    intervalIntegral.integral_const,integral_log,integral_log]
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  have hhalf : Real.log (1/2 : ℝ) = -Real.log 2 := by rw [one_div,Real.log_inv]
  have hquarter : Real.log (1/4 : ℝ) = -(2 * Real.log 2) := by rw [one_div,Real.log_inv,h4]
  rw [h4,hhalf,hquarter,Real.log_one]
  norm_num
  ring

lemma etaTwo_continuous : Continuous etaTwo := by
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : 0 < t
  · exact (etaTwo_continuousOn_pos t ht).continuousAt (Ioi_mem_nhds ht)
  · have hlo : t < (1/4 : ℝ) := by linarith
    apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hlo] with x hx
    apply etaTwo_eq_zero_of_not_mem
    intro h; exact (not_lt_of_ge h.1) hx

lemma etaTwo_hasCompactSupport : HasCompactSupport etaTwo := by
  apply HasCompactSupport.intro (K := Set.Icc (1/4 : ℝ) 1) isCompact_Icc
  exact etaTwo_eq_zero_of_not_mem

lemma etaTwo_integrable : Integrable etaTwo :=
  etaTwo_continuous.integrable_of_hasCompactSupport etaTwo_hasCompactSupport

theorem etaTwo_mass : (∫ t : ℝ, etaTwo t) = 1 := by
  have hind : (Set.Icc (1/4 : ℝ) 1).indicator etaTwo = etaTwo := by
    funext t
    by_cases ht : t ∈ Set.Icc (1/4 : ℝ) 1
    · exact Set.indicator_of_mem ht etaTwo
    · rw [Set.indicator_of_notMem ht,etaTwo_eq_zero_of_not_mem t ht]
  calc
    (∫ t : ℝ, etaTwo t) = ∫ t : ℝ, (Set.Icc (1/4 : ℝ) 1).indicator etaTwo t := by rw [hind]
    _ = ∫ t in Set.Icc (1/4 : ℝ) 1, etaTwo t := integral_indicator measurableSet_Icc
    _ = ∫ t in (1/4 : ℝ)..1, etaTwo t := by
      rw [intervalIntegral.integral_of_le (by norm_num),integral_Icc_eq_integral_Ioc]
    _ = 1 := etaTwo_mass_interval

end Helfgott

open MeasureTheory Set
open scoped Interval

namespace Helfgott

lemma etaTwo_scaled_zero (T w : ℝ) (hT : 0 < T) (hw : w ∉ Icc T (4*T)) :
    etaTwo (T/w) = 0 := by
  by_cases hwp : 0 < w
  · apply etaTwo_eq_zero_of_not_mem
    intro h
    apply hw
    constructor
    · simpa using (div_le_iff₀ hwp).mp h.2
    · have hh := (le_div_iff₀ hwp).mp h.1
      nlinarith
  · have hh : T/w ≤ 0 := div_nonpos_of_nonneg_of_nonpos hT.le (le_of_not_gt hwp)
    simp [etaTwo, not_lt_of_ge hh]

lemma etaTwo_scaled_weight_continuous (T : ℝ) (hT : 0 < T) :
    Continuous (fun w : ℝ => etaTwo (T/w)/w) := by
  apply continuous_iff_continuousAt.mpr
  intro w
  by_cases hw : w = 0
  · subst w
    apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hT] with x hx
    change x < T at hx
    rw [etaTwo_scaled_zero T x hT (by intro hm; linarith [hm.1]), zero_div]
  · have hc : ContinuousAt (fun x : ℝ => T/x) w := by fun_prop
    exact (etaTwo_continuous.continuousAt.comp hc).div continuousAt_id hw

lemma etaTwo_scaled_weight_integrable (T : ℝ) (hT : 0 < T) :
    Integrable (fun w : ℝ => etaTwo (T/w)/w) := by
  apply (etaTwo_scaled_weight_continuous T hT).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (K := Icc T (4*T)) isCompact_Icc
  intro w hw
  rw [etaTwo_scaled_zero T w hT hw,zero_div]

lemma etaTwo_scaled_lower (T w : ℝ) (hT : 0 < T) (hw : w ∈ Icc T (2*T)) :
    etaTwo (T/w) = 4 * (Real.log w - Real.log T) := by
  have hwp : 0 < w := lt_of_lt_of_le hT hw.1
  have hm : T/w ∈ Icc (1/2 : ℝ) 1 := by
    constructor
    · apply (le_div_iff₀ hwp).mpr; linarith [hw.2]
    · apply (div_le_iff₀ hwp).mpr; simpa using hw.1
  rw [etaTwo_eq_upper _ hm, Real.log_div hT.ne' hwp.ne']
  ring

lemma etaTwo_scaled_upper (T w : ℝ) (hT : 0 < T) (hw : w ∈ Icc (2*T) (4*T)) :
    etaTwo (T/w) = 4 * (Real.log (4*T) - Real.log w) := by
  have hwp : 0 < w := by linarith [hw.1]
  have hm : T/w ∈ Icc (1/4 : ℝ) (1/2) := by
    constructor
    · apply (le_div_iff₀ hwp).mpr; linarith [hw.2]
    · apply (div_le_iff₀ hwp).mpr; linarith [hw.1]
  rw [etaTwo_eq_lower _ hm]
  rw [show 4*(T/w) = (4*T)/w by ring,
    Real.log_div (by positivity : 4*T ≠ 0) hwp.ne']

theorem etaTwo_scaled_log_mass (T : ℝ) (hT : 0 < T) :
    (∫ w in Ioi (0 : ℝ), etaTwo (T/w)/w) = 4 * (Real.log 2)^2 := by
  have hf := etaTwo_scaled_weight_continuous T hT
  have hi (a b : ℝ) : IntervalIntegrable (fun w => etaTwo (T/w)/w) volume a b :=
    hf.intervalIntegrable _ _
  have hrestrict : (∫ w in Ioi (0 : ℝ), etaTwo (T/w)/w) =
      ∫ w in T..4*T, etaTwo (T/w)/w := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (show Icc T (4*T) ⊆ Ioi (0 : ℝ) by intro w hw; exact lt_of_lt_of_le hT hw.1)
      (show ∀ w ∈ Ioi (0 : ℝ) \ Icc T (4*T), etaTwo (T/w)/w = 0 by
        intro w hw; rw [etaTwo_scaled_zero T w hT hw.2,zero_div])]
    rw [intervalIntegral.integral_of_le (by linarith),integral_Icc_eq_integral_Ioc]
  rw [hrestrict, ← intervalIntegral.integral_add_adjacent_intervals (hi T (2*T)) (hi (2*T) (4*T))]
  have hlo : (∫ w in T..2*T, etaTwo (T/w)/w) =
      2*(Real.log (2*T)-Real.log T)^2 := by
    have heq : (∫ w in T..2*T, etaTwo (T/w)/w) =
        ∫ w in T..2*T, 4*(Real.log w-Real.log T)/w := by
      apply intervalIntegral.integral_congr
      intro w hw
      rw [Set.uIcc_of_le (by linarith : T ≤ 2*T)] at hw
      dsimp only
      rw [etaTwo_scaled_lower T w hT hw]
    rw [heq]
    have hint : IntervalIntegrable (fun w : ℝ => 4*(Real.log w-Real.log T)/w)
        volume T (2*T) := by
      apply ContinuousOn.intervalIntegrable
      intro w hw
      have hwp : 0 < w := by
        rw [Set.uIcc_of_le (by linarith : T ≤ 2*T)] at hw
        linarith [hw.1]
      apply ContinuousAt.continuousWithinAt
      have hwn : w ≠ 0 := hwp.ne'
      fun_prop
    have hd (w : ℝ) (hw : w ∈ uIcc T (2*T)) :
        HasDerivAt (fun w : ℝ => 2*(Real.log w-Real.log T)^2)
          (4*(Real.log w-Real.log T)/w) w := by
      rw [Set.uIcc_of_le (by linarith : T ≤ 2*T)] at hw
      have hwp : 0 < w := by linarith [hw.1]
      convert! (((Real.hasDerivAt_log hwp.ne').sub_const (Real.log T)).pow 2).const_mul 2 using 1 <;> simp <;> ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
    simp
  have hhi : (∫ w in 2*T..4*T, etaTwo (T/w)/w) =
      2*(Real.log (4*T)-Real.log (2*T))^2 := by
    have heq : (∫ w in 2*T..4*T, etaTwo (T/w)/w) =
        ∫ w in 2*T..4*T, 4*(Real.log (4*T)-Real.log w)/w := by
      apply intervalIntegral.integral_congr
      intro w hw
      rw [Set.uIcc_of_le (by linarith : 2*T ≤ 4*T)] at hw
      dsimp only
      rw [etaTwo_scaled_upper T w hT hw]
    rw [heq]
    have hint : IntervalIntegrable (fun w : ℝ => 4*(Real.log (4*T)-Real.log w)/w)
        volume (2*T) (4*T) := by
      apply ContinuousOn.intervalIntegrable
      intro w hw
      have hwp : 0 < w := by
        rw [Set.uIcc_of_le (by linarith : 2*T ≤ 4*T)] at hw
        linarith [hw.1]
      apply ContinuousAt.continuousWithinAt
      have hwn : w ≠ 0 := hwp.ne'
      fun_prop
    have hd (w : ℝ) (hw : w ∈ uIcc (2*T) (4*T)) :
        HasDerivAt (fun w : ℝ => -2*(Real.log (4*T)-Real.log w)^2)
          (4*(Real.log (4*T)-Real.log w)/w) w := by
      rw [Set.uIcc_of_le (by linarith : 2*T ≤ 4*T)] at hw
      have hwp : 0 < w := by linarith [hw.1]
      convert! (((Real.hasDerivAt_log hwp.ne').const_sub (Real.log (4*T))).pow 2).const_mul (-2) using 1 <;> simp <;> ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
    simp
  rw [hlo,hhi,Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hT.ne',
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hT.ne']
  have h4 : Real.log (4 : ℝ) = 2*Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  rw [h4]
  ring

lemma phi_nonneg (t : ℝ) : 0 ≤ phi t := by unfold phi; positivity

lemma phi_le (t : ℝ) : phi t ≤ 2 / Real.exp 1 := by
  have h := Real.mul_exp_neg_le_exp_neg_one (t^2/2)
  have he : Real.exp (-1 : ℝ) = (Real.exp 1)⁻¹ := Real.exp_neg 1
  rw [he] at h
  unfold phi
  have heq : -(t^2/2) = -(t^2)/2 := by ring
  rw [heq] at h
  calc
    t^2*Real.exp (-(t^2)/2) = 2*((t^2/2)*Real.exp (-(t^2)/2)) := by ring
    _ ≤ 2*(Real.exp 1)⁻¹ := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 2/Real.exp 1 := by ring

lemma mellin_etaTwo_phi_integrable (T : ℝ) (hT : 0 < T) :
    Integrable (fun w : ℝ => etaTwo (T/w)*phi w/w) := by
  have hphi : Continuous phi := by unfold phi; fun_prop
  have hc : Continuous (fun w : ℝ => (etaTwo (T/w)/w)*phi w) :=
    (etaTwo_scaled_weight_continuous T hT).mul hphi
  have hs : HasCompactSupport (fun w : ℝ => (etaTwo (T/w)/w)*phi w) := by
    apply HasCompactSupport.intro (K := Icc T (4*T)) isCompact_Icc
    intro w hw
    rw [etaTwo_scaled_zero T w hT hw,zero_div,zero_mul]
  have hh : Integrable (fun w : ℝ => (etaTwo (T/w)/w)*phi w) := hc.integrable_of_hasCompactSupport hs
  have heq : (fun w : ℝ => etaTwo (T/w)*phi w/w) = (fun w : ℝ => (etaTwo (T/w)/w)*phi w) := by
    funext w; ring
  rw [heq]
  exact hh

lemma mellin_etaTwo_phi_nonneg (T : ℝ) : 0 ≤ mellinConv etaTwo phi T := by
  unfold mellinConv
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  exact div_nonneg (mul_nonneg (etaTwo_nonneg _) (phi_nonneg _)) (le_of_lt hw)

lemma mellin_etaTwo_phi_le (T : ℝ) :
    mellinConv etaTwo phi T ≤ 8*(Real.log 2)^2/Real.exp 1 := by
  by_cases hT : 0 < T
  · have hi := (mellin_etaTwo_phi_integrable T hT).restrict (s := Ioi (0 : ℝ))
    have hg := ((etaTwo_scaled_weight_integrable T hT).const_mul (2/Real.exp 1)).restrict
      (s := Ioi (0 : ℝ))
    have hbound : (∫ w in Ioi (0 : ℝ), etaTwo (T/w)*phi w/w) ≤
        ∫ w in Ioi (0 : ℝ), (2/Real.exp 1)*(etaTwo (T/w)/w) := by
      apply integral_mono_ae hi hg
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      have he := mul_le_mul_of_nonneg_left (phi_le w) (etaTwo_nonneg (T/w))
      have hh := div_le_div_of_nonneg_right he (le_of_lt hw)
      convert! hh using 1 <;> ring
    unfold mellinConv
    refine hbound.trans_eq ?_
    rw [integral_const_mul,etaTwo_scaled_log_mass T hT]
    ring
  · have hz : mellinConv etaTwo phi T = 0 := by
      unfold mellinConv
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      have hh : T/w ≤ 0 := div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hT) (le_of_lt hw)
      simp [etaTwo,not_lt_of_ge hh]
    rw [hz]
    positivity

lemma mellin_etaTwo_phi_le_rational (T : ℝ) :
    mellinConv etaTwo phi T ≤ (707/500 : ℝ) := by
  apply (mellin_etaTwo_phi_le T).trans
  apply (div_le_iff₀ (Real.exp_pos 1)).mpr
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hs : (Real.log 2)^2 ≤ (0.6931471808 : ℝ)^2 :=
    pow_le_pow_left₀ hlog Real.log_two_lt_d9.le 2
  nlinarith only [hs, Real.exp_one_gt_d9]

theorem etaStar_abs_le (t : ℝ) : |etaStar t| ≤ (707/500 : ℝ) := by
  unfold etaStar
  rw [abs_of_nonneg (mellin_etaTwo_phi_nonneg (49*t))]
  exact mellin_etaTwo_phi_le_rational (49*t)

end Helfgott

open MeasureTheory Set Filter

namespace Helfgott

lemma mellin_inner_integrable (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi (0 : ℝ)))
    (w c : ℝ) (hw : 0 < w) :
    IntegrableOn (fun t : ℝ => f (t/w)*c/w) (Ioi (0 : ℝ)) := by
  have hh : IntegrableOn (fun t : ℝ => f (t*w⁻¹)) (Ioi (0 : ℝ)) := by
    apply (integrableOn_Ioi_comp_mul_right_iff f 0 (inv_pos.mpr hw)).mpr
    simpa using hf
  simpa only [IntegrableOn,div_eq_mul_inv,mul_assoc] using (hh.mul_const c).mul_const w⁻¹

lemma mellin_inner_integral (f : ℝ → ℝ) (w c : ℝ) (hw : 0 < w) :
    (∫ t in Ioi (0 : ℝ), f (t/w)*c/w) = c*(∫ t in Ioi (0 : ℝ), f t) := by
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const,integral_mul_const,
    integral_comp_mul_right_Ioi f 0 (inv_pos.mpr hw)]
  simp only [zero_mul,inv_inv,smul_eq_mul]
  field_simp

theorem mellin_integrable_mass (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfi : IntegrableOn f (Ioi (0 : ℝ))) (hgi : IntegrableOn g (Ioi (0 : ℝ)))
    (hfn : ∀ t, 0 < t → 0 ≤ f t) (hgn : ∀ t, 0 < t → 0 ≤ g t) :
    IntegrableOn (mellinConv f g) (Ioi (0 : ℝ)) ∧
    (∫ t in Ioi (0 : ℝ), mellinConv f g t) =
      (∫ t in Ioi (0 : ℝ), f t)*(∫ t in Ioi (0 : ℝ), g t) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hm : Measurable (fun z : ℝ × ℝ => f (z.2/z.1)*g z.1/z.1) := by
    fun_prop
  have hp : Integrable (fun z : ℝ × ℝ => f (z.2/z.1)*g z.1/z.1) (μ.prod μ) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      exact mellin_inner_integrable f hfi w (g w) hw
    · have heq : (fun w : ℝ => ∫ t, ‖f (t/w)*g w/w‖ ∂μ) =ᵐ[μ]
          fun w => g w*(∫ t, f t ∂μ) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
        have hnorm : (∫ t, ‖f (t/w)*g w/w‖ ∂μ) = ∫ t, f (t/w)*g w/w ∂μ := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact Real.norm_of_nonneg
            (div_nonneg (mul_nonneg (hfn _ (div_pos ht hw)) (hgn _ hw)) hw.le)
        rw [hnorm]
        exact mellin_inner_integral f w (g w) hw
      apply (hgi.mul_const (∫ t, f t ∂μ)).congr
      exact heq.symm
  constructor
  · exact hp.integral_prod_right
  unfold mellinConv
  change (∫ t, ∫ w, f (t/w)*g w/w ∂μ ∂μ) = _
  rw [← integral_integral_swap hp]
  have heq : (∫ w, ∫ t, f (t/w)*g w/w ∂μ ∂μ) =
      ∫ w, g w*(∫ t, f t ∂μ) ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    exact mellin_inner_integral f w (g w) hw
  rw [heq,integral_mul_const]
  exact mul_comm _ _

lemma mellin_moment_identity (f g : ℝ → ℝ) (k : ℕ) (t : ℝ) :
    t^k*mellinConv f g t =
      mellinConv (fun t => t^k*f t) (fun w => w^k*g w) t := by
  unfold mellinConv
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  rw [div_pow]
  have hn : w ≠ 0 := hw.ne'
  field_simp

theorem mellin_moment (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (k : ℕ) (hfi : IntegrableOn (fun t => t^k*f t) (Ioi (0 : ℝ)))
    (hgi : IntegrableOn (fun t => t^k*g t) (Ioi (0 : ℝ)))
    (hfn : ∀ t, 0 < t → 0 ≤ f t) (hgn : ∀ t, 0 < t → 0 ≤ g t) :
    IntegrableOn (fun t => t^k*mellinConv f g t) (Ioi (0 : ℝ)) ∧
    (∫ t in Ioi (0 : ℝ), t^k*mellinConv f g t) =
      (∫ t in Ioi (0 : ℝ), t^k*f t)*(∫ t in Ioi (0 : ℝ), t^k*g t) := by
  simp_rw [mellin_moment_identity]
  apply mellin_integrable_mass _ _ ((continuous_id.pow k).mul hf) ((continuous_id.pow k).mul hg)
    hfi hgi
  · intro t ht; exact mul_nonneg (pow_nonneg ht.le k) (hfn t ht)
  · intro t ht; exact mul_nonneg (pow_nonneg ht.le k) (hgn t ht)

end Helfgott

open MeasureTheory Set
open scoped Interval

namespace Helfgott

lemma integral_power_log (k : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (C : ℝ) :
    (∫ t in a..b, t^k*(C+Real.log t)) =
      b^(k+1)/((k:ℝ)+1)*(C+Real.log b-1/((k:ℝ)+1)) -
      a^(k+1)/((k:ℝ)+1)*(C+Real.log a-1/((k:ℝ)+1)) := by
  have hkn : (k:ℝ)+1 ≠ 0 := by have hk := Nat.cast_nonneg (α := ℝ) k; linarith
  have hpos (t : ℝ) (ht : t ∈ uIcc a b) : 0 < t := lt_of_lt_of_le (lt_min ha hb) ht.1
  have hi : IntervalIntegrable (fun t : ℝ => t^k*(C+Real.log t)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have hn : t ≠ 0 := (hpos t ht).ne'
    apply ContinuousAt.continuousWithinAt
    fun_prop
  have hd (t : ℝ) (ht : t ∈ uIcc a b) :
      HasDerivAt (fun t : ℝ => t^(k+1)/((k:ℝ)+1)*(C+Real.log t-1/((k:ℝ)+1)))
        (t^k*(C+Real.log t)) t := by
    have hn : t ≠ 0 := (hpos t ht).ne'
    have hp := ((hasDerivAt_id t).pow (k+1)).div_const ((k:ℝ)+1)
    have hl := ((Real.hasDerivAt_log hn).const_add C).sub_const (1/((k:ℝ)+1))
    convert! hp.mul hl using 1
    all_goals simp only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,one_mul,id_eq,Pi.pow_apply]
    all_goals field_simp
    all_goals simp only [pow_succ]
    all_goals ring
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi

lemma etaTwo_moment_integrable (k : ℕ) : Integrable (fun t : ℝ => t^k*etaTwo t) := by
  apply ((continuous_id.pow k).mul etaTwo_continuous).integrable_of_hasCompactSupport
  exact etaTwo_hasCompactSupport.mul_left

lemma etaTwo_moment_formula (k : ℕ) :
    (∫ t : ℝ, t^k*etaTwo t) =
      4*((1/2:ℝ)^(k+1)/((k:ℝ)+1)*(Real.log 4+Real.log (1/2)-1/((k:ℝ)+1)) -
        (1/4:ℝ)^(k+1)/((k:ℝ)+1)*(Real.log 4+Real.log (1/4)-1/((k:ℝ)+1))) -
      4*(1/((k:ℝ)+1)*(Real.log 1-1/((k:ℝ)+1)) -
        (1/2:ℝ)^(k+1)/((k:ℝ)+1)*(Real.log (1/2)-1/((k:ℝ)+1))) := by
  have hc : Continuous (fun t : ℝ => t^k*etaTwo t) := (continuous_id.pow k).mul etaTwo_continuous
  have heq : (∫ t : ℝ, t^k*etaTwo t) = ∫ t in (1/4:ℝ)..1, t^k*etaTwo t := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (1/4:ℝ) 1)
      (show ∀ t : ℝ, t ∉ Icc (1/4:ℝ) 1 → t^k*etaTwo t = 0 by
        intro t ht; rw [etaTwo_eq_zero_of_not_mem t ht,mul_zero])]
    rw [intervalIntegral.integral_of_le (by norm_num),integral_Icc_eq_integral_Ioc]
  rw [heq, ← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (1/4) (1/2)) (hc.intervalIntegrable (1/2) 1)]
  have hlo : (∫ t in (1/4:ℝ)..(1/2), t^k*etaTwo t) =
      4*∫ t in (1/4:ℝ)..(1/2), t^k*(Real.log 4+Real.log t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (1/4:ℝ) ≤ 1/2)] at ht
    dsimp only
    rw [etaTwo_eq_lower t ht,Real.log_mul (by norm_num) (by linarith [ht.1] : t ≠ 0)]
    ring
  have hhi : (∫ t in (1/2:ℝ)..1, t^k*etaTwo t) =
      -4*∫ t in (1/2:ℝ)..1, t^k*(0+Real.log t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 1)] at ht
    dsimp only
    rw [etaTwo_eq_upper t ht]
    ring
  rw [hlo,hhi,integral_power_log k (1/4) (1/2) (by norm_num) (by norm_num) (Real.log 4),
    integral_power_log k (1/2) 1 (by norm_num) (by norm_num) 0]
  simp
  ring

theorem etaTwo_first_moment : (∫ t : ℝ, t*etaTwo t) = (9/16 : ℝ) := by
  have h := etaTwo_moment_formula 1
  have heq : (fun t : ℝ => t*etaTwo t) = fun t => t^1*etaTwo t := by simp
  rw [heq,h]
  have h4 : Real.log (4 : ℝ) = 2*Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num,Real.log_pow]; norm_num
  have hh : Real.log (1/2 : ℝ) = -Real.log 2 := by rw [one_div,Real.log_inv]
  have hq : Real.log (1/4 : ℝ) = -(2*Real.log 2) := by rw [one_div,Real.log_inv,h4]
  rw [hh,hq,h4,Real.log_one]
  norm_num
  ring

theorem etaTwo_second_moment : (∫ t : ℝ, t^2*etaTwo t) = (49/144 : ℝ) := by
  rw [etaTwo_moment_formula 2]
  have h4 : Real.log (4 : ℝ) = 2*Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num,Real.log_pow]; norm_num
  have hh : Real.log (1/2 : ℝ) = -Real.log 2 := by rw [one_div,Real.log_inv]
  have hq : Real.log (1/4 : ℝ) = -(2*Real.log 2) := by rw [one_div,Real.log_inv,h4]
  rw [hh,hq,h4,Real.log_one]
  norm_num
  ring

end Helfgott

open MeasureTheory Set

namespace Helfgott

lemma etaTwo_moment_pos_integral (k : ℕ) :
    (∫ t in Ioi (0 : ℝ), t^k*etaTwo t) = ∫ t : ℝ, t^k*etaTwo t := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  simp [etaTwo,show ¬0 < t from ht]

lemma mellin_etaTwo_phi_moment (k : ℕ) :
    IntegrableOn (fun t => t^k*mellinConv etaTwo phi t) (Ioi (0 : ℝ)) ∧
    (∫ t in Ioi (0 : ℝ), t^k*mellinConv etaTwo phi t) =
      (∫ t : ℝ, t^k*etaTwo t)*(∫ t in Ioi (0 : ℝ), t^k*phi t) := by
  rw [← etaTwo_moment_pos_integral]
  apply mellin_moment _ _ etaTwo_continuous (by unfold phi; fun_prop)
    k (etaTwo_moment_integrable k).integrableOn (phi_moment_integrable k)
  · intro t ht; exact etaTwo_nonneg t
  · intro t ht; unfold phi; positivity

lemma scaled_moment_integral (F : ℝ → ℝ) (κ : ℝ) (hκ : 0 < κ) (k : ℕ) :
    (∫ t in Ioi (0 : ℝ), t^k*F (κ*t)) =
      (∫ t in Ioi (0 : ℝ), t^k*F t)/κ^(k+1) := by
  have heq : (fun t : ℝ => t^k*F (κ*t)) =
      fun t => (κ^k)⁻¹*((κ*t)^k*F (κ*t)) := by
    funext t
    rw [mul_pow]
    field_simp
  rw [heq,integral_const_mul,
    integral_comp_mul_left_Ioi (fun t => t^k*F t) 0 hκ]
  simp only [mul_zero,smul_eq_mul,pow_succ,div_eq_mul_inv,mul_inv_rev]
  ring

lemma etaStar_moment_integrable (k : ℕ) :
    IntegrableOn (fun t : ℝ => t^k*etaStar t) (Ioi (0 : ℝ)) := by
  have hmc := (mellin_etaTwo_phi_moment k).1
  have hs : IntegrableOn (fun t : ℝ => (49*t)^k*mellinConv etaTwo phi (49*t)) (Ioi (0 : ℝ)) := by
    apply (integrableOn_Ioi_comp_mul_left_iff
      (fun t => t^k*mellinConv etaTwo phi t) 0 (by norm_num : (0 : ℝ) < 49)).mpr
    simpa using hmc
  have hh := hs.const_mul ((49 : ℝ)^k)⁻¹
  have heq : (fun t : ℝ => t^k*etaStar t) =
      fun t => ((49 : ℝ)^k)⁻¹*((49*t)^k*mellinConv etaTwo phi (49*t)) := by
    funext t
    unfold etaStar
    rw [mul_pow]
    field_simp
  rw [heq]
  exact hh

lemma etaStar_moment_formula (k : ℕ) :
    (∫ t in Ioi (0 : ℝ), t^k*etaStar t) =
      ((∫ t : ℝ, t^k*etaTwo t)*(∫ t in Ioi (0 : ℝ), t^k*phi t))/(49 : ℝ)^(k+1) := by
  unfold etaStar
  rw [scaled_moment_integral _ 49 (by norm_num), (mellin_etaTwo_phi_moment k).2]

theorem etaStar_moments :
    (∫ t in Ioi (0 : ℝ), etaStar t) = Real.sqrt (Real.pi/2)/49 ∧
    (∫ t in Ioi (0 : ℝ), t*etaStar t) = (9/19208 : ℝ) ∧
    (∫ t in Ioi (0 : ℝ), t^2*etaStar t) = Real.sqrt (Real.pi/2)/115248 := by
  constructor
  · have h := etaStar_moment_formula 0
    simpa [etaTwo_mass,phi_mass] using h
  constructor
  · have h := etaStar_moment_formula 1
    norm_num [etaTwo_first_moment,phi_first_moment] at h
    simpa using h
  · rw [etaStar_moment_formula 2,etaTwo_second_moment,phi_second_moment]
    norm_num
    ring

end Helfgott

open MeasureTheory Set Filter
open scoped Convolution

namespace Helfgott

lemma etaCircle_le_one (t : ℝ) : etaCircle t ≤ 1 := by
  by_cases ht : t ∈ Icc (0 : ℝ) 2
  · have htn : 0 ≤ t*(2-t) := mul_nonneg ht.1 (by linarith [ht.2])
    have htl : t*(2-t) ≤ 1 := by nlinarith [sq_nonneg (t-1)]
    have hp : (t*(2-t))^3 ≤ 1 := by
      simpa using pow_le_pow_left₀ htn htl 3
    have he : Real.exp (-((t-1)^2)/2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (t-1)])
    rw [etaCircle,indicator_of_mem ht]
    have heq : t^3*(2-t)^3 = (t*(2-t))^3 := by ring
    rw [heq]
    exact mul_le_one₀ hp (by positivity) he
  · simp [etaCircle,ht]

lemma etaCircle_convolution_continuous :
    Continuous (fun ρ : ℝ => ∫ u : ℝ, etaCircle u*etaCircle (ρ-u)) := by
  have h := etaCircle_hasCompactSupport.continuous_convolution_right
    (L := ContinuousLinearMap.lsmul ℝ ℝ) etaCircle_integrable.locallyIntegrable etaCircle_continuous
  exact h

lemma etaCircle_convolution_nonneg (ρ : ℝ) :
    0 ≤ ∫ u : ℝ, etaCircle u*etaCircle (ρ-u) := by
  apply integral_nonneg
  intro u
  exact mul_nonneg (etaCircle_nonneg u) (etaCircle_nonneg (ρ-u))

lemma etaCircle_convolution_le (ρ : ℝ) :
    (∫ u : ℝ, etaCircle u*etaCircle (ρ-u)) ≤ ∫ u : ℝ, etaCircle u := by
  have hc : Continuous (fun u : ℝ => etaCircle u*etaCircle (ρ-u)) :=
    etaCircle_continuous.mul (etaCircle_continuous.comp (continuous_const.sub continuous_id))
  have hi : Integrable (fun u : ℝ => etaCircle u*etaCircle (ρ-u)) :=
    hc.integrable_of_hasCompactSupport etaCircle_hasCompactSupport.mul_right
  apply integral_mono hi etaCircle_integrable
  intro u
  exact mul_le_of_le_one_right (etaCircle_nonneg u) (etaCircle_le_one (ρ-u))

lemma main_convolution_integrable (ρ : ℝ) :
    IntegrableOn (fun w : ℝ => etaStar w*(∫ u : ℝ, etaCircle u*etaCircle (ρ-w-u)))
      (Ioi (0 : ℝ)) := by
  have hs : IntegrableOn etaStar (Ioi (0 : ℝ)) := by
    simpa using etaStar_moment_integrable 0
  have hc : Continuous (fun w : ℝ => ∫ u : ℝ, etaCircle u*etaCircle (ρ-w-u)) :=
    etaCircle_convolution_continuous.comp (continuous_const.sub continuous_id)
  apply (hs.mul_const (∫ u : ℝ, etaCircle u)).mono'
  · exact hs.aestronglyMeasurable.mul hc.aestronglyMeasurable
  · exact Eventually.of_forall (fun w => by
      have hn : 0 ≤ etaStar w := mellin_etaTwo_phi_nonneg (49*w)
      have hcn := etaCircle_convolution_nonneg (ρ-w)
      rw [Real.norm_of_nonneg (mul_nonneg hn hcn)]
      exact mul_le_mul_of_nonneg_left (etaCircle_convolution_le (ρ-w)) hn)

lemma main_convolution_lower (ρ : ℝ) :
    (16/25 : ℝ)*(∫ w in Ioi (0 : ℝ), etaStar w) -
      (17/10 : ℝ)*(∫ w in Ioi (0 : ℝ), etaStar w*((ρ-2)-w)^2) ≤
    ∫ w in Ioi (0 : ℝ), etaStar w*(∫ u : ℝ, etaCircle u*etaCircle (ρ-w-u)) := by
  have hs : IntegrableOn etaStar (Ioi (0 : ℝ)) := by simpa using etaStar_moment_integrable 0
  have h1 : IntegrableOn (fun w : ℝ => w*etaStar w) (Ioi (0 : ℝ)) := by
    simpa using etaStar_moment_integrable 1
  have h2 := etaStar_moment_integrable 2
  have hi : IntegrableOn (fun w : ℝ => etaStar w*((ρ-2)-w)^2) (Ioi (0 : ℝ)) := by
    have h := ((hs.const_mul ((ρ-2)^2)).sub (h1.const_mul (2*(ρ-2)))).add h2
    have heq : (fun w : ℝ => etaStar w*((ρ-2)-w)^2) =
        (((fun w => (ρ-2)^2*etaStar w) - fun w => 2*(ρ-2)*(w*etaStar w)) +
          fun w => w^2*etaStar w) := by
      funext w
      dsimp only [Pi.add_apply,Pi.sub_apply]
      ring
    rw [heq]
    exact h
  have hh : (∫ w in Ioi (0 : ℝ), (16/25 : ℝ)*etaStar w -
      (17/10 : ℝ)*(etaStar w*((ρ-2)-w)^2)) ≤
      ∫ w in Ioi (0 : ℝ), etaStar w*(∫ u : ℝ, etaCircle u*etaCircle (ρ-w-u)) := by
    apply integral_mono ((hs.const_mul (16/25)).sub (hi.const_mul (17/10)))
      (main_convolution_integrable ρ)
    intro w
    have hn : 0 ≤ etaStar w := mellin_etaTwo_phi_nonneg (49*w)
    have h := mul_le_mul_of_nonneg_left (etaCircle_convolution_lower (ρ-w)) hn
    convert! h using 1 <;> dsimp only [Pi.sub_apply] <;> ring
  rw [integral_sub (hs.const_mul (16/25)) (hi.const_mul (17/10)),
    integral_const_mul,integral_const_mul] at hh
  exact hh

lemma etaStar_centered_square_integral (a : ℝ) :
    (∫ w in Ioi (0 : ℝ), etaStar w*(a-w)^2) =
      a^2*(Real.sqrt (Real.pi/2)/49) - 2*a*(9/19208 : ℝ) +
        Real.sqrt (Real.pi/2)/115248 := by
  have hs : IntegrableOn etaStar (Ioi (0 : ℝ)) := by simpa using etaStar_moment_integrable 0
  have h1 : IntegrableOn (fun w : ℝ => w*etaStar w) (Ioi (0 : ℝ)) := by
    simpa using etaStar_moment_integrable 1
  have h2 := etaStar_moment_integrable 2
  have heq : (fun w : ℝ => etaStar w*(a-w)^2) =
      fun w => a^2*etaStar w - (2*a)*(w*etaStar w) + w^2*etaStar w := by
    funext w; ring
  rw [heq,integral_add (f := fun w : ℝ => a^2*etaStar w - (2*a)*(w*etaStar w))
      (g := fun w : ℝ => w^2*etaStar w) ((hs.const_mul (a^2)).sub (h1.const_mul (2*a))) h2,
    integral_sub (f := fun w : ℝ => a^2*etaStar w) (g := fun w : ℝ => (2*a)*(w*etaStar w))
      (hs.const_mul (a^2)) (h1.const_mul (2*a)),integral_const_mul,integral_const_mul,
    etaStar_moments.1,etaStar_moments.2.1,etaStar_moments.2.2]

lemma main_convolution_lower_centered :
    (801/49000 : ℝ) ≤
      ∫ w in Ioi (0 : ℝ), etaStar w*(∫ u : ℝ,
        etaCircle u*etaCircle (2+9/(392*Real.sqrt (Real.pi/2))-w-u)) := by
  let A : ℝ := Real.sqrt (Real.pi/2)
  let a : ℝ := 9/(392*A)
  have hA : 0 < A := Real.sqrt_pos.mpr (by positivity)
  have hAl : (1253/1000 : ℝ) ≤ A := by
    have hs : A^2 = Real.pi/2 := Real.sq_sqrt (by positivity)
    have hn : 0 ≤ A := hA.le
    nlinarith [Real.pi_gt_d4]
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hrel : a*A/49 = (9/19208 : ℝ) := by
    dsimp [a]
    field_simp
    all_goals ring
  have hv : (∫ w in Ioi (0 : ℝ), etaStar w*(a-w)^2) ≤ A/115248 := by
    rw [etaStar_centered_square_integral]
    change a^2*(A/49)-2*a*(9/19208 : ℝ)+A/115248 ≤ A/115248
    have hmul := mul_nonneg ha (by norm_num : (0 : ℝ) ≤ 9/19208)
    have hh : a^2*(A/49) = a*(9/19208 : ℝ) := by rw [← hrel]; ring
    rw [hh]
    nlinarith
  have hb := main_convolution_lower (2+a)
  have heq : ((2+a)-2) = a := by ring
  rw [heq,etaStar_moments.1] at hb
  have hh := mul_le_mul_of_nonneg_left hv (by norm_num : (0 : ℝ) ≤ 17/10)
  have hnum : (801/49000 : ℝ) ≤ (16/25 : ℝ)*(A/49)-(17/10 : ℝ)*(A/115248) := by
    nlinarith only [hAl]
  exact hnum.trans ((sub_le_sub_left hh _).trans hb)

lemma goldbach_center_eq :
    9/(196*Real.sqrt (2*Real.pi)) = 9/(392*Real.sqrt (Real.pi/2)) := by
  have hs : Real.sqrt (2*Real.pi) = 2*Real.sqrt (Real.pi/2) := by
    have h1 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2*Real.pi)
    have h2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Real.pi/2)
    have h3 := Real.sqrt_nonneg (2*Real.pi)
    have h4 := Real.sqrt_nonneg (Real.pi/2)
    nlinarith
  rw [hs]
  congr 1
  ring

theorem etaCircle_etaStar_main_convolution_lower :
    (801/49000 : ℝ) ≤
      ∫ w in Ioi (0 : ℝ), etaStar w*(∫ u : ℝ,
        etaCircle u*etaCircle (2+9/(196*Real.sqrt (2*Real.pi))-w-u)) := by
  rw [goldbach_center_eq]
  exact main_convolution_lower_centered

end Helfgott

open MeasureTheory Set

set_option backward.isDefEq.respectTransparency false

namespace Helfgott

lemma etaPlus_convolution_measurable :
    Measurable (fun ρ : ℝ => ∫ u : ℝ, etaPlus u*etaPlus (ρ-u)) := by
  have hm : Measurable (fun p : ℝ × ℝ => etaPlus p.2*etaPlus (p.1-p.2)) :=
    (etaPlus_measurable.comp measurable_snd).mul
      (etaPlus_measurable.comp (measurable_fst.sub measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma etaCircle_convolution_square_mass_upper (ρ : ℝ) :
    (∫ u : ℝ, etaCircle u*etaCircle (ρ-u)) ≤ 641/1000 := by
  have hg2 := etaCircle_square_integrable
  have hgsq := hg2.comp_sub_left ρ
  have hi := integrable_mul_of_square_integrable etaCircle (fun u => etaCircle (ρ-u))
    etaCircle_continuous.measurable
    (etaCircle_continuous.measurable.comp (measurable_const.sub measurable_id)) hg2 hgsq
  calc
    _ ≤ ∫ u : ℝ, ((etaCircle u)^2+(etaCircle (ρ-u))^2)/2 := by
      apply integral_mono hi ((hg2.add hgsq).div_const 2)
      intro u
      have h := abs_mul_le_half_squares (etaCircle u) (etaCircle (ρ-u))
      exact (le_abs_self _).trans h
    _ = ∫ u : ℝ, (etaCircle u)^2 := by
      rw [integral_div]
      have ha := integral_add hg2 hgsq
      rw [ha,integral_sub_left_eq_self (fun u => (etaCircle u)^2) volume ρ]
      ring
    _ ≤ _ := etaCircle_square_integral_upper

lemma etaPlus_convolution_abs_le_one (ρ : ℝ) :
    |∫ u : ℝ, etaPlus u*etaPlus (ρ-u)| ≤ 1 := by
  have hd := (etaPlus_convolution_approximation ρ).2
  have ht := abs_add_le
    ((∫ u : ℝ, etaPlus u*etaPlus (ρ-u))-(∫ u : ℝ, etaCircle u*etaCircle (ρ-u)))
    (∫ u : ℝ, etaCircle u*etaCircle (ρ-u))
  rw [sub_add_cancel,abs_of_nonneg (etaCircle_convolution_nonneg ρ)] at ht
  linarith [etaCircle_convolution_square_mass_upper ρ]

lemma actual_main_convolution_integrable (ρ : ℝ) :
    IntegrableOn (fun w : ℝ => etaStar w*(∫ u : ℝ, etaPlus u*etaPlus (ρ-w-u)))
      (Ioi (0 : ℝ)) := by
  have hs : IntegrableOn etaStar (Ioi (0 : ℝ)) := by
    simpa using etaStar_moment_integrable 0
  have hm : Measurable (fun w : ℝ => ∫ u : ℝ, etaPlus u*etaPlus (ρ-w-u)) :=
    etaPlus_convolution_measurable.comp (measurable_const.sub measurable_id)
  apply hs.mono' (hs.aestronglyMeasurable.mul hm.aestronglyMeasurable)
  exact ae_of_all _ (fun w => by
    have hn : 0 ≤ etaStar w := mellin_etaTwo_phi_nonneg (49*w)
    simp only [Pi.mul_apply,Real.norm_eq_abs,abs_mul,abs_of_nonneg hn]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (etaPlus_convolution_abs_le_one (ρ-w)) hn)

lemma actual_main_convolution_approximation (ρ : ℝ) :
    |(∫ w in Ioi (0 : ℝ), etaStar w*(∫ u : ℝ, etaPlus u*etaPlus (ρ-w-u)))-
      (∫ w in Ioi (0 : ℝ), etaStar w*(∫ u : ℝ, etaCircle u*etaCircle (ρ-w-u)))| ≤
        (32033/50000000 : ℝ)*(Real.sqrt (Real.pi/2)/49) := by
  let f : ℝ → ℝ := fun w => etaStar w*(∫ u : ℝ, etaPlus u*etaPlus (ρ-w-u))
  let g : ℝ → ℝ := fun w => etaStar w*(∫ u : ℝ, etaCircle u*etaCircle (ρ-w-u))
  have hf : IntegrableOn f (Ioi (0 : ℝ)) := actual_main_convolution_integrable ρ
  have hg : IntegrableOn g (Ioi (0 : ℝ)) := main_convolution_integrable ρ
  have hs : IntegrableOn etaStar (Ioi (0 : ℝ)) := by
    simpa using etaStar_moment_integrable 0
  have hd : IntegrableOn (fun w => f w-g w) (Ioi (0 : ℝ)) := hf.sub hg
  have hb (w : ℝ) : |f w-g w| ≤ etaStar w*(32033/50000000 : ℝ) := by
    have hn : 0 ≤ etaStar w := mellin_etaTwo_phi_nonneg (49*w)
    have he : f w-g w = etaStar w*((∫ u : ℝ, etaPlus u*etaPlus (ρ-w-u))-
      (∫ u : ℝ, etaCircle u*etaCircle (ρ-w-u))) := by dsimp [f,g]; ring
    rw [he,abs_mul,abs_of_nonneg hn]
    exact mul_le_mul_of_nonneg_left (etaPlus_convolution_approximation (ρ-w)).2 hn
  change |(∫ w in Ioi (0 : ℝ), f w)-(∫ w in Ioi (0 : ℝ), g w)| ≤ _
  calc
    _ = |∫ w in Ioi (0 : ℝ), f w-g w| := by rw [integral_sub hf hg]
    _ ≤ ∫ w in Ioi (0 : ℝ), |f w-g w| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun w => f w-g w)
    _ ≤ ∫ w in Ioi (0 : ℝ), etaStar w*(32033/50000000 : ℝ) :=
      integral_mono hd.abs (hs.mul_const (32033/50000000 : ℝ)) hb
    _ = _ := by rw [integral_mul_const,etaStar_moments.1]; ring

theorem etaPlus_etaStar_main_convolution_lower :
    IntegrableOn (fun w : ℝ => etaStar w*(∫ u : ℝ,
      etaPlus u*etaPlus (2+9/(196*Real.sqrt (2*Real.pi))-w-u))) (Ioi (0 : ℝ)) ∧
    (8001/490000 : ℝ) ≤
      ∫ w in Ioi (0 : ℝ), etaStar w*(∫ u : ℝ,
        etaPlus u*etaPlus (2+9/(196*Real.sqrt (2*Real.pi))-w-u)) := by
  refine ⟨actual_main_convolution_integrable _,?_⟩
  have hd := (abs_le.mp (actual_main_convolution_approximation
    (2+9/(196*Real.sqrt (2*Real.pi))))).1
  have hc := etaCircle_etaStar_main_convolution_lower
  have hA : Real.sqrt (Real.pi/2) ≤ 127/100 := by
    have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Real.pi/2)
    have hn := Real.sqrt_nonneg (Real.pi/2)
    nlinarith [Real.pi_lt_d2]
  have hnum : (32033/50000000 : ℝ)*(Real.sqrt (Real.pi/2)/49) ≤ (9/10000 : ℝ)/49 := by
    nlinarith [hA]
  linarith

end Helfgott
end

section
/-! Uniform upper bound for the actual ternary Euler constant. Complete convergence and factor proofs included. Written by Codex. -/

section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Finset Filter

namespace Helfgott

lemma singularEulerFactor_norm_defect_bound (N p : ℕ) :
    ‖singularEulerFactor N p-1‖ ≤ 4/(p:ℝ)^2 := by
  unfold singularEulerFactor
  split_ifs with hp hdvd
  · have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hsq : (0:ℝ) < ((p:ℝ)-1)^2 := by nlinarith
    have hp2 : (0:ℝ) < (p:ℝ)^2 := by positivity
    have hcomp : 1/((p:ℝ)-1)^2 ≤ 4/(p:ℝ)^2 := by
      apply (div_le_div_iff₀ hsq hp2).2
      nlinarith [sq_nonneg ((p:ℝ)-2)]
    have hid : (1-1/((p:ℝ)-1)^2)-1 = -(1/((p:ℝ)-1)^2) := by ring
    rw [hid,norm_neg,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact hcomp
  · have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
    have ha : (1:ℝ) ≤ (p:ℝ)-1 := by linarith
    have hsq : (0:ℝ) < ((p:ℝ)-1)^2 := by nlinarith
    have hp2 : (0:ℝ) < (p:ℝ)^2 := by positivity
    have hcomp : 1/((p:ℝ)-1)^2 ≤ 4/(p:ℝ)^2 := by
      apply (div_le_div_iff₀ hsq hp2).2
      nlinarith [sq_nonneg ((p:ℝ)-2)]
    have hden : ((p:ℝ)-1)^2 ≤ ((p:ℝ)-1)^3 := by
      nlinarith [mul_nonneg (sq_nonneg ((p:ℝ)-1)) (sub_nonneg.mpr ha)]
    have hc : 1/((p:ℝ)-1)^3 ≤ 1/((p:ℝ)-1)^2 :=
      one_div_le_one_div_of_le hsq hden
    have hid : (1+1/((p:ℝ)-1)^3)-1 = 1/((p:ℝ)-1)^3 := by ring
    have hcube : 0 ≤ 1/((p:ℝ)-1)^3 := by positivity
    rw [hid,Real.norm_eq_abs,abs_of_nonneg hcube]
    exact hc.trans hcomp
  · simp only [sub_self,norm_zero]
    positivity

lemma singularEulerFactor_summable_defect (N : ℕ) :
    Summable (fun p : ℕ => ‖singularEulerFactor N p-1‖) := by
  have hs : Summable (fun p : ℕ => 4/(p:ℝ)^2) := by
    simpa only [mul_one_div] using
      ((Real.summable_one_div_nat_pow.mpr (by decide : 1 < (2:ℕ))).mul_left (4:ℝ))
  exact hs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => singularEulerFactor_norm_defect_bound N p)

lemma singularEulerFactor_multipliable (N : ℕ) : Multipliable (singularEulerFactor N) := by
  have hm := multipliable_one_add_of_summable (singularEulerFactor_summable_defect N)
  have he : (fun p : ℕ => 1+(singularEulerFactor N p-1)) = singularEulerFactor N := by
    funext p
    ring
  rw [he] at hm
  exact hm

lemma singularEulerFactor_nonneg (N p : ℕ) : 0 ≤ singularEulerFactor N p := by
  unfold singularEulerFactor
  split_ifs with hp hdvd
  · have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hs : (1:ℝ) ≤ ((p:ℝ)-1)^2 := by nlinarith
    have hpos : (0:ℝ) < ((p:ℝ)-1)^2 := by linarith
    have hi : 1/((p:ℝ)-1)^2 ≤ (1:ℝ) := (div_le_one hpos).2 hs
    linarith
  · have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hden0 : (0:ℝ) ≤ (p:ℝ)-1 := by linarith
    have hc : (0:ℝ) ≤ 1/((p:ℝ)-1)^3 := by positivity
    linarith
  · norm_num


end Helfgott
end

section
open Finset
open scoped BigOperators
namespace Helfgott.SingularAux
lemma prod_one_add_times_one_sub_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∏ i ∈ s, (1+f i))*(1-∑ i ∈ s, f i) ≤ 1 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    have ha0 := hf a (mem_insert_self a s)
    have hs0 : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (mem_insert_of_mem hi)
    have hi := ih hs0
    have hP : 0 ≤ ∏ i ∈ s, (1+f i) := prod_nonneg (fun i hi => by linarith [hs0 i hi])
    have hS : 0 ≤ ∑ i ∈ s, f i := sum_nonneg hs0
    rw [prod_insert ha,sum_insert ha]
    have hh : (1+f a)*(1-(f a+∑ i ∈ s,f i)) ≤ 1-∑ i ∈ s,f i := by
      nlinarith [mul_nonneg ha0 hS, sq_nonneg (f a)]
    calc
      _ = (∏ i ∈ s, (1+f i))*((1+f a)*(1-(f a+∑ i ∈ s,f i))) := by ring
      _ ≤ (∏ i ∈ s, (1+f i))*(1-∑ i ∈ s,f i) := mul_le_mul_of_nonneg_left hh hP
      _ ≤ 1 := hi


end Helfgott.SingularAux
end

section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open Finset
open scoped BigOperators

namespace Helfgott
namespace SingularUpperAux

lemma inv_cube_telescoping (t : ℝ) (ht : 2 ≤ t) :
    1/(t+1)^3 ≤ (1/2:ℝ)*(1/t^2-1/(t+1)^2) := by
  have ht0 : 0 < t := by linarith
  have htp : 0 < t+1 := by linarith
  apply (div_le_iff₀ (pow_pos htp 3)).mpr
  field_simp
  nlinarith

lemma inv_cube_tail_finite (M : ℕ) :
    ∑ k ∈ range M, 1/((k:ℝ)+3)^3 ≤ (1/8:ℝ)-(1/2:ℝ)/((M:ℝ)+2)^2 := by
  induction M with
  | zero => norm_num
  | succ M ih =>
    rw [sum_range_succ]
    have h := inv_cube_telescoping ((M:ℝ)+2) (by linarith [Nat.cast_nonneg (α:=ℝ) M])
    rw [show (M:ℝ)+2+1 = (M:ℝ)+3 by ring] at h
    simp only [Nat.cast_succ]
    rw [show (M:ℝ)+1+2 = (M:ℝ)+3 by ring]
    calc
      _ ≤ ((1/8:ℝ)-(1/2:ℝ)/((M:ℝ)+2)^2) +
          (1/2:ℝ)*(1/((M:ℝ)+2)^2-1/((M:ℝ)+3)^2) := add_le_add ih h
      _ = _ := by ring

lemma inv_cube_prefix (M : ℕ) :
    ∑ k ∈ range M, 1/((k:ℝ)+2)^3 ≤ (1/4:ℝ) := by
  cases M with
  | zero => norm_num
  | succ M =>
    rw [sum_range_succ']
    simp only [Nat.cast_succ,Nat.cast_zero,zero_add]
    have h := inv_cube_tail_finite M
    have he : (fun k : ℕ => 1/((k:ℝ)+1+2)^3) =
        (fun k : ℕ => 1/((k:ℝ)+3)^3) := by funext k;congr 2;ring
    rw [he]
    rw [show (1/(2:ℝ)^3:ℝ) = 1/8 by norm_num]
    have hn : 0 ≤ (1/2:ℝ)/((M:ℝ)+2)^2 := by positivity
    linarith

lemma inv_cube_product (M : ℕ) :
    ∏ k ∈ range M, (1+1/((k:ℝ)+2)^3) ≤ (4/3:ℝ) := by
  have hh := SingularAux.prod_one_add_times_one_sub_sum_le (range M)
    (fun k : ℕ => 1/((k:ℝ)+2)^3) (fun k _ => by positivity)
  have hs := inv_cube_prefix M
  have hp : 0 ≤ ∏ k ∈ range M, (1+1/((k:ℝ)+2)^3) :=
    prod_nonneg (fun k _ => by positivity)
  nlinarith

lemma singular_factor_upper (N k : ℕ) :
    singularEulerFactor N (k+3) ≤ 1+1/((k:ℝ)+2)^3 := by
  have he : ((k+3:ℕ):ℝ)-1 = (k:ℝ)+2 := by push_cast;ring
  by_cases hp : Nat.Prime (k+3)
  · by_cases hd : k+3 ∣ N
    · simp only [singularEulerFactor,if_pos hp,if_pos hd,he]
      have h2 : 0 ≤ 1/((k:ℝ)+2)^2 := by positivity
      have h3 : 0 ≤ 1/((k:ℝ)+2)^3 := by positivity
      linarith
    · simp only [singularEulerFactor,if_pos hp,if_neg hd,he]
      exact le_rfl
  · simp only [singularEulerFactor,if_neg hp]
    linarith [show (0:ℝ) ≤ 1/((k:ℝ)+2)^3 by positivity]

lemma singular_prefix_three (N : ℕ) :
    ∏ p ∈ range 3, singularEulerFactor N p ≤ 2 := by
  norm_num [prod_range_succ,singularEulerFactor]
  split_ifs <;> norm_num

lemma singular_partial_upper (N Q : ℕ) :
    ∏ p ∈ range Q, singularEulerFactor N p ≤ (8/3:ℝ) := by
  by_cases hQ : Q < 3
  · interval_cases Q <;> norm_num [prod_range_succ,singularEulerFactor]
  · obtain ⟨M,rfl⟩ := Nat.exists_eq_add_of_le (by omega : 3 ≤ Q)
    rw [prod_range_add]
    have hp : 0 ≤ ∏ k ∈ range M, singularEulerFactor N (3+k) :=
      prod_nonneg (fun k _ => singularEulerFactor_nonneg N (3+k))
    have hc : (∏ k ∈ range M, singularEulerFactor N (3+k)) ≤
        ∏ k ∈ range M, (1+1/((k:ℝ)+2)^3) := by
      apply Finset.prod_le_prod
      · exact fun k _ => singularEulerFactor_nonneg N (3+k)
      · intro k hk
        simpa only [Nat.add_comm] using singular_factor_upper N k
    have ht := hc.trans (inv_cube_product M)
    have hh := mul_le_mul (singular_prefix_three N) ht hp (by norm_num : (0:ℝ) ≤ 2)
    nlinarith

end SingularUpperAux

theorem singularConstant_upper (N : ℕ) : singularConstant N ≤ (8/3:ℝ) := by
  apply le_of_tendsto (singularEulerFactor_multipliable N).tendsto_prod_tprod_nat
  exact Filter.Eventually.of_forall (SingularUpperAux.singular_partial_upper N)

theorem singularConstant_bounds (N : ℕ) :
    0 ≤ singularConstant N ∧ singularConstant N ≤ (8/3:ℝ) := by
  exact ⟨tprod_nonneg (fun p => singularEulerFactor_nonneg N p),singularConstant_upper N⟩

end Helfgott
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set

namespace Helfgott

theorem singular_main_convolution_perturbation (N : ℕ) (x ρ : ℝ) :
    ‖(((x^2*singularConstant N*(∫ w in Ioi (0:ℝ),etaStar w*
      (∫ u : ℝ,etaPlus u*etaPlus (ρ-w-u))):ℝ):ℂ))-
      (((x^2*singularConstant N*(∫ w in Ioi (0:ℝ),etaStar w*
      (∫ u : ℝ,etaCircle u*etaCircle (ρ-w-u))):ℝ):ℂ))‖ ≤
      (3/1000:ℝ)*(x^2/49) := by
  have hc := singularConstant_bounds N
  have hd := actual_main_convolution_approximation ρ
  have hA : Real.sqrt (Real.pi/2) ≤ 127/100 := by
    have hs := Real.sq_sqrt (by positivity : (0:ℝ) ≤ Real.pi/2)
    nlinarith [Real.sqrt_nonneg (Real.pi/2),Real.pi_lt_d2]
  have hx : 0 ≤ x^2*singularConstant N := mul_nonneg (sq_nonneg x) hc.1
  have hmain := mul_le_mul_of_nonneg_left hd hx
  have hC := mul_le_mul_of_nonneg_left hc.2 (sq_nonneg x)
  have hcoeff : (32033/50000000:ℝ)*(Real.sqrt (Real.pi/2)/49) ≤
      (32033/50000000:ℝ)*((127/100:ℝ)/49) := by nlinarith [hA]
  have ht := mul_le_mul hC hcoeff (by positivity)
    (by positivity : (0:ℝ) ≤ x^2*(8/3:ℝ))
  rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  rw [show x^2*singularConstant N*(∫ w in Ioi (0:ℝ),etaStar w*(∫ u : ℝ,
      etaPlus u*etaPlus (ρ-w-u)))-
      x^2*singularConstant N*(∫ w in Ioi (0:ℝ),etaStar w*(∫ u : ℝ,
      etaCircle u*etaCircle (ρ-w-u))) =
      (x^2*singularConstant N)*((∫ w in Ioi (0:ℝ),etaStar w*(∫ u : ℝ,
      etaPlus u*etaPlus (ρ-w-u)))-
      (∫ w in Ioi (0:ℝ),etaStar w*(∫ u : ℝ,
      etaCircle u*etaCircle (ρ-w-u)))) by ring]
  rw [abs_mul,abs_of_nonneg hx]
  have hn : 0 ≤ x^2 := sq_nonneg x
  nlinarith

end Helfgott
end

open MeasureTheory Set Helfgott

theorem solution (N : ℕ) (x ρ : ℝ) :
    ‖(((x^2*singularConstant N*(∫ w in Ioi (0:ℝ),etaStar w*
      (∫ u : ℝ,etaPlus u*etaPlus (ρ-w-u))):ℝ):ℂ))-
      (((x^2*singularConstant N*(∫ w in Ioi (0:ℝ),etaStar w*
      (∫ u : ℝ,etaCircle u*etaCircle (ρ-w-u))):ℝ):ℂ))‖ ≤
      (3/1000:ℝ)*(x^2/49) := Helfgott.singular_main_convolution_perturbation N x ρ

#print axioms solution
