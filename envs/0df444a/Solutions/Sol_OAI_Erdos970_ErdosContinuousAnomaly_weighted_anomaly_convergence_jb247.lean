-- Prove2me | solution 1 for OAI.Erdos970.ErdosContinuousAnomaly.weighted_anomaly_convergence_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:57:24.542794+00:00
-- url     : https://prove2.me/submissions/c5db1823-5773-45b4-b57f-ac077e54d582

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Tactic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Definitions.Def_OAIQ247J008
import Theorems.Thm_Erdos970_Mertens_LogZetaInteg_log_zeta_eq_integ_aux_jb247
import Theorems.Thm_Erdos970_Mertens_sum_M_eq_summand_le_jb247
import Theorems.Thm_OAI_Erdos970_ErdosContinuousAnomaly_common_anomaly_exponential_jb247

section
-- module Solutions.OAIQ247_JB.Erdos970_MertensClassical
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970

namespace Real

open _root_.Real _root_.Filter _root_.Asymptotics

theorem inv_log_eq_o_one : (fun x ↦ 1 / log x) =o[atTop] (fun _ ↦ (1:ℝ)) := by
    rw [isLittleO_one_iff]
    convert (preTransparency := .instances) tendsto_log_atTop.inv_tendsto_atTop using 1
    all_goals try with_reducible_and_instances rfl
    ext; simp

end Real

section Issue1584
open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology

private lemma integrableOn_log_mul_exp_neg :
    IntegrableOn (fun v : ℝ => Real.log v * Real.exp (-v)) (Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ), integrableOn_union]
  constructor
  ·                                                             
    have hlog : IntegrableOn (fun v : ℝ => Real.log v) (Ioc 0 1) volume := by
      have := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1))
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)] at this
    apply Integrable.mono' hlog.norm
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with v hv
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      have h2 : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hv.1])
      rw [h1]
      nlinarith [abs_nonneg (Real.log v), Real.exp_pos (-v)]
  ·                                                         
    have hexp : IntegrableOn (fun v : ℝ => (2 : ℝ) * Real.exp ((-1/2) * v)) (Ioi 1) volume := by
      exact (integrableOn_exp_mul_Ioi (by norm_num : (-1/2 : ℝ) < 0) 1).const_mul 2
    apply Integrable.mono' hexp
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v hv
      have hv1 : (1 : ℝ) ≤ v := le_of_lt hv
      have hvpos : (0 : ℝ) < v := by linarith
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hlogabs : |Real.log v| = Real.log v :=
        abs_of_nonneg (Real.log_nonneg hv1)
      have hexpabs : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      rw [hlogabs, hexpabs]
                    
      have hlogv : Real.log v ≤ v := (Real.log_le_sub_one_of_pos hvpos).trans (by linarith)
                            
      have hvexp : v ≤ 2 * Real.exp (v/2) := by
        have := Real.add_one_le_exp (v/2)
        nlinarith [Real.exp_pos (v/2)]
                                                                                  
      have hstep : Real.log v * Real.exp (-v) ≤ 2 * Real.exp (v/2) * Real.exp (-v) := by
        apply mul_le_mul_of_nonneg_right (hlogv.trans hvexp) (le_of_lt (Real.exp_pos _))
      have heq : 2 * Real.exp (v/2) * Real.exp (-v) = 2 * Real.exp ((-1/2) * v) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
      rw [heq] at hstep
      exact hstep

private lemma integral_log_mul_exp_neg_eq_deriv_Gamma :
    ∫ t in Ioi (0:ℝ), Real.log t * Real.exp (-t) = deriv Real.Gamma 1 := by
  set I : ℝ := ∫ t in Ioi (0:ℝ), Real.log t * Real.exp (-t) with hI
                                              
  have h1 := Complex.hasDerivAt_GammaIntegral (s := (1 : ℂ)) (by norm_num)
                                                                                   
  have hval : (∫ t : ℝ in Ioi 0, (↑t : ℂ) ^ ((1 : ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t))))
      = (I : ℂ) := by
    have key : ∀ t : ℝ, (↑t : ℂ) ^ ((1 : ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t)))
        = ((Real.log t * Real.exp (-t) : ℝ) : ℂ) := by
      intro t
      rw [sub_self, Complex.cpow_zero, one_mul, Complex.ofReal_mul]
    simp_rw [key]
    rw [integral_complex_ofReal, hI]
  rw [hval] at h1
                                                                                 
  have h2 : HasDerivAt Complex.Gamma (I : ℂ) 1 := by
    apply h1.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (0:ℝ) < (1:ℂ).re by norm_num)] with z hz
    exact Complex.Gamma_eq_integral hz
                            
  have h3 := h2.real_of_complex
  have h4 : HasDerivAt Real.Gamma I 1 := by
    have hcongr : (fun x : ℝ => (Complex.Gamma ↑x).re) = Real.Gamma := by
      funext x
      rw [Complex.Gamma_ofReal, Complex.ofReal_re]
    rw [hcongr, Complex.ofReal_re] at h3
    exact h3
  rw [← h4.deriv]

private theorem mul_integ_log_log_eq_aux (s : ℝ) (hs : 1 < s) :
    (s - 1) * ∫ x in Ioi (1:ℝ), Real.log (Real.log x) * x ^ (-s) =
      - Real.log (s - 1) + deriv Real.Gamma 1 := by
  have hs0 : 0 < s - 1 := by linarith
  set f : ℝ → ℝ := fun x => (s - 1) * Real.log x with hf_def
  set f' : ℝ → ℝ := fun x => (s - 1) / x with hf'_def
  set g : ℝ → ℝ := fun u => (Real.log u - Real.log (s - 1)) * Real.exp (-u) with hg_def
            
  have hf1 : f 1 = 0 := by simp [hf_def]
                           
  have hf_cont : ContinuousOn f (Ici 1) := by
    apply ContinuousOn.mul continuousOn_const
    apply Real.continuousOn_log.mono
    intro x hx
    simp only [mem_Ici] at hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith
                          
  have hft : Tendsto f atTop atTop := by
    apply Filter.Tendsto.const_mul_atTop hs0
    exact Real.tendsto_log_atTop
                                                      
  have hff' : ∀ x ∈ Ioi (1:ℝ), HasDerivWithinAt f (f' x) (Ioi x) x := by
    intro x hx
    simp only [mem_Ioi] at hx
    have hxne : x ≠ 0 := by linarith
    have := (Real.hasDerivAt_log hxne).const_mul (s - 1)
    have h2 : HasDerivAt f ((s - 1) * x⁻¹) x := this
    have : (s - 1) * x⁻¹ = f' x := by rw [hf'_def]; field_simp
    rw [this] at h2
    exact h2.hasDerivWithinAt
                                          
  have hmono : StrictMonoOn f (Ici 1) := by
    intro a ha b hb hab
    simp only [mem_Ici] at ha hb
    apply mul_lt_mul_of_pos_left _ hs0
    exact Real.log_lt_log (by linarith) hab
  have himg_Ioi : f '' Ioi 1 = Ioi 0 := by
    ext y
    simp only [Set.mem_image, mem_Ioi]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : 0 < Real.log x := Real.log_pos hx
      positivity
    · intro hy
      refine ⟨Real.exp (y / (s - 1)), ?_, ?_⟩
      · exact Real.one_lt_exp_iff.mpr (div_pos hy hs0)
      · rw [hf_def]
        simp only [Real.log_exp]
        field_simp
  have himg_Ici : f '' Ici 1 = Ici 0 := by
    ext y
    simp only [Set.mem_image, mem_Ici]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : 0 ≤ Real.log x := Real.log_nonneg hx
      rw [hf_def]; positivity
    · intro hy
      refine ⟨Real.exp (y / (s - 1)), ?_, ?_⟩
      · exact Real.one_le_exp_iff.mpr (div_nonneg hy hs0.le)
      · rw [hf_def]
        simp only [Real.log_exp]
        field_simp
                                                         
  have hg_cont : ContinuousOn g (f '' Ioi 1) := by
    rw [himg_Ioi]
    apply ContinuousOn.mul
    · apply ContinuousOn.sub _ continuousOn_const
      apply Real.continuousOn_log.mono
      intro u hu
      simp only [mem_Ioi] at hu
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith
    · exact (Real.continuous_exp.comp continuous_neg).continuousOn
                                                         
  have hg1 : IntegrableOn g (f '' Ici 1) := by
    rw [himg_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
    have e1 : IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Ioi 0) :=
      integrableOn_log_mul_exp_neg
    have e2 : IntegrableOn (fun u => Real.log (s - 1) * Real.exp (-u)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul _
    have : g = fun u => Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u) := by
      funext u; rw [hg_def]; ring
    rw [this]
    exact e1.sub e2
                                                     
  have hg2 : IntegrableOn (fun x => (g ∘ f) x * f' x) (Ici 1) := by
                                                         
    have hff'_Ici : ∀ x ∈ Ici (1:ℝ), HasDerivWithinAt f (f' x) (Ici 1) x := by
      intro x hx
      simp only [mem_Ici] at hx
      have hxne : x ≠ 0 := by linarith
      have hd : HasDerivAt f ((s - 1) * x⁻¹) x := (Real.hasDerivAt_log hxne).const_mul (s - 1)
      have heq : (s - 1) * x⁻¹ = f' x := by rw [hf'_def]; field_simp
      rw [heq] at hd
      exact hd.hasDerivWithinAt
                            
    have hinj : InjOn f (Ici 1) := hmono.injOn
                                                                  
    have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul
      (s := Ici (1:ℝ)) (f := f) (f' := f') measurableSet_Ici hff'_Ici hinj g
    rw [hiff] at hg1
                                        
    apply hg1.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    simp only [mem_Ici] at hx
    have hxpos : (0:ℝ) < x := by linarith
    have hf'pos : 0 < f' x := by rw [hf'_def]; positivity
    simp only [smul_eq_mul, Function.comp, abs_of_pos hf'pos]
    ring
                               
  have hcov := integral_comp_mul_deriv_Ioi hf_cont hft hff' hg_cont hg1 hg2
  rw [hf1] at hcov
                                                       
  have hrhs : ∫ u in Ioi (0:ℝ), g u = deriv Real.Gamma 1 - Real.log (s - 1) := by
    have e1 : IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Ioi 0) :=
      integrableOn_log_mul_exp_neg
    have e2 : IntegrableOn (fun u => Real.log (s - 1) * Real.exp (-u)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul _
    have hsplit : (fun u => g u)
        = fun u => Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u) := by
      funext u; rw [hg_def]; ring
    rw [show (∫ u in Ioi (0:ℝ), g u)
        = ∫ u in Ioi (0:ℝ), (Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u))
        from by rw [hsplit]]
    rw [integral_sub e1 e2, integral_log_mul_exp_neg_eq_deriv_Gamma]
    rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
                                                                                  
  have hlhs : ∫ x in Ioi (1:ℝ), (g ∘ f) x * f' x
      = (s - 1) * ∫ x in Ioi (1:ℝ), Real.log (Real.log x) * x ^ (-s) := by
    have hpt : ∀ x ∈ Ioi (1:ℝ), (g ∘ f) x * f' x
        = (s - 1) * (Real.log (Real.log x) * x ^ (-s)) := by
      intro x hx
      simp only [mem_Ioi] at hx
      have hxpos : (0:ℝ) < x := by linarith
      have hlogpos : 0 < Real.log x := Real.log_pos hx
      have hlogne : Real.log x ≠ 0 := ne_of_gt hlogpos
      have hs1ne : s - 1 ≠ 0 := ne_of_gt hs0
      simp only [Function.comp, hf_def, hg_def, hf'_def]
                                                      
      rw [Real.log_mul hs1ne hlogne]
                                              
      have hexp : Real.exp (-((s - 1) * Real.log x)) = x ^ (-(s - 1)) := by
        rw [Real.rpow_def_of_pos hxpos]
        ring_nf
      rw [hexp]
                                                  
      have hx1 : x ^ (-(s - 1)) * ((s - 1) / x) = (s - 1) * x ^ (-s) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one x]
        rw [show x ^ (-(s - 1)) * ((s - 1) * x ^ (-1 : ℝ))
            = (s - 1) * (x ^ (-(s - 1)) * x ^ (-1 : ℝ)) by ring]
        rw [← Real.rpow_add hxpos]
        ring_nf
      rw [show (Real.log (s - 1) + Real.log (Real.log x) - Real.log (s - 1))
          = Real.log (Real.log x) by ring]
      linear_combination Real.log (Real.log x) * hx1
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  rw [hlhs, hrhs] at hcov
  rw [hcov]
  ring

end Issue1584

namespace Mertens

open _root_.Real Erdos970.Real _root_.Finset _root_.Filter _root_.Asymptotics _root_.Topology
open _root_.ArithmeticFunction hiding log

lemma sum_Ioc_one_eq_sum_Ioc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf : f 1 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Ioc 0 x, f n := by
  rw [(by rfl : Ioc 0 x = Icc 1 x), ← add_sum_Ioc_eq_sum_Icc hx]
  simpa

theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)

lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]

theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert (preTransparency := .instances) MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all <;> linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp only [integral_log, log_one, mul_zero, sub_zero, ge_iff_le,
    tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right, zero_le_one]
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]

theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]

theorem sum_mangoldt_div_eq (x : ℝ) : ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d = log x + E₁Λ x := by
    grind

theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    exact Nat.floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring

theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring

theorem sum_mangoldt_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x| ≤ log 4 + 4 := by
  grind [E₁Λ.le hx, E₁Λ.ge hx, log_nonneg]

theorem E₁Λ.bounded' : ∃ c > 0, ∀ x ≥ 1, |E₁Λ x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun x hx ↦ sum_mangoldt_div_eq_log hx⟩

theorem sum_log_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p = log x + E₁p x := by
    grind

theorem E₁p.le_E₁Λ (x : ℝ) :
    E₁p x ≤ E₁Λ x := by
    unfold E₁p E₁Λ; rw [sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    have : 0 ≤ Λ p := vonMangoldt_nonneg
    positivity

theorem E₁p.le {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≤ log 4 + 4 := by
    linarith [E₁Λ.le hx, E₁p.le_E₁Λ x]

lemma E₁.summand_nonneg (p : ℕ) : 0 ≤ if p.Prime then (log p) / (p*(p-1)) else 0 := by
  split_ifs with h
  · refine div_nonneg (log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ?_)
    suffices 1 ≤ (p : ℝ) by linarith
    exact_mod_cast h.one_le
  · rfl

theorem E₁.summable : Summable (fun p : ℕ ↦ if p.Prime then (log p) / (p*(p-1)) else 0) := by
  refine (Real.summable_one_div_nat_rpow.mpr (by norm_num: 1 < (3 : ℝ) / 2)|>.const_div
    4).of_nonneg_of_le E₁.summand_nonneg fun n ↦ ?_
  split_ifs with h
  · grw [Real.log_le_rpow_div (Nat.cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2)]
    · have denom : (n : ℝ) * ((n : ℝ) - 1) ≥ n ^ 2/ 2 := by
        rw [sq, mul_div_assoc]
        gcongr
        suffices (n : ℝ) ≥ 2 by linarith
        exact_mod_cast h.two_le
      grw [denom]
      · apply le_of_eq
        rw [← Real.rpow_natCast]
        field_simp
        rw [mul_div_assoc, ← Real.rpow_sub (mod_cast h.pos)]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        field
      · exact div_pos (pow_pos (mod_cast h.pos) _) (by norm_num)
    · apply mul_nonneg (Nat.cast_nonneg _)
      suffices 1 ≤ (n : ℝ) by linarith
      exact_mod_cast h.one_le
  · positivity

private lemma antitoneOn_log_div_sq :
    AntitoneOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp at ht
    have : (t + 2) ≠ 0 := by simp <;> linarith
    fun_prop (disch := grind)
  · refine fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_
    simp at ht
    have : (t + 2) ^ 2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · intro t ht
    simp at ht
    rw [deriv_fun_div (by fun_prop (disch := grind)) (by fun_prop) (by simp; grind), deriv_comp_add_const, deriv_log]
    simp
    field_simp
    simp only [mul_zero, tsub_le_iff_right, zero_add]
    rw [← log_rpow (by linarith), ← log_exp 1, rpow_ofNat]
    gcongr
    nlinarith [exp_one_lt_three]

private lemma log_div_sq_nonneg :
    ∀ t ∈ Set.Ioi 0, 0 ≤ log (t + 2) / (t + 2) ^ 2 := by
  exact fun t ht ↦  div_nonneg (log_nonneg (by simp_all <;> linarith)) (by positivity)

private lemma log_div_sq_is_deriv :
    ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ (-log (t + 2) - 1) / (t + 2)) (log (x + 2) / (x + 2) ^ 2) x := by
  intro t ht
  simp at ht
  apply HasDerivAt.comp_add_const (f := (fun t ↦ (-log t - 1)/ t)) t 2
  convert! (preTransparency := .instances) HasDerivAt.fun_div (c' := -1 / (t + 2)) (d' := (1 : ℝ)) _ _  _ using 1
  · field
  · apply HasDerivAt.sub_const
    convert! (preTransparency := .instances) (hasDerivAt_log (by linarith : t + 2 ≠ 0)).neg using 1
    all_goals try with_reducible_and_instances rfl
    ring_nf
  · exact hasDerivAt_id _
  · linarith

private lemma tendsto_antideriv_log_div_sq :
    Tendsto (fun t ↦ (-log (t + 2) - 1) / (t + 2)) atTop (nhds 0) := by
  have : Tendsto (fun (t : ℝ) ↦ t + 2) atTop atTop := by exact tendsto_atTop_add_const_right atTop 2 tendsto_id
  apply Tendsto.comp (g := (fun t ↦ (-log t - 1) / t)) _ this
  convert! (preTransparency := .instances) Tendsto.sub (f := (fun t ↦ -log t / t)) (a := 0) _ tendsto_inv_atTop_zero using 1
  · ring_nf
  · ring_nf
  · convert! (preTransparency := .instances) (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by linarith)).neg using 1
    · ext; ring
    · simp

private lemma integrableOn_log_div_sq :
    MeasureTheory.IntegrableOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ioi 0) := by
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq

private lemma integral_log_div_sq :
    ∫ t in Set.Ioi 0, log (t + 2) / (t + 2) ^ 2 = (log 2 + 1) / 2 := by
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq]
  ring_nf

private lemma summable_log_div_sq :
    Summable (fun (n : ℕ)↦ log (n + 3) / (n + 3) ^ 2) := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  suffices Summable (fun (n : ℕ) ↦ g n ) by
    convert! (preTransparency := .instances) summable_nat_add_iff 1|>.mpr this using 2
    all_goals try with_reducible_and_instances rfl
    unfold g
    push_cast
    ring_nf
  exact antitoneOn_log_div_sq.summable_of_integrableOn_Ioi_zero integrableOn_log_div_sq log_div_sq_nonneg

private lemma sum_log_div_sq_le :
    ∑' (n : ℕ), log (n + 3) / (n + 3) ^2 ≤ (log 2 + 1) / 2 := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  calc
  _ = ∑' (n : ℕ), g (n + 1 : ℕ):= by
    unfold g
    congr
    push_cast
    ring_nf
  _ ≤ ∫ x in Set.Ioi 0, g x := by
    exact antitoneOn_log_div_sq.tsum_add_one_le_integral integrableOn_log_div_sq log_div_sq_nonneg
  _ = _ := by
    exact integral_log_div_sq

theorem E₁.le : E₁ ≤ (5 * log 2 + 3) / 4 := by
  unfold E₁
  calc
  _ = log 2 / 2 + ∑' (n : ℕ), if (n + 3).Prime then log (n + 3) / ((n + 3) * (n + 2)) else 0 := by
    rw [← E₁.summable.sum_add_tsum_nat_add 3, (by rfl : range 3 = {0, 1, 2})]
    simp [Nat.prime_two]
    ring_nf
  _ ≤ log 2 / 2 + ∑' (n : ℕ), (3 / 2) * (log (n + 3) / (n + 3) ^ 2) := by
    gcongr with n
    · convert! (preTransparency := .instances) summable_nat_add_iff 3|>.mpr E₁.summable using 4
      · norm_cast
      · push_cast <;> ring
    · exact summable_log_div_sq.mul_left _
    · split_ifs with h
      · grw [(by linarith : (n + 2 : ℝ) ≥ 2 * (n + 3) / 3)]
        · field_simp
          rfl
        · exact log_nonneg (by grind)
      · exact mul_nonneg (by norm_num) (div_nonneg (log_nonneg (by grind)) (by positivity))
  _ = log 2 / 2 + (3 / 2) * ∑' (n : ℕ), log (n + 3) / (n + 3) ^ 2 := by
    rw [tsum_mul_left]
  _ ≤ _ := by
    grw [sum_log_div_sq_le]
    ring_nf
    rfl

theorem E₁Λ.le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ E₁p x + E₁ := by
  unfold E₁Λ E₁p
  suffices ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / p + E₁ by linarith
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, Chebyshev.sum_PrimePow_eq_sum_sum _ (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all <;> linarith)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    simp only [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast <;> linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg
    · gcongr
      exact le_max_right ..
    · exact fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
  _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, (log p / p) + ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    rw [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
    simp
  _ ≤ _ := by
    gcongr
    rw [sum_comm]
    conv => lhs; arg 2; ext p; arg 2; ext k; rw [← mul_one_div, Nat.cast_pow, ← one_div_pow]
    simp_rw [← mul_sum]
    calc
    _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p * (p - 1)) := by
      gcongr with p hp
      simp only [mem_filter, mem_Ioc] at hp
      conv => rhs; rw [← mul_one_div]
      gcongr
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := by
      rw [sum_filter]
      exact E₁.summable.sum_le_tsum _ fun p hp ↦ E₁.summand_nonneg p

theorem E₁p.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≥ -2 - E₁ := by
    linarith [E₁Λ.le_E₁p_add_E₁ hx, E₁Λ.ge hx]

theorem sum_log_prime_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x| ≤ log 4 + 4 := by
    rw [abs_le']
    refine ⟨ E₁p.le hx, ?_ ⟩
    have : log 2 > 0 := by apply _root_.Real.log_pos; norm_num
    have : log 4 = 2 * log 2 := by rw [←Real.log_rpow (by norm_num)]; norm_num
    grind [E₁p.ge hx, E₁.le]

theorem E₁p.bounded : ∃ c > 0, ∀ x ≥ 1, |E₁p x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun _ hx ↦ sum_log_prime_div_eq_log  hx⟩

lemma sum_Ioc_one_eq_sum_Icc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf1 : f 1 = 0) (hf0 : f 0 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Icc 0 x, f n := by
  rw [sum_Ioc_one_eq_sum_Ioc_zero hx hf1, ← add_sum_Ioc_eq_sum_Icc (by linarith)]
  simpa

private theorem sum_div_log_eq {x : ℝ} (hx : 2 ≤ x) (f : ℕ → ℝ) :
    ∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n / log n =
      (∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n) / log x + ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊ t ⌋₊, f n) / (t * log t^2) := by
  let g : ℕ → ℝ := (fun n ↦ if n < 2 then 0 else f n)
  trans ∑ n ∈ Icc 0 ⌊ x ⌋₊, (log n)⁻¹ * g n
  · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp) (by simp)]
    refine sum_congr rfl fun n hn ↦ ?_
    have : ¬(n ≤ 1) := by simp_all
    simp [g, this]
    field
  rw [sum_mul_eq_sub_integral_mul₁ g (f := (fun n ↦ (log n)⁻¹)) (by simp [g]) (by simp [g])]
  · rw [intervalIntegral.integral_of_le hx, mul_comm, ← div_eq_mul_inv, ← sub_neg_eq_add]
    simp_rw [deriv_inv_log]
    congr 1
    · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      congr 1
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
    · rw [← MeasureTheory.integral_neg]
      refine  MeasureTheory.setIntegral_congr_fun (by measurability) fun t ht ↦ ?_
      simp only [Set.mem_Ioc] at ht
      rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      field_simp
      congr 2
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
  · intro t ht
    simp only [Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp only [Set.mem_Icc] at ht
    conv => arg 1; ext x; rw [deriv_inv_log]
    have : log t ^2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)

private theorem integrable_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ c / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  conv => arg 1; ext t; rw [← mul_one_div]
  apply MeasureTheory.Integrable.const_mul
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' ?_ ?_ tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t ht
    simp only [Set.mem_Ici] at ht
    have : log t ≠ 0 := by simp; grind
    have : DifferentiableAt ℝ (fun t ↦ -(log t)⁻¹) t := by
      fun_prop (disch := grind)
    convert! (preTransparency := .instances) this.hasDerivAt using 1
    all_goals try with_reducible_and_instances rfl
    simp [deriv_inv_log]
    field
  · intro t ht
    simp only [Set.mem_Ioi] at ht
    exact one_div_nonneg.mpr <| mul_nonneg (by linarith) (sq_nonneg _)

attribute [fun_prop] measurable_from_top

private theorem integrable_E₁Λ_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁Λ x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁Λ.bounded'
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

private theorem integrable_E₁p_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁p x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁p.bounded
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

lemma deriv_log_log {x : ℝ} (hx : 1 < x) :
    deriv (fun t ↦ log (log t)) x = 1 / (x * log x) := by
  rw [deriv.log (differentiableAt_log (by linarith)) (by simp; grind), deriv_log]
  field

lemma integral_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in 2..x, 1 / (t * log t) = log (log x) - log (log 2) := by
  rw [← intervalIntegral.integral_deriv_eq_sub (f := fun t ↦ log (log t))]
  · refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [deriv_log_log]
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    linarith
  · intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.intervalIntegrable ?_
    apply ContinuousOn.congr (f := (fun t ↦ 1 / (t * log t)))
    · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      have : log t ≠ 0 := by simp; grind
      fun_prop (disch := grind)
    · intro t ht
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      exact deriv_log_log (by linarith)

lemma intervalIntegrable_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t ↦ 1 / (t * log t)) MeasureTheory.volume 2 x := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
  have : log t ≠ 0 := by simp; grind
  fun_prop (disch := grind)

theorem E₂Λ.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂Λ x = E₁Λ x / log x - ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) := by
  unfold E₂Λ
  rw [← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp)]
  conv => lhs; arg 1; arg 1; arg 2; ext n; rw [(by field : Λ n / (n * log n) = (Λ n / n) / log n)]
  rw [sum_div_log_eq hx]
  rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), sum_mangoldt_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, Λ n / n) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁Λ t / (t * log t ^ 2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top), sum_mangoldt_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold γ
    calc
    _ = E₁Λ x / log x + (∫ (x : ℝ) in 2..x, E₁Λ x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁Λ t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁Λ_div_mul_log_sq (by rfl)) (integrable_E₁Λ_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁Λ_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

private theorem integ_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioi x, c / (t * log t^2) = c / log x := by
    convert! (preTransparency := .instances) MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) (f := fun x ↦ - c / log x) ?_
      (integrable_const_div_mul_log_sq c hx) ?_ using 1
    · grind
    · intro t ht; simp at ht
      convert! (preTransparency := .instances) HasDerivAt.fun_div (hasDerivAt_const _ (-c)) (hasDerivAt_log (by linarith)) ?_ using 1
      · grind
      simp; grind
    convert! (preTransparency := .instances) tendsto_log_atTop.inv_tendsto_atTop.const_mul (-c) using 1
    all_goals try with_reducible_and_instances rfl
    simp

theorem E₂Λ.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂Λ x| ≤ (log 4 + 6) / log x := by
    have : 0 < log x := by apply _root_.Real.log_pos; linarith
    rw [E₂Λ.eq hx, abs_le']
    constructor
    · grw [E₁Λ.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) ≥ - 2 / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2) hx)
            (integrable_E₁Λ_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := _root_.Real.log_pos this
          gcongr; exact E₁Λ.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2) hx
      grw [this]
      grind
    grw [E₁Λ.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁Λ_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := _root_.Real.log_pos this
          gcongr; exact E₁Λ.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind

theorem E₂Λ.bound : E₂Λ =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [one_div, isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop]
    use log 4 + 6, 2
    intro x hx
    convert (preTransparency := .instances) E₂Λ.abs_le hx using 1
    all_goals try with_reducible_and_instances rfl
    have : 0 < log x := by apply _root_.Real.log_pos; linarith
    grind [abs_of_pos this]

theorem E₂Λ.bound' : E₂Λ =o[atTop] (fun _ ↦ (1:ℝ)) := E₂Λ.bound.trans_isLittleO inv_log_eq_o_one

private theorem log_zeta_eq_integ (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = (s - 1) * ∫ x in .Ioi 1, (log (log x) + γ + E₂Λ x) * x^(-s) :=
  LogZetaInteg.log_zeta_eq_integ_aux_jb247 s hs

private theorem mul_integ_log_log_eq (s : ℝ) (hs : 1 < s) :
    (s - 1) * ∫ x in .Ioi 1, log (log x) * x^(-s) = - log (s - 1) + deriv Gamma 1 :=
  mul_integ_log_log_eq_aux s hs

private theorem mul_integ_gamma_eq (s) (hs : 1 < s) : (s - 1) * ∫ x in .Ioi 1, γ * x^(-s) = γ := by
  rw [MeasureTheory.integral_const_mul γ (· ^ (-s)), @integral_Ioi_rpow_of_lt (-s), one_rpow] <;>
    grind

private theorem integrableOn_Ioi_mul_rpow_neg_of_abs_le
    {c B a s : ℝ} (hc : 0 < c) (has : a + 1 < s) {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ x ∈ Set.Ioi c, |f x| ≤ B * x ^ a) :
    MeasureTheory.IntegrableOn (fun x => f x * x ^ (-s)) (Set.Ioi c) := by
  have hg : MeasureTheory.IntegrableOn (fun x => B * x ^ (a - s)) (Set.Ioi c) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : a - s < -1) hc).const_mul B
  refine MeasureTheory.Integrable.mono' hg
    (hf.mul (measurable_id.pow_const (-s))).aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : (0:ℝ) < x := hc.trans hx
  have hxs : (0:ℝ) < x ^ (-s) := Real.rpow_pos_of_pos hxpos _
  rw [norm_mul, norm_eq_abs, norm_eq_abs, abs_of_pos hxs]
  calc |f x| * x ^ (-s) ≤ B * x ^ a * x ^ (-s) :=
        mul_le_mul_of_nonneg_right (hbound x hx) hxs.le
    _ = B * x ^ (a - s) := by rw [mul_assoc, ← Real.rpow_add hxpos, sub_eq_add_neg]

private theorem integrableOn_log_log_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => log (log x) * x ^ (-s)) (Set.Ioi 1) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (1:ℝ) ≤ 2)]
  apply MeasureTheory.IntegrableOn.union
  ·                                                                                 
    have hll : MeasureTheory.IntegrableOn (fun x => log (log x)) (Set.Ioc 1 2) := by
      have h : IntervalIntegrable (log ∘ log) MeasureTheory.volume 1 2 := by
        apply MeromorphicOn.intervalIntegrable_log
        intro x hx
        rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)] at hx
        exact (analyticAt_log (by linarith [hx.1] : 0 < x)).meromorphicAt
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp h
    have hmul : MeasureTheory.IntegrableOn (fun x => x ^ (-s) * log (log x)) (Set.Ioc 1 2) := by
      apply hll.bdd_mul (c := 1)
      · fun_prop
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
        rw [norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith [hx.1] : (0:ℝ) ≤ x) _)]
        calc x ^ (-s) ≤ (1:ℝ) ^ (-s) :=
              Real.rpow_le_rpow_of_nonpos (by norm_num) hx.1.le (by linarith)
          _ = 1 := Real.one_rpow _
    simpa [mul_comm] using hmul
  ·                                                                                                
    set ε := (s - 1) / 2 with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    refine integrableOn_Ioi_mul_rpow_neg_of_abs_le (a := ε) (B := 1 / ε + |log (log 2)|)
      (by norm_num) (by rw [hε]; linarith) (Real.measurable_log.comp Real.measurable_log) ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hx1 : (1:ℝ) ≤ x ^ ε := Real.one_le_rpow (by linarith) hεpos.le
    have hlogx : 0 < log x := Real.log_pos (by linarith)
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
    have hmono : log 2 ≤ log x := Real.log_le_log (by norm_num) (by linarith)
    have hub : log (log x) ≤ x ^ ε / ε :=
      calc log (log x) ≤ log x := (Real.log_le_sub_one_of_pos hlogx).trans (by linarith)
        _ ≤ x ^ ε / ε := Real.log_le_rpow_div (by linarith) hεpos
    have hlb : log (log 2) ≤ log (log x) := Real.log_le_log hlog2 hmono
    have hxε : 0 ≤ x ^ ε / ε := by positivity
    calc |log (log x)| ≤ x ^ ε / ε + |log (log 2)| := by
          rw [abs_le]
          exact ⟨by linarith [neg_abs_le (log (log 2))],
            by linarith [abs_nonneg (log (log 2))]⟩
      _ ≤ (1 / ε + |log (log 2)|) * x ^ ε := by
          have h2 : |log (log 2)| ≤ |log (log 2)| * x ^ ε := le_mul_of_one_le_right (abs_nonneg _) hx1
          have h1 : x ^ ε / ε = 1 / ε * x ^ ε := by ring
          rw [add_mul]; linarith

private theorem integrableOn_γ_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => γ * x ^ (-s)) (Set.Ioi 1) := by
  exact (integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) one_pos).const_mul γ

private theorem integrableOn_E₂Λ_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => E₂Λ x * x ^ (-s)) (Set.Ioi 1) := by
  rw [← Set.Ioo_union_Ici_eq_Ioi (by norm_num : (1:ℝ) < 2)]
  apply MeasureTheory.IntegrableOn.union
  ·                                                                        
    have hsub : Set.Ioo (1:ℝ) 2 ⊆ Set.Ioi 1 := fun x hx => hx.1
    have h1 := (integrableOn_γ_mul_rpow s hs).mono_set hsub
    have h2 := (integrableOn_log_log_mul_rpow s hs).mono_set hsub
    have hb : MeasureTheory.IntegrableOn
        (fun x => -(log (log x) * x ^ (-s)) - γ * x ^ (-s)) (Set.Ioo 1 2) :=
      h2.neg.sub h1
    apply hb.congr_fun _ measurableSet_Ioo
    intro x hx
    simp only [Set.mem_Ioo] at hx
    have hfloor : ⌊ x ⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by linarith)]
      exact ⟨by push_cast <;> linarith [hx.1], by push_cast <;> linarith [hx.2]⟩
    have hsum : (∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / ((d:ℝ) * log d)) = 0 := by rw [hfloor]; norm_num
    change -(log (log x) * x ^ (-s)) - γ * x ^ (-s)
        = (∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - γ) * x ^ (-s)
    rw [hsum]; ring
  ·                                                                                              
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine integrableOn_Ioi_mul_rpow_neg_of_abs_le (a := 0) (B := (log 4 + 6) / log 2)
      (by norm_num) (by linarith) (by fun_prop) ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
    have hc : 0 ≤ log 4 + 6 := by positivity
    rw [Real.rpow_zero, mul_one]
    have hb2 : (log 4 + 6) / log x ≤ (log 4 + 6) / log 2 :=
      div_le_div_of_nonneg_left hc hlog2 (Real.log_le_log (by norm_num) (le_of_lt hx))
    exact (E₂Λ.abs_le (le_of_lt hx)).trans hb2

private theorem log_zeta_eq (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = - log (s - 1) + deriv Gamma 1 + γ + (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x^(-s) := by
                                                          
  rw [log_zeta_eq_integ s hs]
                                                                                               
  have key : (∫ x in Set.Ioi 1, (log (log x) + γ + E₂Λ x) * x ^ (-s))
      = (∫ x in Set.Ioi 1, log (log x) * x ^ (-s))
        + (∫ x in Set.Ioi 1, γ * x ^ (-s))
        + (∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)) := by
    rw [← MeasureTheory.integral_add (integrableOn_log_log_mul_rpow s hs)
      (integrableOn_γ_mul_rpow s hs)]
    rw [← MeasureTheory.integral_add (f := fun x => log (log x) * x ^ (-s) + γ * x ^ (-s))
      (g := fun x => E₂Λ x * x ^ (-s))
      ((integrableOn_log_log_mul_rpow s hs).add (integrableOn_γ_mul_rpow s hs))
      (integrableOn_E₂Λ_mul_rpow s hs)]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x _
    ring
                                                                
  rw [key, mul_add, mul_add, mul_integ_log_log_eq s hs, mul_integ_gamma_eq s hs]

private lemma zeta_pole_mul_re_tendsto_one :
    Filter.Tendsto (fun s : ℝ => (s - 1) * (riemannZeta (s : ℂ)).re)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
  have hofReal :
      Filter.Tendsto (fun s : ℝ => (s : ℂ)) (nhdsWithin 1 (Set.Ioi 1))
        (nhdsWithin (1 : ℂ) ({1} : Set ℂ)ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact Set.mem_compl_singleton_iff.mpr (by
        norm_num
        exact ne_of_gt (Set.mem_Ioi.mp hs))
  have hcomplex :
      Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) * riemannZeta (s : ℂ))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) :=
    riemannZeta_residue_one.comp hofReal
  have hreal :
      Filter.Tendsto
        (fun s : ℝ => (((s : ℂ) - 1) * riemannZeta (s : ℂ)).re)
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 : ℝ)) :=
    (Complex.continuous_re.tendsto (1 : ℂ)).comp hcomplex
  simpa [Complex.ofReal_sub, Complex.ofReal_mul] using hreal

private theorem log_zeta_limit :
    Filter.Tendsto
      (fun s : ℝ => Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  have hlog :
      Filter.Tendsto
        (fun s : ℝ => Real.log ((s - 1) * (riemannZeta (s : ℂ)).re))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (Real.log 1)) :=
    (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
      zeta_pole_mul_re_tendsto_one
  have hEq :
      (fun s : ℝ => Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1))
        =ᶠ[nhdsWithin 1 (Set.Ioi 1)]
      fun s : ℝ => Real.log ((s - 1) * (riemannZeta (s : ℂ)).re) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hspos : 0 < s - 1 := sub_pos.mpr (Set.mem_Ioi.mp hs)
    have hzpos : 0 < (riemannZeta (s : ℂ)).re :=
      riemannZeta_re_pos_of_one_lt (Set.mem_Ioi.mp hs)
    rw [Real.log_mul hspos.ne' hzpos.ne']
    ring
  simpa using hlog.congr' (hEq.mono fun s hs => hs.symm)

section
open _root_.MeasureTheory _root_.Set

private lemma measurable_E₂Λ : Measurable E₂Λ := by fun_prop

private lemma E₂Λ_eq_on_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1 : ℝ) 2) :
    E₂Λ x = - log (log x) - γ := by
  obtain ⟨h1, h2⟩ := hx
  have hf : ⌊x⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by linarith)]
    exact ⟨by exact_mod_cast h1.le, by exact_mod_cast h2⟩
  unfold E₂Λ
  rw [hf]
  simp

private lemma abs_E₂Λ_le_on_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1 : ℝ) 2) :
    |E₂Λ x| ≤ |log (x - 1)| + log 2 + |γ| := by
  obtain ⟨hx1, hx2⟩ := hx
  have hloglog : |log (log x)| ≤ |log (x - 1)| + log 2 := by
    have hxpos : (0:ℝ) < x := by linarith
    have hlogx_pos : 0 < log x := Real.log_pos hx1
    have hxm1 : 0 < x - 1 := by linarith
    have hub : log x ≤ x - 1 := by have := Real.log_le_sub_one_of_pos hxpos; linarith
    have hlb2 : (x - 1) / 2 ≤ log x := by
      have h := Real.log_le_sub_one_of_pos (x := 1 / x) (by positivity)
      rw [Real.log_div one_ne_zero (by positivity), Real.log_one] at h
      simp only [zero_sub] at h
      have h12 : (x - 1) / 2 ≤ 1 - 1 / x := by
        rw [← sub_nonneg]
        have e : (1 - 1 / x) - (x - 1) / 2 = (3 * x - 2 - x ^ 2) / (2 * x) := by field_simp <;> ring
        rw [e]; exact div_nonneg (by nlinarith [hx1, hx2]) (by positivity)
      linarith
    have hupper : log (log x) ≤ log (x - 1) := Real.log_le_log hlogx_pos hub
    have hlower : log (x - 1) - log 2 ≤ log (log x) := by
      have := Real.log_le_log (show (0:ℝ) < (x - 1) / 2 by positivity) hlb2
      rwa [Real.log_div (by linarith) (by norm_num)] at this
    have h2 : (0:ℝ) ≤ log 2 := Real.log_nonneg (by norm_num)
    rw [abs_le]
    exact ⟨by have := neg_abs_le (log (x - 1)); linarith,
          by have := le_abs_self (log (x - 1)); linarith⟩
  rw [E₂Λ_eq_on_Ioo ⟨hx1, hx2⟩]
  have htri : |(- log (log x) - γ)| ≤ |log (log x)| + |γ| := by
    have h := abs_sub (-log (log x)) γ
    rwa [abs_neg] at h
  linarith

private lemma abs_E₂Λ_le_const {x : ℝ} (hx : 2 ≤ x) :
    |E₂Λ x| ≤ (log 4 + 6) / log 2 :=
  (E₂Λ.abs_le hx).trans <| div_le_div_of_nonneg_left (by positivity)
    (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) hx)

private lemma integrableOn_log_sub_one_bound :
    IntegrableOn (fun x => |log (x - 1)| + log 2 + |γ|) (Set.Ioo 1 2) volume := by
  have hlog : IntegrableOn (fun x => |log (x - 1)|) (Set.Ioo 1 2) volume := by
    have h0 : IntervalIntegrable (fun x => log x) volume 0 1 :=
      intervalIntegral.intervalIntegrable_log'
    have h1 : IntervalIntegrable (fun x => log (x - 1)) volume (0 + 1) (1 + 1) :=
      h0.comp_sub_right 1
    norm_num at h1
    exact (h1.1.mono_set Set.Ioo_subset_Ioc_self).abs
  have hc : IntegrableOn (fun _ : ℝ => log 2 + |γ|) (Set.Ioo (1 : ℝ) 2) volume :=
    integrableOn_const (measure_Ioo_lt_top).ne (by finiteness)
  have hsum : IntegrableOn (fun x => |log (x - 1)| + (log 2 + |γ|)) (Set.Ioo 1 2) volume :=
    hlog.add hc
  exact hsum.congr_fun (fun x _ => by ring) measurableSet_Ioo

private lemma integrableOn_E₂Λ_Ioo {X : ℝ} (_hX : 2 ≤ X) :
    IntegrableOn E₂Λ (Set.Ioo 1 X) volume := by
  have hsub : Set.Ioo (1 : ℝ) X ⊆ Set.Ioo 1 2 ∪ Set.Icc 2 X := by
    intro x hx; simp only [Set.mem_Ioo, Set.mem_union, Set.mem_Icc] at *
    rcases lt_or_ge x 2 with h | h
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨h, hx.2.le⟩
  apply IntegrableOn.mono_set _ hsub
  apply IntegrableOn.union
  · have hg := integrableOn_log_sub_one_bound
    refine Integrable.mono' hg measurable_E₂Λ.aestronglyMeasurable ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs]; exact abs_E₂Λ_le_on_Ioo hx
  · refine Integrable.mono' (g := fun _ => (log 4 + 6) / log 2) ?_
      measurable_E₂Λ.aestronglyMeasurable ?_
    · exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by finiteness)
    · filter_upwards [self_mem_ae_restrict measurableSet_Icc] with x hx
      rw [Real.norm_eq_abs]; exact abs_E₂Λ_le_const hx.1

private lemma sub_one_mul_integral_E₂Λ_tendsto :
    Filter.Tendsto (fun s : ℝ => (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
                                                                           
  obtain ⟨X₀, hX₀⟩ : ∃ X, ∀ x ≥ X, |E₂Λ x| ≤ ε / 2 := by
    have := E₂Λ.bound'.def (by positivity : (0:ℝ) < ε / 2)
    simp only [Real.norm_eq_abs, abs_one, mul_one] at this
    rw [Filter.eventually_atTop] at this; exact this
  set X := max X₀ 2 with hXdef
  have hX2 : 2 ≤ X := le_max_right _ _
  have hXge : ∀ x ≥ X, |E₂Λ x| ≤ ε / 2 := fun x hx => hX₀ x (le_trans (le_max_left _ _) hx)
                                                     
  set B := ∫ x in Set.Ioo 1 X, |E₂Λ x| with hBdef
  have hB0 : 0 ≤ B := setIntegral_nonneg measurableSet_Ioo (fun x _ => abs_nonneg _)
  refine ⟨min 1 (ε / 2 / (B + 1)), by positivity, ?_⟩
  intro s hs hdist
  simp only [Set.mem_Ioi] at hs
  rw [Real.dist_eq] at hdist
  have hs1 : s - 1 < min 1 (ε / 2 / (B + 1)) := by
    rw [abs_of_pos (by linarith)] at hdist; exact hdist
  have hsm1 : 0 < s - 1 := by linarith
                                                                  
  have hintAbs : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioi 1) volume := by
    have h2 : IntegrableOn (fun x => |E₂Λ x * x ^ (-s)|) (Set.Ioi 1) volume :=
      (integrableOn_E₂Λ_mul_rpow s hs).abs
    refine h2.congr_fun ?_ measurableSet_Ioi
    intro x hx; simp only [Set.mem_Ioi] at hx
    change |E₂Λ x * x ^ (-s)| = |E₂Λ x| * x ^ (-s)
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  have hintAbsIoc : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioc 1 X) volume :=
    hintAbs.mono_set Set.Ioc_subset_Ioi_self
  have hintAbsIoiX : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioi X) volume :=
    hintAbs.mono_set (Set.Ioi_subset_Ioi (by linarith))
                                               
  have hsplit : ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) =
      (∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s)) + ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) := by
    have hu : Set.Ioi (1:ℝ) = Set.Ioc 1 X ∪ Set.Ioi X :=
      (Set.Ioc_union_Ioi_eq_Ioi (by linarith)).symm
    rw [hu, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hintAbs.mono_set (by rw [hu]; exact Set.subset_union_left))
      (hintAbs.mono_set (by rw [hu]; exact Set.subset_union_right))]
                                                                 
  have hp1 : ∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s) ≤ B := by
    rw [hBdef]
    have ha : IntegrableOn (fun x => |E₂Λ x|) (Set.Ioo 1 X) volume := (integrableOn_E₂Λ_Ioo hX2).abs
    have habsIoc : IntegrableOn (fun x => |E₂Λ x|) (Set.Ioc 1 X) volume :=
      ha.congr_set_ae (Ioo_ae_eq_Ioc).symm
    rw [← integral_Ioc_eq_integral_Ioo]
    apply setIntegral_mono_on hintAbsIoc habsIoc measurableSet_Ioc
    intro x hx
    have hx1 : (1:ℝ) ≤ x := by have := hx.1; linarith
    have hle1 : x ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    calc |E₂Λ x| * x ^ (-s) ≤ |E₂Λ x| * 1 := by gcongr
      _ = |E₂Λ x| := mul_one _
                                                                                
  have hp2 : ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) ≤ (ε / 2) * (X ^ (1 - s) / (s - 1)) := by
    have hrpow_int : IntegrableOn (fun x : ℝ => x ^ (-s)) (Set.Ioi X) volume :=
      integrableOn_Ioi_rpow_of_lt (by linarith) (by linarith : (0:ℝ) < X)
    have hval : ∫ x in Set.Ioi X, x ^ (-s) = X ^ (1 - s) / (s - 1) := by
      rw [integral_Ioi_rpow_of_lt (by linarith) (by linarith : (0:ℝ) < X),
        show -s + 1 = 1 - s by ring, show (1:ℝ) - s = -(s - 1) by ring]
      rw [div_neg, neg_div, neg_neg]
    rw [← hval, ← integral_const_mul]
    apply setIntegral_mono_on hintAbsIoiX (hrpow_int.const_mul (ε / 2)) measurableSet_Ioi
    intro x hx
    have hxpos : (0:ℝ) < x := by simp only [Set.mem_Ioi] at hx <;> linarith
    have hnn : 0 ≤ x ^ (-s) := Real.rpow_nonneg hxpos.le _
    have hb : |E₂Λ x| ≤ ε / 2 := hXge x (by simp only [Set.mem_Ioi] at hx <;> linarith)
    gcongr
  have hXpow : X ^ (1 - s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
                                                     
  have hbound : (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) ≤ (s - 1) * B + ε / 2 := by
    rw [hsplit, mul_add]
    have ht2 : (s - 1) * ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) ≤ ε / 2 := by
      calc (s - 1) * ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s)
          ≤ (s - 1) * ((ε / 2) * (X ^ (1 - s) / (s - 1))) :=
            mul_le_mul_of_nonneg_left hp2 hsm1.le
        _ = (ε / 2) * X ^ (1 - s) := by
              have hne : s - 1 ≠ 0 := by linarith
              field_simp
        _ ≤ (ε / 2) * 1 := by gcongr
        _ = ε / 2 := mul_one _
    have ht1 : (s - 1) * ∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s) ≤ (s - 1) * B :=
      mul_le_mul_of_nonneg_left hp1 hsm1.le
    linarith
                                                  
  have habs_le : |(s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)|
      ≤ (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) := by
    rw [abs_mul, abs_of_pos hsm1]
    gcongr
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    simp only [Set.mem_Ioi] at hx
    change ‖E₂Λ x * x ^ (-s)‖ = |E₂Λ x| * x ^ (-s)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  rw [Real.dist_eq, sub_zero]
                                                   
  have hfin : (s - 1) * B + ε / 2 < ε := by
    have hlt : s - 1 < ε / 2 / (B + 1) := lt_of_lt_of_le hs1 (min_le_right _ _)
    have hBp : 0 < B + 1 := by linarith
    have h1 : (s - 1) * B ≤ (s - 1) * (B + 1) := by nlinarith
    have h2 : (s - 1) * (B + 1) < (ε / 2 / (B + 1)) * (B + 1) := mul_lt_mul_of_pos_right hlt hBp
    have h3 : (ε / 2 / (B + 1)) * (B + 1) = ε / 2 := by field_simp
    linarith
  calc |(s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)|
      ≤ (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) := habs_le
    _ ≤ (s - 1) * B + ε / 2 := hbound
    _ < ε := hfin

end

theorem deriv_gamma_add_γ_eq_zero : deriv Gamma 1 + γ = 0 := by
                                                                  
  have key : ∀ s : ℝ, 1 < s →
      (Real.log (riemannZeta (s:ℂ)).re + Real.log (s - 1))
        - (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s) = deriv Gamma 1 + γ := by
    intro s hs
    have h := log_zeta_eq s hs
    linarith
                                                                   
  have hconst : Filter.Tendsto
      (fun s : ℝ => (Real.log (riemannZeta (s:ℂ)).re + Real.log (s - 1))
        - (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (deriv Gamma 1 + γ)) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (key s hs).symm
                                                                    
  have hlim := log_zeta_limit.sub sub_one_mul_integral_E₂Λ_tendsto
  rw [sub_zero] at hlim
  exact tendsto_nhds_unique hconst hlim

theorem γ.eq_eulerMascheroni : γ = eulerMascheroniConstant := by
  linarith [Real.eulerMascheroniConstant_eq_neg_deriv, deriv_gamma_add_γ_eq_zero]

theorem E₂p.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂p x = E₁p x / log x - ∫ t in Set.Ioi x, E₁p t / (t * log t^2) := by
  unfold E₂p
  rw [sum_filter, ← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp [Nat.not_prime_one])]
  have (n : ℕ) : (if Nat.Prime n then (1 : ℝ) / n else 0) = (if Nat.Prime n then log n / n else 0) / log n := by
    split_ifs with h
    · have : log n ≠ 0 := by simp; grind [h.two_le]
      field
    · simp
  simp_rw [this]
  rw [sum_div_log_eq hx, sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter]
  rw [sum_log_prime_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, if Nat.Prime n then log ↑n / ↑n else 0) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁p t / (t * log t ^2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top), ← sum_filter, sum_log_prime_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold M
    calc
    _ = E₁p x / log x + (∫ (x : ℝ) in 2..x, E₁p x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁p t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁p_div_mul_log_sq (by rfl)) (integrable_E₁p_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁p_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

theorem E₂p.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂p x| ≤ (log 4 + 6 + E₁) / log x := by
    have : 0 < log x := by apply _root_.Real.log_pos; linarith
    rw [E₂p.eq hx, abs_le']
    constructor
    · grw [E₁p.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≥ (- 2 - E₁) / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2 - E₁) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2 - E₁) hx)
            (integrable_E₁p_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := _root_.Real.log_pos this
          gcongr; exact E₁p.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2 - E₁) hx
      grw [this]
      grind
    grw [E₁p.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁p_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := _root_.Real.log_pos this
          gcongr; exact E₁p.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind

theorem E₂p.bound : E₂p =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [one_div, isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop]
    use log 4 + 6 + E₁, 2
    intro x hx
    convert (preTransparency := .instances) E₂p.abs_le hx using 1
    all_goals try with_reducible_and_instances rfl
    have : 0 < log x := by apply _root_.Real.log_pos; linarith
    grind [abs_of_pos this]

theorem E₂p.bound' : E₂p =o[atTop] (fun _ ↦ (1:ℝ)) := E₂p.bound.trans_isLittleO inv_log_eq_o_one

theorem prod_one_minus_div_prime_eq {x : ℝ} (hx : 1 < x) :
    ∏ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 - (1 : ℝ) / p) =
      exp (-eulerMascheroniConstant) * exp (E₃ x) / log x := by
  have hlog : 0 < log x := _root_.Real.log_pos hx
  have hpos : ∀ {p : ℕ}, p.Prime → (0 : ℝ) < 1 - 1 / p := fun {p} hp ↦ by
    have : (2 : ℝ) ≤ p := mod_cast hp.two_le
    grind [one_div_le_one_div_of_le two_pos this]
  rw [E₃, exp_add, exp_add, exp_sum, exp_log hlog, exp_neg,
    prod_congr rfl fun p hp ↦ exp_log (hpos (mem_filter.mp hp).2)]
  field_simp

lemma sum_M_eq_summand_le' {x : ℝ} (hx : 2 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_summand n - (M - γ)| ≤ 4 / x := by
  have := sum_M_eq_summand_le_jb247 (by grind : 0 < ⌊x⌋₊ + 1)
  rw [Nat.range_eq_Icc_zero_sub_one _ (by grind), ← add_sum_Ioc_eq_sum_Icc (by grind),
    (by simp : M_eq_summand 0 = 0), zero_add] at this
  simp only [add_tsub_cancel_right, Nat.cast_add, Nat.cast_one] at this
  grw [this]
  gcongr
  exact Nat.lt_floor_add_one _|>.le

theorem E₃.abs_le : ∃ C, ∀ x, 2 ≤ x → |E₃ x| ≤ C / log x := by
  unfold E₃
  refine ⟨4 + (log 4 + 6 + E₁), fun x hx ↦ ?_⟩
  calc
  _ = |(∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_summand n - (M - γ)) - E₂p x| := by
    unfold E₂p
    have (n : ℕ) : M_eq_summand n = (if n.Prime then log (1 - 1 / n) else 0) + (if n.Prime then (1 : ℝ) / n else 0) := by
      unfold M_eq_summand
      split_ifs
      · rfl
      · ring
    simp_rw [this]
    rw [sum_filter, sum_filter, sum_add_distrib, γ.eq_eulerMascheroni]
    ring_nf
  _ ≤ _ := by
    grw [abs_sub, E₂p.abs_le hx, sum_M_eq_summand_le' hx]
    have : 4 / x ≤ 4 / log x := by
      gcongr
      · exact _root_.Real.log_pos (by linarith)
      · exact log_le_self (by linarith)
    grw [this]
    rw [← add_div]

theorem E₃.bound : E₃ =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [isBigO_iff, norm_eq_abs, eventually_atTop]
    obtain ⟨ C, hC ⟩ := E₃.abs_le
    use C, 2
    convert (preTransparency := .instances) hC using 3 with x hx
    have : 0 < log x := by apply _root_.Real.log_pos; linarith
    have : 0 < 1 / log x := by positivity
    grind [abs_of_pos this]

theorem E₃.bound' : E₃ =o[atTop] (fun _ ↦ (1:ℝ)) := E₃.bound.trans_isLittleO inv_log_eq_o_one

end Mertens

end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_BoundedOrderIntervals
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory
namespace ErdosMonotoneQuadrature

theorem bounded_orderConnected_interval {S : Set ℝ} {u v : ℝ}
    (hS : S.OrdConnected) (hne : S.Nonempty) (hsub : S ⊆ Icc u v) :
    ∃ a b : ℝ, u ≤ a ∧ a ≤ b ∧ b ≤ v ∧
      (S = Icc a b ∨ S = Ico a b ∨ S = Ioc a b ∨ S = Ioo a b) := by
  have hb : BddBelow S := ⟨u,fun x hx => (hsub hx).1⟩
  have ha : BddAbove S := ⟨v,fun x hx => (hsub hx).2⟩
  have hu : u ≤ sInf S := le_csInf hne (fun x hx => (hsub hx).1)
  have hv : sSup S ≤ v := csSup_le hne (fun x hx => (hsub hx).2)
  obtain ⟨x,hx⟩ := hne
  have hab : sInf S ≤ sSup S := (csInf_le hb hx).trans (le_csSup ha hx)
  have hc : IsConnected S := ⟨⟨x,hx⟩,hS.isPreconnected⟩
  have hi := mem_Icc_Ico_Ioc_Ioo_of_subset_of_subset
    (hc.Ioo_csInf_csSup_subset hb ha) (subset_Icc_csInf_csSup hb ha)
  exact ⟨sInf S,sSup S,hu,hab,hv,hi⟩

theorem orderConnected_measure_discrepancy (μ ν : Measure ℝ) (u v E : ℝ)
    (hE : 0 ≤ E)
    (hinterval : ∀ a b : ℝ, u ≤ a → a ≤ b → b ≤ v →
      |μ.real (Icc a b)-ν.real (Icc a b)| ≤ E ∧
      |μ.real (Ico a b)-ν.real (Ico a b)| ≤ E ∧
      |μ.real (Ioc a b)-ν.real (Ioc a b)| ≤ E ∧
      |μ.real (Ioo a b)-ν.real (Ioo a b)| ≤ E)
    {S : Set ℝ} (hS : S.OrdConnected) (hsub : S ⊆ Icc u v) :
    |μ.real S-ν.real S| ≤ E := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simpa using hE
  obtain ⟨a,b,hu,hab,hv,he⟩ := bounded_orderConnected_interval hS hne hsub
  obtain ⟨hcc,hco,hoc,hoo⟩ := hinterval a b hu hab hv
  rcases he with rfl | rfl | rfl | rfl
  · exact hcc
  · exact hco
  · exact hoc
  · exact hoo

end ErdosMonotoneQuadrature

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_WeightedMonotoneBound
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open MeasureTheory Set
namespace ErdosMonotoneQuadrature

theorem integrable_layercake_discrepancy
    {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : α → ℝ) (K E : ℝ) (hK : 0 ≤ K)
    (hfm : Integrable f μ) (hfn : Integrable f ν)
    (hloμ : 0 ≤ᵐ[μ] f) (hloν : 0 ≤ᵐ[ν] f)
    (hhiμ : f ≤ᵐ[μ] (fun _ => K)) (hhiν : f ≤ᵐ[ν] (fun _ => K))
    (hd : ∀ t ∈ Ioc 0 K, |μ.real {x | t ≤ f x} - ν.real {x | t ≤ f x}| ≤ E) :
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ E*K := by
  have hm : Antitone (fun t : ℝ => μ.real {x | t ≤ f x}) := by
    intro s t hst
    exact measureReal_mono (fun x hx => hst.trans hx)
  have hn : Antitone (fun t : ℝ => ν.real {x | t ≤ f x}) := by
    intro s t hst
    exact measureReal_mono (fun x hx => hst.trans hx)
  have him : IntegrableOn (fun t : ℝ => μ.real {x | t ≤ f x}) (Ioc 0 K) :=
    ((hm.antitoneOn (Icc 0 K)).integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hin : IntegrableOn (fun t : ℝ => ν.real {x | t ≤ f x}) (Ioc 0 K) :=
    ((hn.antitoneOn (Icc 0 K)).integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self
  rw [hfm.integral_eq_integral_Ioc_meas_le hloμ hhiμ,
    hfn.integral_eq_integral_Ioc_meas_le hloν hhiν, ← integral_sub him hin]
  calc
    _ ≤ ∫ t in Ioc 0 K, |μ.real {x | t ≤ f x} - ν.real {x | t ≤ f x}| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _t in Ioc 0 K, E := integral_mono_ae (him.sub hin).abs (integrable_const E)
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun t ht => hd t ht))
    _ = E*K := by simp [Real.volume_real_Ioc,max_eq_left hK,mul_comm]

theorem monotone_level_orderConnected {f : ℝ → ℝ} {J : Set ℝ}
    (hJ : J.OrdConnected) (hf : MonotoneOn f J ∨ AntitoneOn f J) (t : ℝ) :
    ({x | t ≤ f x} ∩ J).OrdConnected := by
  constructor
  intro x hx y hy z hz
  have hzJ : z ∈ J := hJ.out hx.2 hy.2 hz
  refine ⟨?_,hzJ⟩
  rcases hf with hm | ha
  · exact hx.1.trans (hm hx.2 hzJ hz.1)
  · exact hy.1.trans (ha hzJ hy.2 hz.2)

theorem nonnegative_monotone_integral_discrepancy
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (u v K E : ℝ) (hK : 0 ≤ K) (f : ℝ → ℝ)
    (hf : MonotoneOn f (Icc u v) ∨ AntitoneOn f (Icc u v))
    (hlo : ∀ x ∈ Icc u v, 0 ≤ f x) (hhi : ∀ x ∈ Icc u v, f x ≤ K)
    (hd : ∀ S : Set ℝ, S.OrdConnected → S ⊆ Icc u v → |μ.real S-ν.real S| ≤ E)
    {J : Set ℝ} (hJ : J.OrdConnected) (hsub : J ⊆ Icc u v) :
    |(∫ x in J, f x ∂μ) - ∫ x in J, f x ∂ν| ≤ E*K := by
  have hfm : IntegrableOn f (Icc u v) μ := by
    rcases hf with hm | ha
    · exact hm.integrableOn_isCompact isCompact_Icc
    · exact ha.integrableOn_isCompact isCompact_Icc
  have hfn : IntegrableOn f (Icc u v) ν := by
    rcases hf with hm | ha
    · exact hm.integrableOn_isCompact isCompact_Icc
    · exact ha.integrableOn_isCompact isCompact_Icc
  have hflocal : MonotoneOn f J ∨ AntitoneOn f J := hf.elim
    (fun hm => Or.inl (hm.mono hsub)) (fun ha => Or.inr (ha.mono hsub))
  apply integrable_layercake_discrepancy (μ.restrict J) (ν.restrict J) f K E hK
    (hfm.mono_set hsub) (hfn.mono_set hsub)
  · exact (ae_restrict_iff' hJ.measurableSet).mpr
      (Filter.Eventually.of_forall fun x hx => hlo x (hsub hx))
  · exact (ae_restrict_iff' hJ.measurableSet).mpr
      (Filter.Eventually.of_forall fun x hx => hlo x (hsub hx))
  · exact (ae_restrict_iff' hJ.measurableSet).mpr
      (Filter.Eventually.of_forall fun x hx => hhi x (hsub hx))
  · exact (ae_restrict_iff' hJ.measurableSet).mpr
      (Filter.Eventually.of_forall fun x hx => hhi x (hsub hx))
  · intro t _ht
    rw [measureReal_restrict_apply' hJ.measurableSet,measureReal_restrict_apply' hJ.measurableSet]
    exact hd _ (monotone_level_orderConnected hJ hflocal t) (fun x hx => hsub hx.2)

end ErdosMonotoneQuadrature

end

section

open MeasureTheory Set
namespace ErdosMonotoneQuadrature

theorem reciprocalWeight_pos {u : ℝ} (hu : 0 < u) (x : ℝ) :
    0 < reciprocalWeight u x := inv_pos.mpr (hu.trans_le (le_max_left _ _))

theorem reciprocalWeight_le {u : ℝ} (hu : 0 < u) (x : ℝ) :
    reciprocalWeight u x ≤ u⁻¹ := inv_anti₀ hu (le_max_left _ _)

theorem reciprocalWeight_continuous {u : ℝ} (hu : 0 < u) :
    Continuous (reciprocalWeight u) :=
  (continuous_const.max continuous_id).inv₀ (fun x => ne_of_gt (hu.trans_le (le_max_left u x)))

theorem reciprocalWeight_eq {u x : ℝ} (hx : u ≤ x) : reciprocalWeight u x=x⁻¹ := by
  simp only [reciprocalWeight,max_eq_right hx]

theorem reciprocalMeasure_finite (μ : Measure ℝ) [IsFiniteMeasure μ] {u : ℝ} (hu : 0 < u) :
    IsFiniteMeasure (reciprocalMeasure μ u) := by
  have h : Integrable (reciprocalWeight u) μ :=
    Integrable.of_bound (reciprocalWeight_continuous hu).measurable.aestronglyMeasurable u⁻¹
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs,abs_of_pos (reciprocalWeight_pos hu x)] using reciprocalWeight_le hu x)
  exact isFiniteMeasure_withDensity_ofReal h.hasFiniteIntegral

theorem reciprocalMeasure_integral (μ : Measure ℝ) {u : ℝ} (hu : 0 < u)
    (g : ℝ → ℝ) {J : Set ℝ} (hJ : MeasurableSet J) :
    (∫ x in J, g x ∂reciprocalMeasure μ u) = ∫ x in J, reciprocalWeight u x*g x ∂μ := by
  have h := setIntegral_withDensity_eq_setIntegral_toReal_smul
    (μ:=μ) ((reciprocalWeight_continuous hu).measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) g hJ
  simpa only [reciprocalMeasure,ENNReal.toReal_ofReal (reciprocalWeight_pos hu _).le,smul_eq_mul] using h

theorem reciprocalMeasure_real (μ : Measure ℝ) {u : ℝ} (hu : 0 < u)
    {J : Set ℝ} (hJ : MeasurableSet J) :
    (reciprocalMeasure μ u).real J = ∫ x in J, reciprocalWeight u x ∂μ := by
  simpa only [integral_const,smul_eq_mul,mul_one,measureReal_restrict_apply_univ] using
    reciprocalMeasure_integral μ hu (fun _ => (1:ℝ)) hJ

end ErdosMonotoneQuadrature

end

section

open MeasureTheory Set
namespace ErdosMonotoneQuadrature

theorem signed_monotone_integral_discrepancy
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (u v D E : ℝ) (hD : 0 ≤ D) (g : ℝ → ℝ)
    (hg : MonotoneOn g (Icc u v) ∨ AntitoneOn g (Icc u v))
    (hbound : ∀ x ∈ Icc u v, |g x| ≤ D)
    (hd : ∀ S : Set ℝ, S.OrdConnected → S ⊆ Icc u v → |μ.real S-ν.real S| ≤ E)
    {J : Set ℝ} (hJ : J.OrdConnected) (hsub : J ⊆ Icc u v) :
    |(∫ x in J, g x ∂μ) - ∫ x in J, g x ∂ν| ≤ 3*E*D := by
  have hgm : IntegrableOn g J μ := by
    rcases hg with hm | ha
    · exact (hm.integrableOn_isCompact isCompact_Icc).mono_set hsub
    · exact (ha.integrableOn_isCompact isCompact_Icc).mono_set hsub
  have hgn : IntegrableOn g J ν := by
    rcases hg with hm | ha
    · exact (hm.integrableOn_isCompact isCompact_Icc).mono_set hsub
    · exact (ha.integrableOn_isCompact isCompact_Icc).mono_set hsub
  have hshift : MonotoneOn (fun x => g x+D) (Icc u v) ∨
      AntitoneOn (fun x => g x+D) (Icc u v) := by
    rcases hg with hm | ha
    · exact Or.inl (fun x hx y hy hxy => by dsimp <;> linarith [hm hx hy hxy])
    · exact Or.inr (fun x hx y hy hxy => by dsimp <;> linarith [ha hx hy hxy])
  have hpos : ∀ x ∈ Icc u v, 0 ≤ g x+D := by
    intro x hx
    have h := (abs_le.mp (hbound x hx)).1
    linarith
  have hhi : ∀ x ∈ Icc u v, g x+D ≤ 2*D := by
    intro x hx
    have h := (abs_le.mp (hbound x hx)).2
    linarith
  have h := nonnegative_monotone_integral_discrepancy μ ν u v (2*D) E
    (by positivity) (fun x => g x+D) hshift hpos hhi hd hJ hsub
  have heq : (∫ x in J, g x ∂μ) - ∫ x in J, g x ∂ν =
      ((∫ x in J, g x+D ∂μ) - ∫ x in J, g x+D ∂ν) - D*(μ.real J-ν.real J) := by
    rw [integral_add hgm (integrable_const D),integral_add hgn (integrable_const D)]
    simp only [integral_const,smul_eq_mul,measureReal_restrict_apply_univ]
    ring
  rw [heq]
  calc
    _ ≤ |(∫ x in J, g x+D ∂μ) - ∫ x in J, g x+D ∂ν| + |D*(μ.real J-ν.real J)| :=
      abs_sub _ _
    _ ≤ E*(2*D) + D*E := add_le_add h (by
      rw [abs_mul,abs_of_nonneg hD]
      exact mul_le_mul_of_nonneg_left (hd J hJ hsub) hD)
    _ = 3*E*D := by ring

end ErdosMonotoneQuadrature

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_HighPrimeRemoval
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace ErdosPrimeInputs.MertensStrong

open _root_.Filter _root_.Asymptotics _root_.Finset
open scoped Topology
open PrimeAbel PrimeErrorDecay

lemma second_error_difference {a b : ℝ} (hab : a ≤ b) :
    _root_.Erdos970.Mertens.E₂p b - _root_.Erdos970.Mertens.E₂p a =
      reciprocalPrimes a b - (Real.log (Real.log b) - Real.log (Real.log a)) := by
  have h := Finset.sum_Ioc_consecutive
    (fun p : ℕ => if p.Prime then (p : ℝ)⁻¹ else 0) (Nat.zero_le ⌊a⌋₊) (Nat.floor_mono hab)
  unfold _root_.Erdos970.Mertens.E₂p reciprocalPrimes
  simp only [Finset.sum_filter, one_div] at *
  linarith

theorem second_error_strong : ∃ c C a₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < a₀ ∧
    ∀ a : ℝ, a₀ ≤ a → |_root_.Erdos970.Mertens.E₂p a| ≤ C * decay c a := by
  obtain ⟨c,C,a₀,hc,hC,ha₀,_,h⟩ := uniform_prime_interval_error
  refine ⟨c,C,a₀,hc,hC,ha₀,?_⟩
  intro a ha
  have ht : Tendsto _root_.Erdos970.Mertens.E₂p atTop (𝓝 0) := (isLittleO_one_iff ℝ).mp _root_.Erdos970.Mertens.E₂p.bound'
  have hb : |0 - _root_.Erdos970.Mertens.E₂p a| ≤ C * decay c a := by
    apply le_of_tendsto (ht.sub_const (_root_.Erdos970.Mertens.E₂p a)).abs
    filter_upwards [eventually_ge_atTop a] with b hab
    rw [second_error_difference hab]
    exact h a b ha hab
  simpa only [zero_sub, abs_neg] using hb

lemma reciprocal_le_decay {c x : ℝ} (hc : c ≤ 1) (hx : 0 < x) (hlog : 1 ≤ Real.log x) :
    1 / x ≤ decay c x := by
  have hs := Real.sqrt_nonneg (Real.log x)
  have hs2 := Real.sq_sqrt (show 0 ≤ Real.log x by linarith)
  have hsmall : Real.sqrt (Real.log x) ≤ Real.log x := by nlinarith
  have hexp : -Real.log x ≤ -c * Real.sqrt (Real.log x) := by nlinarith
  calc
    1 / x = Real.exp (-Real.log x) := by rw [Real.exp_neg, Real.exp_log hx, one_div]
    _ ≤ decay c x := Real.exp_le_exp.mpr hexp

lemma third_error_identity (x : ℝ) :
    _root_.Erdos970.Mertens.E₃ x =
      (∑ n ∈ Ioc 0 ⌊x⌋₊, _root_.Erdos970.Mertens.M_eq_summand n - 0) - (_root_.Erdos970.Mertens.M - _root_.Erdos970.Mertens.γ) - _root_.Erdos970.Mertens.E₂p x := by
  unfold _root_.Erdos970.Mertens.E₃ _root_.Erdos970.Mertens.E₂p
  have h (n : ℕ) : _root_.Erdos970.Mertens.M_eq_summand n =
      (if n.Prime then Real.log (1 - 1 / n) else 0) + (if n.Prime then (1 : ℝ) / n else 0) := by
    unfold _root_.Erdos970.Mertens.M_eq_summand
    split_ifs <;> ring
  simp_rw [sub_zero, h]
  rw [sum_filter, sum_filter, sum_add_distrib, _root_.Erdos970.Mertens.γ.eq_eulerMascheroni]
  ring

theorem third_error_strong : ∃ c C a₀ : ℝ, 0 < c ∧ 0 < C ∧ 2 ≤ a₀ ∧
    ∀ x : ℝ, a₀ ≤ x → |_root_.Erdos970.Mertens.E₃ x| ≤ C * decay c x := by
  obtain ⟨c,C,a₀,hc,hC,ha₀,h⟩ := second_error_strong
  let c' := min c 1
  let x₀ := max a₀ (Real.exp 1)
  have hc' : 0 < c' := lt_min hc zero_lt_one
  have hx₀ : 2 ≤ x₀ := (le_of_lt Real.exp_one_gt_two).trans (le_max_right _ _)
  refine ⟨c',C+4,x₀,hc',by positivity,hx₀,?_⟩
  intro x hx
  have hx2 : 2 ≤ x := hx₀.trans hx
  have hx0 : 0 < x := by linarith
  have hlog : 1 ≤ Real.log x := by
    have h' := Real.log_le_log (Real.exp_pos 1) ((le_max_right a₀ (Real.exp 1)).trans hx)
    simpa only [Real.log_exp] using h'
  have hd : decay c x ≤ decay c' x := by
    apply Real.exp_le_exp.mpr
    have := min_le_left c (1:ℝ)
    have := Real.sqrt_nonneg (Real.log x)
    dsimp [c']
    nlinarith
  rw [third_error_identity]
  simp only [sub_zero]
  calc
    _ ≤ |(∑ n ∈ Ioc 0 ⌊x⌋₊, _root_.Erdos970.Mertens.M_eq_summand n) - (_root_.Erdos970.Mertens.M - _root_.Erdos970.Mertens.γ)| + |_root_.Erdos970.Mertens.E₂p x| := abs_sub _ _
    _ ≤ 4 / x + C * decay c x := add_le_add (_root_.Erdos970.Mertens.sum_M_eq_summand_le' hx2) (h x ((le_max_left _ _).trans hx))
    _ ≤ 4 * decay c' x + C * decay c' x := by
      apply add_le_add
      · have hrec := reciprocal_le_decay (min_le_right c 1) hx0 hlog
        calc
          4 / x = 4 * (1/x) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hrec (by norm_num)
      · exact mul_le_mul_of_nonneg_left hd hC.le
    _ = (C+4) * decay c' x := by ring

theorem prime_product_strong : ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ 2 ≤ x₀ ∧
    ∀ x : ℝ, x₀ ≤ x →
      |primeProduct x / (Real.exp (-Real.eulerMascheroniConstant) / Real.log x) - 1| ≤
        C * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c,C,a₀,hc,hC,ha₀,h⟩ := third_error_strong
  have ht : Tendsto _root_.Erdos970.Mertens.E₃ atTop (𝓝 0) := (isLittleO_one_iff ℝ).mp _root_.Erdos970.Mertens.E₃.bound'
  have hs : ∀ᶠ x : ℝ in atTop, |_root_.Erdos970.Mertens.E₃ x| < 1 :=
    ht.abs.eventually (gt_mem_nhds (show |(0:ℝ)| < 1 by norm_num))
  obtain ⟨x₁,hx₁⟩ := eventually_atTop.mp hs
  refine ⟨c,2*C,max a₀ x₁,hc,by positivity,ha₀.trans (le_max_left _ _),?_⟩
  intro x hx
  have hxa := (le_max_left a₀ x₁).trans hx
  have hxx := (le_max_right a₀ x₁).trans hx
  have hx2 : 2 ≤ x := ha₀.trans hxa
  have hx1 : 1 < x := by linarith
  have hl : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
  have he : primeProduct x / (Real.exp (-Real.eulerMascheroniConstant) / Real.log x) =
      Real.exp (_root_.Erdos970.Mertens.E₃ x) := by
    rw [primeProduct, _root_.Erdos970.Mertens.prod_one_minus_div_prime_eq hx1]
    field_simp
  rw [he]
  calc
    _ ≤ 2 * |_root_.Erdos970.Mertens.E₃ x| := Real.abs_exp_sub_one_le (hx₁ x hxx).le
    _ ≤ 2 * (C * decay c x) := mul_le_mul_of_nonneg_left (h x hxa) (by norm_num)
    _ = _ := by unfold decay; ring

end ErdosPrimeInputs.MertensStrong



namespace ErdosPrimeInputs.PrimePrefixTail

open _root_.Finset
open PrimePrefixMass

lemma prefixWeight_nonneg (l : List ℕ) : 0 ≤ prefixWeight l := by
  unfold prefixWeight
  apply List.prod_nonneg
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  positivity

end ErdosPrimeInputs.PrimePrefixTail



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_HarmonicReferenceMeasure
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.HarmonicReferenceMeasure

open _root_.MeasureTheory _root_.Set
open ErdosMonotoneQuadrature ErdosPrimeInputs.PrimeEndpoints

theorem referenceMeasure_finite {u v : ℝ} (hu : 0 < u) : IsFiniteMeasure (referenceMeasure u v) :=
  reciprocalMeasure_finite _ hu

theorem referenceMeasure_real {u v : ℝ} (hu : 0 < u) {J : Set ℝ}
    (hJ : MeasurableSet J) (hsub : J ⊆ Icc u v) :
    (referenceMeasure u v).real J=∫ x in J,(1:ℝ)/x := by
  rw [referenceMeasure,reciprocalMeasure_real _ hu hJ,Measure.restrict_restrict hJ,
    inter_eq_left.mpr hsub]
  apply setIntegral_congr_fun hJ
  intro x hx
  rw [reciprocalWeight_eq (hsub hx).1,one_div]

theorem intervalGuard_subset {u v a b : ℝ} (hua : u ≤ a) (hbv : b ≤ v) (lc rc : Bool) :
    {x | intervalGuard lc rc a b x} ⊆ Icc u v := by
  intro x hx
  have ha : a ≤ x := by cases lc <;> simp only [intervalGuard,ite_true, if_true,Bool.false_eq_true,ite_false, if_false] at hx <;> linarith [hx.1]
  have hb : x ≤ b := by cases rc <;> simp only [intervalGuard,ite_true, if_true,Bool.false_eq_true,ite_false, if_false] at hx <;> linarith [hx.2]
  exact ⟨hua.trans ha,hb.trans hbv⟩

theorem intervalGuard_measurable (lc rc : Bool) (a b : ℝ) : MeasurableSet {x | intervalGuard lc rc a b x} := by
  cases lc <;> cases rc <;> simp only [intervalGuard,ite_true, if_true,Bool.false_eq_true,ite_false, if_false] <;> measurability

theorem referenceMeasure_interval {u v a b : ℝ} (hu : 0 < u) (hua : u ≤ a) (hab : a ≤ b) (hbv : b ≤ v)
    (lc rc : Bool) :
    (referenceMeasure u v).real {x | intervalGuard lc rc a b x}=Real.log b-Real.log a := by
  rw [referenceMeasure_real hu (intervalGuard_measurable lc rc a b) (intervalGuard_subset hua hbv lc rc)]
  have ha : 0 < a := hu.trans_le hua
  have hb : 0 < b := ha.trans_le hab
  have hbase : (∫ x in Ioc a b,(1:ℝ)/x)=Real.log b-Real.log a := by
    rw [← intervalIntegral.integral_of_le hab,integral_one_div_of_pos ha hb,Real.log_div (ne_of_gt hb) (ne_of_gt ha)]
  cases lc <;> cases rc
  · change (∫ x in Ioo a b,(1:ℝ)/x)=_
    rw [← integral_Ioc_eq_integral_Ioo]
    exact hbase
  · exact hbase
  · change (∫ x in Ico a b,(1:ℝ)/x)=_
    rw [integral_Ico_eq_integral_Ioc]
    exact hbase
  · change (∫ x in Icc a b,(1:ℝ)/x)=_
    rw [integral_Icc_eq_integral_Ioc]
    exact hbase

end NumberTheoryLean.HarmonicReferenceMeasure

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_LipschitzMeasureQuadrature
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open MeasureTheory Set
namespace ErdosContinuousBoundary
open ErdosMonotoneQuadrature

theorem lipschitz_add_linear_monotone {g : ℝ → ℝ} {L : NNReal}
    (hg : LipschitzOnWith L g (Icc 1 2)) :
    MonotoneOn (fun x => g x+(L:ℝ)*x) (Icc 1 2) := by
  intro x hx y hy hxy
  have h := hg.dist_le_mul x hx y hy
  rw [Real.dist_eq,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hxy)] at h
  have hle := le_abs_self (g x-g y)
  dsimp only
  nlinarith

theorem lipschitz_measure_discrepancy
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (g : ℝ → ℝ) (L : NNReal) (D E : ℝ) (hD : 0 ≤ D)
    (hg : LipschitzOnWith L g (Icc 1 2)) (hbound : ∀ x ∈ Icc 1 2,|g x| ≤ D)
    (hd : ∀ S : Set ℝ,S.OrdConnected → S ⊆ Icc 1 2 → |μ.real S-ν.real S| ≤ E)
    {J : Set ℝ} (hJ : J.OrdConnected) (hsub : J ⊆ Icc 1 2) :
    |(∫ x in J,g x ∂μ)-(∫ x in J,g x ∂ν)| ≤ 3*E*(D+4*(L:ℝ)) := by
  let A : ℝ → ℝ := fun x => g x+(L:ℝ)*x
  let B : ℝ → ℝ := fun x => (L:ℝ)*x
  have hL : 0 ≤ (L:ℝ) := L.property
  have hA : MonotoneOn A (Icc 1 2) := lipschitz_add_linear_monotone hg
  have hB : MonotoneOn B (Icc 1 2) := fun x _ y _ hxy => mul_le_mul_of_nonneg_left hxy hL
  have hBb : ∀ x ∈ Icc 1 2,|B x| ≤ 2*(L:ℝ) := by
    intro x hx
    rw [abs_of_nonneg (mul_nonneg hL (by linarith [hx.1]))]
    nlinarith [hx.2]
  have hAb : ∀ x ∈ Icc 1 2,|A x| ≤ D+2*(L:ℝ) := by
    intro x hx
    exact (abs_add_le _ _).trans (add_le_add (hbound x hx) (hBb x hx))
  have hqa := signed_monotone_integral_discrepancy μ ν 1 2 (D+2*(L:ℝ)) E
    (by positivity) A (Or.inl hA) hAb hd hJ hsub
  have hqb := signed_monotone_integral_discrepancy μ ν 1 2 (2*(L:ℝ)) E
    (by positivity) B (Or.inl hB) hBb hd hJ hsub
  have hAm : IntegrableOn A J μ := (hA.integrableOn_isCompact isCompact_Icc).mono_set hsub
  have hAn : IntegrableOn A J ν := (hA.integrableOn_isCompact isCompact_Icc).mono_set hsub
  have hBm : IntegrableOn B J μ := (hB.integrableOn_isCompact isCompact_Icc).mono_set hsub
  have hBn : IntegrableOn B J ν := (hB.integrableOn_isCompact isCompact_Icc).mono_set hsub
  have he : g = fun x => A x-B x := by funext x; dsimp [A,B] <;> ring
  have heq : (∫ x in J,g x ∂μ)-(∫ x in J,g x ∂ν) =
      ((∫ x in J,A x ∂μ)-(∫ x in J,A x ∂ν))-
        ((∫ x in J,B x ∂μ)-(∫ x in J,B x ∂ν)) := by
    rw [he,integral_sub hAm hBm,integral_sub hAn hBn]
    ring
  rw [heq]
  calc
    _ ≤ |(∫ x in J,A x ∂μ)-(∫ x in J,A x ∂ν)|+
        |(∫ x in J,B x ∂μ)-(∫ x in J,B x ∂ν)| := abs_sub _ _
    _ ≤ 3*E*(D+2*(L:ℝ))+3*E*(2*(L:ℝ)) := add_le_add hqa hqb
    _ = _ := by ring

end ErdosContinuousBoundary

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_ActualPrimeQuadrature
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.HarmonicPrimeAtomicMeasure

attribute [local instance] Classical.propDecidable
open _root_.MeasureTheory _root_.Set _root_.Finset
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimeEndpoints

theorem integrable_primeAtom (w : ℝ) (p : ℕ) (F : ℝ → ℝ) : Integrable F (primeAtom w p) := by
  unfold primeAtom
  exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

theorem primeMeasure_integral (w V : ℝ) (F : ℝ → ℝ) :
    (∫ x,F x ∂primeMeasure w V)=∑ p ∈ Nat.primesLE ⌊w^V⌋₊,(p:ℝ)⁻¹*F (primeExponent w p) := by
  unfold primeMeasure
  rw [integral_finsetSum_measure (fun p _ => integrable_primeAtom w p F)]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [primeAtom,integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal (by positivity)]
  rfl

theorem primeMeasure_setIntegral (w V : ℝ) (F : ℝ → ℝ) {J : Set ℝ} (hJ : MeasurableSet J) :
    (∫ x in J,F x ∂primeMeasure w V)=
      ∑ p ∈ Nat.primesLE ⌊w^V⌋₊,if primeExponent w p ∈ J then (p:ℝ)⁻¹*F (primeExponent w p) else 0 := by
  rw [← integral_indicator hJ,primeMeasure_integral]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hp : primeExponent w p ∈ J <;> simp [hp]

theorem primeMeasure_real (w V : ℝ) {J : Set ℝ} (hJ : MeasurableSet J) :
    (primeMeasure w V).real J=
      ∑ p ∈ Nat.primesLE ⌊w^V⌋₊,if primeExponent w p ∈ J then (p:ℝ)⁻¹ else 0 := by
  have h := primeMeasure_setIntegral w V (fun _ => (1:ℝ)) hJ
  simpa only [integral_const,smul_eq_mul,measureReal_restrict_apply_univ,mul_one] using h

theorem intervalGuard_measurable (lc rc : Bool) (a b : ℝ) :
    MeasurableSet {x | intervalGuard lc rc a b x} := by
  cases lc <;> cases rc <;> simp only [intervalGuard,ite_true, if_true,Bool.false_eq_true,ite_false, if_false] <;> measurability

theorem primeMeasure_interval {w a b V : ℝ} (hw : 1 < w) (hbV : b ≤ V) (lc rc : Bool) :
    (primeMeasure w V).real {x | intervalGuard lc rc a b x}=harmonicMass w lc rc a b := by
  rw [primeMeasure_real w V (intervalGuard_measurable lc rc a b),harmonicMass]
  have hw0 : 0 < w := by linarith
  have hpow : w^b ≤ w^V := Real.rpow_le_rpow_of_exponent_le hw.le hbV
  have hsub : Nat.primesLE ⌊w^b⌋₊ ⊆ Nat.primesLE ⌊w^V⌋₊ := by
    intro p hp
    obtain ⟨hpB,hprime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpB.trans (Nat.floor_mono hpow),hprime⟩
  symm
  apply Finset.sum_subset hsub
  intro p hpV hpB
  have hprime := (Nat.mem_primesLE.mp hpV).2
  have hp0 : 0 < (p:ℝ) := by exact_mod_cast hprime.pos
  have hnot : ¬intervalGuard lc rc a b (primeExponent w p) := by
    intro hguard
    have hxp : primeExponent w p ≤ b := by
      have hh := hguard.2
      cases rc with
      | false => exact hh.le
      | true => exact hh
    have hpx := (exponent_le_iff hw hp0).mp hxp
    exact hpB (Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff (Real.rpow_pos_of_pos hw0 b).le).mpr hpx,hprime⟩)
  exact ite_eq_right hnot

end NumberTheoryLean.HarmonicPrimeAtomicMeasure

end

section

open _root_.MeasureTheory _root_.Set _root_.Filter
open scoped Topology
namespace ErdosContinuousBoundary
open ErdosMonotoneQuadrature ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimeEndpoints
open NumberTheoryLean.HarmonicPrimeAtomicMeasure NumberTheoryLean.HarmonicReferenceMeasure

theorem boundaryPrimeError_tendsto_zero {c : ℝ} (hc : 0 < c) (C : ℝ) :
    Tendsto (boundaryPrimeError c C) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0:ℝ) c hc).const_mul C
  have h' : Tendsto (fun x : ℝ => C*Real.exp (-c*x)) atTop (𝓝 0) := by
    simpa only [Real.rpow_zero,one_mul,mul_zero] using h
  exact h'.comp (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)

theorem boundary_interval_discrepancy : ∃ c C w₀ : ℝ,0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → ∀ J : Set ℝ,J.OrdConnected → J ⊆ Icc 1 2 →
      |(primeMeasure w 2).real J-(referenceMeasure 1 2).real J| ≤ boundaryPrimeError c C w := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,h⟩ := harmonic_prime_measure
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro w hw J hJ hsub
  have hw1 : 1 < w := hw₀.trans_le hw
  apply orderConnected_measure_discrepancy (primeMeasure w 2) (referenceMeasure 1 2) 1 2
    (boundaryPrimeError c C w) (by unfold boundaryPrimeError; positivity) _ hJ hsub
  intro a b ha hab hb
  have hall (lc rc : Bool) :
      |(primeMeasure w 2).real {x | intervalGuard lc rc a b x}-
        (referenceMeasure 1 2).real {x | intervalGuard lc rc a b x}| ≤ boundaryPrimeError c C w := by
    rw [primeMeasure_interval hw1 hb,referenceMeasure_interval (by norm_num : (0:ℝ)<1) ha hab hb]
    have hh := h w hw a b (by linarith) hab lc rc
    have hs : Real.sqrt (Real.log w) ≤ Real.sqrt (a*Real.log w) := by
      apply Real.sqrt_le_sqrt
      have hlog := (Real.log_pos hw1).le
      nlinarith
    have he : Real.exp (-c*Real.sqrt (a*Real.log w)) ≤ Real.exp (-c*Real.sqrt (Real.log w)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    exact hh.trans (mul_le_mul_of_nonneg_left he hC.le)
  exact ⟨hall true true,hall true false,hall false true,hall false false⟩

theorem reference_unit_interval_mass : (referenceMeasure 1 2).real (Icc 1 2)=Real.log 2 := by
  have h := referenceMeasure_interval (u:=1) (v:=2) (a:=1) (b:=2)
    (by norm_num) le_rfl (by norm_num) le_rfl true true
  simpa only [intervalGuard,ite_true, if_true,Real.log_one,sub_zero] using! h

theorem boundary_measure_control : ∃ c C w₀ : ℝ,0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w →
      (primeMeasure w 2).real (Icc 1 2) ≤ 1 ∧
      ∀ J : Set ℝ,J.OrdConnected → J ⊆ Icc 1 2 →
        |(primeMeasure w 2).real J-(referenceMeasure 1 2).real J| ≤ boundaryPrimeError c C w := by
  obtain ⟨c,C,wH,hc,hC,hwH,h⟩ := boundary_interval_discrepancy
  have hlog : Real.log 2 < 1 := by
    have hh := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1)
    norm_num at hh
    exact hh
  have he := (boundaryPrimeError_tendsto_zero hc C).eventually
    (Iio_mem_nhds (by linarith : (0:ℝ)<1-Real.log 2))
  obtain ⟨wE,hwE⟩ := eventually_atTop.mp he
  refine ⟨c,C,max wH wE,hc,hC,hwH.trans_le (le_max_left _ _),?_⟩
  intro w hw
  have hwh : wH ≤ w := (le_max_left _ _).trans hw
  have hwe := hwE w ((le_max_right _ _).trans hw)
  refine ⟨?_,h w hwh⟩
  have hm := h w hwh (Icc 1 2) ordConnected_Icc (subset_refl _)
  rw [reference_unit_interval_mass] at hm
  have hmass := (abs_le.mp hm).2
  change boundaryPrimeError c C w < 1-Real.log 2 at hwe
  linarith

end ErdosContinuousBoundary

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_DickmanFiniteDecay
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.DickmanFiniteDecay

open Dickman

theorem rho_le_one (u : ℝ) : rho u ≤ 1 := by
  by_cases hu : u ≤ 1
  · rw [rho_initial hu]
  · have h := rho_antitone (le_of_lt (lt_of_not_ge hu))
    simpa only [rho_initial (le_refl (1:ℝ))] using h

end NumberTheoryLean.DickmanFiniteDecay

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReferenceWeightedQuadrature
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ReferenceBenchmarkDecay

open FinitePathGeometry LinearSieveFunctions BuchstabBridge NormalizedDeficits
open Dickman DickmanFiniteDecay

theorem benchmark_deviation_le_gap (i : Side) {s : ℝ} (hs : 1 ≤ s) :
    |benchmark i s-1| ≤ gap s := by
  obtain ⟨hl,hu⟩ := deficits_pos hs
  have hsum := deficit_sum s
  cases i with
  | even =>
    have he : benchmark .even s-1 = -lowerDeficit s := by unfold benchmark lowerDeficit; ring
    rw [he,abs_neg,abs_of_pos hl]
    linarith
  | odd =>
    change |upperDeficit s| ≤ gap s
    rw [abs_of_pos hu]
    linarith

theorem gap_le_rho {s : ℝ} (hs : 1 ≤ s) : gap s ≤ sieveA*rho (s-1) := by
  rw [gap_eq_rho hs]
  exact div_le_self (mul_nonneg sieveA_pos.le (rho_nonneg _)) hs

theorem gap_le_constant {s : ℝ} (hs : 1 ≤ s) : gap s ≤ sieveA := by
  calc
    _ ≤ sieveA*rho (s-1) := gap_le_rho hs
    _ ≤ sieveA*1 := mul_le_mul_of_nonneg_left (rho_le_one _) sieveA_pos.le
    _ = _ := mul_one _

end NumberTheoryLean.ReferenceBenchmarkDecay



section

open _root_.Set
namespace ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.ReferenceAdmission

theorem upperCutoff_bounds (i : Side) (r b : ℝ) : 1 ≤ upperCutoff i r b ∧ upperCutoff i r b ≤ 2 := by
  cases i
  · exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
  · exact ⟨le_max_left _ _,max_le (by norm_num) ((min_le_left _ _).trans (min_le_left _ _))⟩

theorem upperCutoff_continuous (i : Side) :
    Continuous (fun p : ℝ×ℝ => upperCutoff i p.1 p.2) := by
  cases i <;> unfold upperCutoff <;> fun_prop

theorem upperCutoff_odd_small {r b : ℝ} (hr : r ≤ 4) : upperCutoff .odd r b=1 := by
  apply max_eq_left
  exact (min_le_right _ _).trans (by linarith)

theorem strong_gate_below_two {r x : ℝ} (hx : x ≤ 2) :
    childAdmitted .odd r x ↔ x ≤ (r-2)/2 := by
  change max (2*x) (x+2) ≤ r-x ↔ x ≤ (r-2)/2
  rw [max_eq_right (by linarith : 2*x ≤ x+2)]
  constructor <;> intro h <;> linarith

theorem le_clipped_upper {x t : ℝ} (hx : 1 < x) : x ≤ max 1 t ↔ x ≤ t := by
  rw [le_max_iff]
  exact or_iff_right (not_le_of_gt hx)

theorem mem_upperCutoff (i : Side) (r b x : ℝ) :
    x ∈ Ioc 1 (upperCutoff i r b) ↔
      1 < x ∧ x ≤ 2 ∧ x ≤ b ∧ childAdmitted i r x := by
  constructor
  · intro hx
    cases i with
    | even =>
      have h : x ≤ min 2 b := (le_clipped_upper hx.1).mp hx.2
      exact ⟨hx.1,(le_min_iff.mp h).1,(le_min_iff.mp h).2,trivial⟩
    | odd =>
      have h : x ≤ min (min 2 b) ((r-2)/2) := (le_clipped_upper hx.1).mp hx.2
      obtain ⟨hb,hgate⟩ := le_min_iff.mp h
      obtain ⟨hx2,hxb⟩ := le_min_iff.mp hb
      exact ⟨hx.1,hx2,hxb,(strong_gate_below_two hx2).mpr hgate⟩
  · rintro ⟨hx,hx2,hxb,hgate⟩
    refine ⟨hx,?_⟩
    cases i with
    | even => exact (le_clipped_upper hx).mpr (le_min hx2 hxb)
    | odd => exact (le_clipped_upper hx).mpr (le_min (le_min hx2 hxb) ((strong_gate_below_two hx2).mp hgate))

end ErdosContinuousBoundary

end



namespace ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry

theorem upperCutoff_b_lipschitz (i : Side) (r : ℝ) :
    LipschitzWith 1 (fun b => upperCutoff i r b) := by
  cases i with
  | even => exact (LipschitzWith.id.const_min (2:ℝ)).const_max 1
  | odd => exact ((LipschitzWith.id.const_min (2:ℝ)).min_const ((r-2)/2)).const_max 1

theorem upperCutoff_r_lipschitz (i : Side) (b : ℝ) :
    LipschitzWith 1 (fun r => upperCutoff i r b) := by
  cases i with
  | even =>
    apply LipschitzWith.of_dist_le_mul
    intro r s
    simp [upperCutoff]
  | odd =>
    have h : LipschitzWith 1 (fun r : ℝ => (r-2)/2) := by
      apply LipschitzWith.of_dist_le_mul
      intro r s
      simp only [Real.dist_eq,NNReal.coe_one,one_mul]
      have he : (r-2)/2-(s-2)/2=(r-s)/2 := by ring
      rw [he,abs_div]
      norm_num
    exact (h.const_min (min 2 b)).const_max 1

theorem upperCutoff_b_difference (i : Side) (r b c : ℝ) :
    |upperCutoff i r b-upperCutoff i r c| ≤ |b-c| := by
  simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using (upperCutoff_b_lipschitz i r).dist_le_mul b c

theorem upperCutoff_r_difference (i : Side) (b r s : ℝ) :
    |upperCutoff i r b-upperCutoff i s b| ≤ |r-s| := by
  simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using (upperCutoff_r_lipschitz i b).dist_le_mul r s

end ErdosContinuousBoundary



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_PrefixCompletions
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferencePruning
attribute [local instance] Classical.propDecidable
open ErdosPrimeInputs.PrimePrefixMass

theorem append_mem_decreasing_iff {P : Finset ℕ} {pre suf : List ℕ}
    (hpre : pre ∈ decreasingPrefixes P) :
    pre++suf ∈ decreasingPrefixes P ↔ suf ∈ decreasingPrefixes (suffixPrimes P pre) := by
  obtain ⟨hpp,hpm⟩ := mem_decreasingPrefixes.mp hpre
  constructor
  · intro h
    obtain ⟨hp,hm⟩ := mem_decreasingPrefixes.mp h
    obtain ⟨_,hs,hcross⟩ := List.pairwise_append.mp hp
    apply mem_decreasingPrefixes.mpr
    refine ⟨hs,?_⟩
    intro q hq
    apply Finset.mem_filter.mpr
    exact ⟨hm q (List.mem_append.mpr (Or.inr hq)),fun p hp => hcross p hp q hq⟩
  · intro h
    obtain ⟨hs,hm⟩ := mem_decreasingPrefixes.mp h
    apply mem_decreasingPrefixes.mpr
    refine ⟨List.pairwise_append.mpr ⟨hpp,hs,?_⟩,?_⟩
    · intro p hp q hq
      exact (Finset.mem_filter.mp (hm q hq)).2 p hp
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hpm p hp
      · exact (Finset.mem_filter.mp (hm p hp)).1

end NumberTheoryLean.ReferencePruning

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReferenceProductsBasics
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferenceProductsBasics

attribute [local instance] Classical.propDecidable
open _root_.Finset
open ReferencePruning ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.MertensStrong

theorem primeProduct_eq_survivor (x : ℝ) : primeProduct x=survivorProduct (Nat.primesLE ⌊x⌋₊) := by
  have he : (Ioc 0 ⌊x⌋₊).filter Nat.Prime=Nat.primesLE ⌊x⌋₊ := by
    ext p
    simp only [mem_filter,mem_Ioc,Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨_,hpx⟩,hp⟩
      exact ⟨hpx,hp⟩
    · rintro ⟨hpx,hp⟩
      exact ⟨⟨hp.pos,hpx⟩,hp⟩
  unfold primeProduct survivorProduct
  rw [he]
  simp only [one_div]

theorem prime_factor_pos {p : ℕ} (hp : p.Prime) : 0 < 1-(p:ℝ)⁻¹ := by
  apply sub_pos.mpr
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

theorem actual_primeProduct_pos (x : ℝ) : 0 < primeProduct x := by
  rw [primeProduct_eq_survivor]
  exact Finset.prod_pos (fun p hp => prime_factor_pos (Nat.mem_primesLE.mp hp).2)

theorem availableProduct_pos (a x : ℝ) (closed : Bool) : 0 < availableProduct a x closed := by
  unfold availableProduct survivorProduct
  apply Finset.prod_pos
  intro p hp
  exact prime_factor_pos (Nat.mem_primesLE.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).2

theorem primesBetween_eq_sdiff {a x : ℝ} (ha : 0 ≤ a) :
    primesBetween a x=Nat.primesLE ⌊x⌋₊ \ Nat.primesLE ⌊a⌋₊ := by
  ext p
  simp only [primesBetween,Finset.mem_filter,Finset.mem_sdiff,Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpx,hp⟩,hap⟩
    refine ⟨⟨hpx,hp⟩,?_⟩
    intro hpa
    have h : (p:ℝ) ≤ a := (Nat.le_floor_iff ha).mp hpa.1
    linarith
  · rintro ⟨⟨hpx,hp⟩,hnot⟩
    refine ⟨⟨hpx,hp⟩,?_⟩
    by_contra hn
    exact hnot ⟨(Nat.le_floor_iff ha).mpr (le_of_not_gt hn),hp⟩

theorem closed_product_ratio {a x : ℝ} (ha : 0 ≤ a) (hax : a ≤ x) :
    availableProduct a x true=primeProduct x/primeProduct a := by
  have hsub : Nat.primesLE ⌊a⌋₊ ⊆ Nat.primesLE ⌊x⌋₊ := by
    intro p hp
    obtain ⟨hpa,hp⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpa.trans (Nat.floor_mono hax),hp⟩
  apply (eq_div_iff (ne_of_gt (actual_primeProduct_pos a))).mpr
  rw [availableProduct,availablePrimes_closed,primesBetween_eq_sdiff ha,
    primeProduct_eq_survivor,primeProduct_eq_survivor]
  exact Finset.prod_sdiff hsub

theorem endpoint_card_le_one (P : Finset ℕ) (x : ℝ) :
    (P.filter (fun p : ℕ => (p:ℝ)=x)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  have he := (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
  exact_mod_cast he

theorem endpoint_product_factor {a x : ℝ} (hx : 0 ≤ x) :
    availableProduct a x true = availableProduct a x false ∨
    availableProduct a x true = availableProduct a x false*(1-x⁻¹) := by
  let P := primesBetween a x
  have hpx : ∀ p ∈ P,(p:ℝ) ≤ x := by
    intro p hp
    exact (Nat.le_floor_iff hx).mp (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).1
  have hfilter : P.filter (fun p : ℕ => ¬(p:ℝ)<x)=P.filter (fun p : ℕ => (p:ℝ)=x) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp,hn⟩
      exact ⟨hp,le_antisymm (hpx p hp) (le_of_not_gt hn)⟩
    · rintro ⟨hp,he⟩
      exact ⟨hp,by rw [he]; exact lt_irrefl _⟩
  have hprod := Finset.prod_filter_mul_prod_filter_not P (fun p : ℕ => (p:ℝ)<x) (fun p => 1-(p:ℝ)⁻¹)
  rw [hfilter] at hprod
  have hbd : (∏ p ∈ P.filter (fun p : ℕ => (p:ℝ)=x),(1-(p:ℝ)⁻¹)) =
      (1-x⁻¹)^(P.filter (fun p : ℕ => (p:ℝ)=x)).card := by
    rw [← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro p hp
    rw [(Finset.mem_filter.mp hp).2]
  rw [hbd] at hprod
  have hopen : availableProduct a x false=survivorProduct (P.filter (fun p : ℕ => (p:ℝ)<x)) := by
    simp only [availableProduct,availablePrimes,Bool.false_eq_true,false_or,P]
  have hclosed : availableProduct a x true=survivorProduct P := by
    simp only [availableProduct,availablePrimes_closed,P]
  have hcard := endpoint_card_le_one P x
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with hzero | hone
  · left
    rw [hzero,pow_zero,mul_one] at hprod
    exact hclosed.trans (hprod.symm.trans hopen.symm)
  · right
    rw [hone,pow_one] at hprod
    rw [hclosed,hopen]
    exact hprod.symm

theorem endpoint_relative_bound {a x : ℝ} (hx : 2 ≤ x) :
    |availableProduct a x false/availableProduct a x true-1| ≤ 2/x := by
  have hc := availableProduct_pos a x true
  have ho := availableProduct_pos a x false
  rcases endpoint_product_factor (a:=a) (by linarith : 0 ≤ x) with he | he
  · rw [he,div_self (ne_of_gt ho),sub_self,abs_zero]
    positivity
  · have hx0 : 0 < x := by linarith
    have hx1 : x⁻¹ ≤ 1/2 := by
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hx
    have hfac : 0 < 1-x⁻¹ := by linarith
    have hratio : availableProduct a x false/availableProduct a x true-1=x⁻¹/(1-x⁻¹) := by
      rw [he,div_mul_eq_div_div,div_self (ne_of_gt ho)]
      rw [div_sub_one (ne_of_gt hfac)]
      congr 1
      ring
    rw [hratio,abs_of_nonneg (div_nonneg (inv_nonneg.mpr hx0.le) hfac.le)]
    apply (div_le_iff₀ hfac).mpr
    have hsmall : 0 ≤ x⁻¹ := inv_nonneg.mpr hx0.le
    rw [div_eq_mul_inv]
    nlinarith

end NumberTheoryLean.ReferenceProductsBasics

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_ReferencePrefixRecurrence
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferencePrefixRecurrence

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry ReferenceAdmission ReferencePruning
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.HarmonicPrimeMeasure

theorem singleton_prefix_mem {P : Finset ℕ} {p : ℕ} (hp : p ∈ P) : [p] ∈ decreasingPrefixes P := by
  apply mem_decreasingPrefixes.mpr
  exact ⟨by simp,by intro q hq; simpa using List.mem_singleton.mp hq ▸ hp⟩

theorem nonempty_eq_first_completions (P : Finset ℕ) :
    nonemptyPrefixes P=P.biUnion (fun p => completions P [p]) := by
  ext ps
  constructor
  · intro hp
    obtain ⟨hpD,hne⟩ := Finset.mem_filter.mp hp
    cases ps with
    | nil => exact False.elim (hne rfl)
    | cons p ps =>
      have hpP : p ∈ P := (mem_decreasingPrefixes.mp hpD).2 p (by simp)
      have ht := (append_mem_decreasing_iff (singleton_prefix_mem hpP)).mp hpD
      exact Finset.mem_biUnion.mpr ⟨p,hpP,Finset.mem_image.mpr ⟨ps,ht,rfl⟩⟩
  · intro hp
    obtain ⟨p,hpP,hps⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨tail,htail,rfl⟩ := Finset.mem_image.mp hps
    exact Finset.mem_filter.mpr ⟨(append_mem_decreasing_iff (singleton_prefix_mem hpP)).mpr htail,by simp⟩

theorem first_completions_disjoint (P : Finset ℕ) :
    (P:Set ℕ).PairwiseDisjoint (fun p => completions P [p]) := by
  intro p _hp q _hq hne
  apply Finset.disjoint_left.mpr
  intro ps hp hq
  obtain ⟨sp,_hsp,he⟩ := Finset.mem_image.mp hp
  obtain ⟨sq,_hsq,hf⟩ := Finset.mem_image.mp hq
  have hh := he.trans hf.symm
  simp only [List.singleton_append] at hh
  exact hne (List.cons.inj hh).1

theorem sum_decreasing_by_first (P : Finset ℕ) (F : List ℕ → ℝ) :
    (∑ ps ∈ decreasingPrefixes P,F ps)=F []+
      ∑ p ∈ P,∑ ps ∈ decreasingPrefixes (P.filter (fun q => q<p)),F (p::ps) := by
  have he : (decreasingPrefixes P).filter (fun ps => ps=[])= {[]} := by
    ext ps
    simp only [Finset.mem_filter,Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · intro h
      subst ps
      exact ⟨mem_decreasingPrefixes.mpr ⟨by simp,by simp⟩,rfl⟩
  have hs := Finset.sum_filter_add_sum_filter_not (decreasingPrefixes P) (fun ps => ps=[]) F
  rw [he,Finset.sum_singleton] at hs
  change F []+(∑ ps ∈ nonemptyPrefixes P,F ps)=(∑ ps ∈ decreasingPrefixes P,F ps) at hs
  rw [← hs,nonempty_eq_first_completions,Finset.sum_biUnion (first_completions_disjoint P)]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  unfold completions
  rw [Finset.sum_image]
  · have hsuf : suffixPrimes P [p]=P.filter (fun q => q<p) := by simp [suffixPrimes]
    rw [hsuf]
    apply Finset.sum_congr rfl
    intro ps _
    rfl
  · intro a _ b _ h
    exact List.append_cancel_left h

end NumberTheoryLean.ReferencePrefixRecurrence

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_ReferenceSourcePrimeSets
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferenceMertens

open _root_.Filter _root_.Asymptotics
open scoped Topology
open ReferenceProductsBasics ErdosPrimeInputs.MertensStrong

theorem normalization_pos {w : ℝ} (hw : 1 < w) : 0 < normalization w :=
  div_pos (Real.exp_pos _) (mul_pos (Real.log_pos hw) (actual_primeProduct_pos w))

theorem normalization_eq_exp {w : ℝ} (hw : 1 < w) :
    normalization w=Real.exp (-_root_.Erdos970.Mertens.E₃ w) := by
  unfold normalization primeProduct
  rw [_root_.Erdos970.Mertens.prod_one_minus_div_prime_eq hw,Real.exp_neg]
  field_simp [ne_of_gt (Real.log_pos hw)]
  rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]

theorem normalization_tendsto_one : Tendsto normalization atTop (𝓝 1) := by
  have h := (isLittleO_one_iff ℝ).mp _root_.Erdos970.Mertens.E₃.bound'
  have hl : Tendsto (fun w => Real.exp (-_root_.Erdos970.Mertens.E₃ w)) atTop (𝓝 1) := by
    convert! Real.continuous_exp.continuousAt.tendsto.comp h.neg using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with w hw
  exact (normalization_eq_exp hw).symm

theorem closed_normalized_identity {w b : ℝ} (hw : 1 < w) (hb : 1 ≤ b) :
    referenceProduct w b true/(normalization w/b)=
      primeProduct (w^b)/(Real.exp (-Real.eulerMascheroniConstant)/Real.log (w^b)) := by
  have hw0 : 0 < w := by linarith
  have hb0 : 0 < b := by linarith
  have hwb : w ≤ w^b := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hw.le hb
  rw [referenceProduct,closed_product_ratio hw0.le hwb,normalization,Real.log_rpow hw0]
  field_simp [ne_of_gt (actual_primeProduct_pos w),ne_of_gt (Real.log_pos hw),ne_of_gt hb0]

theorem exp_error_mono_rate {c₁ c₂ t : ℝ} (hc : c₂ ≤ c₁) :
    Real.exp (-c₁*Real.sqrt t) ≤ Real.exp (-c₂*Real.sqrt t) :=
  Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_nonneg t])

theorem reference_product_strong : ∃ c C w₀ : ℝ,0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → ∀ b : ℝ,2 ≤ b → ∀ closed : Bool,
      |referenceProduct w b closed/(normalization w/b)-1| ≤
        C*Real.exp (-c*Real.sqrt (b*Real.log w)) := by
  obtain ⟨c,C,x₀,hc,hC,hx₀,hprod⟩ := prime_product_strong
  let c' := min c 1
  let W := max x₀ (Real.exp 1)
  have hc' : 0 < c' := lt_min hc zero_lt_one
  refine ⟨c',3*C+2,W,hc',by positivity,
    (by have hh := le_max_left x₀ (Real.exp 1); dsimp [W] <;> linarith),?_⟩
  intro w hw b hb closed
  have hwX : x₀ ≤ w := (le_max_left _ _).trans hw
  have hwE : Real.exp 1 ≤ w := (le_max_right _ _).trans hw
  have hw1 : 1 < w := by linarith [hx₀.trans hwX]
  have hw0 : 0 < w := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have hxw : w ≤ w^b := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hw1.le hb1
  have hx2 : 2 ≤ w^b := (hx₀.trans hwX).trans hxw
  have hx0 : 0 < w^b := Real.rpow_pos_of_pos hw0 b
  have hlog : 1 ≤ Real.log (w^b) := by
    have hh := Real.log_le_log (Real.exp_pos 1) (hwE.trans hxw)
    simpa only [Real.log_exp] using hh
  let E := Real.exp (-c'*Real.sqrt (b*Real.log w))
  have hEpos : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc'.le) (Real.sqrt_nonneg _))
  have hclosed : |referenceProduct w b true/(normalization w/b)-1| ≤ C*E := by
    rw [closed_normalized_identity hw1 hb1]
    have h := hprod (w^b) (hwX.trans hxw)
    have hm := exp_error_mono_rate (t:=Real.log (w^b)) (min_le_left c 1)
    rw [Real.log_rpow hw0] at h hm ⊢
    exact h.trans (mul_le_mul_of_nonneg_left hm hC.le)
  cases closed with
  | true => exact hclosed.trans (mul_le_mul_of_nonneg_right (by linarith : C ≤ 3*C+2) hEpos.le)
  | false =>
    let D := normalization w/b
    let q := referenceProduct w b true/D
    let k := referenceProduct w b false/referenceProduct w b true
    have hD : 0 < D := div_pos (normalization_pos hw1) hb0
    have hP : 0 < referenceProduct w b true := availableProduct_pos _ _ _
    have hq0 : 0 < q := div_pos hP hD
    have hq : q ≤ C+1 := by
      have hh := (abs_le.mp hclosed).2
      have hh' := mul_le_mul_of_nonneg_left hE1 hC.le
      dsimp only [q,D]
      linarith
    have hk : |k-1| ≤ 2/(w^b) := endpoint_relative_bound hx2
    have hrec : 1/(w^b) ≤ E := by
      have h := ErdosPrimeInputs.MertensStrong.reciprocal_le_decay (min_le_right c 1) hx0 hlog
      simpa only [E,ErdosPrimeInputs.PrimeErrorDecay.decay,Real.log_rpow hw0] using h
    have heq : referenceProduct w b false/D=k*q := by
      dsimp only [k,q]
      field_simp
    change |referenceProduct w b false/D-1| ≤ (3*C+2)*E
    rw [heq]
    calc
      _ = |(k-1)*q+(q-1)| := by congr 1; ring
      _ ≤ |(k-1)*q|+|q-1| := abs_add_le _ _
      _ = |k-1| *q+|q-1| := by rw [abs_mul,abs_of_pos hq0]
      _ ≤ (2/(w^b))*(C+1)+C*E :=
        add_le_add (mul_le_mul hk hq hq0.le (by positivity)) hclosed
      _ ≤ 2*E*(C+1)+C*E := by
        apply add_le_add_left
        apply mul_le_mul_of_nonneg_right _ (by linarith : 0 ≤ C+1)
        simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hrec (by norm_num : (0:ℝ) ≤ 2)
      _ = _ := by ring

end NumberTheoryLean.ReferenceMertens

end

section

namespace NumberTheoryLean.ReferenceSourcePrimeSets

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry PrimeTiltGeometry ReferenceAdmission ReferencePruning ReferenceProductsBasics
open ReferenceMertens ReferenceCutoffRecurrence
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass

theorem availablePrimes_membership {a x : ℝ} (hx : 0 ≤ x) (closed : Bool) (p : ℕ) :
    p ∈ availablePrimes a x closed ↔ p.Prime ∧ a<(p:ℝ) ∧ (if closed then (p:ℝ) ≤ x else (p:ℝ)<x) := by
  simp only [availablePrimes,primesBetween,Finset.mem_filter,Nat.mem_primesLE,Nat.le_floor_iff hx]
  cases closed
  · simp only [Bool.false_eq_true,false_or,ite_false, if_false]
    constructor
    · rintro ⟨⟨⟨_,hp⟩,ha⟩,hx⟩
      exact ⟨hp,ha,hx⟩
    · rintro ⟨hp,ha,hx⟩
      exact ⟨⟨⟨hx.le,hp⟩,ha⟩,hx⟩
  · simp only [true_or,ite_true, if_true,and_true]
    tauto

theorem sourcePrimes_membership {w : ℝ} (hw : 1 < w) (b : ℝ) (closed : Bool) (p : ℕ) :
    p ∈ sourcePrimes w b closed ↔ p.Prime ∧ 1<primeExponent w p ∧ capGuard closed b (primeExponent w p) := by
  rw [sourcePrimes,availablePrimes_membership (Real.rpow_pos_of_pos (by linarith : 0 < w) b).le]
  constructor
  · rintro ⟨hp,hlo,hhi⟩
    have hp0 : 0 < (p:ℝ) := by exact_mod_cast hp.pos
    refine ⟨hp,?_,?_⟩
    · exact (lt_exponent_iff hw hp0).mpr (by simpa only [Real.rpow_one] using hlo)
    · cases closed with
      | false => exact (exponent_lt_iff hw hp0).mpr hhi
      | true => exact (exponent_le_iff hw hp0).mpr hhi
  · rintro ⟨hp,hlo,hhi⟩
    have hp0 : 0 < (p:ℝ) := by exact_mod_cast hp.pos
    refine ⟨hp,?_,?_⟩
    · simpa only [Real.rpow_one] using (lt_exponent_iff hw hp0).mp hlo
    · cases closed with
      | false => exact (exponent_lt_iff hw hp0).mp hhi
      | true => exact (exponent_le_iff hw hp0).mp hhi

theorem rpow_primeExponent {w : ℝ} (hw : 1 < w) {p : ℕ} (hp : p.Prime) :
    w^primeExponent w p=(p:ℝ) := by
  have hw0 : 0 < w := by linarith
  rw [Real.rpow_def_of_pos hw0]
  have he : Real.log w*primeExponent w p=Real.log p := by
    unfold primeExponent
    field_simp [ne_of_gt (Real.log_pos hw)]
  rw [he,Real.exp_log (by exact_mod_cast hp.pos)]

theorem sourcePrimes_at_selected {w b : ℝ} (hw : 1 < w) (closed : Bool) {p : ℕ}
    (hp : p ∈ sourcePrimes w b closed) :
    sourcePrimes w (primeExponent w p) false=(sourcePrimes w b closed).filter (fun q => q<p) := by
  have hpM := (sourcePrimes_membership hw b closed p).mp hp
  have hpCap : primeExponent w p ≤ b := by
    cases closed with
    | false => exact hpM.2.2.le
    | true => exact hpM.2.2
  ext q
  rw [sourcePrimes_membership hw,Finset.mem_filter,sourcePrimes_membership hw]
  constructor
  · rintro ⟨hq,hqLo,hqCap⟩
    have hqCap' : primeExponent w q < primeExponent w p := hqCap
    have hqP : q<p := by
      have hreal := (exponent_lt_iff hw (by exact_mod_cast hq.pos)).mp hqCap'
      rw [rpow_primeExponent hw hpM.1] at hreal
      exact_mod_cast hreal
    refine ⟨⟨hq,hqLo,?_⟩,hqP⟩
    cases closed with
    | false => exact hqCap'.trans_le hpCap
    | true => exact hqCap'.le.trans hpCap
  · rintro ⟨⟨hq,hqLo,_hqCap⟩,hqp⟩
    refine ⟨hq,hqLo,?_⟩
    apply (exponent_lt_iff hw (by exact_mod_cast hq.pos)).mpr
    rw [rpow_primeExponent hw hpM.1]
    exact_mod_cast hqp

end NumberTheoryLean.ReferenceSourcePrimeSets

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReferenceProductErrors
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferenceProductErrors

open _root_.Filter _root_.Erdos970.Filter
open scoped Topology
open ReferenceProductsBasics ReferenceMertens

theorem normalization_eventually_bounded : ∀ᶠ w : ℝ in atTop,1/2 ≤ normalization w ∧ normalization w ≤ 2 := by
  have h := normalization_tendsto_one.eventually
    (Ioo_mem_nhds (by norm_num : (1/2:ℝ)<1) (by norm_num : (1:ℝ)<2))
  filter_upwards [h] with w hw
  exact ⟨hw.1.le,hw.2.le⟩

theorem reference_product_absolute : ∃ c C w₀ : ℝ,0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → 1/2 ≤ normalization w ∧ normalization w ≤ 2 ∧
      ∀ b : ℝ,2 ≤ b → ∀ closed : Bool,
        |referenceProduct w b closed-normalization w/b| ≤
          (C/b)*Real.exp (-c*Real.sqrt (b*Real.log w)) := by
  obtain ⟨c,C,wM,hc,hC,hwM,h⟩ := reference_product_strong
  obtain ⟨wN,hwN⟩ := eventually_atTop.mp normalization_eventually_bounded
  refine ⟨c,2*C,max wM wN,hc,by positivity,hwM.trans_le (le_max_left _ _),?_⟩
  intro w hw
  have hwm : wM ≤ w := (le_max_left _ _).trans hw
  have hwn := hwN w ((le_max_right _ _).trans hw)
  refine ⟨hwn.1,hwn.2,?_⟩
  intro b hb closed
  have hw1 : 1 < w := hwM.trans_le hwm
  have hb0 : 0 < b := by linarith
  have hD : 0 < normalization w/b := div_pos (normalization_pos hw1) hb0
  have hh := h w hwm b hb closed
  rw [div_sub_one (ne_of_gt hD),abs_div,abs_of_pos hD] at hh
  have hm := (div_le_iff₀ hD).mp hh
  calc
    _ ≤ (C*Real.exp (-c*Real.sqrt (b*Real.log w)))*(normalization w/b) := hm
    _ ≤ (C*Real.exp (-c*Real.sqrt (b*Real.log w)))*(2/b) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hwn.2 hb0.le) (by positivity)
    _ = _ := by ring

end NumberTheoryLean.ReferenceProductErrors

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_BoundaryProductLimit
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter _root_.Erdos970.Filter
open scoped Topology
namespace ErdosContinuousAnomaly
open ErdosContinuousBoundary
open NumberTheoryLean.ReferenceAdmission NumberTheoryLean.ReferencePruning
open NumberTheoryLean.ReferenceProductsBasics NumberTheoryLean.ReferenceMertens
open NumberTheoryLean.ReferenceProductErrors

theorem boundaryProduct_eq_referenceProduct (w : ℝ) :
    boundaryProduct w=referenceProduct w 2 true := by
  simp only [boundaryProduct,referenceProduct,availableProduct,availablePrimes_closed,boundaryPrimes]

theorem boundaryProduct_tendsto_half : Tendsto boundaryProduct atTop (𝓝 (1/2:ℝ)) := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,h⟩ := reference_product_absolute
  have he : ∀ᶠ w : ℝ in atTop,
      ‖referenceProduct w 2 true-normalization w/2‖ ≤ boundaryPrimeError c (C/2) w := by
    filter_upwards [eventually_ge_atTop w₀] with w hw
    have hh := (h w hw).2.2 2 le_rfl true
    have hw1 : 1 < w := hw₀.trans_le hw
    have hs : Real.sqrt (Real.log w) ≤ Real.sqrt (2*Real.log w) := by
      apply Real.sqrt_le_sqrt
      nlinarith [Real.log_pos hw1]
    have hm : Real.exp (-c*Real.sqrt (2*Real.log w)) ≤ Real.exp (-c*Real.sqrt (Real.log w)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    rw [Real.norm_eq_abs]
    exact hh.trans (mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ C/2))
  have hz : Tendsto (fun w : ℝ => referenceProduct w 2 true-normalization w/2) atTop (𝓝 0) :=
    squeeze_zero_norm' he (boundaryPrimeError_tendsto_zero hc (C/2))
  have hsum := hz.add (normalization_tendsto_one.div_const (2:ℝ))
  have hv : Tendsto (fun w : ℝ => referenceProduct w 2 true) atTop (𝓝 (1/2:ℝ)) := by
    simpa only [sub_add_cancel,zero_add] using! hsum
  exact hv.congr' (Eventually.of_forall fun w => (boundaryProduct_eq_referenceProduct w).symm)

end ErdosContinuousAnomaly

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_IntegralDifferenceBound
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open MeasureTheory Set
namespace ErdosContinuousBoundary

theorem integral_upper_difference_bound
    (F G : ℝ → ℝ) (hF : Continuous F) (hG : Continuous G)
    (a b D : ℝ) (ha : a ∈ Icc 1 2) (hD : 0 ≤ D)
    (hFG : ∀ x, |F x-G x| ≤ D) (hGb : ∀ x, |G x| ≤ 1) :
    |(∫ x in (1:ℝ)..a,F x)-(∫ x in (1:ℝ)..b,G x)| ≤ D+|a-b| := by
  have hs := intervalIntegral.integral_sub (hF.intervalIntegrable (μ:=volume) 1 a) (hG.intervalIntegrable (μ:=volume) 1 a)
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hG.intervalIntegrable (μ:=volume) 1 b) (hG.intervalIntegrable (μ:=volume) b a)
  have he : (∫ x in (1:ℝ)..a,F x)-(∫ x in (1:ℝ)..b,G x) =
      (∫ x in (1:ℝ)..a,F x-G x)+(∫ x in b..a,G x) := by
    rw [hs]
    linarith
  have hfirst := intervalIntegral.norm_integral_le_of_norm_le_const (a:=1) (b:=a)
    (f:=fun x => F x-G x) (C:=D) (fun x _ => by simpa only [Real.norm_eq_abs] using hFG x)
  have hsecond := intervalIntegral.norm_integral_le_of_norm_le_const (a:=b) (b:=a)
    (f:=G) (C:=1) (fun x _ => by simpa only [Real.norm_eq_abs] using hGb x)
  rw [Real.norm_eq_abs,abs_of_nonneg (by linarith [ha.1] : 0 ≤ a-1)] at hfirst
  rw [Real.norm_eq_abs,one_mul] at hsecond
  have hfirst' : |∫ x in (1:ℝ)..a,F x-G x| ≤ D := by
    apply hfirst.trans
    nlinarith [ha.2]
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hfirst' hsecond)

end ErdosContinuousBoundary

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_VariableUpperIntegral
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open MeasureTheory Set
namespace ErdosContinuousBoundary

theorem continuous_variable_upper_integral
    (F : (ℝ×ℝ) → ℝ → ℝ) (hF : Continuous F.uncurry)
    (c : (ℝ×ℝ) → ℝ) (hc : Continuous c) :
    Continuous (fun p => ∫ x in (1:ℝ)..c p,F p x) := by
  let G : (ℝ×ℝ) → ℝ → ℝ := fun p t => F p ((c p-1)*t+1)
  have hG : Continuous G.uncurry := by
    change Continuous (F.uncurry ∘ (fun q : (ℝ×ℝ)×ℝ => (q.1,(c q.1-1)*q.2+1)))
    apply hF.comp
    exact continuous_fst.prodMk
      (((hc.comp continuous_fst).sub continuous_const).mul continuous_snd |>.add continuous_const)
  have hi : Continuous (fun p => ∫ t in Icc (0:ℝ) 1,G p t) :=
    continuous_parametric_integral_of_continuous hG isCompact_Icc
  have heq (p : ℝ×ℝ) : (c p-1)*(∫ t in Icc (0:ℝ) 1,G p t)=∫ x in (1:ℝ)..c p,F p x := by
    have h := intervalIntegral.smul_integral_comp_mul_add (a:=0) (b:=1) (fun x => F p x) (c p-1) 1
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),← integral_Icc_eq_integral_Ioc] at h
    simpa only [smul_eq_mul,mul_zero,zero_add,mul_one,sub_add_cancel,G] using h
  exact ((hc.sub continuous_const).mul hi).congr heq

end ErdosContinuousBoundary

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_BoundaryGateSets
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.MeasureTheory _root_.Set
namespace ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry

theorem boundaryTerm_continuous (n : ℕ) (i : Side) :
    Continuous (fun p : ℝ×ℝ => boundaryTerm n i p.1 p.2) := by
  induction n generalizing i with
  | zero => exact continuous_const
  | succ n ih =>
    let F : (ℝ×ℝ) → ℝ → ℝ := fun p x => boundaryTerm n i.flip (p.1-x) x/(max 1 x)
    have hchild : Continuous (fun q : (ℝ×ℝ)×ℝ => boundaryTerm n i.flip (q.1.1-q.2) q.2) :=
      (ih i.flip).comp ((continuous_fst.fst.sub continuous_snd).prodMk continuous_snd)
    have hden : Continuous (fun q : (ℝ×ℝ)×ℝ => (max 1 q.2)⁻¹) :=
      (continuous_const.max continuous_snd).inv₀ (fun q => ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left 1 q.2)))
    have hF : Continuous F.uncurry := by
      have he : F.uncurry = (fun q : (ℝ×ℝ)×ℝ => boundaryTerm n i.flip (q.1.1-q.2) q.2) *
          (fun q => (max 1 q.2)⁻¹) := by
        funext ⟨p,x⟩
        exact div_eq_mul_inv _ _
      rw [he]
      exact hchild.mul hden
    exact continuous_variable_upper_integral F hF (fun p => upperCutoff i p.1 p.2) (upperCutoff_continuous i)

theorem boundaryTerm_reciprocal (n : ℕ) (i : Side) (r b : ℝ) :
    boundaryTerm (n+1) i r b =
      ∫ x in (1:ℝ)..upperCutoff i r b,boundaryTerm n i.flip (r-x) x/x := by
  change (∫ x in (1:ℝ)..upperCutoff i r b,boundaryTerm n i.flip (r-x) x/(max 1 x)) = _
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le (upperCutoff_bounds i r b).1] at hx
  dsimp only
  rw [max_eq_right hx.1]

theorem boundaryTerm_odd_small (n : ℕ) {r b : ℝ} (hr : r ≤ 4) :
    boundaryTerm (n+1) .odd r b=0 := by
  rw [boundaryTerm,upperCutoff_odd_small hr,intervalIntegral.integral_same]

theorem boundaryTerm_depth_zero (n : ℕ) (i : Side) {r b : ℝ} (hr : r ≤ (n:ℝ)+1) :
    boundaryTerm (n+2) i r b=0 := by
  induction n generalizing i r b with
  | zero =>
    cases i with
    | odd => exact boundaryTerm_odd_small 1 (by norm_num at hr <;> linarith)
    | even =>
      rw [boundaryTerm]
      calc
        _ = ∫ _x in (1:ℝ)..upperCutoff .even r b,(0:ℝ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [uIcc_of_le (upperCutoff_bounds .even r b).1] at hx
          dsimp only [Side.flip]
          rw [boundaryTerm_odd_small 0 (by norm_num at hr <;> linarith [hx.1]),zero_div]
        _ = 0 := by simp
  | succ n ih =>
    rw [show n+1+2=(n+2)+1 by omega,boundaryTerm]
    calc
      _ = ∫ _x in (1:ℝ)..upperCutoff i r b,(0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (upperCutoff_bounds i r b).1] at hx
        dsimp only
        have hchild : r-x ≤ (n:ℝ)+1 := by push_cast at hr <;> linarith [hx.1]
        rw [ih i.flip hchild,zero_div]
      _ = 0 := by simp

end ErdosContinuousBoundary

end

section

open _root_.MeasureTheory _root_.Set
namespace ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry

theorem boundaryIntegrand_continuous (n : ℕ) (i : Side) (r : ℝ) :
    Continuous (boundaryIntegrand n i r) := by
  have hc : Continuous (fun x : ℝ => boundaryTerm n i.flip (r-x) x) :=
    (boundaryTerm_continuous n i.flip).comp ((continuous_const.sub continuous_id).prodMk continuous_id)
  have hd : Continuous (fun x : ℝ => (max 1 x)⁻¹) :=
    (continuous_const.max continuous_id).inv₀ (fun x => ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left 1 x)))
  have he : boundaryIntegrand n i r = (fun x => boundaryTerm n i.flip (r-x) x)*(fun x => (max 1 x)⁻¹) := by
    funext x
    exact div_eq_mul_inv _ _
  rw [he]
  exact hc.mul hd

theorem boundaryTerm_abs_le_one (n : ℕ) (i : Side) (r b : ℝ) : |boundaryTerm n i r b| ≤ 1 := by
  induction n generalizing i r b with
  | zero => norm_num [boundaryTerm]
  | succ n ih =>
    have hf (x : ℝ) : |boundaryTerm n i.flip (r-x) x/(max 1 x)| ≤ 1 := by
      have hd : 0 < max (1:ℝ) x := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
      rw [abs_div,abs_of_pos hd]
      exact (div_le_one hd).mpr ((ih i.flip (r-x) x).trans (le_max_left 1 x))
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a:=1) (b:=upperCutoff i r b)
      (C:=1) (f:=fun x => boundaryTerm n i.flip (r-x) x/(max 1 x))
      (fun x _ => by simpa only [Real.norm_eq_abs] using hf x)
    have hc := upperCutoff_bounds i r b
    change |boundaryTerm (n+1) i r b| ≤ 1
    rw [Real.norm_eq_abs,one_mul,abs_of_nonneg (by linarith : 0 ≤ upperCutoff i r b-1)] at h
    exact h.trans (by linarith)

theorem boundaryIntegrand_abs_le_one (n : ℕ) (i : Side) (r x : ℝ) :
    |boundaryIntegrand n i r x| ≤ 1 := by
  have hd : 0 < max (1:ℝ) x := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  rw [boundaryIntegrand,abs_div,abs_of_pos hd]
  exact (div_le_one hd).mpr ((boundaryTerm_abs_le_one n i.flip (r-x) x).trans (le_max_left 1 x))

end ErdosContinuousBoundary

end

section

namespace ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry

theorem boundaryTerm_r_difference (n : ℕ) (i : Side) (b r s : ℝ) :
    |boundaryTerm n i r b-boundaryTerm n i s b| ≤ (n:ℝ)*|r-s| := by
  induction n generalizing i b r s with
  | zero => simp [boundaryTerm]
  | succ n ih =>
    let D : ℝ := (n:ℝ)*|r-s|
    have hD : 0 ≤ D := by dsimp [D] <;> positivity
    have hFG (x : ℝ) : |boundaryIntegrand n i r x-boundaryIntegrand n i s x| ≤ D := by
      have hd : 0 < max (1:ℝ) x := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
      have hnum := ih i.flip x (r-x) (s-x)
      have he : (r-x)-(s-x)=r-s := by ring
      rw [he] at hnum
      unfold boundaryIntegrand
      rw [← sub_div,abs_div,abs_of_pos hd]
      exact (div_le_div_of_nonneg_right hnum hd.le).trans (div_le_self hD (le_max_left 1 x))
    have h := integral_upper_difference_bound
      (boundaryIntegrand n i r) (boundaryIntegrand n i s)
      (boundaryIntegrand_continuous n i r) (boundaryIntegrand_continuous n i s)
      (upperCutoff i r b) (upperCutoff i s b) D (upperCutoff_bounds i r b) hD hFG
      (boundaryIntegrand_abs_le_one n i s)
    have hc := upperCutoff_r_difference i b r s
    have hh : |boundaryTerm (n+1) i r b-boundaryTerm (n+1) i s b| ≤ D+|r-s| :=
      h.trans (add_le_add le_rfl hc)
    simpa only [D,Nat.cast_add,Nat.cast_one,add_mul,one_mul] using hh

theorem boundaryTerm_b_difference (n : ℕ) (i : Side) (r b c : ℝ) :
    |boundaryTerm n i r b-boundaryTerm n i r c| ≤ |b-c| := by
  cases n with
  | zero => simp [boundaryTerm]
  | succ n =>
    have h := integral_upper_difference_bound
      (boundaryIntegrand n i r) (boundaryIntegrand n i r)
      (boundaryIntegrand_continuous n i r) (boundaryIntegrand_continuous n i r)
      (upperCutoff i r b) (upperCutoff i r c) 0 (upperCutoff_bounds i r b) le_rfl
      (by intro x; simp) (boundaryIntegrand_abs_le_one n i r)
    have hh : |boundaryTerm (n+1) i r b-boundaryTerm (n+1) i r c| ≤
        |upperCutoff i r b-upperCutoff i r c| := by simpa only [zero_add] using! h
    exact hh.trans (upperCutoff_b_difference i r b c)

theorem boundaryTerm_child_lipschitz (n : ℕ) (i : Side) (r : ℝ) :
    LipschitzWith ((n:NNReal)+1) (fun x => boundaryTerm n i (r-x) x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]
  have h1 := boundaryTerm_r_difference n i x (r-x) (r-y)
  have he : (r-x)-(r-y)=-(x-y) := by ring
  rw [he,abs_neg] at h1
  have h2 := boundaryTerm_b_difference n i (r-y) x y
  calc
    _ = |(boundaryTerm n i (r-x) x-boundaryTerm n i (r-y) x)+
        (boundaryTerm n i (r-y) x-boundaryTerm n i (r-y) y)| := by congr 1; ring
    _ ≤ |boundaryTerm n i (r-x) x-boundaryTerm n i (r-y) x|+
        |boundaryTerm n i (r-y) x-boundaryTerm n i (r-y) y| := abs_add_le _ _
    _ ≤ (n:ℝ)*|x-y|+|x-y| := add_le_add h1 h2
    _ = _ := by ring

end ErdosContinuousBoundary

end

section

open _root_.MeasureTheory _root_.Set
namespace ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.ReferenceAdmission
open NumberTheoryLean.HarmonicPrimeAtomicMeasure NumberTheoryLean.HarmonicReferenceMeasure
open ErdosMonotoneQuadrature

theorem boundaryGateSet_closed (i : Side) (r b : ℝ) :
    boundaryGateSet i r b true=Ioc 1 (upperCutoff i r b) := by
  ext x
  exact (mem_upperCutoff i r b x).symm

theorem boundaryGateSet_open_inter (i : Side) (r b : ℝ) :
    boundaryGateSet i r b false=Ioc 1 (upperCutoff i r b) ∩ Iio b := by
  rw [← boundaryGateSet_closed]
  ext x
  change (1 < x ∧ x ≤ 2 ∧ x < b ∧ childAdmitted i r x) ↔
    (1 < x ∧ x ≤ 2 ∧ x ≤ b ∧ childAdmitted i r x) ∧ x < b
  constructor
  · rintro ⟨h1,h2,hb,hg⟩
    exact ⟨⟨h1,h2,hb.le,hg⟩,hb⟩
  · rintro ⟨⟨h1,h2,_hb,hg⟩,hb⟩
    exact ⟨h1,h2,hb,hg⟩

theorem boundaryGateSet_open_diff (i : Side) (r b : ℝ) :
    boundaryGateSet i r b false=Ioc 1 (upperCutoff i r b) \ {b} := by
  rw [← boundaryGateSet_closed]
  ext x
  change (1 < x ∧ x ≤ 2 ∧ x < b ∧ childAdmitted i r x) ↔
    (1 < x ∧ x ≤ 2 ∧ x ≤ b ∧ childAdmitted i r x) ∧ x ≠ b
  constructor
  · rintro ⟨h1,h2,hb,hg⟩
    exact ⟨⟨h1,h2,hb.le,hg⟩,ne_of_lt hb⟩
  · rintro ⟨⟨h1,h2,hb,hg⟩,hne⟩
    exact ⟨h1,h2,lt_of_le_of_ne hb hne,hg⟩

theorem boundaryGateSet_orderConnected (i : Side) (r b : ℝ) (closed : Bool) :
    (boundaryGateSet i r b closed).OrdConnected := by
  cases closed with
  | false => rw [boundaryGateSet_open_inter]; exact ordConnected_Ioc.inter ordConnected_Iio
  | true => rw [boundaryGateSet_closed]; exact ordConnected_Ioc

theorem boundaryGateSet_subset (i : Side) (r b : ℝ) (closed : Bool) :
    boundaryGateSet i r b closed ⊆ Icc 1 2 := fun _ hx => ⟨hx.1.le,hx.2.1⟩

theorem boundary_reference_integral (g : ℝ → ℝ) {J : Set ℝ}
    (hJ : MeasurableSet J) (hsub : J ⊆ Icc 1 2) :
    (∫ x in J,g x ∂referenceMeasure 1 2)=∫ x in J,g x/x := by
  rw [referenceMeasure,reciprocalMeasure_integral _ (by norm_num : (0:ℝ)<1) _ hJ,
    Measure.restrict_restrict hJ,inter_eq_left.mpr hsub]
  apply setIntegral_congr_fun hJ
  intro x hx
  dsimp only
  rw [reciprocalWeight_eq (hsub hx).1]
  simp only [div_eq_mul_inv,mul_comm]

theorem boundaryTerm_gate_integral (n : ℕ) (i : Side) (r b : ℝ) (closed : Bool) :
    (∫ x in boundaryGateSet i r b closed,boundaryTerm n i.flip (r-x) x ∂referenceMeasure 1 2)=
      boundaryTerm (n+1) i r b := by
  rw [boundary_reference_integral _ (boundaryGateSet_orderConnected i r b closed).measurableSet
    (boundaryGateSet_subset i r b closed),boundaryTerm_reciprocal,
    intervalIntegral.integral_of_le (upperCutoff_bounds i r b).1]
  cases closed with
  | true => rw [boundaryGateSet_closed]
  | false =>
    rw [boundaryGateSet_open_diff]
    exact setIntegral_congr_set (sdiff_null_ae_eq_self (measure_singleton b))

end ErdosContinuousBoundary

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_ContinuousReference
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.MeasureTheory _root_.Set _root_.Filter
open scoped Topology
namespace ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry

theorem boundaryTerm_zero_of_index (n : ℕ) (hn : 2 ≤ n) (i : Side) {r b : ℝ}
    (hr : r ≤ (n:ℝ)-1) : boundaryTerm n i r b=0 := by
  have he : n=(n-2)+2 := by omega
  rw [he]
  apply boundaryTerm_depth_zero
  have hc : ((n-2:ℕ):ℝ)=(n:ℝ)-2 := by rw [Nat.cast_sub hn]; norm_num
  linarith

theorem truncatedReference_stable {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M)
    (i : Side) {r b : ℝ} (hr : r ≤ (N:ℝ)-1) :
    truncatedReference N i r b=truncatedReference M i r b := by
  unfold truncatedReference
  apply Finset.sum_subset (Finset.range_mono hNM)
  intro n _hnM hnN
  have hNn : N ≤ n := le_of_not_gt (by simpa only [Finset.mem_range] using hnN)
  have hrn : r ≤ (n:ℝ)-1 := hr.trans (sub_le_sub_right (by exact_mod_cast hNn) 1)
  rw [boundaryTerm_zero_of_index n (hN.trans hNn) i hrn,mul_zero]

theorem referenceDepth_bounds (r : ℝ) : 2 ≤ referenceDepth r ∧ r ≤ (referenceDepth r : ℝ)-1 := by
  have h := Nat.le_ceil (max r 0)
  have hr : r ≤ max r 0 := le_max_left _ _
  unfold referenceDepth
  constructor
  · omega
  · push_cast
    linarith

theorem boundaryReference_eq_truncated (N : ℕ) (hN : 2 ≤ N) (i : Side)
    {r b : ℝ} (hr : r ≤ (N:ℝ)-1) : boundaryReference i r b=truncatedReference N i r b := by
  unfold boundaryReference
  rcases le_total (referenceDepth r) N with h | h
  · exact truncatedReference_stable (referenceDepth_bounds r).1 h i (referenceDepth_bounds r).2
  · exact (truncatedReference_stable hN h i hr).symm

end ErdosContinuousBoundary

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_BoundaryPrimeStep
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.MeasureTheory _root_.Set _root_.Finset
namespace ErdosContinuousBoundary
attribute [local instance] Classical.propDecidable
open NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.HarmonicPrimeAtomicMeasure NumberTheoryLean.HarmonicReferenceMeasure
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem boundary_prime_step_control : ∃ c C w₀ : ℝ,0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → (primeMeasure w 2).real (Icc 1 2) ≤ 1 ∧
      ∀ (n : ℕ) (i : Side) (r b : ℝ) (closed : Bool),
        |(∑ p ∈ Nat.primesLE ⌊w^(2:ℝ)⌋₊,if primeExponent w p ∈ boundaryGateSet i r b closed then
          (p:ℝ)⁻¹*boundaryTerm n i.flip (r-primeExponent w p) (primeExponent w p) else 0)-
          boundaryTerm (n+1) i r b| ≤ (12*(n:ℝ)+15)*boundaryPrimeError c C w := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,h⟩ := boundary_measure_control
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro w hw
  obtain ⟨hmass,hdiscr⟩ := h w hw
  refine ⟨hmass,?_⟩
  intro n i r b closed
  have hJ := boundaryGateSet_orderConnected i r b closed
  have hsub := boundaryGateSet_subset i r b closed
  let := referenceMeasure_finite (u:=1) (v:=2) (by norm_num)
  have hq := lipschitz_measure_discrepancy (primeMeasure w 2) (referenceMeasure 1 2)
    (fun x => boundaryTerm n i.flip (r-x) x) ((n:NNReal)+1) 1 (boundaryPrimeError c C w)
    (by norm_num) (boundaryTerm_child_lipschitz n i.flip r).lipschitzOnWith
    (fun x _ => boundaryTerm_abs_le_one n i.flip (r-x) x) hdiscr hJ hsub
  rw [primeMeasure_setIntegral w 2 _ hJ.measurableSet,boundaryTerm_gate_integral] at hq
  simp only [NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] at hq
  calc
    _ ≤ 3*boundaryPrimeError c C w*(1+4*((n:ℝ)+1)) := hq
    _ = _ := by ring

end ErdosContinuousBoundary

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_BoundaryReferenceConvergence
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.DiscreteBoundaryTerms

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry ReferenceAdmission ReferencePruning ReferencePrefixRecurrence
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail ErdosPrimeInputs.HarmonicPrimeMeasure

theorem D_sum (n : ℕ) (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) :
    D n w P i r=∑ ps ∈ decreasingPrefixes P,
      if admitted w i r ps ∧ ps.length=n then prefixWeight ps else 0 := by
  rw [D,referencePrefixes,Finset.filter_filter,Finset.sum_filter]

theorem D_zero (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) : D 0 w P i r=1 := by
  have he : (referencePrefixes w P i r).filter (fun ps => ps.length=0)={[]} := by
    ext ps
    simp only [Finset.mem_filter,List.length_eq_zero_iff,Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · intro hp
      subst ps
      refine ⟨Finset.mem_filter.mpr ⟨mem_decreasingPrefixes.mpr ⟨by simp,by simp⟩,trivial⟩,rfl⟩
  rw [D,he,Finset.sum_singleton]
  simp [prefixWeight]

theorem D_succ (n : ℕ) (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) :
    D (n+1) w P i r=∑ p ∈ P,if childAdmitted i r (primeExponent w p) then
      (p:ℝ)⁻¹*D n w (P.filter (fun q => q<p)) i.flip (r-primeExponent w p) else 0 := by
  rw [D_sum,sum_decreasing_by_first]
  have hempty : (if admitted w i r [] ∧ ([]:List ℕ).length=n+1 then prefixWeight [] else 0)=0 := by simp
  rw [hempty,zero_add]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hc : childAdmitted i r (primeExponent w p)
  · rw [ite_eq_left hc,D_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ps _hps
    simp only [admitted,hc,true_and,List.length_cons,Nat.add_right_cancel_iff]
    split_ifs <;> simp [prefixWeight]
  · simp [admitted,hc]

end NumberTheoryLean.DiscreteBoundaryTerms

end

section

namespace NumberTheoryLean.DiscreteBoundaryDepth

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry ReferenceAdmission DiscreteBoundaryTerms
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail ErdosPrimeInputs.HarmonicPrimeMeasure

theorem odd_gate_impossible {w r : ℝ} {p : ℕ} (hp : 1 < primeExponent w p) (hr : r ≤ 4) :
    ¬childAdmitted .odd r (primeExponent w p) := by
  intro h
  have hh := (le_max_right (2*primeExponent w p) (primeExponent w p+2)).trans h
  nlinarith

theorem odd_term_zero (n : ℕ) (w : ℝ) (P : Finset ℕ) {r : ℝ}
    (hP : ∀ p ∈ P,1 < primeExponent w p) (hr : r ≤ 4) : D (n+1) w P .odd r=0 := by
  rw [D_succ]
  apply Finset.sum_eq_zero
  intro p hp
  rw [ite_eq_right (odd_gate_impossible (hP p hp) hr)]

theorem D_two_zero (w : ℝ) (P : Finset ℕ) (i : Side) {r : ℝ}
    (hP : ∀ p ∈ P,1 < primeExponent w p) (hr : r ≤ 1) : D 2 w P i r=0 := by
  cases i with
  | odd => exact odd_term_zero 1 w P hP (by linarith)
  | even =>
    rw [show (2:ℕ)=1+1 from rfl,D_succ]
    apply Finset.sum_eq_zero
    intro p hp
    have ht : D 1 w (P.filter (fun q => q<p)) .odd (r-primeExponent w p)=0 :=
      odd_term_zero 0 w _ (fun q hq => hP q (Finset.mem_filter.mp hq).1) (by have hx := hP p hp; linarith)
    simp only [childAdmitted,ite_true, if_true,Side.flip,ht,mul_zero]

theorem D_vanish (n : ℕ) (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ)
    (hP : ∀ p ∈ P,1 < primeExponent w p) (hr : r ≤ (n:ℝ)+1) : D (n+2) w P i r=0 := by
  induction n generalizing P i r with
  | zero => exact D_two_zero w P i hP (by simpa only [Nat.cast_zero,zero_add] using hr)
  | succ n ih =>
    rw [show n+1+2=(n+2)+1 by omega,D_succ]
    apply Finset.sum_eq_zero
    intro p hp
    have hx := hP p hp
    have hr' : r-primeExponent w p ≤ (n:ℝ)+1 := by
      push_cast at hr
      linarith
    have hz := ih (P:=P.filter (fun q => q<p)) (i:=i.flip) (r:=r-primeExponent w p)
      (fun q hq => hP q (Finset.mem_filter.mp hq).1) hr'
    simp only [hz,mul_zero,ite_self]

theorem prefixWeight_positive {w : ℝ} {P : Finset ℕ} {ps : List ℕ}
    (hP : ∀ p ∈ P,1 < primeExponent w p) (hm : ∀ p ∈ ps,p ∈ P) : 0 < prefixWeight ps := by
  induction ps with
  | nil => simp [prefixWeight]
  | cons p ps ih =>
    have hp := hP p (hm p (by simp))
    have hp0 : p ≠ 0 := by
      intro he
      simp only [he,primeExponent,Nat.cast_zero,Real.log_zero,zero_div] at hp
      linarith
    have hpr : 0 < (p:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hp0
    have ht := ih (fun q hq => hm q (by simp [hq]))
    simpa only [prefixWeight,List.map_cons,List.prod_cons] using mul_pos (inv_pos.mpr hpr) ht

theorem D_positive_of_member {w r : ℝ} {P : Finset ℕ} {i : Side} {ps : List ℕ}
    (hP : ∀ p ∈ P,1 < primeExponent w p) (hp : ps ∈ referencePrefixes w P i r) :
    0 < D ps.length w P i r := by
  apply Finset.sum_pos' (fun qs _ => prefixWeight_nonneg qs)
  refine ⟨ps,Finset.mem_filter.mpr ⟨hp,rfl⟩,?_⟩
  exact prefixWeight_positive hP (mem_decreasingPrefixes.mp (Finset.mem_filter.mp hp).1).2

theorem admitted_length_lt {w r : ℝ} {P : Finset ℕ} {i : Side} {N : ℕ}
    (hP : ∀ p ∈ P,1 < primeExponent w p) (hN : 2 ≤ N) (hr : r ≤ (N:ℝ)-1)
    {ps : List ℕ} (hp : ps ∈ referencePrefixes w P i r) : ps.length<N := by
  by_contra hn
  have hlen : N ≤ ps.length := le_of_not_gt hn
  have hlen2 : 2 ≤ ps.length := hN.trans hlen
  have he : ps.length-2+2=ps.length := Nat.sub_add_cancel hlen2
  have hcast : (N:ℝ) ≤ (ps.length:ℝ) := by exact_mod_cast hlen
  have hecast : ((ps.length-2:ℕ):ℝ)+2=(ps.length:ℝ) := by exact_mod_cast he
  have hr' : r ≤ ((ps.length-2:ℕ):ℝ)+1 := by linarith
  have hz := D_vanish (ps.length-2) w P i r hP hr'
  rw [he] at hz
  have hpos := D_positive_of_member hP hp
  rw [hz] at hpos
  linarith

end NumberTheoryLean.DiscreteBoundaryDepth

end

section

namespace NumberTheoryLean.DiscreteBoundaryExpansion

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry ReferenceAdmission DiscreteBoundaryTerms DiscreteBoundaryDepth
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.HarmonicPrimeMeasure

theorem referencePolynomial_finite_sum (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) (N : ℕ)
    (hP : ∀ p ∈ P,1 < primeExponent w p) (hN : 2 ≤ N) (hr : r ≤ (N:ℝ)-1) :
    referencePolynomial w P i r=∑ n ∈ Finset.range N,(-1:ℝ)^n*D n w P i r := by
  have hmap : ∀ ps ∈ referencePrefixes w P i r,ps.length ∈ Finset.range N := by
    intro ps hp
    exact Finset.mem_range.mpr (admitted_length_lt hP hN hr hp)
  have hf := Finset.sum_fiberwise_of_maps_to (g:=List.length) hmap
    (fun ps : List ℕ => (-1:ℝ)^ps.length*prefixWeight ps)
  calc
    _ = ∑ n ∈ Finset.range N,∑ ps ∈ (referencePrefixes w P i r).filter (fun ps => ps.length=n),
        (-1:ℝ)^ps.length*prefixWeight ps := hf.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [D,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ps hp
      rw [(Finset.mem_filter.mp hp).2]

end NumberTheoryLean.DiscreteBoundaryExpansion

end

section

namespace NumberTheoryLean.ActualDiscreteBoundaryTerms

attribute [local instance] Classical.propDecidable

open _root_.Finset
open FinitePathGeometry ReferenceAdmission ReferenceProductsBasics ReferenceSourcePrimeSets
open DiscreteBoundaryTerms DiscreteBoundaryDepth DiscreteBoundaryExpansion
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem actualD_zero (w b : ℝ) (closed : Bool) (i : Side) (r : ℝ) : actualD 0 w b closed i r=1 :=
  D_zero w _ i r

theorem selected_exponent_bounds {w : ℝ} (hw : 1 < w) (b : ℝ) (closed : Bool) {p : ℕ}
    (hp : p ∈ availablePrimes w (w^b) closed) : 1 < primeExponent w p ∧ primeExponent w p ≤ b := by
  obtain ⟨_hp,hlo,hcap⟩ := (sourcePrimes_membership hw b closed p).mp hp
  refine ⟨hlo,?_⟩
  cases closed
  · exact hcap.le
  · exact hcap

theorem selected_available_set {w : ℝ} (hw : 1 < w) (b : ℝ) (closed : Bool) {p : ℕ}
    (hp : p ∈ availablePrimes w (w^b) closed) :
    availablePrimes w (w^primeExponent w p) false=
      (availablePrimes w (w^b) closed).filter (fun q => q<p) :=
  sourcePrimes_at_selected hw closed hp

theorem actualD_succ (n : ℕ) {w : ℝ} (hw : 1 < w) (b : ℝ) (closed : Bool) (i : Side) (r : ℝ) :
    actualD (n+1) w b closed i r=
      ∑ p ∈ availablePrimes w (w^b) closed,if childAdmitted i r (primeExponent w p) then
        (p:ℝ)⁻¹*actualD n w (primeExponent w p) false i.flip (r-primeExponent w p) else 0 := by
  unfold actualD
  rw [D_succ]
  apply Finset.sum_congr rfl
  intro p hp
  rw [selected_available_set hw b closed hp]

theorem boundary_exponent_bounds {w b : ℝ} (hw : 1 < w) (_hb1 : 1 ≤ b) (hb2 : b ≤ 2) (closed : Bool) :
    ∀ p ∈ availablePrimes w (w^b) closed,1 < primeExponent w p ∧ primeExponent w p ≤ 2 := by
  intro p hp
  have h := selected_exponent_bounds hw b closed hp
  exact ⟨h.1,h.2.trans hb2⟩

theorem actual_reference_finite_sum {w b : ℝ} (hw : 1 < w) (hb1 : 1 ≤ b) (hb2 : b ≤ 2)
    (closed : Bool) (i : Side) (r : ℝ) (N : ℕ) (hN : 2 ≤ N) (hr : r ≤ (N:ℝ)-1) :
    referencePolynomial w (availablePrimes w (w^b) closed) i r=
      ∑ n ∈ Finset.range N,(-1:ℝ)^n*actualD n w b closed i r :=
  referencePolynomial_finite_sum w _ i r N (fun p hp => (boundary_exponent_bounds hw hb1 hb2 closed p hp).1) hN hr

end NumberTheoryLean.ActualDiscreteBoundaryTerms

end

section

open _root_.MeasureTheory _root_.Set _root_.Finset
namespace ErdosContinuousBoundary
attribute [local instance] Classical.propDecidable
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.ReferenceAdmission
open NumberTheoryLean.ReferenceProductsBasics NumberTheoryLean.ReferenceSourcePrimeSets
open NumberTheoryLean.ActualDiscreteBoundaryTerms NumberTheoryLean.HarmonicPrimeAtomicMeasure
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem available_boundary_subset {w b : ℝ} (hw : 1 < w) (hb : b ≤ 2) (closed : Bool) :
    availablePrimes w (w^b) closed ⊆ Nat.primesLE ⌊w^(2:ℝ)⌋₊ := by
  intro p hp
  have hpm := (sourcePrimes_membership hw b closed p).mp hp
  have hx := (selected_exponent_bounds hw b closed hp).2.trans hb
  have hpReal := (exponent_le_iff hw (by exact_mod_cast hpm.1.pos)).mp hx
  exact Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff (Real.rpow_pos_of_pos (by linarith : 0 < w) 2).le).mpr hpReal,hpm.1⟩

theorem boundary_gate_membership {w b : ℝ} (hw : 1 < w) (hb : b ≤ 2)
    (closed : Bool) (i : Side) (r : ℝ) {p : ℕ} (hp : p ∈ Nat.primesLE ⌊w^(2:ℝ)⌋₊) :
    primeExponent w p ∈ boundaryGateSet i r b closed ↔
      p ∈ availablePrimes w (w^b) closed ∧ childAdmitted i r (primeExponent w p) := by
  have hprime := (Nat.mem_primesLE.mp hp).2
  constructor
  · intro h
    refine ⟨(sourcePrimes_membership hw b closed p).mpr ⟨hprime,h.1,?_⟩,h.2.2.2⟩
    exact h.2.2.1
  · rintro ⟨hP,hgate⟩
    have h := (sourcePrimes_membership hw b closed p).mp hP
    have hx2 := (selected_exponent_bounds hw b closed hP).2.trans hb
    exact ⟨h.2.1,hx2,h.2.2,hgate⟩

theorem available_gate_sum {w b : ℝ} (hw : 1 < w) (hb : b ≤ 2)
    (closed : Bool) (i : Side) (r : ℝ) (F : ℕ → ℝ) :
    (∑ p ∈ availablePrimes w (w^b) closed,if childAdmitted i r (primeExponent w p) then
      (p:ℝ)⁻¹*F p else 0) =
    ∑ p ∈ Nat.primesLE ⌊w^(2:ℝ)⌋₊,if primeExponent w p ∈ boundaryGateSet i r b closed then
      (p:ℝ)⁻¹*F p else 0 := by
  have hsub := available_boundary_subset hw hb closed
  calc
    _ = ∑ p ∈ availablePrimes w (w^b) closed,if primeExponent w p ∈ boundaryGateSet i r b closed then
        (p:ℝ)⁻¹*F p else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      have he : primeExponent w p ∈ boundaryGateSet i r b closed ↔ childAdmitted i r (primeExponent w p) := by
        rw [boundary_gate_membership hw hb closed i r (hsub hp)]
        simp only [hp,true_and]
      simp only [he]
    _ = _ := Finset.sum_subset hsub (by
      intro p hp hnot
      apply ite_eq_right
      intro hgate
      exact hnot ((boundary_gate_membership hw hb closed i r hp).mp hgate).1)

theorem actualD_succ_gate_sum (n : ℕ) {w b : ℝ} (hw : 1 < w) (hb : b ≤ 2)
    (closed : Bool) (i : Side) (r : ℝ) :
    actualD (n+1) w b closed i r =
      ∑ p ∈ Nat.primesLE ⌊w^(2:ℝ)⌋₊,if primeExponent w p ∈ boundaryGateSet i r b closed then
        (p:ℝ)⁻¹*actualD n w (primeExponent w p) false i.flip (r-primeExponent w p) else 0 := by
  rw [actualD_succ n hw b closed i r]
  exact available_gate_sum hw hb closed i r _

theorem prime_gate_sum_difference (w : ℝ) (i : Side) (r b : ℝ) (closed : Bool)
    (F G : ℕ → ℝ) (A : ℝ)
    (hFG : ∀ p ∈ Nat.primesLE ⌊w^(2:ℝ)⌋₊,primeExponent w p ∈ boundaryGateSet i r b closed → |F p-G p| ≤ A) :
    |(∑ p ∈ Nat.primesLE ⌊w^(2:ℝ)⌋₊,if primeExponent w p ∈ boundaryGateSet i r b closed then (p:ℝ)⁻¹*F p else 0)-
      (∑ p ∈ Nat.primesLE ⌊w^(2:ℝ)⌋₊,if primeExponent w p ∈ boundaryGateSet i r b closed then (p:ℝ)⁻¹*G p else 0)| ≤
      A*(primeMeasure w 2).real (boundaryGateSet i r b closed) := by
  rw [primeMeasure_real w 2 (boundaryGateSet_orderConnected i r b closed).measurableSet,Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  by_cases hg : primeExponent w p ∈ boundaryGateSet i r b closed
  · rw [ite_eq_left hg,ite_eq_left hg,ite_eq_left hg,← mul_sub,abs_mul,abs_of_nonneg (by positivity : 0 ≤ (p:ℝ)⁻¹)]
    have h := mul_le_mul_of_nonneg_left (hFG p hp hg) (by positivity : 0 ≤ (p:ℝ)⁻¹)
    simpa only [mul_comm] using h
  · simp only [hg,ite_false, if_false,sub_self,abs_zero,mul_zero,le_refl]

end ErdosContinuousBoundary

end

section

open _root_.MeasureTheory _root_.Set _root_.Finset
namespace ErdosContinuousBoundary
attribute [local instance] Classical.propDecidable
open NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.ActualDiscreteBoundaryTerms NumberTheoryLean.HarmonicPrimeAtomicMeasure
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem actualD_uniform_approximation : ∃ c C w₀ : ℝ,0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ (n : ℕ) (w : ℝ),w₀ ≤ w → ∀ (i : Side) (r b : ℝ) (closed : Bool),
      1 ≤ b → b ≤ 2 →
      |actualD n w b closed i r-boundaryTerm n i r b| ≤ 15*(n:ℝ)^2*boundaryPrimeError c C w := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,hControl⟩ := boundary_prime_step_control
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro n
  induction n with
  | zero =>
    intro w _hw i r b closed _hb1 _hb2
    rw [actualD_zero]
    norm_num [boundaryTerm]
  | succ n ih =>
    intro w hw i r b closed _hb1 hb2
    have hw1 : 1 < w := hw₀.trans_le hw
    obtain ⟨hMass,hStep⟩ := hControl w hw
    let E := boundaryPrimeError c C w
    have hE : 0 ≤ E := by dsimp [E,boundaryPrimeError] <;> positivity
    let A := 15*(n:ℝ)^2*E
    have hA : 0 ≤ A := by dsimp [A] <;> positivity
    let J := boundaryGateSet i r b closed
    let F : ℕ → ℝ := fun p => actualD n w (primeExponent w p) false i.flip (r-primeExponent w p)
    let G : ℕ → ℝ := fun p => boundaryTerm n i.flip (r-primeExponent w p) (primeExponent w p)
    have hFG : ∀ p ∈ Nat.primesLE ⌊w^(2:ℝ)⌋₊,primeExponent w p ∈ J → |F p-G p| ≤ A := by
      intro p _hp hJ
      exact ih w hw i.flip (r-primeExponent w p) (primeExponent w p) false hJ.1.le hJ.2.1
    have hsum := prime_gate_sum_difference w i r b closed F G A hFG
    have hM : (primeMeasure w 2).real J ≤ 1 :=
      (measureReal_mono (boundaryGateSet_subset i r b closed)).trans hMass
    have hsum' :
        |(∑ p ∈ Nat.primesLE ⌊w^(2:ℝ)⌋₊,if primeExponent w p ∈ J then (p:ℝ)⁻¹*F p else 0)-
          (∑ p ∈ Nat.primesLE ⌊w^(2:ℝ)⌋₊,if primeExponent w p ∈ J then (p:ℝ)⁻¹*G p else 0)| ≤ A := by
      exact hsum.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hM hA)
    have hstep := hStep n i r b closed
    have heq := actualD_succ_gate_sum n hw1 hb2 closed i r
    rw [heq]
    calc
      _ ≤ A+(12*(n:ℝ)+15)*E := by
        have he :
            (∑ p ∈ Nat.primesLE ⌊w^(2:ℝ)⌋₊,if primeExponent w p ∈ J then (p:ℝ)⁻¹*F p else 0)-boundaryTerm (n+1) i r b =
            ((∑ p ∈ Nat.primesLE ⌊w^(2:ℝ)⌋₊,if primeExponent w p ∈ J then (p:ℝ)⁻¹*F p else 0)-
              (∑ p ∈ Nat.primesLE ⌊w^(2:ℝ)⌋₊,if primeExponent w p ∈ J then (p:ℝ)⁻¹*G p else 0))+
            ((∑ p ∈ Nat.primesLE ⌊w^(2:ℝ)⌋₊,if primeExponent w p ∈ J then (p:ℝ)⁻¹*G p else 0)-boundaryTerm (n+1) i r b) := by ring
        change |(∑ p ∈ Nat.primesLE ⌊w^(2:ℝ)⌋₊,if primeExponent w p ∈ J then (p:ℝ)⁻¹*F p else 0)-boundaryTerm (n+1) i r b| ≤ _
        rw [he]
        exact (abs_add_le _ _).trans (add_le_add hsum' hstep)
      _ = (15*(n:ℝ)^2+(12*(n:ℝ)+15))*E := by dsimp [A] <;> ring
      _ ≤ 15*((n+1:ℕ):ℝ)^2*E := by
        apply mul_le_mul_of_nonneg_right _ hE
        push_cast
        nlinarith [Nat.cast_nonneg (α:=ℝ) n]

end ErdosContinuousBoundary

end

section

open _root_.MeasureTheory _root_.Set _root_.Finset _root_.Filter
open scoped Topology
namespace ErdosContinuousBoundary
attribute [local instance] Classical.propDecidable
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.ReferenceAdmission
open NumberTheoryLean.ReferenceProductsBasics NumberTheoryLean.ActualDiscreteBoundaryTerms

theorem finite_reference_error {c C w : ℝ} (hC : 0 ≤ C) (hw : 1 < w)
    (hterms : ∀ (n : ℕ) (i : Side) (r b : ℝ) (closed : Bool),1 ≤ b → b ≤ 2 →
      |actualD n w b closed i r-boundaryTerm n i r b| ≤ 15*(n:ℝ)^2*boundaryPrimeError c C w)
    (N : ℕ) (hN : 2 ≤ N) (i : Side) (r b : ℝ) (closed : Bool)
    (hr : r ≤ (N:ℝ)-1) (hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    |referencePolynomial w (availablePrimes w (w^b) closed) i r-boundaryReference i r b| ≤
      15*(N:ℝ)^3*boundaryPrimeError c C w := by
  rw [actual_reference_finite_sum hw hb1 hb2 closed i r N hN hr,
    boundaryReference_eq_truncated N hN i hr,truncatedReference,← Finset.sum_sub_distrib]
  have hE : 0 ≤ boundaryPrimeError c C w := by unfold boundaryPrimeError; positivity
  calc
    _ ≤ ∑ n ∈ Finset.range N,
        |(-1:ℝ)^n*actualD n w b closed i r-(-1:ℝ)^n*boundaryTerm n i r b| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.range N,15*(N:ℝ)^2*boundaryPrimeError c C w := by
      apply Finset.sum_le_sum
      intro n hn
      rw [← mul_sub,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
      apply (hterms n i r b closed hb1 hb2).trans
      have hnN : (n:ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.mp hn).le
      gcongr
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] <;> ring

theorem uniform_boundary_reference_convergence (R eps : ℝ) (heps : 0 < eps) :
    ∃ w₀ : ℝ,1 < w₀ ∧ ∀ w : ℝ,w₀ ≤ w → ∀ (i : Side) (r b : ℝ) (closed : Bool),
      r ≤ R → 1 ≤ b → b ≤ 2 →
      |referencePolynomial w (availablePrimes w (w^b) closed) i r-boundaryReference i r b| ≤ eps := by
  obtain ⟨c,C,wD,hc,hC,hwD,hD⟩ := actualD_uniform_approximation
  let N := referenceDepth R
  have hN : 2 ≤ N := (referenceDepth_bounds R).1
  have hdepth : R ≤ (N:ℝ)-1 := (referenceDepth_bounds R).2
  have ht := (boundaryPrimeError_tendsto_zero hc C).const_mul (15*(N:ℝ)^3)
  have he := ht.eventually (Iio_mem_nhds (by simpa only [mul_zero] using heps))
  obtain ⟨wE,hwE⟩ := eventually_atTop.mp he
  refine ⟨max wD wE,hwD.trans_le (le_max_left _ _),?_⟩
  intro w hw i r b closed hr hb1 hb2
  have hwd : wD ≤ w := (le_max_left _ _).trans hw
  have hwe := hwE w ((le_max_right _ _).trans hw)
  have hh := finite_reference_error hC.le (hwD.trans_le hwd)
    (fun n j s a cl ha1 ha2 => hD n w hwd j s a cl ha1 ha2)
    N hN i r b closed (hr.trans hdepth) hb1 hb2
  exact hh.trans hwe.le

theorem boundary_two_convergence (R eps : ℝ) (heps : 0 < eps) :
    ∃ w₀ : ℝ,1 < w₀ ∧ ∀ w : ℝ,w₀ ≤ w → ∀ (i : Side) (r : ℝ),r ≤ R →
      |referencePolynomial w (boundaryPrimes w) i r-boundaryReference i r 2| ≤ eps := by
  obtain ⟨w₀,hw₀,h⟩ := uniform_boundary_reference_convergence R eps heps
  refine ⟨w₀,hw₀,?_⟩
  intro w hw i r hr
  simpa only [availablePrimes_closed,boundaryPrimes] using h w hw i r 2 true hr (by norm_num) le_rfl

end ErdosContinuousBoundary

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_WeightedAnomalyConvergence
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.MeasureTheory _root_.Set _root_.Filter
open _root_.Erdos970.MeasureTheory _root_.Erdos970.Set _root_.Erdos970.Filter
open scoped Topology
namespace ErdosContinuousAnomaly
open ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.ReferenceAdmission
open NumberTheoryLean.ReferenceBenchmarkDecay NumberTheoryLean.BoundaryAnomaly
open NumberTheoryLean.LinearSieveFunctions NumberTheoryLean.BuchstabBridge

theorem boundary_benchmark_bound (i : Side) {r : ℝ} (hr : 2 ≤ r) :
    |benchmark i (r/2)| ≤ sieveA+1 := by
  have hs : 1 ≤ r/2 := by linarith
  have h := (benchmark_deviation_le_gap i hs).trans (gap_le_constant hs)
  calc
    _ = |(benchmark i (r/2)-1)+1| := by congr 1; ring
    _ ≤ |benchmark i (r/2)-1|+|1| := abs_add_le _ _
    _ ≤ sieveA+1 := by simpa only [abs_one] using add_le_add h (le_refl (1:ℝ))

theorem anomaly_difference (w r : ℝ) (i : Side) :
    anomaly w i r-continuousAnomaly i r =
      (referencePolynomial w (boundaryPrimes w) i r-boundaryReference i r 2)-
        (boundaryProduct w-1/2)*benchmark i (r/2) := by
  unfold anomaly continuousAnomaly boundaryProduct
  ring

theorem uniform_anomaly_convergence (R eps : ℝ) (heps : 0 < eps) :
    ∃ w₀ : ℝ,1 < w₀ ∧ ∀ w : ℝ,w₀ ≤ w → ∀ (i : Side) (r : ℝ),2 ≤ r → r ≤ R →
      |anomaly w i r-continuousAnomaly i r| ≤ eps := by
  let A : ℝ := sieveA+1
  have hA : 0 < A := by dsimp [A] <;> linarith [sieveA_pos]
  obtain ⟨wQ,hwQ,hQ⟩ := boundary_two_convergence R (eps/2) (by positivity)
  have ht := (boundaryProduct_tendsto_half.sub_const (1/2)).abs
  have he := ht.eventually (Iio_mem_nhds (by simpa only [sub_self,abs_zero] using
    (div_pos heps (by positivity : 0 < 2*A))))
  obtain ⟨wP,hwP⟩ := eventually_atTop.mp he
  refine ⟨max wQ wP,hwQ.trans_le (le_max_left _ _),?_⟩
  intro w hw i r hr hrR
  have hqw := hQ w ((le_max_left _ _).trans hw) i r hrR
  have hpw := hwP w ((le_max_right _ _).trans hw)
  have hb : |benchmark i (r/2)| ≤ A := boundary_benchmark_bound i hr
  have hp : |boundaryProduct w-1/2| * |benchmark i (r/2)| ≤ (eps/(2*A))*A := by
    exact mul_le_mul hpw.le hb (abs_nonneg _) (by positivity)
  rw [anomaly_difference]
  apply (abs_sub _ _).trans
  rw [abs_mul]
  calc
    _ ≤ eps/2+(eps/(2*A))*A := add_le_add hqw hp
    _ = eps := by field_simp [ne_of_gt hA] <;> ring

end ErdosContinuousAnomaly

end

section

open _root_.Set _root_.Filter _root_.Erdos970.Set _root_.Erdos970.Filter
open scoped Topology
namespace ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.BoundaryAnomaly

theorem weighted_anomaly_convergence_jb247_oai : ∃ c : ℝ,0 < c ∧
    ∀ eps : ℝ,0 < eps → ∃ w₀ : ℝ,1 < w₀ ∧
      ∀ w : ℝ,w₀ ≤ w → ∀ r : ℝ,2 ≤ r → ∀ i : Side,
        |anomaly w i r-continuousAnomaly i r| ≤ eps*Real.exp (-c*r) := by
  obtain ⟨C,c₀,wA,hC,hc₀,hwA,hdiscrete,hcontinuous⟩ := common_anomaly_exponential_jb247
  let c := c₀/2
  have hc : 0 < c := by dsimp [c] <;> positivity
  refine ⟨c,hc,?_⟩
  intro eps heps
  have ht : Tendsto (fun r : ℝ => (2*C)*Real.exp (-c*r)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0:ℝ) c hc).const_mul (2*C)
    simpa only [Real.rpow_zero,one_mul,mul_zero] using h
  obtain ⟨R₁,hR₁⟩ := eventually_atTop.mp (ht.eventually (Iio_mem_nhds heps))
  let R := max 2 R₁
  obtain ⟨wQ,hwQ,hQ⟩ := uniform_anomaly_convergence R (eps*Real.exp (-c*R)) (by positivity)
  refine ⟨max wA wQ,hwA.trans_le (le_max_left _ _),?_⟩
  intro w hw r hr i
  have hwa : wA ≤ w := (le_max_left _ _).trans hw
  have hwq : wQ ≤ w := (le_max_right _ _).trans hw
  by_cases hrR : r ≤ R
  · apply (hQ w hwq i r hr hrR).trans
    apply mul_le_mul_of_nonneg_left _ heps.le
    apply Real.exp_le_exp.mpr
    nlinarith
  · have htail : 2*C*Real.exp (-c*r) ≤ eps :=
      (hR₁ r ((le_max_right 2 R₁).trans (le_of_not_ge hrR))).le
    have hbound : |anomaly w i r-continuousAnomaly i r| ≤ 2*C*Real.exp (-c₀*r) := by
      calc
        _ ≤ |anomaly w i r|+|continuousAnomaly i r| := abs_sub _ _
        _ ≤ C*Real.exp (-c₀*r)+C*Real.exp (-c₀*r) :=
          add_le_add (hdiscrete w hwa r hr i) (hcontinuous r hr i)
        _ = _ := by ring
    have he : -c₀*r=(-c*r)+(-c*r) := by dsimp [c] <;> ring
    rw [he,Real.exp_add] at hbound
    calc
      _ ≤ 2*C*(Real.exp (-c*r)*Real.exp (-c*r)) := hbound
      _ = (2*C*Real.exp (-c*r))*Real.exp (-c*r) := by ring
      _ ≤ eps*Real.exp (-c*r) := mul_le_mul_of_nonneg_right htail (Real.exp_pos _).le

end ErdosContinuousAnomaly

end

end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.ErdosContinuousAnomaly.weighted_anomaly_convergence_jb247_oai := @OAI.Erdos970.ErdosContinuousAnomaly.weighted_anomaly_convergence_jb247_oai
