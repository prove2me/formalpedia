-- Prove2me | solution 1 for OAI.Erdos970.NumberTheoryLean.LowStateResidualBound.low_state_normalized_residual_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:06:25.007322+00:00
-- url     : https://prove2.me/submissions/84181b38-4e3f-4107-843f-e53b524569cb

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.GeomSum
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
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
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
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Divisors
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
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UrysohnsLemma
import Definitions.Def_OAIQ247J010
import Theorems.Thm_Erdos970_Mertens_LogZetaInteg_log_zeta_eq_integ_aux_jb247
import Theorems.Thm_Erdos970_Mertens_sum_M_eq_summand_le_jb247

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

theorem reciprocalWeight_antitone {u : ℝ} (hu : 0 < u) :
    Antitone (reciprocalWeight u) := by
  intro x y hxy
  exact inv_anti₀ (hu.trans_le (le_max_left u x)) (max_le_max_left u hxy)

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

theorem reciprocalMeasure_discrepancy
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (u v E : ℝ) (hu : 0 < u)
    (hd : ∀ S : Set ℝ, S.OrdConnected → S ⊆ Icc u v → |μ.real S-ν.real S| ≤ E)
    {J : Set ℝ} (hJ : J.OrdConnected) (hsub : J ⊆ Icc u v) :
    |(reciprocalMeasure μ u).real J-(reciprocalMeasure ν u).real J| ≤ E*u⁻¹ := by
  rw [reciprocalMeasure_real μ hu hJ.measurableSet,reciprocalMeasure_real ν hu hJ.measurableSet]
  exact nonnegative_monotone_integral_discrepancy μ ν u v u⁻¹ E (inv_nonneg.mpr hu.le)
    (reciprocalWeight u) (Or.inr ((reciprocalWeight_antitone hu).antitoneOn _))
    (fun x _ => (reciprocalWeight_pos hu x).le) (fun x _ => reciprocalWeight_le hu x) hd hJ hsub

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

section

open MeasureTheory Set
namespace ErdosMonotoneQuadrature

theorem weighted_monotone_discrepancy
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (u v D E : ℝ) (hu : 0 < u) (hD : 0 ≤ D) (g : ℝ → ℝ)
    (hg : MonotoneOn g (Icc u v) ∨ AntitoneOn g (Icc u v))
    (hbound : ∀ x ∈ Icc u v, |g x| ≤ D)
    (hd : ∀ S : Set ℝ, S.OrdConnected → S ⊆ Icc u v → |μ.real S-ν.real S| ≤ E)
    {J : Set ℝ} (hJ : J.OrdConnected) (hsub : J ⊆ Icc u v) :
    |(∫ x in J, g x/x ∂μ) - ∫ x in J, g x/x ∂ν| ≤ 3*E*D/u := by
  let := reciprocalMeasure_finite μ hu
  let := reciprocalMeasure_finite ν hu
  have h := signed_monotone_integral_discrepancy (reciprocalMeasure μ u)
    (reciprocalMeasure ν u) u v D (E*u⁻¹) hD g hg hbound
    (fun S hS hs => reciprocalMeasure_discrepancy μ ν u v E hu hd hS hs) hJ hsub
  have hm : (∫ x in J, g x ∂reciprocalMeasure μ u) = ∫ x in J, g x/x ∂μ := by
    rw [reciprocalMeasure_integral μ hu g hJ.measurableSet]
    apply setIntegral_congr_fun hJ.measurableSet
    intro x hx
    dsimp only
    rw [reciprocalWeight_eq (hsub hx).1]
    simp only [div_eq_mul_inv,mul_comm]
  have hn : (∫ x in J, g x ∂reciprocalMeasure ν u) = ∫ x in J, g x/x ∂ν := by
    rw [reciprocalMeasure_integral ν hu g hJ.measurableSet]
    apply setIntegral_congr_fun hJ.measurableSet
    intro x hx
    dsimp only
    rw [reciprocalWeight_eq (hsub hx).1]
    simp only [div_eq_mul_inv,mul_comm]
  rw [hm,hn] at h
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem weighted_from_all_endpoint_intervals
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (u v D E : ℝ) (hu : 0 < u) (hD : 0 ≤ D) (hE : 0 ≤ E) (g : ℝ → ℝ)
    (hg : MonotoneOn g (Icc u v) ∨ AntitoneOn g (Icc u v))
    (hbound : ∀ x ∈ Icc u v, |g x| ≤ D)
    (hinterval : ∀ a b : ℝ, u ≤ a → a ≤ b → b ≤ v →
      |μ.real (Icc a b)-ν.real (Icc a b)| ≤ E ∧
      |μ.real (Ico a b)-ν.real (Ico a b)| ≤ E ∧
      |μ.real (Ioc a b)-ν.real (Ioc a b)| ≤ E ∧
      |μ.real (Ioo a b)-ν.real (Ioo a b)| ≤ E)
    {J : Set ℝ} (hJ : J.OrdConnected) (hsub : J ⊆ Icc u v) :
    |(∫ x in J, g x/x ∂μ) - ∫ x in J, g x/x ∂ν| ≤ 3*E*D/u :=
  weighted_monotone_discrepancy μ ν u v D E hu hD g hg hbound
    (fun _ hS hs => orderConnected_measure_discrepancy μ ν u v E hE hinterval hS hs) hJ hsub

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

theorem referenceMeasure_weightedIntegral {u v : ℝ} (hu : 0 < u) (g : ℝ → ℝ) {J : Set ℝ}
    (hJ : MeasurableSet J) (hsub : J ⊆ Icc u v) :
    (∫ x in J,g x/x ∂referenceMeasure u v)=∫ x in J,g x/x^2 := by
  rw [referenceMeasure,reciprocalMeasure_integral _ hu _ hJ,Measure.restrict_restrict hJ,
    inter_eq_left.mpr hsub]
  apply setIntegral_congr_fun hJ
  intro x hx
  dsimp only
  rw [reciprocalWeight_eq (hsub hx).1]
  simp only [div_eq_mul_inv,pow_two,mul_inv_rev]
  ring

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_LinearSieveFunctions
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.LinearSieveFunctions

open MeasureTheory Filter
open scoped Topology

theorem startingExtension_eq_f (A : ℝ) {s : ℝ} (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    startingExtension A s = f A s := (f_first_formula A hs2 hs4).symm

end NumberTheoryLean.LinearSieveFunctions

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_WeightFutureIntegrals
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.DeficitFutureIntegrals

open Filter Set MeasureTheory
open scoped Topology
open LinearSieveFunctions BuchstabBridge NormalizedDeficits

theorem lowerDeficit_nonneg (s : ℝ) : 0 ≤ lowerDeficit s := by
  by_cases hs : 1 ≤ s
  · exact (deficits_pos hs).1.le
  · simp only [lowerDeficit, f_initial sieveA (by linarith : s ≤ 2), sub_zero, zero_le_one]

end NumberTheoryLean.DeficitFutureIntegrals

end

section

namespace NumberTheoryLean.DerivativeWeights

open Filter Set MeasureTheory
open scoped Topology
open LinearSieveFunctions BuchstabBridge NormalizedDeficits DeficitFutureIntegrals

theorem F_hasDerivAt {s : ℝ} (hs : 0 < s) :
    HasDerivAt (F sieveA) (-phiOdd s / s ^ 2) s := by
  by_cases hs1 : 1 < s
  · convert! (upperDeficit_hasDerivAt hs1).add_const 1 using 1
    all_goals try with_reducible_and_instances rfl
    ext t
    change F sieveA t = (F sieveA t - 1) + 1
    ring
  · have heq : F sieveA =ᶠ[𝓝 s] (fun t => sieveA / t) := by
      filter_upwards [Ioo_mem_nhds hs (show s < 3 by linarith)] with t ht
      exact F_initial sieveA ht.1 ht.2.le
    have hd := ((hasDerivAt_const s sieveA).div (hasDerivAt_id s) (ne_of_gt hs)).congr_of_eventuallyEq heq
    convert! hd using 1
    all_goals try with_reducible_and_instances rfl
    rw [phiOdd_initial (by linarith)]
    simp only [id_eq, zero_mul, zero_sub, mul_one]

end NumberTheoryLean.DerivativeWeights

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_WeightIntegrals
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.TwoStepDensityBounds

open Set
open DerivativeWeights WeightFutureIntegrals FinitePathGeometry

theorem valid_of_three_le (i : Side) {s : ℝ} (hs : 3 ≤ s) : Valid i s := by
  cases i <;> dsimp [Valid] <;> linarith

theorem weight_antitone {i : Side} {s t : ℝ} (hs : Valid i s) (ht : Valid i t) (hst : s ≤ t) :
    weight i t ≤ weight i s := by
  cases i with
  | even =>
    exact phiEven_strictAntiOn.antitoneOn
      (by change 1 < s; dsimp [Valid] at hs <;> linarith)
      (by change 1 < t; dsimp [Valid] at ht <;> linarith) hst
  | odd => exact phiOdd_antitone hst

end NumberTheoryLean.TwoStepDensityBounds

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

namespace NumberTheoryLean.ActualPrimeQuadrature

attribute [local instance] Classical.propDecidable
open _root_.MeasureTheory _root_.Set _root_.Finset
open ErdosMonotoneQuadrature ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimeEndpoints
open HarmonicPrimeAtomicMeasure HarmonicReferenceMeasure

theorem actual_interval_discrepancy : ∃ c C w₀ : ℝ,0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → ∀ u v : ℝ,2 ≤ u → u ≤ v → ∀ a b : ℝ,u ≤ a → a ≤ b → b ≤ v →
      ∀ lc rc : Bool,
        |(primeMeasure w v).real {x | intervalGuard lc rc a b x}-
          (referenceMeasure u v).real {x | intervalGuard lc rc a b x}| ≤
          C*Real.exp (-c*Real.sqrt (u*Real.log w)) := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,h⟩ := harmonic_prime_measure
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro w hw u v hu _huv a b hua hab hbv lc rc
  have hw1 : 1 < w := hw₀.trans_le hw
  have hu0 : 0 < u := by linarith
  rw [primeMeasure_interval hw1 hbv,referenceMeasure_interval hu0 hua hab hbv]
  have hh := h w hw a b (by linarith) hab lc rc
  have hm : Real.exp (-c*Real.sqrt (a*Real.log w)) ≤ Real.exp (-c*Real.sqrt (u*Real.log w)) := by
    apply Real.exp_le_exp.mpr
    have hs := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hua (Real.log_pos hw1).le)
    nlinarith
  exact hh.trans (mul_le_mul_of_nonneg_left hm hC.le)

theorem actual_weighted_prime_quadrature : ∃ c C w₀ : ℝ,0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → ∀ u v : ℝ,2 ≤ u → u ≤ v → ∀ D : ℝ,0 ≤ D → ∀ g : ℝ → ℝ,
      (MonotoneOn g (Icc u v) ∨ AntitoneOn g (Icc u v)) →
      (∀ x ∈ Icc u v,|g x| ≤ D) → ∀ J : Set ℝ,J.OrdConnected → J ⊆ Icc u v →
        |(∑ p ∈ Nat.primesLE ⌊w^v⌋₊,if primeExponent w p ∈ J then
            (p:ℝ)⁻¹*g (primeExponent w p)/primeExponent w p else 0)-
          ∫ x in J,g x/x^2| ≤ (C*D/u)*Real.exp (-c*Real.sqrt (u*Real.log w)) := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,h⟩ := actual_interval_discrepancy
  refine ⟨c,3*C,w₀,hc,by positivity,hw₀,?_⟩
  intro w hw u v hu huv D hD g hg hbound J hJ hsub
  have hu0 : 0 < u := by linarith
  let := referenceMeasure_finite (v:=v) hu0
  let E := C*Real.exp (-c*Real.sqrt (u*Real.log w))
  have hinter : ∀ a b : ℝ,u ≤ a → a ≤ b → b ≤ v →
      |(primeMeasure w v).real (Icc a b)-(referenceMeasure u v).real (Icc a b)| ≤ E ∧
      |(primeMeasure w v).real (Ico a b)-(referenceMeasure u v).real (Ico a b)| ≤ E ∧
      |(primeMeasure w v).real (Ioc a b)-(referenceMeasure u v).real (Ioc a b)| ≤ E ∧
      |(primeMeasure w v).real (Ioo a b)-(referenceMeasure u v).real (Ioo a b)| ≤ E := by
    intro a b hua hab hbv
    have hh := h w hw u v hu huv a b hua hab hbv
    exact ⟨hh true true,hh true false,hh false true,hh false false⟩
  have hq := weighted_from_all_endpoint_intervals (primeMeasure w v) (referenceMeasure u v)
    u v D E hu0 hD (by dsimp [E] <;> positivity) g hg hbound hinter hJ hsub
  rw [primeMeasure_setIntegral w v _ hJ.measurableSet,
    referenceMeasure_weightedIntegral hu0 g hJ.measurableSet hsub] at hq
  calc
    _ ≤ 3*E*D/u := by simpa only [mul_div_assoc] using hq
    _ = _ := by dsimp [E] <;> ring

end NumberTheoryLean.ActualPrimeQuadrature

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReferenceWeightedQuadrature
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.ReferenceDifferentiation

open _root_.Filter _root_.Set
open scoped Topology
open FinitePathGeometry LinearSieveFunctions BuchstabBridge ReferenceBenchmarkDecay

theorem parent_even_eq_starting {s : ℝ} (hs : s ≤ 4) :
    parentBenchmark .even s = startingExtension sieveA s := by
  simp only [parentBenchmark]
  split_ifs with h
  · rfl
  · exact (startingExtension_eq_f sieveA (le_of_lt (lt_of_not_ge h)) hs).symm

theorem parent_even_eq_ordinary {s : ℝ} (hs : 2 ≤ s) :
    parentBenchmark .even s = benchmark .even s := by
  simp only [parentBenchmark,benchmark]
  split_ifs with h
  · exact startingExtension_eq_f sieveA hs (by linarith)
  · rfl

theorem parent_mass_derivative (i : Side) {s : ℝ} (hs : ParentDomain i s) :
    HasDerivAt (fun t => t*parentBenchmark i t) (benchmark i.flip (s-1)) s := by
  cases i with
  | even =>
    change 1 < s at hs
    by_cases hs2 : 2 < s
    · have heq : (fun t => t*parentBenchmark .even t) =ᶠ[𝓝 s] (fun t => t*f sieveA t) := by
        filter_upwards [Ioi_mem_nhds hs2] with t ht
        rw [parent_even_eq_ordinary ht.le]
        rfl
      exact (mass_f_hasDerivAt sieveA hs2).congr_of_eventuallyEq heq
    · have hsle : s ≤ 2 := le_of_not_gt hs2
      have heq : (fun t => t*parentBenchmark .even t) =ᶠ[𝓝 s] (fun t => sieveA*Real.log (t-1)) := by
        filter_upwards [Ioo_mem_nhds hs (show s < 3 by linarith)] with t ht
        rw [parent_even_eq_starting (by linarith [ht.2] : t ≤ 4)]
        unfold startingExtension
        field_simp [show t ≠ 0 by linarith [ht.1]]
      have hd := ((((hasDerivAt_id s).sub_const 1).log (by linarith : s-1 ≠ 0)).const_mul sieveA)
      have h := hd.congr_of_eventuallyEq heq
      convert! h using 1
      all_goals try with_reducible_and_instances rfl
      change F sieveA (s-1) = _
      rw [F_initial sieveA (by linarith) (by linarith)]
      simp only [id_eq]
      ring
  | odd =>
    change 0 < s at hs
    by_cases hs2 : 2 < s
    · exact mass_F_hasDerivAt sieveA hs2
    · have hsle : s ≤ 2 := le_of_not_gt hs2
      have heq : (fun t => t*parentBenchmark .odd t) =ᶠ[𝓝 s] (fun _ => sieveA) := by
        filter_upwards [Ioo_mem_nhds hs (show s < 3 by linarith)] with t ht
        change t*F sieveA t=sieveA
        rw [F_initial sieveA ht.1 ht.2.le]
        field_simp [ne_of_gt ht.1]
      have hd := (hasDerivAt_const s sieveA).congr_of_eventuallyEq heq
      convert! hd using 1
      all_goals try with_reducible_and_instances rfl
      change f sieveA (s-1)=0
      exact f_initial sieveA (by linarith)

theorem reference_derivative (i : Side) {r b : ℝ} (hb : 0 < b)
    (hdomain : ParentDomain i (r/b)) :
    HasDerivAt (fun x => (parentBenchmark i (r/x)-1)/x)
      (-(benchmark i.flip (r/b-1)-1)/b^2) b := by
  have hrb : 0 < r/b := by cases i <;> simp only [ParentDomain] at hdomain <;> linarith
  have hr : 0 < r := (div_pos_iff.mp hrb).resolve_right (by intro h; linarith [h.2]) |>.1
  have hmass := (parent_mass_derivative i hdomain).sub (hasDerivAt_id (r/b))
  have hcomp := hmass.comp b ((hasDerivAt_const b r).div (hasDerivAt_id b) (ne_of_gt hb))
  have h := hcomp.div_const r
  have heq : (fun x => (parentBenchmark i (r/x)-1)/x) =ᶠ[𝓝 b]
      (fun x => ((r/x)*parentBenchmark i (r/x)-r/x)/r) := by
    filter_upwards [Ioi_mem_nhds hb] with x hx
    change 0 < x at hx
    field_simp [ne_of_gt hr,ne_of_gt hx]
  have hh := h.congr_of_eventuallyEq heq
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [zero_mul,mul_one,zero_sub]
  field_simp

end NumberTheoryLean.ReferenceDifferentiation



namespace NumberTheoryLean.ReferenceCancellation

open _root_.MeasureTheory _root_.Set
open FinitePathGeometry LinearSieveFunctions BuchstabBridge ReferenceBenchmarkDecay
open ReferenceDifferentiation ReferenceAdmission

theorem parent_domain_mono (i : Side) {s t : ℝ} (hs : ParentDomain i s) (hst : s ≤ t) :
    ParentDomain i t := by cases i <;> simp only [ParentDomain] at hs ⊢ <;> linarith

theorem positive_gap_of_parent_domain (i : Side) {r b : ℝ} (hb : 0 < b)
    (hs : ParentDomain i (r/b)) : 0 < r := by
  have hrb : 0 < r/b := by cases i <;> simp only [ParentDomain] at hs <;> linarith
  exact ((div_pos_iff.mp hrb).resolve_right (by intro h; linarith [h.2])).1

theorem parent_domain_interval (i : Side) {r b x : ℝ} (hb : 2 ≤ b)
    (hs : ParentDomain i (r/b)) (hx : x ∈ Icc 2 b) : ParentDomain i (r/x) := by
  have hr := positive_gap_of_parent_domain i (by linarith : 0 < b) hs
  exact parent_domain_mono i hs (div_le_div_of_nonneg_left hr.le (by linarith [hx.1]) hx.2)

theorem prospective_integrand_continuousAt (i : Side) {r x : ℝ} (hx : 0 < x)
    (hs : ParentDomain i (r/x)) :
    ContinuousAt (fun t => (benchmark i.flip (r/t-1)-1)/t^2) x := by
  have hmap : ContinuousAt (fun t : ℝ => r/t-1) x :=
    (continuousAt_const.div continuousAt_id (ne_of_gt hx)).sub continuousAt_const
  have hchild : ContinuousAt (fun t => benchmark i.flip (r/t-1)) x := by
    cases i with
    | even =>
      have hF : ContinuousAt (F sieveA) (r/x-1) :=
        F_continuousAt sieveA (by change 1 < r/x at hs; linarith)
      exact hF.comp (f := fun t => r/t-1) hmap
    | odd => exact (f_continuous sieveA).continuousAt.comp hmap
  exact (hchild.sub continuousAt_const).div (continuousAt_id.pow 2) (pow_ne_zero 2 (ne_of_gt hx))

theorem prospective_interval_integrable (i : Side) {r b : ℝ} (hb : 2 ≤ b)
    (hs : ParentDomain i (r/b)) :
    IntervalIntegrable (fun x => (benchmark i.flip (r/x-1)-1)/x^2) volume 2 b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hb
  intro x hx
  exact (prospective_integrand_continuousAt i (by linarith [hx.1])
    (parent_domain_interval i hb hs hx)).continuousWithinAt

theorem continuous_reference_cancellation (i : Side) {r b : ℝ} (hb : 2 ≤ b)
    (hs : ParentDomain i (r/b)) :
    (parentBenchmark i (r/2)-1)/2-(parentBenchmark i (r/b)-1)/b-
      (∫ x in (2:ℝ)..b,(benchmark i.flip (r/x-1)-1)/x^2)=0 := by
  have hderiv : ∀ x ∈ uIcc 2 b,
      HasDerivAt (fun t => (parentBenchmark i (r/t)-1)/t)
        (-(benchmark i.flip (r/x-1)-1)/x^2) x := by
    intro x hx
    rw [uIcc_of_le hb] at hx
    exact reference_derivative i (by linarith [hx.1]) (parent_domain_interval i hb hs hx)
  have hint : IntervalIntegrable (fun x => -(benchmark i.flip (r/x-1)-1)/x^2) volume 2 b := by
    convert! (prospective_interval_integrable i hb hs).neg using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    exact neg_div _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simp_rw [neg_div] at h
  rw [intervalIntegral.integral_neg] at h
  linarith

end NumberTheoryLean.ReferenceCancellation



namespace NumberTheoryLean.ReferenceDeviationMonotonicity

open _root_.Filter _root_.Set
open scoped Topology
open FinitePathGeometry LinearSieveFunctions BuchstabBridge NormalizedDeficits
open DeficitFutureIntegrals DerivativeWeights ReferenceBenchmarkDecay ReferenceDifferentiation ReferenceCancellation

theorem lower_deficit_antitone : Antitone lowerDeficit := by
  have htail : AntitoneOn lowerDeficit (Ici 2) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 2) lowerDeficit_continuous.continuousOn
    · intro s hs
      rw [interior_Ici] at hs
      exact (lowerDeficit_hasDerivAt hs).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      change 2 < s at hs
      rw [(lowerDeficit_hasDerivAt hs).deriv]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (phiEven_pos (by linarith)).le) (sq_nonneg _)
  intro x y hxy
  by_cases hy : y ≤ 2
  · simp only [lowerDeficit,f_initial sieveA hy,f_initial sieveA (hxy.trans hy),sub_zero,le_refl]
  · by_cases hx : x ≤ 2
    · have hh := htail (show (2:ℝ) ∈ Ici 2 by norm_num) (le_of_not_ge hy) (le_of_not_ge hy)
      simpa only [lowerDeficit,f_initial sieveA hx,f_initial sieveA (le_refl (2:ℝ)),sub_zero] using hh
    · exact htail (le_of_not_ge hx) (le_of_not_ge hy) hxy

theorem upper_deficit_pos_positive {s : ℝ} (hs : 0 < s) : 0 < upperDeficit s := by
  by_cases hs1 : 1 ≤ s
  · exact (deficits_pos hs1).2
  · change 0 < F sieveA s-1
    rw [F_initial sieveA hs (by linarith)]
    have h : 1 < sieveA/s := (one_lt_div hs).mpr (by linarith [sieveA_gt_two])
    linarith

theorem upper_deficit_antitone : AntitoneOn upperDeficit (Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · intro s hs
    exact ((F_continuousAt sieveA (ne_of_gt hs)).sub continuousAt_const).continuousWithinAt
  · intro s hs
    rw [interior_Ioi] at hs
    exact ((F_hasDerivAt hs).sub_const 1).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Ioi] at hs
    change deriv (fun t => F sieveA t-1) s ≤ 0
    rw [((F_hasDerivAt hs).sub_const 1).deriv]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (phiOdd_pos s).le) (sq_nonneg _)

theorem even_abs_deviation (s : ℝ) : |benchmark .even s-1| = lowerDeficit s := by
  have he : benchmark .even s-1 = -lowerDeficit s := by unfold benchmark lowerDeficit; ring
  rw [he,abs_neg,abs_of_nonneg (lowerDeficit_nonneg s)]

theorem odd_abs_deviation {s : ℝ} (hs : 0 < s) : |benchmark .odd s-1| = upperDeficit s :=
  abs_of_pos (upper_deficit_pos_positive hs)

theorem prospective_absolute_monotone (i : Side) {r u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v)
    (hs : ParentDomain i (r/v)) :
    MonotoneOn (fun x => |benchmark i.flip (r/x-1)-1|) (Icc u v) := by
  have hv : 2 ≤ v := hu.trans huv
  have hr := positive_gap_of_parent_domain i (by linarith : 0 < v) hs
  intro x hx y hy hxy
  have harg : r/y-1 ≤ r/x-1 := sub_le_sub_right
    (div_le_div_of_nonneg_left hr.le (by linarith [hx.1]) hxy) 1
  cases i with
  | even =>
    have hdx := parent_domain_interval .even hv hs ⟨hu.trans hx.1,hx.2⟩
    have hdy := parent_domain_interval .even hv hs ⟨hu.trans hy.1,hy.2⟩
    change 1 < r/x at hdx
    change 1 < r/y at hdy
    change |benchmark .odd (r/x-1)-1| ≤ |benchmark .odd (r/y-1)-1|
    rw [odd_abs_deviation (by linarith),odd_abs_deviation (by linarith)]
    exact upper_deficit_antitone (by change 0 < r/y-1; linarith) (by change 0 < r/x-1; linarith) harg
  | odd =>
    change |benchmark .even (r/x-1)-1| ≤ |benchmark .even (r/y-1)-1|
    rw [even_abs_deviation,even_abs_deviation]
    exact lower_deficit_antitone harg

theorem prospective_signed_monotone (i : Side) {r u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v)
    (hs : ParentDomain i (r/v)) :
    (i=.even → MonotoneOn (fun x => benchmark i.flip (r/x-1)-1) (Icc u v)) ∧
    (i=.odd → AntitoneOn (fun x => benchmark i.flip (r/x-1)-1) (Icc u v)) := by
  have hm := prospective_absolute_monotone i hu huv hs
  cases i with
  | even =>
    refine ⟨?_,by intro h; cases h⟩
    intro _ x hx y hy hxy
    have hp := hm hx hy hxy
    have hxD := parent_domain_interval .even (hu.trans huv) hs ⟨hu.trans hx.1,hx.2⟩
    have hyD := parent_domain_interval .even (hu.trans huv) hs ⟨hu.trans hy.1,hy.2⟩
    change 1 < r/x at hxD
    change 1 < r/y at hyD
    change benchmark .odd (r/x-1)-1 ≤ benchmark .odd (r/y-1)-1
    change |benchmark .odd (r/x-1)-1| ≤ |benchmark .odd (r/y-1)-1| at hp
    rw [odd_abs_deviation (by linarith),odd_abs_deviation (by linarith)] at hp
    exact hp
  | odd =>
    constructor
    · intro h
      cases h
    intro _ x hx y hy hxy
    have hp := hm hx hy hxy
    change |benchmark .even (r/x-1)-1| ≤ |benchmark .even (r/y-1)-1| at hp
    rw [even_abs_deviation,even_abs_deviation] at hp
    change f sieveA (r/y-1)-1 ≤ f sieveA (r/x-1)-1
    unfold lowerDeficit at hp
    linarith

end NumberTheoryLean.ReferenceDeviationMonotonicity



namespace NumberTheoryLean.ReferenceWeightDomination

open FinitePathGeometry LinearSieveFunctions BuchstabBridge NormalizedDeficits
open DeficitFutureIntegrals DerivativeWeights ReferenceBenchmarkDecay ReferenceDifferentiation ReferenceCancellation
open ReferenceDeviationMonotonicity

theorem starting_parent_nonpos {s : ℝ} (hs : 1 < s) (hs2 : s ≤ 2) :
    parentBenchmark .even s ≤ 0 := by
  rw [parent_even_eq_starting (by linarith)]
  unfold startingExtension
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos sieveA_pos.le (Real.log_nonpos (by linarith) (by linarith))) (by linarith)

theorem even_parent_le_one {s : ℝ} (hs : 1 < s) : parentBenchmark .even s ≤ 1 := by
  by_cases hs2 : 2 ≤ s
  · rw [parent_even_eq_ordinary hs2]
    have h := lowerDeficit_nonneg s
    change 0 ≤ 1-f sieveA s at h
    change f sieveA s ≤ 1
    linarith
  · exact (starting_parent_nonpos hs (le_of_lt (lt_of_not_ge hs2))).trans (by norm_num)

theorem even_parent_abs {s : ℝ} (hs : 1 < s) :
    |parentBenchmark .even s-1| = 1-parentBenchmark .even s := by
  rw [abs_of_nonpos (sub_nonpos.mpr (even_parent_le_one hs))]
  ring

theorem weight_deviation_identity (i : Side) {s : ℝ} (hs : ParentDomain i s) :
    weight i s = s*(|parentBenchmark i s-1|+|benchmark i.flip (s-1)-1|) := by
  cases i with
  | even =>
    change 1 < s at hs
    change phiEven s = s*(|parentBenchmark .even s-1|+|benchmark .odd (s-1)-1|)
    rw [even_parent_abs hs,odd_abs_deviation (by linarith)]
    by_cases hs2 : 2 ≤ s
    · rw [phiEven_eq_deficits hs2,parent_even_eq_ordinary hs2]
      rfl
    · have hsle : s ≤ 2 := le_of_lt (lt_of_not_ge hs2)
      rw [phiEven_initial hsle,parent_even_eq_starting (by linarith)]
      unfold evenInitial startingExtension upperDeficit
      rw [F_initial sieveA (by linarith) (by linarith)]
      field_simp
      ring
  | odd =>
    change 0 < s at hs
    change phiOdd s = s*(|benchmark .odd s-1|+|benchmark .even (s-1)-1|)
    rw [odd_abs_deviation hs,even_abs_deviation]
    by_cases hs1 : 1 ≤ s
    · exact phiOdd_eq_deficits hs1
    · rw [phiOdd_initial (by linarith)]
      unfold upperDeficit lowerDeficit
      rw [F_initial sieveA hs (by linarith),f_initial sieveA (by linarith)]
      field_simp
      ring

theorem valid_parent_domain {i : Side} {s : ℝ} (hs : Valid i s) : ParentDomain i s := by
  cases i <;> simp only [Valid,ParentDomain] at hs ⊢ <;> linarith

theorem source_deviation_sum {i : Side} {s : ℝ} (hs : Valid i s) :
    |parentBenchmark i s-1|+|benchmark i.flip (s-1)-1| ≤ 2*weight i s := by
  have hd := valid_parent_domain hs
  have hpos := valid_pos hs
  have he := weight_deviation_identity i hd
  have hs2 : (1/2:ℝ) ≤ s := by cases i <;> simp only [Valid] at hs <;> linarith
  have hsum : 0 ≤ |parentBenchmark i s-1|+|benchmark i.flip (s-1)-1| := by positivity
  nlinarith

theorem ordinary_deviation_le_parent (i : Side) {s : ℝ} (hs : ParentDomain i s) :
    |benchmark i s-1| ≤ |parentBenchmark i s-1| := by
  cases i with
  | odd => exact le_rfl
  | even =>
    change 1 < s at hs
    rw [even_abs_deviation,even_parent_abs hs]
    by_cases hs2 : 2 ≤ s
    · rw [parent_even_eq_ordinary hs2]
      exact le_rfl
    · have hsle := le_of_lt (lt_of_not_ge hs2)
      have h := starting_parent_nonpos hs hsle
      simp only [lowerDeficit,f_initial sieveA hsle,sub_zero]
      linarith

theorem benchmark_absolute_antitone (i : Side) {s t : ℝ} (hs : ParentDomain i s) (hst : s ≤ t) :
    |benchmark i t-1| ≤ |benchmark i s-1| := by
  cases i with
  | even => rw [even_abs_deviation,even_abs_deviation]; exact lower_deficit_antitone hst
  | odd =>
    change 0 < s at hs
    rw [odd_abs_deviation (hs.trans_le hst),odd_abs_deviation hs]
    exact upper_deficit_antitone hs (hs.trans_le hst) hst

theorem residual_deviations_bound (i : Side) {r b x : ℝ} (hb : 2 ≤ b)
    (hs : Valid i (r/b)) (hx : x ∈ Set.Icc 2 b) :
    |parentBenchmark i (r/b)-1|+|benchmark i (r/2)-1|+
      |benchmark i.flip (r/x-1)-1| ≤ 4*weight i (r/b) := by
  have hd := valid_parent_domain hs
  have hr := positive_gap_of_parent_domain i (by linarith : 0 < b) hd
  have hratio : r/b ≤ r/2 := div_le_div_of_nonneg_left hr.le (by norm_num) hb
  have hboundary := (benchmark_absolute_antitone i hd hratio).trans (ordinary_deviation_le_parent i hd)
  have hmono := prospective_absolute_monotone i (u := 2) le_rfl hb hd
  have hnext := hmono hx (show b ∈ Set.Icc 2 b from ⟨hb,le_rfl⟩) hx.2
  have hsum := source_deviation_sum hs
  have hn := abs_nonneg (benchmark i.flip (r/b-1)-1)
  linarith

end NumberTheoryLean.ReferenceWeightDomination



namespace NumberTheoryLean.ReferenceParentMonotonicity

open _root_.Set
open FinitePathGeometry LinearSieveFunctions BuchstabBridge NormalizedDeficits DerivativeWeights
open ReferenceBenchmarkDecay ReferenceDifferentiation ReferenceCancellation ReferenceWeightDomination ReferenceDeviationMonotonicity

theorem even_parent_deficit_antitone : AntitoneOn (fun s => 1-parentBenchmark .even s) (Ioi 1) := by
  have hd : ∀ s : ℝ,1 < s → HasDerivAt (parentBenchmark .even)
      ((benchmark .odd (s-1)-parentBenchmark .even s)/s) s := by
    intro s hs
    exact hasDerivAt_of_mass (by linarith) (parent_mass_derivative .even hs)
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 1)
  · intro s hs
    exact ((hd s hs).const_sub 1).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ioi] at hs
    exact ((hd s hs).const_sub 1).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Ioi] at hs
    change 1 < s at hs
    rw [((hd s hs).const_sub 1).deriv]
    have hu := upper_deficit_pos_positive (s:=s-1) (by linarith)
    have he := even_parent_le_one hs
    have hnum : 0 ≤ benchmark .odd (s-1)-parentBenchmark .even s := by
      change 0 < F sieveA (s-1)-1 at hu
      change 0 ≤ F sieveA (s-1)-parentBenchmark .even s
      linarith
    exact neg_nonpos.mpr (div_nonneg hnum (by linarith))

theorem parent_absolute_antitone (i : Side) {s t : ℝ} (hs : ParentDomain i s) (hst : s ≤ t) :
    |parentBenchmark i t-1| ≤ |parentBenchmark i s-1| := by
  cases i with
  | even =>
    change 1 < s at hs
    rw [even_parent_abs (hs.trans_le hst),even_parent_abs hs]
    exact even_parent_deficit_antitone hs (hs.trans_le hst) hst
  | odd => exact benchmark_absolute_antitone .odd hs hst

theorem interval_deviations_bound (i : Side) {r a b x : ℝ} (ha : 2 ≤ a) (hab : a ≤ b)
    (hs : Valid i (r/b)) (hx : x ∈ Icc a b) :
    |parentBenchmark i (r/a)-1|+|parentBenchmark i (r/b)-1|+
      |benchmark i.flip (r/x-1)-1| ≤ 4*weight i (r/b) := by
  have hb : 2 ≤ b := ha.trans hab
  have hd := valid_parent_domain hs
  have hr := positive_gap_of_parent_domain i (by linarith : 0 < b) hd
  have hrat : r/b ≤ r/a := div_le_div_of_nonneg_left hr.le (by linarith) hab
  have hleft := parent_absolute_antitone i hd hrat
  have hmono := prospective_absolute_monotone i (u:=2) le_rfl hb hd
  have hnext := hmono ⟨ha.trans hx.1,hx.2⟩ ⟨hb,le_rfl⟩ hx.2
  have hsum := source_deviation_sum hs
  linarith [abs_nonneg (benchmark i.flip (r/b-1)-1)]

end NumberTheoryLean.ReferenceParentMonotonicity



namespace NumberTheoryLean.ReferenceWeightedQuadrature

attribute [local instance] Classical.propDecidable
open _root_.MeasureTheory _root_.Set _root_.Finset
open FinitePathGeometry ReferenceBenchmarkDecay ReferenceDifferentiation ReferenceCancellation
open ReferenceDeviationMonotonicity ReferenceWeightDomination ActualPrimeQuadrature
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem source_weighted_quadrature : ∃ c C w₀ : ℝ,0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → ∀ u v b r : ℝ,2 ≤ u → u ≤ v → v ≤ b → ∀ i : Side,
      Valid i (r/b) → ∀ J : Set ℝ,J.OrdConnected → J ⊆ Icc u v →
        |(∑ p ∈ Nat.primesLE ⌊w^v⌋₊,if primeExponent w p ∈ J then
          (p:ℝ)⁻¹*(benchmark i.flip (r/primeExponent w p-1)-1)/primeExponent w p else 0)-
          ∫ x in J,(benchmark i.flip (r/x-1)-1)/x^2| ≤
          (C*weight i (r/b)/u)*Real.exp (-c*Real.sqrt (u*Real.log w)) := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,h⟩ := actual_weighted_prime_quadrature
  refine ⟨c,4*C,w₀,hc,by positivity,hw₀,?_⟩
  intro w hw u v b r hu huv hvb i hs J hJ hsub
  have hb : 2 ≤ b := hu.trans (huv.trans hvb)
  have hparent := valid_parent_domain hs
  have hvdom : ParentDomain i (r/v) := parent_domain_interval i hb hparent ⟨hu.trans huv,hvb⟩
  let g : ℝ → ℝ := fun x => benchmark i.flip (r/x-1)-1
  have hmono : MonotoneOn g (Icc u v) ∨ AntitoneOn g (Icc u v) := by
    have hm := prospective_signed_monotone i hu huv hvdom
    cases i with
    | even => exact Or.inl (hm.1 rfl)
    | odd => exact Or.inr (hm.2 rfl)
  have hbound : ∀ x ∈ Icc u v,|g x| ≤ 4*weight i (r/b) := by
    intro x hx
    have hh := residual_deviations_bound i hb hs ⟨hu.trans hx.1,hx.2.trans hvb⟩
    have hp := abs_nonneg (parentBenchmark i (r/b)-1)
    have hbnd := abs_nonneg (benchmark i (r/2)-1)
    dsimp only [g]
    linarith
  have hq := h w hw u v hu huv (4*weight i (r/b)) (by have hp := weight_pos hs; positivity)
    g hmono hbound J hJ hsub
  calc
    _ ≤ (C*(4*weight i (r/b))/u)*Real.exp (-c*Real.sqrt (u*Real.log w)) := hq
    _ = _ := by ring

end NumberTheoryLean.ReferenceWeightedQuadrature


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

theorem highPrimes_membership {w : ℝ} (hw : 1 < w) (b : ℝ) (closed : Bool) (p : ℕ) :
    p ∈ highPrimes w b closed ↔ p.Prime ∧ 2<primeExponent w p ∧ capGuard closed b (primeExponent w p) := by
  rw [highPrimes,Finset.mem_filter,sourcePrimes_membership hw]
  constructor
  · rintro ⟨⟨hp,_hlo,hcap⟩,hhi⟩
    exact ⟨hp,(lt_exponent_iff hw (by exact_mod_cast hp.pos)).mpr hhi,hcap⟩
  · rintro ⟨hp,hhi,hcap⟩
    exact ⟨⟨hp,by linarith,hcap⟩,(lt_exponent_iff hw (by exact_mod_cast hp.pos)).mp hhi⟩

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReferenceSourceDecomposition
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ActualBoundaryDomain

attribute [local instance] Classical.propDecidable

open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeTiltGeometry
open ActualPrimeHigh
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem boundary_gap_ge_two {i : Side} {r : ℝ} (h : BoundaryDomain i r) : 2 ≤ r := by
  cases i <;> simp only [BoundaryDomain] at h <;> linarith

end NumberTheoryLean.ActualBoundaryDomain

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_ReferenceHighIntervals
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferenceHighIntervals

attribute [local instance] Classical.propDecidable
open _root_.Finset _root_.Set _root_.MeasureTheory
open FinitePathGeometry PrimeTiltGeometry ReferenceSourcePrimeSets ReferenceMertens
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimeEndpoints

theorem highInterval_orderConnected (b : ℝ) (closed : Bool) : (highInterval b closed).OrdConnected := by
  cases closed
  · exact ordConnected_Ioo
  · exact ordConnected_Ioc

theorem highInterval_subset (b : ℝ) (closed : Bool) : highInterval b closed ⊆ Icc 2 b := by
  intro x hx
  refine ⟨hx.1.le,?_⟩
  cases closed
  · exact hx.2.le
  · exact hx.2

theorem highPrimes_eq_filter {w : ℝ} (hw : 1 < w) (b : ℝ) (closed : Bool) :
    highPrimes w b closed=(Nat.primesLE ⌊w^b⌋₊).filter (fun p => primeExponent w p ∈ highInterval b closed) := by
  ext p
  rw [highPrimes_membership hw,Finset.mem_filter]
  constructor
  · rintro ⟨hp,hlo,hcap⟩
    have hup : primeExponent w p ≤ b := by
      cases closed
      · exact hcap.le
      · exact hcap
    have hpx := (exponent_le_iff hw (by exact_mod_cast hp.pos)).mp hup
    have hfloor := (Nat.le_floor_iff (Real.rpow_pos_of_pos (by linarith : 0 < w) b).le).mpr hpx
    exact ⟨Nat.mem_primesLE.mpr ⟨hfloor,hp⟩,hlo,hcap⟩
  · rintro ⟨hp,hlo,hcap⟩
    exact ⟨(Nat.mem_primesLE.mp hp).2,hlo,hcap⟩

theorem highPrime_sum {w : ℝ} (hw : 1 < w) (b : ℝ) (closed : Bool) (F : ℕ → ℝ) :
    (∑ p ∈ highPrimes w b closed,F p)=
      ∑ p ∈ Nat.primesLE ⌊w^b⌋₊,if primeExponent w p ∈ highInterval b closed then F p else 0 := by
  rw [highPrimes_eq_filter hw,Finset.sum_filter]

theorem highPrime_mass_eq {w : ℝ} (hw : 1 < w) (b : ℝ) (closed : Bool) :
    (∑ p ∈ highPrimes w b closed,(p:ℝ)⁻¹)=harmonicMass w false closed 2 b := by
  rw [highPrime_sum hw,harmonicMass]
  apply Finset.sum_congr rfl
  intro p _hp
  simp only [highInterval,capGuard,intervalGuard,Bool.false_eq_true,ite_false, if_false,Set.mem_ofPred_eq]
  split_ifs <;> rfl

theorem highInterval_integral {b : ℝ} (hb : 2 ≤ b) (closed : Bool) (F : ℝ → ℝ) :
    (∫ x in highInterval b closed,F x)=∫ x in (2:ℝ)..b,F x := by
  cases closed
  · change (∫ x in Ioo 2 b,F x)=_
    rw [← integral_Ioc_eq_integral_Ioo,intervalIntegral.integral_of_le hb]
  · exact (intervalIntegral.integral_of_le hb).symm

theorem highPrime_mass_bound : ∃ C w₀ : ℝ,0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → ∀ b : ℝ,2 ≤ b → ∀ closed : Bool,
      (∑ p ∈ highPrimes w b closed,(p:ℝ)⁻¹) ≤ C*(1+Real.log b) := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,h⟩ := harmonic_prime_measure
  refine ⟨C+1,w₀,by positivity,hw₀,?_⟩
  intro w hw b hb closed
  have hw1 : 1 < w := hw₀.trans_le hw
  rw [highPrime_mass_eq hw1]
  have hh := h w hw 2 b (by norm_num) hb false closed
  have he : Real.exp (-c*Real.sqrt (2*Real.log w)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (Real.sqrt_nonneg _))
  have hu := (abs_le.mp hh).2
  have hlog : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
  have hl2 : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left he hC.le]

end NumberTheoryLean.ReferenceHighIntervals

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_MovingLocalReference
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.WeightDistantDecay

open FinitePathGeometry DerivativeWeights WeightDickmanComparison TwoStepDensityBounds
open Dickman DickmanDecay DickmanFiniteDecay

theorem sided_rho_bounds : ∃ c C : ℝ,0 < c ∧ 0 < C ∧ ∀ i : Side,∀ s : ℝ,2 ≤ s →
    c*rho (s-2) ≤ weight i s ∧ weight i s ≤ C*rho (s-2) := by
  obtain ⟨c,C,hc,hC,h⟩ := weights_dickman_bounds
  refine ⟨c,C,hc,hC,?_⟩
  intro i s hs
  cases i with
  | even => exact (h s hs).1
  | odd => exact (h s hs).2

theorem compact_weight_lower : ∃ m : ℝ,0 < m ∧ ∀ i s,Valid i s → s ≤ 4 → m ≤ weight i s := by
  let m := min (weight .even 4) (weight .odd 4)
  have he : 0 < weight .even 4 := weight_pos (valid_of_three_le .even (by norm_num))
  have ho : 0 < weight .odd 4 := weight_pos (valid_of_three_le .odd (by norm_num))
  refine ⟨m,lt_min he ho,?_⟩
  intro i s hs hs4
  have hm : m ≤ weight i 4 := by cases i; exact min_le_left _ _; exact min_le_right _ _
  exact hm.trans (weight_antitone hs (valid_of_three_le i (by norm_num)) hs4)

theorem rho_one_rate {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    rho b ≤ rho a*Real.exp (-(b-a)) := by
  simpa only [one_mul,neg_mul] using
    rho_exponential_comparison 2 1 a b le_rfl (fun t ht => hazard_ge_one ht) ha hab

theorem relative_weight_decay : ∃ C : ℝ,0 < C ∧ ∀ i j : Side,∀ s t : ℝ,
    Valid i s → s+4 ≤ t → weight j t ≤ C*weight i s*Real.exp (-(t-s)/2) := by
  obtain ⟨c₀,C₀,hc₀,hC₀,hρ⟩ := sided_rho_bounds
  obtain ⟨m,hm,hmLower⟩ := compact_weight_lower
  let CL := C₀/c₀
  let CS := C₀*Real.exp 4/m
  have hCL : 0 < CL := div_pos hC₀ hc₀
  have hCS : 0 < CS := div_pos (mul_pos hC₀ (Real.exp_pos _)) hm
  refine ⟨max CL CS,hCL.trans_le (le_max_left _ _),?_⟩
  intro i j s t hs hst
  have hs0 := valid_pos hs
  have ht4 : 4 ≤ t := by linarith
  have ht2 : 2 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hwt := (hρ j t ht2).2
  have hφ := weight_pos hs
  by_cases hs4 : 4 ≤ s
  · have hcomp := rho_one_rate (a:=s-2) (b:=t-2) (by linarith) (by linarith)
    have hlow := (hρ i s (by linarith)).1
    have hdiv : rho (s-2) ≤ weight i s/c₀ := (le_div_iff₀ hc₀).mpr (by nlinarith)
    have he : Real.exp (-((t-2)-(s-2))) ≤ Real.exp (-(t-s)/2) := Real.exp_le_exp.mpr (by linarith)
    calc
      _ ≤ C₀*rho (t-2) := hwt
      _ ≤ C₀*(rho (s-2)*Real.exp (-((t-2)-(s-2)))) := mul_le_mul_of_nonneg_left hcomp hC₀.le
      _ ≤ C₀*((weight i s/c₀)*Real.exp (-(t-s)/2)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul hdiv he (Real.exp_pos _).le (by positivity)) hC₀.le
      _ = CL*weight i s*Real.exp (-(t-s)/2) := by dsimp [CL] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left CL CS) hφ.le) (Real.exp_pos _).le
  · have hs4' : s ≤ 4 := le_of_lt (lt_of_not_ge hs4)
    have hmin := hmLower i s hs hs4'
    have hcomp := rho_one_rate (a:=2) (b:=t-2) le_rfl (by linarith)
    have hbound : rho (t-2) ≤ Real.exp 4*Real.exp (-(t-s)/2) := by
      calc
        _ ≤ rho 2*Real.exp (-((t-2)-2)) := hcomp
        _ ≤ Real.exp (-((t-2)-2)) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right (rho_le_one 2) (Real.exp_pos _).le
        _ ≤ _ := by rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith
    have hcoeff : C₀*Real.exp 4 ≤ CS*weight i s := by
      calc
        _ = CS*m := by dsimp [CS]; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hmin hCS.le
    calc
      _ ≤ C₀*rho (t-2) := hwt
      _ ≤ C₀*(Real.exp 4*Real.exp (-(t-s)/2)) := mul_le_mul_of_nonneg_left hbound hC₀.le
      _ ≤ CS*weight i s*Real.exp (-(t-s)/2) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right CL CS) hφ.le) (Real.exp_pos _).le

end NumberTheoryLean.WeightDistantDecay



namespace NumberTheoryLean.ReferenceResidualErrors

open _root_.Finset _root_.MeasureTheory
open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeTiltGeometry ActualBoundaryDomain
open ReferenceBenchmarkDecay ReferenceDifferentiation ReferenceCancellation ReferenceWeightDomination
open ReferenceSourcePrimeSets ReferenceMertens ReferenceLocalResidual ReferenceHighIntervals
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem ratio_eq_gap_div_cutoff {z : Node} (hs : Valid z.side z.ratio) (hz : Consistent z)
    (hb : 0 < z.cutoff) : z.ratio=z.gap/z.cutoff := by
  have he := (eq_div_iff (ne_of_gt (valid_pos hs))).mp hz
  apply (eq_div_iff (ne_of_gt hb)).mpr
  nlinarith

theorem boundary_parent_eq (i : Side) {r : ℝ} (hr : BoundaryDomain i r) :
    parentBenchmark i (r/2)=benchmark i (r/2) := by
  cases i with
  | even => exact parent_even_eq_ordinary (by change 4 ≤ r at hr; linarith)
  | odd => rfl

theorem actual_continuous_zero (w : ℝ) {z : Node} (hs : Valid z.side z.ratio) (hz : Consistent z)
    (hb : 2 ≤ z.cutoff) (hdom : BoundaryDomain z.side z.gap) :
    (normalization w/2)*(benchmark z.side (z.gap/2)-1)-
      (normalization w/z.cutoff)*(parentBenchmark z.side z.ratio-1)-
      normalization w*(∫ x in highInterval z.cutoff z.closed,(benchmark z.side.flip (z.gap/x-1)-1)/x^2)=0 := by
  have hr := ratio_eq_gap_div_cutoff hs hz (by linarith)
  have hd : ParentDomain z.side (z.gap/z.cutoff) := by rw [← hr]; exact valid_parent_domain hs
  have hc := continuous_reference_cancellation z.side hb hd
  rw [boundary_parent_eq z.side hdom,← hr] at hc
  rw [highInterval_integral hb]
  have hm := congrArg (fun t : ℝ => normalization w*t) hc
  convert! hm using 1 <;> first | (with_reducible_and_instances rfl) | ring

theorem residual_error_identity (w : ℝ) {z : Node} (hs : Valid z.side z.ratio) (hz : Consistent z)
    (hb : 2 ≤ z.cutoff) (hdom : BoundaryDomain z.side z.gap) :
    sourceResidual w z=boundaryProductError w z-parentProductError w z-primeProductError w z-
      normalization w*quadratureError w z := by
  have hc := actual_continuous_zero w hs hz hb hdom
  have hp : (∑ p ∈ highPrimes w z.cutoff z.closed,(p:ℝ)⁻¹*referenceProduct w (primeExponent w p) false*
        (benchmark z.side.flip (childRatio w z.gap p)-1))=
      primeProductError w z+normalization w*(∑ p ∈ highPrimes w z.cutoff z.closed,(p:ℝ)⁻¹*
        (benchmark z.side.flip (childRatio w z.gap p)-1)/primeExponent w p) := by
    rw [primeProductError,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    ring
  unfold sourceResidual boundaryProductError parentProductError quadratureError
  rw [hp]
  nlinarith

end NumberTheoryLean.ReferenceResidualErrors



namespace NumberTheoryLean.ReferenceProductErrorBounds

open _root_.Finset
open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeTiltGeometry
open ReferenceMertens ReferenceSourcePrimeSets ReferenceBenchmarkDecay ReferenceDifferentiation
open ReferenceWeightDomination ReferenceResidualErrors
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem primeError_pos (c w t : ℝ) : 0 < primeError c w t := Real.exp_pos _

theorem primeError_antitone {c w t s : ℝ} (hc : 0 ≤ c) (hw : 1 < w) (hts : t ≤ s) :
    primeError c w s ≤ primeError c w t := by
  apply Real.exp_le_exp.mpr
  have h := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hts (Real.log_pos hw).le)
  nlinarith

theorem divided_error_bound {c C w t : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C) (hw : 1 < w) (ht : 2 ≤ t) :
    (C/t)*primeError c w t ≤ (C/2)*primeError c w 2 := by
  apply mul_le_mul (div_le_div_of_nonneg_left hC (by norm_num : (0:ℝ)<2) ht)
    (primeError_antitone hc hw ht) (primeError_pos _ _ _).le (by positivity)

theorem finite_product_error_bounds {c C w : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C) (hw : 1 < w)
    (hP : ∀ t : ℝ,2 ≤ t → ∀ closed : Bool,
      |referenceProduct w t closed-normalization w/t| ≤ (C/t)*primeError c w t)
    {z : Node} (hs : Valid z.side z.ratio) (hz : Consistent z) (hb : 2 ≤ z.cutoff) :
    |boundaryProductError w z| ≤ 2*C*weight z.side z.ratio*primeError c w 2 ∧
    |parentProductError w z| ≤ 2*C*weight z.side z.ratio*primeError c w 2 ∧
    |primeProductError w z| ≤ (2*C*weight z.side z.ratio*primeError c w 2)*
      (∑ p ∈ highPrimes w z.cutoff z.closed,(p:ℝ)⁻¹) := by
  have hφ := weight_pos hs
  have hE := primeError_pos c w 2
  have hr := ratio_eq_gap_div_cutoff hs hz (by linarith)
  have hs' : Valid z.side (z.gap/z.cutoff) := by rwa [← hr]
  have hD := residual_deviations_bound z.side hb hs' ⟨hb,le_rfl⟩
  rw [← hr] at hD
  have hparent : |parentBenchmark z.side z.ratio-1| ≤ 4*weight z.side z.ratio := by
    linarith [abs_nonneg (benchmark z.side (z.gap/2)-1),abs_nonneg (benchmark z.side.flip (z.ratio-1)-1)]
  have hboundary : |benchmark z.side (z.gap/2)-1| ≤ 4*weight z.side z.ratio := by
    linarith [abs_nonneg (parentBenchmark z.side z.ratio-1),abs_nonneg (benchmark z.side.flip (z.ratio-1)-1)]
  have hscale : ∀ t : ℝ,2 ≤ t → ∀ closed : Bool,
      |referenceProduct w t closed-normalization w/t| ≤ (C/2)*primeError c w 2 := by
    intro t ht closed
    exact (hP t ht closed).trans (divided_error_bound hc hC hw ht)
  constructor
  · unfold boundaryProductError
    rw [abs_mul]
    have h := mul_le_mul (hscale 2 le_rfl true) hboundary (abs_nonneg _) (by positivity)
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  constructor
  · unfold parentProductError
    rw [abs_mul]
    have h := mul_le_mul (hscale z.cutoff hb z.closed) hparent (abs_nonneg _) (by positivity)
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · unfold primeProductError
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨_hprime,hxp,hcap⟩ := (highPrimes_membership hw z.cutoff z.closed p).mp hp
    have hxb : primeExponent w p ≤ z.cutoff := by
      cases hcl : z.closed with
      | false => have h : primeExponent w p < z.cutoff := by simpa [capGuard,hcl] using hcap
                 exact h.le
      | true => simpa [capGuard,hcl] using hcap
    have hchild0 := residual_deviations_bound z.side hb hs' ⟨hxp.le,hxb⟩
    rw [← hr] at hchild0
    have hchild : |benchmark z.side.flip (childRatio w z.gap p)-1| ≤ 4*weight z.side z.ratio := by
      unfold childRatio
      linarith [abs_nonneg (parentBenchmark z.side z.ratio-1),abs_nonneg (benchmark z.side (z.gap/2)-1)]
    rw [abs_mul,abs_mul,abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p))]
    have hleft := mul_le_mul_of_nonneg_left (hscale (primeExponent w p) hxp.le false)
      (inv_nonneg.mpr (Nat.cast_nonneg p))
    have h := mul_le_mul hleft hchild (abs_nonneg _) (by positivity)
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    ring

end NumberTheoryLean.ReferenceProductErrorBounds



namespace NumberTheoryLean.GlobalResidualScale

open ReferenceProductErrorBounds

theorem powerDecay_pos (M B : ℝ) : 0 < powerDecay M B := Real.exp_pos _

theorem primeError_le_one {c : ℝ} (hc : 0 ≤ c) (w t : ℝ) : primeError c w t ≤ 1 :=
  Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (Real.sqrt_nonneg _))

theorem powerDecay_nat {B : ℝ} (hB : 0 < B) (n : ℕ) : powerDecay n B=(B^n)⁻¹ := by
  rw [powerDecay,neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log hB]

theorem linear_log_cutoff_saving {c d M : ℝ} (hc : 0 < c) (hd : 0 < d) (hM : 0 < M) :
    ∃ K : ℝ,1 ≤ K ∧ ∀ B w : ℝ,1 ≤ B → 1 < w → Real.log B ≤ d*Real.log w →
      primeError c w (K*Real.log B) ≤ powerDecay M B := by
  let q := M/c
  let K := 1+d*q^2
  have hq : 0 < q := div_pos hM hc
  have hK : 1 ≤ K := by dsimp [K]; exact le_add_of_nonneg_right (mul_nonneg hd.le (sq_nonneg q))
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  refine ⟨K,hK,?_⟩
  intro B w hB hw hcomp
  have hL : 0 ≤ Real.log B := Real.log_nonneg hB
  have hW : 0 ≤ Real.log w := (Real.log_pos hw).le
  have hm := mul_le_mul_of_nonneg_left hcomp (mul_nonneg (sq_nonneg q) hL)
  have hsquare : (q*Real.log B)^2 ≤ (K*Real.log B)*Real.log w := by
    dsimp only [K]
    nlinarith only [hm,mul_nonneg hL hW]
  have harg : 0 ≤ (K*Real.log B)*Real.log w := by positivity
  have hsqrt : q*Real.log B ≤ Real.sqrt ((K*Real.log B)*Real.log w) := by
    nlinarith only [hsquare,Real.sq_sqrt harg,Real.sqrt_nonneg ((K*Real.log B)*Real.log w),mul_nonneg hq.le hL]
  have hcq : c*q=M := by dsimp [q]; field_simp
  have hpay : M*Real.log B ≤ c*Real.sqrt ((K*Real.log B)*Real.log w) := by
    calc
      _ = c*(q*Real.log B) := by rw [← mul_assoc,hcq]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsqrt hc.le
  change Real.exp (-c*Real.sqrt ((K*Real.log B)*Real.log w)) ≤ Real.exp (-M*Real.log B)
  exact Real.exp_le_exp.mpr (by linarith)

theorem rebased_ratio_separation {K M L s b : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M)
    (hLK : K ≤ L) (hLM : 4*M+10 ≤ L) (hs : (1/2:ℝ) ≤ s) (hb : L^4 < b) :
    s+4 ≤ (b*s)/(K*L) ∧ 2*M*L ≤ (b*s)/(K*L)-s := by
  have hL : 1 ≤ L := hK.trans hLK
  have hK0 : 0 < K := by linarith
  have hL0 : 0 < L := by linarith
  have ha : 0 < K*L := mul_pos hK0 hL0
  have hcoef : (K*L)*L^2 ≤ b := by
    have hh := mul_le_mul_of_nonneg_right hLK (pow_nonneg hL0.le 3)
    nlinarith
  have hratio : L^2 ≤ b/(K*L) := (le_div_iff₀ ha).mpr (by nlinarith)
  have ht : s*L^2 ≤ (b*s)/(K*L) := by
    have hh := mul_le_mul_of_nonneg_left hratio (show 0 ≤ s by linarith)
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hdiff : (L^2-1)/2 ≤ (b*s)/(K*L)-s := by
    have hh := mul_le_mul_of_nonneg_right hs (show 0 ≤ L^2-1 by nlinarith)
    nlinarith
  have hpoly : 2*M*L ≤ (L^2-1)/2 ∧ 4 ≤ (L^2-1)/2 := by
    have hh := mul_nonneg hL0.le (show 0 ≤ L-(4*M+10) by linarith)
    constructor <;> nlinarith
  exact ⟨by linarith [hpoly.2],hpoly.1.trans hdiff⟩

end NumberTheoryLean.GlobalResidualScale



namespace NumberTheoryLean.ReferenceResidualQuadrature

open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeTiltGeometry
open ReferenceMertens ReferenceResidualErrors ReferenceProductErrorBounds ReferenceHighIntervals
open ReferenceWeightedQuadrature

theorem actual_quadrature_error : ∃ c C w₀ : ℝ,0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → ∀ z : Node,Valid z.side z.ratio → Consistent z → 2 ≤ z.cutoff →
      |quadratureError w z| ≤ (C*weight z.side z.ratio/2)*primeError c w 2 := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,h⟩ := source_weighted_quadrature
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro w hw z hs hz hb
  have hw1 : 1 < w := hw₀.trans_le hw
  have hr := ratio_eq_gap_div_cutoff hs hz (by linarith)
  have hs' : Valid z.side (z.gap/z.cutoff) := by rwa [← hr]
  have hh := h w hw 2 z.cutoff z.cutoff z.gap le_rfl hb le_rfl z.side hs'
    (highInterval z.cutoff z.closed) (highInterval_orderConnected _ _) (highInterval_subset _ _)
  rw [← hr] at hh
  unfold quadratureError
  rw [highPrime_sum hw1]
  simpa only [childRatio,primeError] using hh

end NumberTheoryLean.ReferenceResidualQuadrature



namespace NumberTheoryLean.WeightPowerBounds

open FinitePathGeometry WeightDistantDecay GlobalResidualScale

theorem relative_weight_power : ∃ C : ℝ,0 < C ∧ ∀ M B : ℝ,∀ i j : Side,∀ s t : ℝ,
    Valid i s → s+4 ≤ t → 2*M*Real.log B ≤ t-s →
      weight j t ≤ C*weight i s*powerDecay M B := by
  obtain ⟨C,hC,h⟩ := relative_weight_decay
  refine ⟨C,hC,?_⟩
  intro M B i j s t hs hst hgap
  apply (h i j s t hs hst).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (weight_pos hs).le)
  change Real.exp (-(t-s)/2) ≤ Real.exp (-M*Real.log B)
  exact Real.exp_le_exp.mpr (by linarith)

end NumberTheoryLean.WeightPowerBounds



namespace NumberTheoryLean.ReferenceResidualPointwise

open _root_.Finset
open FinitePathGeometry PrimeHistories PrimeBinMembership ActualBoundaryDomain
open ReferenceSourcePrimeSets ReferenceMertens ReferenceProductErrors ReferenceLocalResidual
open ReferenceResidualErrors ReferenceProductErrorBounds ReferenceResidualQuadrature ReferenceHighIntervals

theorem residual_abs_triangle (w : ℝ) {z : Node} (hs : Valid z.side z.ratio) (hz : Consistent z)
    (hb : 2 ≤ z.cutoff) (hdom : BoundaryDomain z.side z.gap) :
    |sourceResidual w z| ≤ |boundaryProductError w z|+|parentProductError w z|+
      |primeProductError w z|+|normalization w*quadratureError w z| := by
  rw [residual_error_identity w hs hz hb hdom]
  have h1 := abs_sub (boundaryProductError w z-parentProductError w z-primeProductError w z)
    (normalization w*quadratureError w z)
  have h2 := abs_sub (boundaryProductError w z-parentProductError w z) (primeProductError w z)
  have h3 := abs_sub (boundaryProductError w z) (parentProductError w z)
  linarith

theorem source_residual_pointwise : ∃ c C w₀ : ℝ,0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → ∀ z : Node,Valid z.side z.ratio → Consistent z → 2 ≤ z.cutoff →
      BoundaryDomain z.side z.gap →
      |sourceResidual w z| ≤ C*weight z.side z.ratio*(1+Real.log z.cutoff)*primeError c w 2 := by
  obtain ⟨cP,CP,wP,hcP,hCP,hwP,hP⟩ := reference_product_absolute
  obtain ⟨cQ,CQ,wQ,hcQ,hCQ,hwQ,hQ⟩ := actual_quadrature_error
  obtain ⟨CH,wH,hCH,_hwH,hH⟩ := highPrime_mass_bound
  let c := min cP cQ
  let C := 4*CP+2*CP*CH+CQ
  have hc : 0 < c := lt_min hcP hcQ
  refine ⟨c,C,max wP (max wQ wH),hc,by dsimp [C] <;> positivity,
    hwP.trans_le (le_max_left _ _),?_⟩
  intro w hw z hs hz hb hdom
  have hwp : wP ≤ w := (le_max_left _ _).trans hw
  have hwq : wQ ≤ w := ((le_max_left _ _).trans (le_max_right _ _)).trans hw
  have hwh : wH ≤ w := ((le_max_right _ _).trans (le_max_right _ _)).trans hw
  have hw1 : 1 < w := hwP.trans_le hwp
  obtain ⟨_hNlo,hNhi,hProd⟩ := hP w hwp
  have hP' : ∀ t : ℝ,2 ≤ t → ∀ closed : Bool,
      |referenceProduct w t closed-normalization w/t| ≤ (CP/t)*primeError c w t := by
    intro t ht closed
    have he := exp_error_mono_rate (t:=t*Real.log w) (min_le_left cP cQ)
    exact (hProd t ht closed).trans (mul_le_mul_of_nonneg_left he (div_nonneg hCP.le (by linarith)))
  obtain ⟨hB,hPar,hPrime⟩ := finite_product_error_bounds hc.le hCP.le hw1 hP' hs hz hb
  have hφ := weight_pos hs
  have hQ' : |quadratureError w z| ≤ (CQ*weight z.side z.ratio/2)*primeError c w 2 := by
    have he := exp_error_mono_rate (t:=2*Real.log w) (min_le_right cP cQ)
    exact (hQ w hwq z hs hz hb).trans (mul_le_mul_of_nonneg_left he (by positivity))
  have hN : |normalization w| ≤ 2 := by rw [abs_of_pos (normalization_pos hw1)]; exact hNhi
  have hNQ : |normalization w*quadratureError w z| ≤ CQ*weight z.side z.ratio*primeError c w 2 := by
    rw [abs_mul]
    have hh := mul_le_mul hN hQ' (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hMass := hH w hwh z.cutoff hb z.closed
  have hE := primeError_pos c w 2
  have hPrime' : |primeProductError w z| ≤
      (2*CP*weight z.side z.ratio*primeError c w 2)*(CH*(1+Real.log z.cutoff)) :=
    hPrime.trans (mul_le_mul_of_nonneg_left hMass (by positivity))
  have htri := residual_abs_triangle w hs hz hb hdom
  have hL : 1 ≤ 1+Real.log z.cutoff := by have hh := Real.log_nonneg (show 1 ≤ z.cutoff by linarith); linarith
  have hpay : (4*CP+CQ)*weight z.side z.ratio*primeError c w 2 ≤
      (4*CP+CQ)*weight z.side z.ratio*primeError c w 2*(1+Real.log z.cutoff) :=
    le_mul_of_one_le_right (by positivity) hL
  calc
    _ ≤ (4*CP+CQ)*weight z.side z.ratio*primeError c w 2+
      (2*CP*weight z.side z.ratio*primeError c w 2)*(CH*(1+Real.log z.cutoff)) := by
        nlinarith only [htri,hB,hPar,hPrime',hNQ]
    _ ≤ (4*CP+CQ)*weight z.side z.ratio*primeError c w 2*(1+Real.log z.cutoff)+
      (2*CP*weight z.side z.ratio*primeError c w 2)*(CH*(1+Real.log z.cutoff)) :=
        add_le_add_left hpay _
    _ = _ := by dsimp [C] <;> ring

end NumberTheoryLean.ReferenceResidualPointwise



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_ReferenceIntervalBound
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferenceIntervalCutoff

attribute [local instance] Classical.propDecidable
open _root_.Finset _root_.Set _root_.MeasureTheory
open FinitePathGeometry PrimeHistories PrimeTiltGeometry PrimeBinMembership
open ReferenceSourcePrimeSets ReferenceMertens ReferenceLocalResidual ReferenceHighIntervals ReferenceResidualErrors
open ReferenceBenchmarkDecay ReferenceDifferentiation
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem primeInterval_orderConnected (a b : ℝ) (closed : Bool) : (primeInterval a b closed).OrdConnected := by
  cases closed
  · exact ordConnected_Ioo
  · exact ordConnected_Ioc

theorem primeInterval_subset (a b : ℝ) (closed : Bool) : primeInterval a b closed ⊆ Icc a b := by
  intro x hx
  refine ⟨hx.1.le,?_⟩
  cases closed
  · exact hx.2.le
  · exact hx.2

theorem primeInterval_integral {a b : ℝ} (hab : a ≤ b) (closed : Bool) (F : ℝ → ℝ) :
    (∫ x in primeInterval a b closed,F x)=∫ x in a..b,F x := by
  cases closed
  · change (∫ x in Ioo a b,F x)=_
    rw [← integral_Ioc_eq_integral_Ioo,intervalIntegral.integral_of_le hab]
  · exact (intervalIntegral.integral_of_le hab).symm

theorem intervalPrimes_eq_filter {w a : ℝ} (hw : 1 < w) (ha : 2 ≤ a) (b : ℝ) (closed : Bool) :
    intervalPrimes w a b closed=(Nat.primesLE ⌊w^b⌋₊).filter (fun p => primeExponent w p ∈ primeInterval a b closed) := by
  rw [intervalPrimes,highPrimes_eq_filter hw,Finset.filter_filter]
  apply Finset.filter_congr
  intro p _hp
  simp only [highInterval,primeInterval,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨_h2,hcap⟩,haP⟩
    exact ⟨haP,hcap⟩
  · rintro ⟨haP,hcap⟩
    exact ⟨⟨ha.trans_lt haP,hcap⟩,haP⟩

theorem intervalPrime_sum {w a : ℝ} (hw : 1 < w) (ha : 2 ≤ a) (b : ℝ) (closed : Bool) (F : ℕ → ℝ) :
    (∑ p ∈ intervalPrimes w a b closed,F p)=
      ∑ p ∈ Nat.primesLE ⌊w^b⌋₊,if primeExponent w p ∈ primeInterval a b closed then F p else 0 := by
  rw [intervalPrimes_eq_filter hw ha,Finset.sum_filter]

theorem lowerHigh_subset {w a b : ℝ} (hw : 1 < w) (hab : a < b) (closed : Bool) :
    highPrimes w a true ⊆ highPrimes w b closed := by
  intro p hp
  obtain ⟨hpP,h2,ha⟩ := (highPrimes_membership hw a true p).mp hp
  have ha' : primeExponent w p ≤ a := ha
  apply (highPrimes_membership hw b closed p).mpr
  refine ⟨hpP,h2,?_⟩
  cases closed
  · exact ha'.trans_lt hab
  · exact ha'.trans hab.le

theorem highPrimes_split {w a b : ℝ} (hw : 1 < w) (hab : a < b) (closed : Bool) :
    highPrimes w b closed=highPrimes w a true ∪ intervalPrimes w a b closed := by
  ext p
  constructor
  · intro hp
    by_cases hx : a<primeExponent w p
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hp,hx⟩))
    · obtain ⟨hpP,h2,_hcap⟩ := (highPrimes_membership hw b closed p).mp hp
      exact Finset.mem_union.mpr (Or.inl ((highPrimes_membership hw a true p).mpr ⟨hpP,h2,le_of_not_gt hx⟩))
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact lowerHigh_subset hw hab closed hp
    · exact (Finset.mem_filter.mp hp).1

theorem highPrimes_split_disjoint {w a b : ℝ} (hw : 1 < w) (closed : Bool) :
    Disjoint (highPrimes w a true) (intervalPrimes w a b closed) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hlow : primeExponent w p ≤ a := ((highPrimes_membership hw a true p).mp hp).2.2
  have hhigh := (Finset.mem_filter.mp hq).2
  exact (not_lt_of_ge hlow) hhigh

theorem highPrime_sum_split {w a b : ℝ} (hw : 1 < w) (hab : a < b) (closed : Bool) (F : ℕ → ℝ) :
    (∑ p ∈ highPrimes w b closed,F p)=
      (∑ p ∈ highPrimes w a true,F p)+(∑ p ∈ intervalPrimes w a b closed,F p) := by
  rw [highPrimes_split hw hab,Finset.sum_union (highPrimes_split_disjoint hw closed)]

theorem residual_split {w : ℝ} (hw : 1 < w) (z : Node) {a : ℝ} (hab : a < z.cutoff) :
    sourceResidual w z=sourceResidual w (rebase z a)+intervalResidual w z a := by
  unfold sourceResidual intervalResidual
  simp only [rebase]
  rw [highPrime_sum_split hw hab z.closed]
  ring

theorem rebase_invariants {z : Node} (hs : Valid z.side z.ratio) (hr : 0 < z.gap) (hz : Consistent z)
    {a : ℝ} (ha : 0 < a) (hab : a ≤ z.cutoff) :
    Valid (rebase z a).side (rebase z a).ratio ∧ Consistent (rebase z a) := by
  have hb : 0 < z.cutoff := ha.trans_le hab
  have hrat := ratio_eq_gap_div_cutoff hs hz hb
  have hdiv := div_le_div_of_nonneg_left hr.le ha hab
  rw [← hrat] at hdiv
  constructor
  · change Valid z.side (z.gap/a)
    cases hi : z.side <;> simp only [hi,Valid] at hs ⊢ <;> linarith
  · change a=z.gap/(z.gap/a)
    field_simp

end NumberTheoryLean.ReferenceIntervalCutoff

end

section

namespace NumberTheoryLean.ReferenceIntervalErrors

open _root_.Finset _root_.Set _root_.MeasureTheory
open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeTiltGeometry
open ReferenceBenchmarkDecay ReferenceDifferentiation ReferenceCancellation ReferenceWeightDomination
open ReferenceMertens ReferenceResidualErrors ReferenceIntervalCutoff
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem continuous_interval_cancellation (i : Side) {r a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b)
    (hs : ParentDomain i (r/b)) :
    (parentBenchmark i (r/a)-1)/a-(parentBenchmark i (r/b)-1)/b-
      (∫ x in a..b,(benchmark i.flip (r/x-1)-1)/x^2)=0 := by
  have hb : 2 ≤ b := ha.trans hab
  have hi : IntervalIntegrable (fun x => (benchmark i.flip (r/x-1)-1)/x^2) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro x hx
    exact (prospective_integrand_continuousAt i (by linarith [hx.1])
      (parent_domain_interval i hb hs ⟨ha.trans hx.1,hx.2⟩)).continuousWithinAt
  have hd : ∀ x ∈ uIcc a b,HasDerivAt (fun t => (parentBenchmark i (r/t)-1)/t)
      (-(benchmark i.flip (r/x-1)-1)/x^2) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact reference_derivative i (by linarith [hx.1]) (parent_domain_interval i hb hs ⟨ha.trans hx.1,hx.2⟩)
  have hin : IntervalIntegrable (fun x => -(benchmark i.flip (r/x-1)-1)/x^2) volume a b := by
    convert! hi.neg using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    exact neg_div _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hin
  simp_rw [neg_div] at h
  rw [intervalIntegral.integral_neg] at h
  linarith

theorem normalized_interval_zero (w : ℝ) {z : Node} (hs : Valid z.side z.ratio) (hz : Consistent z)
    {a : ℝ} (ha : 2 ≤ a) (hab : a ≤ z.cutoff) :
    (normalization w/a)*(parentBenchmark z.side (z.gap/a)-1)-
      (normalization w/z.cutoff)*(parentBenchmark z.side z.ratio-1)-
      normalization w*(∫ x in primeInterval a z.cutoff z.closed,(benchmark z.side.flip (z.gap/x-1)-1)/x^2)=0 := by
  have hr := ratio_eq_gap_div_cutoff hs hz (by linarith)
  have hd : ParentDomain z.side (z.gap/z.cutoff) := by rw [← hr]; exact valid_parent_domain hs
  have hc := continuous_interval_cancellation z.side ha hab hd
  rw [← hr] at hc
  rw [primeInterval_integral hab]
  have hm := congrArg (fun t : ℝ => normalization w*t) hc
  convert! hm using 1 <;> first | (with_reducible_and_instances rfl) | ring

theorem interval_error_identity (w : ℝ) {z : Node} (hs : Valid z.side z.ratio) (hz : Consistent z)
    {a : ℝ} (ha : 2 ≤ a) (hab : a ≤ z.cutoff) :
    intervalResidual w z a=lowerProductError w z a-parentProductError w z-intervalPrimeError w z a-
      normalization w*intervalQuadratureError w z a := by
  have hc := normalized_interval_zero w hs hz ha hab
  have hp : (∑ p ∈ intervalPrimes w a z.cutoff z.closed,(p:ℝ)⁻¹*referenceProduct w (primeExponent w p) false*
      (benchmark z.side.flip (childRatio w z.gap p)-1))=
    intervalPrimeError w z a+normalization w*(∑ p ∈ intervalPrimes w a z.cutoff z.closed,(p:ℝ)⁻¹*
      (benchmark z.side.flip (childRatio w z.gap p)-1)/primeExponent w p) := by
    rw [intervalPrimeError,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    ring
  unfold intervalResidual lowerProductError parentProductError intervalQuadratureError
  rw [hp]
  nlinarith

end NumberTheoryLean.ReferenceIntervalErrors

end

section

namespace NumberTheoryLean.ReferenceIntervalProductBounds

open _root_.Finset
open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeTiltGeometry
open ReferenceMertens ReferenceSourcePrimeSets ReferenceBenchmarkDecay ReferenceDifferentiation
open ReferenceResidualErrors ReferenceProductErrorBounds ReferenceIntervalCutoff ReferenceIntervalErrors ReferenceParentMonotonicity
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem finite_interval_product_bounds {c C w : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C) (hw : 1 < w)
    (hP : ∀ t : ℝ,2 ≤ t → ∀ closed : Bool,
      |referenceProduct w t closed-normalization w/t| ≤ (C/t)*primeError c w t)
    {z : Node} (hs : Valid z.side z.ratio) (hz : Consistent z) {a : ℝ} (ha : 2 ≤ a) (hab : a ≤ z.cutoff) :
    |lowerProductError w z a| ≤ 2*C*weight z.side z.ratio*primeError c w a ∧
    |parentProductError w z| ≤ 2*C*weight z.side z.ratio*primeError c w a ∧
    |intervalPrimeError w z a| ≤ (2*C*weight z.side z.ratio*primeError c w a)*
      (∑ p ∈ intervalPrimes w a z.cutoff z.closed,(p:ℝ)⁻¹) := by
  have hφ := weight_pos hs
  have hE := primeError_pos c w a
  have hr := ratio_eq_gap_div_cutoff hs hz (by linarith)
  have hs' : Valid z.side (z.gap/z.cutoff) := by rwa [← hr]
  have hD := interval_deviations_bound z.side ha hab hs' ⟨hab,le_rfl⟩
  rw [← hr] at hD
  have hparent : |parentBenchmark z.side z.ratio-1| ≤ 4*weight z.side z.ratio := by
    linarith [abs_nonneg (parentBenchmark z.side (z.gap/a)-1),abs_nonneg (benchmark z.side.flip (z.ratio-1)-1)]
  have hlower : |parentBenchmark z.side (z.gap/a)-1| ≤ 4*weight z.side z.ratio := by
    linarith [abs_nonneg (parentBenchmark z.side z.ratio-1),abs_nonneg (benchmark z.side.flip (z.ratio-1)-1)]
  have hscale : ∀ t : ℝ,a ≤ t → ∀ closed : Bool,
      |referenceProduct w t closed-normalization w/t| ≤ (C/2)*primeError c w a := by
    intro t ht closed
    apply (hP t (ha.trans ht) closed).trans
    exact mul_le_mul (div_le_div_of_nonneg_left hC (by norm_num) (ha.trans ht))
      (primeError_antitone hc hw ht) (primeError_pos _ _ _).le (by positivity)
  constructor
  · unfold lowerProductError
    rw [abs_mul]
    have h := mul_le_mul (hscale a le_rfl true) hlower (abs_nonneg _) (by positivity)
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  constructor
  · unfold parentProductError
    rw [abs_mul]
    have h := mul_le_mul (hscale z.cutoff hab z.closed) hparent (abs_nonneg _) (by positivity)
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · unfold intervalPrimeError
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpH := (Finset.mem_filter.mp hp).1
    have hxa : a ≤ primeExponent w p := (Finset.mem_filter.mp hp).2.le
    obtain ⟨_hprime,_hxp,hcap⟩ := (highPrimes_membership hw z.cutoff z.closed p).mp hpH
    have hxb : primeExponent w p ≤ z.cutoff := by
      cases hcl : z.closed with
      | false => have h : primeExponent w p < z.cutoff := by simpa [capGuard,hcl] using hcap
                 exact h.le
      | true => simpa [capGuard,hcl] using hcap
    have hchild0 := interval_deviations_bound z.side ha hab hs' ⟨hxa,hxb⟩
    rw [← hr] at hchild0
    have hchild : |benchmark z.side.flip (childRatio w z.gap p)-1| ≤ 4*weight z.side z.ratio := by
      unfold childRatio
      linarith [abs_nonneg (parentBenchmark z.side z.ratio-1),abs_nonneg (parentBenchmark z.side (z.gap/a)-1)]
    rw [abs_mul,abs_mul,abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p))]
    have hleft := mul_le_mul_of_nonneg_left (hscale (primeExponent w p) hxa false)
      (inv_nonneg.mpr (Nat.cast_nonneg p))
    have h := mul_le_mul hleft hchild (abs_nonneg _) (by positivity)
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    ring

end NumberTheoryLean.ReferenceIntervalProductBounds

end

section

namespace NumberTheoryLean.ReferenceIntervalQuadrature

open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeTiltGeometry
open ReferenceProductErrorBounds ReferenceResidualErrors ReferenceIntervalCutoff ReferenceIntervalErrors
open ReferenceWeightedQuadrature

theorem actual_interval_quadrature : ∃ c C w₀ : ℝ,0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → ∀ z : Node,Valid z.side z.ratio → Consistent z →
      ∀ a : ℝ,2 ≤ a → a ≤ z.cutoff →
      |intervalQuadratureError w z a| ≤ (C*weight z.side z.ratio/2)*primeError c w a := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,h⟩ := source_weighted_quadrature
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro w hw z hs hz a ha hab
  have hw1 : 1 < w := hw₀.trans_le hw
  have hr := ratio_eq_gap_div_cutoff hs hz (by linarith)
  have hs' : Valid z.side (z.gap/z.cutoff) := by rwa [← hr]
  have hh := h w hw a z.cutoff z.cutoff z.gap ha hab le_rfl z.side hs'
    (primeInterval a z.cutoff z.closed) (primeInterval_orderConnected _ _ _) (primeInterval_subset _ _ _)
  rw [← hr] at hh
  have hφ := weight_pos hs
  have hl : C*weight z.side z.ratio/a ≤ C*weight z.side z.ratio/2 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) ha
  unfold intervalQuadratureError
  rw [intervalPrime_sum hw1 ha]
  apply le_trans (by simpa only [childRatio] using hh)
  exact mul_le_mul_of_nonneg_right hl (primeError_pos _ _ _).le

end NumberTheoryLean.ReferenceIntervalQuadrature

end

section

namespace NumberTheoryLean.ReferenceIntervalBound

open _root_.Finset
open FinitePathGeometry PrimeHistories PrimeBinMembership
open ReferenceSourcePrimeSets ReferenceMertens ReferenceProductErrors ReferenceLocalResidual ReferenceHighIntervals
open ReferenceResidualErrors ReferenceProductErrorBounds ReferenceIntervalCutoff ReferenceIntervalErrors
open ReferenceIntervalProductBounds ReferenceIntervalQuadrature

theorem interval_abs_triangle (w : ℝ) {z : Node} (hs : Valid z.side z.ratio) (hz : Consistent z)
    {a : ℝ} (ha : 2 ≤ a) (hab : a ≤ z.cutoff) :
    |intervalResidual w z a| ≤ |lowerProductError w z a|+|parentProductError w z|+
      |intervalPrimeError w z a|+|normalization w*intervalQuadratureError w z a| := by
  rw [interval_error_identity w hs hz ha hab]
  have h1 := abs_sub (lowerProductError w z a-parentProductError w z-intervalPrimeError w z a)
    (normalization w*intervalQuadratureError w z a)
  have h2 := abs_sub (lowerProductError w z a-parentProductError w z) (intervalPrimeError w z a)
  have h3 := abs_sub (lowerProductError w z a) (parentProductError w z)
  linarith

theorem actual_interval_residual_bound : ∃ c C w₀ : ℝ,0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → ∀ z : Node,Valid z.side z.ratio → Consistent z →
      ∀ a : ℝ,2 ≤ a → a ≤ z.cutoff →
      |intervalResidual w z a| ≤ C*weight z.side z.ratio*(1+Real.log z.cutoff)*primeError c w a := by
  obtain ⟨cP,CP,wP,hcP,hCP,hwP,hP⟩ := reference_product_absolute
  obtain ⟨cQ,CQ,wQ,hcQ,hCQ,_hwQ,hQ⟩ := actual_interval_quadrature
  obtain ⟨CH,wH,hCH,_hwH,hH⟩ := highPrime_mass_bound
  let c := min cP cQ
  let C := 4*CP+2*CP*CH+CQ
  have hc : 0 < c := lt_min hcP hcQ
  refine ⟨c,C,max wP (max wQ wH),hc,by dsimp [C] <;> positivity,hwP.trans_le (le_max_left _ _),?_⟩
  intro w hw z hs hz a ha hab
  have hwp : wP ≤ w := (le_max_left _ _).trans hw
  have hwq : wQ ≤ w := ((le_max_left _ _).trans (le_max_right _ _)).trans hw
  have hwh : wH ≤ w := ((le_max_right _ _).trans (le_max_right _ _)).trans hw
  have hw1 : 1 < w := hwP.trans_le hwp
  obtain ⟨_hNlo,hNhi,hProd⟩ := hP w hwp
  have hP' : ∀ t : ℝ,2 ≤ t → ∀ closed : Bool,
      |referenceProduct w t closed-normalization w/t| ≤ (CP/t)*primeError c w t := by
    intro t ht closed
    exact (hProd t ht closed).trans (mul_le_mul_of_nonneg_left
      (exp_error_mono_rate (t:=t*Real.log w) (min_le_left cP cQ)) (by positivity))
  obtain ⟨hLow,hPar,hPrime⟩ := finite_interval_product_bounds hc.le hCP.le hw1 hP' hs hz ha hab
  have hφ := weight_pos hs
  have hE := primeError_pos c w a
  have hQ' : |intervalQuadratureError w z a| ≤ (CQ*weight z.side z.ratio/2)*primeError c w a := by
    exact (hQ w hwq z hs hz a ha hab).trans (mul_le_mul_of_nonneg_left
      (exp_error_mono_rate (t:=a*Real.log w) (min_le_right cP cQ)) (by positivity))
  have hN : |normalization w| ≤ 2 := by rw [abs_of_pos (normalization_pos hw1)]; exact hNhi
  have hNQ : |normalization w*intervalQuadratureError w z a| ≤ CQ*weight z.side z.ratio*primeError c w a := by
    rw [abs_mul]
    have hh := mul_le_mul hN hQ' (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hMass : (∑ p ∈ intervalPrimes w a z.cutoff z.closed,(p:ℝ)⁻¹) ≤ CH*(1+Real.log z.cutoff) := by
    apply le_trans _ (hH w hwh z.cutoff (ha.trans hab) z.closed)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun p _ _ => by positivity)
  have hPrime' : |intervalPrimeError w z a| ≤
      (2*CP*weight z.side z.ratio*primeError c w a)*(CH*(1+Real.log z.cutoff)) :=
    hPrime.trans (mul_le_mul_of_nonneg_left hMass (by positivity))
  have htri := interval_abs_triangle w hs hz ha hab
  have hL : 1 ≤ 1+Real.log z.cutoff := by
    have hh := Real.log_nonneg (show 1 ≤ z.cutoff by linarith)
    linarith
  have hpay : (4*CP+CQ)*weight z.side z.ratio*primeError c w a ≤
      (4*CP+CQ)*weight z.side z.ratio*primeError c w a*(1+Real.log z.cutoff) :=
    le_mul_of_one_le_right (by positivity) hL
  calc
    _ ≤ (4*CP+CQ)*weight z.side z.ratio*primeError c w a+
      (2*CP*weight z.side z.ratio*primeError c w a)*(CH*(1+Real.log z.cutoff)) := by
        nlinarith only [htri,hLow,hPar,hPrime',hNQ]
    _ ≤ (4*CP+CQ)*weight z.side z.ratio*primeError c w a*(1+Real.log z.cutoff)+
      (2*CP*weight z.side z.ratio*primeError c w a)*(CH*(1+Real.log z.cutoff)) := add_le_add_left hpay _
    _ = _ := by dsimp [C] <;> ring

theorem source_residual_split_bound : ∃ c C w₀ : ℝ,0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → ∀ z : Node,Valid z.side z.ratio → Consistent z →
      ∀ a : ℝ,2 ≤ a → a < z.cutoff →
      |sourceResidual w z| ≤ |sourceResidual w (rebase z a)|+
        C*weight z.side z.ratio*(1+Real.log z.cutoff)*primeError c w a := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,h⟩ := actual_interval_residual_bound
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro w hw z hs hz a ha hab
  rw [residual_split (hw₀.trans_le hw) z hab]
  exact (abs_add_le _ _).trans (add_le_add_right (h w hw z hs hz a ha hab.le) _)

end NumberTheoryLean.ReferenceIntervalBound

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceReferenceRemainders
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.LargeCutoffResidual

open FinitePathGeometry PrimeHistories PrimeBinMembership ActualBoundaryDomain
open ReferenceLocalResidual ReferenceResidualErrors ReferenceResidualPointwise ReferenceProductErrorBounds
open ReferenceIntervalCutoff ReferenceIntervalBound GlobalResidualScale WeightPowerBounds

theorem large_cutoff_relative_power (d M : ℝ) (hd : 0 < d) (hM : 0 < M) :
    ∃ C T w₀ : ℝ,0 < C ∧ 2 ≤ T ∧ 1 < w₀ ∧ ∀ B w : ℝ,0 < B → T ≤ Real.log B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ z : Node,Valid z.side z.ratio → Consistent z →
        BoundaryDomain z.side z.gap → z.cutoff ≤ B → (Real.log B)^4 < z.cutoff →
        |sourceResidual w z| ≤ C*weight z.side z.ratio*(1+Real.log B)*powerDecay M B := by
  obtain ⟨cP,CP,wP,hcP,hCP,hwP,hP⟩ := source_residual_pointwise
  obtain ⟨cI,CI,wI,hcI,hCI,_hwI,hI⟩ := source_residual_split_bound
  obtain ⟨K,hK,hSave⟩ := linear_log_cutoff_saving hcI hd hM
  obtain ⟨CR,hCR,hRelative⟩ := relative_weight_power
  let T := max K (4*M+10)
  have hT : 2 ≤ T := by have h := le_max_right K (4*M+10); dsimp [T] <;> linarith
  refine ⟨CP*CR+CI,T,max wP wI,by positivity,hT,hwP.trans_le (le_max_left _ _),?_⟩
  intro B w hB hBT hw hcomp z hs hz hdom hcap hbig
  have hL2 : 2 ≤ Real.log B := hT.trans hBT
  have hL : 0 ≤ Real.log B := by linarith
  have hKL : K ≤ Real.log B := (le_max_left _ _).trans hBT
  have hML : 4*M+10 ≤ Real.log B := (le_max_right _ _).trans hBT
  have hB1 : 1 ≤ B := (Real.log_nonneg_iff hB).mp hL
  have hKpos : 0 < K := by linarith
  have hwp : wP ≤ w := (le_max_left _ _).trans hw
  have hwi : wI ≤ w := (le_max_right _ _).trans hw
  have hw1 : 1 < w := hwP.trans_le hwp
  let a := K*Real.log B
  have ha : 2 ≤ a := by dsimp [a] <;> nlinarith
  have hab : a < z.cutoff := by
    have ha2 : a ≤ (Real.log B)^2 := by dsimp [a] <;> nlinarith [mul_le_mul_of_nonneg_right hKL hL]
    have h24 : (Real.log B)^2 ≤ (Real.log B)^4 := by
      nlinarith [mul_le_mul_of_nonneg_right (show 1 ≤ (Real.log B)^2 by nlinarith) (sq_nonneg (Real.log B))]
    exact (ha2.trans h24).trans_lt hbig
  have hsHalf : (1/2:ℝ) ≤ z.ratio := by cases hi : z.side <;> simp only [hi,Valid] at hs <;> linarith
  have he := (eq_div_iff (ne_of_gt (valid_pos hs))).mp hz
  have hr : 0 < z.gap := by rw [← he]; exact mul_pos (by linarith) (valid_pos hs)
  have hsep := rebased_ratio_separation hK hM.le hKL hML hsHalf hbig
  rw [he] at hsep
  obtain ⟨hvs,hzs⟩ := rebase_invariants hs hr hz (by linarith : 0 < a) hab.le
  have hφ := weight_pos hs
  have hφa := weight_pos hvs
  have hWeight : weight (rebase z a).side (rebase z a).ratio ≤ CR*weight z.side z.ratio*powerDecay M B :=
    hRelative M B z.side z.side z.ratio (z.gap/a) hs hsep.1 hsep.2
  have hLogA : Real.log a ≤ Real.log B := Real.log_le_log (by linarith) (hab.le.trans hcap)
  have hLogB : Real.log z.cutoff ≤ Real.log B := Real.log_le_log (by linarith) hcap
  have hLA : 0 ≤ 1+Real.log a := by have hh := Real.log_nonneg (show 1 ≤ a by linarith); linarith
  have hLb : 0 ≤ 1+Real.log z.cutoff := by have hh := Real.log_nonneg (show 1 ≤ z.cutoff by linarith); linarith
  have hLB : 0 ≤ 1+Real.log B := by linarith
  have hPow := powerDecay_pos M B
  have hE2pos := primeError_pos cP w 2
  have hEApos := primeError_pos cI w a
  have hE2 := primeError_le_one hcP.le w 2
  have hEA := hSave B w hB1 hw1 hcomp
  have hLow : |sourceResidual w (rebase z a)| ≤ CP*CR*weight z.side z.ratio*(1+Real.log B)*powerDecay M B := by
    have hh := hP w hwp (rebase z a) hvs hzs ha hdom
    calc
      _ ≤ CP*weight (rebase z a).side (rebase z a).ratio*(1+Real.log a)*primeError cP w 2 := hh
      _ ≤ CP*(CR*weight z.side z.ratio*powerDecay M B)*(1+Real.log B)*1 := by gcongr
      _ = _ := by ring
  have hHigh : CI*weight z.side z.ratio*(1+Real.log z.cutoff)*primeError cI w a ≤
      CI*weight z.side z.ratio*(1+Real.log B)*powerDecay M B := by gcongr
  have hh := hI w hwi z hs hz a ha hab
  calc
    _ ≤ CP*CR*weight z.side z.ratio*(1+Real.log B)*powerDecay M B+
        CI*weight z.side z.ratio*(1+Real.log B)*powerDecay M B := hh.trans (add_le_add hLow hHigh)
    _ = _ := by ring

end NumberTheoryLean.LargeCutoffResidual



namespace NumberTheoryLean.LowStateResidualBound

open FinitePathGeometry PrimeHistories PrimeBinMembership ActualBoundaryDomain
open ReferenceLocalResidual ReferenceResidualPointwise ReferenceProductErrorBounds GlobalResidualScale LargeCutoffResidual

theorem low_state_normalized_residual_jb247_oai (d : ℝ) (hd : 0 < d) :
    ∃ c C T w₀ : ℝ,0 < c ∧ 0 < C ∧ 2 ≤ T ∧ 1 < w₀ ∧
      ∀ B w : ℝ,0 < B → T ≤ Real.log B → w₀ ≤ w → Real.log B ≤ d*Real.log w →
      ∀ z : Node,Valid z.side z.ratio → Consistent z → BoundaryDomain z.side z.gap →
        2 ≤ z.cutoff → z.cutoff ≤ B → z.gap ≤ (23/10:ℝ)*B → z.ratio ≤ (Real.log B)^2 →
        (z.gap^2/weight z.side z.ratio)*|sourceResidual w z| ≤
          C*((Real.log B)^13*primeError c w 2+1/B^7) := by
  obtain ⟨c,CP,wP,hc,hCP,hwP,hP⟩ := source_residual_pointwise
  obtain ⟨CL,TL,wL,hCL,hTL,_hwL,hLarge⟩ := large_cutoff_relative_power d 10 hd (by norm_num)
  let C := 2*CP+6*CL
  have hC : 0 < C := by dsimp [C] <;> positivity
  refine ⟨c,C,TL,max wP wL,hc,hC,hTL,hwP.trans_le (le_max_left _ _),?_⟩
  intro B w hB hT hw hcomp z hs hz hdom hb hcap hgap hratio
  have hL2 : 2 ≤ Real.log B := hTL.trans hT
  have hL : 0 ≤ Real.log B := by linarith
  have hwp : wP ≤ w := (le_max_left _ _).trans hw
  have hwL : wL ≤ w := (le_max_right _ _).trans hw
  have hφ := weight_pos hs
  have hr : 0 < z.gap := by have hh := boundary_gap_ge_two hdom; linarith
  have hE := primeError_pos c w 2
  have hSmallC : 2*CP ≤ C := by dsimp [C] <;> linarith
  have hLargeC : 6*CL ≤ C := by dsimp [C] <;> linarith
  have hterm0 : 0 ≤ (Real.log B)^13*primeError c w 2 := by positivity
  have hinv0 : 0 ≤ (1:ℝ)/B^7 := by positivity
  by_cases hsmall : z.cutoff ≤ (Real.log B)^4
  · have he := (eq_div_iff (ne_of_gt (valid_pos hs))).mp hz
    have hr6 : z.gap ≤ (Real.log B)^6 := by
      have hm := mul_le_mul hsmall hratio (valid_pos hs).le (pow_nonneg hL 4)
      rw [he] at hm
      nlinarith
    have hr12 : z.gap^2 ≤ (Real.log B)^12 := by
      have hm := pow_le_pow_left₀ hr.le hr6 2
      simpa only [← pow_mul] using hm
    have hlog := Real.log_le_log (by linarith : 0 < z.cutoff) hcap
    have hLf : 0 ≤ 1+Real.log z.cutoff := by have hh := Real.log_nonneg (show 1 ≤ z.cutoff by linarith); linarith
    have hLup : 1+Real.log z.cutoff ≤ 2*Real.log B := by linarith
    have hp := hP w hwp z hs hz hb hdom
    have hm := mul_le_mul_of_nonneg_left hp (div_nonneg (sq_nonneg z.gap) hφ.le)
    have hn : (z.gap^2/weight z.side z.ratio)*|sourceResidual w z| ≤
        CP*z.gap^2*(1+Real.log z.cutoff)*primeError c w 2 := by
      convert! hm using 1
      all_goals try with_reducible_and_instances rfl
      field_simp
    calc
      _ ≤ CP*z.gap^2*(1+Real.log z.cutoff)*primeError c w 2 := hn
      _ ≤ CP*(Real.log B)^12*(2*Real.log B)*primeError c w 2 := by gcongr
      _ = (2*CP)*((Real.log B)^13*primeError c w 2) := by ring
      _ ≤ C*((Real.log B)^13*primeError c w 2) := mul_le_mul_of_nonneg_right hSmallC hterm0
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hinv0) hC.le
  · have hlarge := hLarge B w hB hT hwL hcomp z hs hz hdom hcap (lt_of_not_ge hsmall)
    have hr2 : z.gap^2 ≤ 6*B^2 := by
      have hm := pow_le_pow_left₀ hr.le hgap 2
      nlinarith [sq_nonneg B]
    have hLB : 1+Real.log B ≤ B := by linarith [Real.log_le_sub_one_of_pos hB]
    have hLB0 : 0 ≤ 1+Real.log B := by linarith
    have hPow := powerDecay_pos 10 B
    have hm := mul_le_mul_of_nonneg_left hlarge (div_nonneg (sq_nonneg z.gap) hφ.le)
    have hn : (z.gap^2/weight z.side z.ratio)*|sourceResidual w z| ≤
        CL*z.gap^2*(1+Real.log B)*powerDecay 10 B := by
      convert! hm using 1
      all_goals try with_reducible_and_instances rfl
      field_simp
    calc
      _ ≤ CL*z.gap^2*(1+Real.log B)*powerDecay 10 B := hn
      _ ≤ CL*(6*B^2)*B*powerDecay 10 B := by gcongr
      _ = (6*CL)*(1/B^7) := by
        have hpow10 := powerDecay_nat hB 10
        norm_num only [Nat.cast_ofNat] at hpow10
        rw [hpow10]
        field_simp
      _ ≤ C*(1/B^7) := mul_le_mul_of_nonneg_right hLargeC hinv0
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hterm0) hC.le

end NumberTheoryLean.LowStateResidualBound



open _root_.Set _root_.Filter
open scoped Topology


end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.NumberTheoryLean.LowStateResidualBound.low_state_normalized_residual_jb247_oai := @OAI.Erdos970.NumberTheoryLean.LowStateResidualBound.low_state_normalized_residual_jb247_oai
