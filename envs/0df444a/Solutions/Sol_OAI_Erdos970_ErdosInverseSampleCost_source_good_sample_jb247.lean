-- Prove2me | solution 1 for OAI.Erdos970.ErdosInverseSampleCost.source_good_sample_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:57:29.420287+00:00
-- url     : https://prove2.me/submissions/9d9596ad-f571-4f0e-9b63-3ef1a75d3b9a

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.GroupTheory.Index
import Mathlib.Logic.Equiv.Prod
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.CircleAverage
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
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Order.SuccPred.IntervalSucc
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
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UrysohnsLemma
import Definitions.Def_OAIQ247J008
import Theorems.Thm_Erdos970_Mertens_LogZetaInteg_log_zeta_eq_integ_aux_jb247
import Theorems.Thm_Erdos970_Mertens_sum_M_eq_summand_le_jb247
import Theorems.Thm_OAI_Erdos970_ErdosInverseFrozen_frozen_exceptional_mean_jb247

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeBinCounting
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosInversePrimeBin

theorem primeBin_log_sum {R xi : ℝ} (hR : 0 ≤ R) (hxi : 0 ≤ xi) :
    (∑ p ∈ primeBin R xi,Real.log p) = Chebyshev.theta ((1+xi)*R)-Chebyshev.theta R := by
  have hsub : Nat.primesLE ⌊R⌋₊ ⊆ Nat.primesLE ⌊(1+xi)*R⌋₊ := by
    intro p hp
    obtain ⟨hle,hprime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hle.trans (Nat.floor_mono (by nlinarith)),hprime⟩
  rw [Chebyshev.theta_eq_sum_primesLE,Chebyshev.theta_eq_sum_primesLE]
  simpa only [primeBin] using (Finset.sum_sdiff_eq_sub (f := fun p : ℕ => Real.log p) hsub)

theorem primeBin_log_sum_upper {R xi : ℝ} (hR : 2 ≤ R) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1) :
    (∑ p ∈ primeBin R xi,Real.log p) ≤ (primeBin R xi).card*(2*Real.log R) := by
  have hR0 : 0 < R := by linarith
  have hupper : (1+xi)*R ≤ R^2 := by nlinarith
  have hb0 : 0 < (1+xi)*R := by positivity
  have hlog : Real.log ((1+xi)*R) ≤ 2*Real.log R := by
    have h := Real.log_le_log hb0 hupper
    simpa only [Real.log_pow,Nat.cast_ofNat] using h
  calc
    _ ≤ ∑ _p ∈ primeBin R xi,2*Real.log R := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hprime,_,hhi⟩ := (mem_primeBin hR0.le hxi p).mp hp
      exact (Real.log_le_log (by exact_mod_cast hprime.pos) hhi).trans hlog
    _ = _ := by simp

end ErdosInversePrimeBin

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



namespace ErdosInversePrimeBin
open _root_.Filter _root_.Asymptotics
open scoped Topology
open ErdosPrimeInputs.StrongChebyshev ErdosPrimeInputs.PrimeErrorDecay

theorem prime_bin_theta_error : ∃ c C R₀ : ℝ,0 < c ∧ 0 < C ∧ 2 ≤ R₀ ∧
    ∀ R : ℝ,R₀ ≤ R → ∀ xi : ℝ,0 ≤ xi → xi ≤ 1 →
      |Chebyshev.theta ((1+xi)*R)-Chebyshev.theta R-xi*R| ≤ 3*C*R*decay c R := by
  obtain ⟨c,hc,hstrong⟩ := theta_strong
  obtain ⟨C,hC,hbig⟩ := hstrong.exists_pos
  obtain ⟨A,hA⟩ := eventually_atTop.mp hbig.bound
  refine ⟨c,C,max A 2,hc,hC,le_max_right _ _,?_⟩
  intro R hR xi hxi hxi1
  have hR2 : 2 ≤ R := (le_max_right _ _).trans hR
  have hR0 : 0 < R := by linarith
  have hRA : A ≤ R := (le_max_left _ _).trans hR
  have hbR : R ≤ (1+xi)*R := by nlinarith
  have hb2 : (1+xi)*R ≤ 2*R := by nlinarith
  have htheta (x : ℝ) (hx : A ≤ x) (hx0 : 0 ≤ x) :
      |Chebyshev.theta x-x| ≤ C*(x*decay c x) := by
    have h := hA x hx
    simp only [Real.norm_eq_abs] at h
    rw [abs_of_nonneg (errorScale_nonneg c hx0)] at h
    exact h
  have hr := htheta R hRA hR0.le
  have hb : |Chebyshev.theta ((1+xi)*R)-(1+xi)*R| ≤ 2*C*R*decay c R := by
    calc
      _ ≤ C*(((1+xi)*R)*decay c ((1+xi)*R)) := htheta _ (hRA.trans hbR) (hR0.le.trans hbR)
      _ ≤ C*((2*R)*decay c R) := mul_le_mul_of_nonneg_left
        (mul_le_mul hb2 (decay_antitone hc.le hR0 hbR) (decay_pos _ _).le (by positivity)) hC.le
      _ = _ := by ring
  have he : Chebyshev.theta ((1+xi)*R)-Chebyshev.theta R-xi*R =
      (Chebyshev.theta ((1+xi)*R)-(1+xi)*R)-(Chebyshev.theta R-R) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by nlinarith only [hb,hr])

theorem decay_tendsto_zero {c : ℝ} (hc : 0 < c) : Tendsto (decay c) atTop (𝓝 0) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (Tendsto.const_mul_atTop hc (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [Function.comp_apply,decay,neg_mul]

theorem uniform_bin_theta_error {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ R : ℝ in atTop,2 ≤ R ∧ ∀ xi : ℝ,eta ≤ xi → xi ≤ 1 →
      |Chebyshev.theta ((1+xi)*R)-Chebyshev.theta R-xi*R| ≤ xi*R/2 := by
  obtain ⟨c,C,R₀,hc,hC,hR₀,hbound⟩ := prime_bin_theta_error
  have hdec : Tendsto (fun R : ℝ => 3*C*decay c R) atTop (𝓝 0) := by
    simpa only [mul_zero] using (decay_tendsto_zero hc).const_mul (3*C)
  filter_upwards [eventually_ge_atTop R₀,
    hdec.eventually (eventually_le_nhds (show 0 < eta/2 by positivity))] with R hR hd
  have hR2 := hR₀.trans hR
  refine ⟨hR2,?_⟩
  intro xi hxi hxi1
  have hxi0 : 0 ≤ xi := heta.le.trans hxi
  have he := hbound R hR xi hxi0 hxi1
  have hm := mul_le_mul_of_nonneg_right hd (show 0 ≤ R by linarith)
  have hwidth := mul_le_mul_of_nonneg_right hxi (show 0 ≤ R by linarith)
  exact he.trans (by nlinarith only [hm,hwidth])

end ErdosInversePrimeBin



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

end NumberTheoryLean.ReferenceMertens

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeBinRationalList
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open scoped BigOperators
namespace ErdosInversePrimeBin
open _root_.Filter
open scoped Topology

theorem primeBin_log_sum_lower {R xi : ℝ} (hR : 0 < R) (hxi : 0 ≤ xi) :
    (primeBin R xi).card*Real.log R ≤ ∑ p ∈ primeBin R xi,Real.log p := by
  calc
    _ = ∑ _p ∈ primeBin R xi,Real.log R := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      exact Real.log_le_log hR ((mem_primeBin hR.le hxi p).mp hp).2.1.le

theorem uniform_prime_bin_count {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ R : ℝ in atTop,2 ≤ R ∧ ∀ xi : ℝ,eta ≤ xi → xi ≤ 1 →
      xi*R/(4*Real.log R) ≤ (primeBin R xi).card ∧
      (primeBin R xi).card ≤ 2*xi*R/Real.log R := by
  filter_upwards [uniform_bin_theta_error heta] with R hR
  refine ⟨hR.1,?_⟩
  intro xi hxi hxi1
  have hxi0 := heta.le.trans hxi
  have hR0 : 0 < R := by linarith [hR.1]
  have hlog : 0 < Real.log R := Real.log_pos (by linarith [hR.1])
  have he := hR.2 xi hxi hxi1
  rw [← primeBin_log_sum hR0.le hxi0] at he
  have hlow := (abs_le.mp he).1
  have hhigh := (abs_le.mp he).2
  have hcountupper := primeBin_log_sum_upper hR.1 hxi0 hxi1
  have hcountlower := primeBin_log_sum_lower hR0 hxi0
  constructor
  · apply (div_le_iff₀ (show 0 < 4*Real.log R by positivity)).mpr
    nlinarith only [hlow,hcountupper]
  · apply (le_div_iff₀ hlog).mpr
    have hprod := mul_nonneg hxi0 hR0.le
    nlinarith only [hhigh,hcountlower,hprod]

theorem log_le_two_sqrt {R : ℝ} (hR : 0 < R) : Real.log R ≤ 2*Real.sqrt R := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hR)
  have he : Real.log R = 2*Real.log (Real.sqrt R) := by
    rw [← Real.sq_sqrt hR.le,Real.log_pow]
    norm_num
  rw [he]
  linarith

theorem bin_scale_sqrt_lower {R xi eta : ℝ} (hR : 2 ≤ R) (heta : 0 < eta) (hxi : eta ≤ xi) :
    eta*Real.sqrt R/8 ≤ xi*R/(4*Real.log R) := by
  have hR0 : 0 < R := by linarith
  have hlog : 0 < Real.log R := Real.log_pos (by linarith)
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 8) (show 0 < 4*Real.log R by positivity)).mpr
  have hlogbound := mul_le_mul_of_nonneg_left (log_le_two_sqrt hR0)
    (show 0 ≤ eta*Real.sqrt R by positivity)
  have hRxi := mul_le_mul_of_nonneg_right hxi hR0.le
  have hs := Real.sq_sqrt hR0.le
  have he : eta*Real.sqrt R*(2*Real.sqrt R) = 2*eta*R := by
    calc
      _ = 2*eta*(Real.sqrt R)^2 := by ring
      _ = _ := by rw [hs]
  rw [he] at hlogbound
  nlinarith only [hlogbound,hRxi]

end ErdosInversePrimeBin

end

section

namespace ErdosInversePrimeBin
open _root_.Filter
open scoped Topology

theorem uniform_prime_bin_many {eta : ℝ} (heta : 0 < eta) (N : ℕ) :
    ∀ᶠ R : ℝ in atTop,2 ≤ R ∧ ∀ xi : ℝ,eta ≤ xi → xi ≤ 1 → N ≤ (primeBin R xi).card := by
  filter_upwards [uniform_prime_bin_count heta,
    eventually_ge_atTop ((8*(N : ℝ)/eta)^2)] with R hR hsize
  have hR0 : 0 < R := by linarith [hR.1]
  have hs : 8*(N : ℝ)/eta ≤ Real.sqrt R :=
    (Real.le_sqrt (by positivity) hR0.le).mpr hsize
  have hn : (N : ℝ) ≤ eta*Real.sqrt R/8 := by
    have h := (div_le_iff₀ heta).mp hs
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
    nlinarith only [h]
  refine ⟨hR.1,?_⟩
  intro xi hxi hxi1
  have h := hn.trans ((bin_scale_sqrt_lower hR.1 heta hxi).trans (hR.2 xi hxi hxi1).1)
  exact_mod_cast h

end ErdosInversePrimeBin

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_EulerProductRatio
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.SmallSieveFinite

open scoped BigOperators

theorem all_integer_euler_product (z : ℕ) (hz : 1 ≤ z) :
    (∏ n ∈ Finset.Icc 2 z, (1 - (n : ℝ)⁻¹)) = (z : ℝ)⁻¹ := by
  induction z, hz using Nat.le_induction with
  | base => simp
  | succ z hz ih =>
      rw [Finset.prod_Icc_succ_top (by omega), ih]
      have hz0 : (z : ℝ) ≠ 0 := by exact_mod_cast (show z ≠ 0 by omega)
      have hzs : ((z + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

theorem smallEuler_ge_inv (z : ℕ) (hz : 2 ≤ z) : (z : ℝ)⁻¹ ≤ smallEuler z := by
  have hsubset : LargePrimeDeletion.cutoffPrimes z ⊆ Finset.Icc 2 z := by
    intro p hp
    obtain ⟨hprime, hpz⟩ := LargePrimeDeletion.mem_cutoffPrimes.mp hp
    exact Finset.mem_Icc.mpr ⟨hprime.two_le, hpz⟩
  rw [← all_integer_euler_product z (by omega)]
  apply Finset.prod_le_prod_of_subset_of_le_one hsubset
  · intro n hn
    apply sub_nonneg.mpr
    exact inv_le_one_of_one_le₀ (by exact_mod_cast (show 1 ≤ n by have := (Finset.mem_Icc.mp hn).1; omega))
  · intro n _ _
    have h := inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) n)
    linarith

theorem smallEuler_floor_ge_inv (u : ℝ) (hu : 2 ≤ u) : u⁻¹ ≤ smallEuler ⌊u⌋₊ := by
  have hz : 2 ≤ ⌊u⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hu)
  have hzpos : (0 : ℝ) < (⌊u⌋₊ : ℝ) := by exact_mod_cast (show 0 < ⌊u⌋₊ by omega)
  exact ((inv_le_inv₀ (by linarith) hzpos).mpr (Nat.floor_le (by linarith))).trans (smallEuler_ge_inv _ hz)

end NumberTheoryLean.SmallSieveFinite

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_CellLengthLower
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseTail

theorem common_length_from_log (Y p q u : ℕ) (hp : 0 < p) (hq : 0 < q) (hu : 0 < u)
    (Qplus xi w aStar : ℝ) (hqQ : (q : ℝ) ≤ Qplus) (hQq : Qplus ≤ (1+xi)*(q : ℝ))
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1) (hw : 1 < w) (ha : 0 < aStar)
    (hlen : 3*aStar/4 ≤ Real.log ((Y : ℝ)/((p : ℝ)*q*u))/Real.log w) :
    w^(3*aStar/4) ≤ 2*(commonParentLength Y p Qplus : ℝ)/(u : ℝ)+2 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hQ : 0 < Qplus := hqR.trans_le hqQ
  have hw0 : 0 < w := by linarith
  have hlogw : 0 < Real.log w := Real.log_pos hw
  have hlog := (le_div_iff₀ hlogw).mp hlen
  have hlogpos : 0 < Real.log ((Y : ℝ)/((p : ℝ)*q*u)) := by nlinarith
  have hR1 : 1 < (Y : ℝ)/((p : ℝ)*q*u) := (Real.log_pos_iff (by positivity)).mp hlogpos
  have hpow : w^(3*aStar/4) ≤ (Y : ℝ)/((p : ℝ)*q*u) := by
    rw [Real.rpow_def_of_pos hw0]
    calc
      _ ≤ Real.exp (Real.log ((Y : ℝ)/((p : ℝ)*q*u))) := Real.exp_le_exp.mpr (by nlinarith [hlog])
      _ = _ := Real.exp_log (by linarith)
  have hA : 0 ≤ (Y : ℝ)/((p : ℝ)*Qplus) := by positivity
  have hJlt : (Y : ℝ)/((p : ℝ)*Qplus) < (commonParentLength Y p Qplus : ℝ)+1 := Nat.lt_floor_add_one _
  have hratio : Qplus/(q : ℝ) ≤ 1+xi := (div_le_iff₀ hqR).mpr hQq
  have hRupper : (Y : ℝ)/((p : ℝ)*q*u) ≤ 2*((commonParentLength Y p Qplus : ℝ)+1)/(u : ℝ) := by
    calc
      _ = ((Y : ℝ)/((p : ℝ)*Qplus))*(Qplus/(q : ℝ))/(u : ℝ) := by field_simp
      _ ≤ ((Y : ℝ)/((p : ℝ)*Qplus))*(1+xi)/(u : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hA) huR.le
      _ ≤ ((commonParentLength Y p Qplus : ℝ)+1)*(1+xi)/(u : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hJlt.le (by linarith)) huR.le
      _ ≤ 2*((commonParentLength Y p Qplus : ℝ)+1)/(u : ℝ) := by
        apply div_le_div_of_nonneg_right _ huR.le
        nlinarith [show (0 : ℝ) ≤ commonParentLength Y p Qplus from Nat.cast_nonneg _]
  have htwo : (2 : ℝ)/(u : ℝ) ≤ 2 := (div_le_iff₀ huR).mpr (by linarith)
  calc
    _ ≤ (Y : ℝ)/((p : ℝ)*q*u) := hpow
    _ ≤ 2*((commonParentLength Y p Qplus : ℝ)+1)/(u : ℝ) := hRupper
    _ = 2*(commonParentLength Y p Qplus : ℝ)/(u : ℝ)+2/(u : ℝ) := by ring
    _ ≤ _ := add_le_add le_rfl htwo

end ErdosInverseTail

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ClosedEulerIndividualUpper
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseEuler
open NumberTheoryLean ErdosPrimeInputs.MertensStrong

theorem cutoffPrimes_eq_filtered_Ioc (z : ℕ) :
    LargePrimeDeletion.cutoffPrimes z = (Finset.Ioc 0 z).filter Nat.Prime := by
  ext p
  rw [LargePrimeDeletion.mem_cutoffPrimes]
  simp only [Finset.mem_filter,Finset.mem_Ioc]
  exact ⟨fun h => ⟨⟨h.1.pos,h.2⟩,h.1⟩,fun h => ⟨h.2,h.1.2⟩⟩

theorem smallEuler_eq_primeProduct (w : ℝ) :
    SmallSieveFinite.smallEuler ⌊w⌋₊ = primeProduct w := by
  unfold SmallSieveFinite.smallEuler primeProduct
  rw [cutoffPrimes_eq_filtered_Ioc]
  simp only [one_div]

open _root_.Filter
open scoped Topology

theorem smallEuler_log_bounds : ∀ᶠ w : ℝ in atTop,
    2 ≤ w ∧ 0 < SmallSieveFinite.smallEuler ⌊w⌋₊ ∧
      Real.exp (-Real.eulerMascheroniConstant)/(2*Real.log w) ≤ SmallSieveFinite.smallEuler ⌊w⌋₊ ∧
      (SmallSieveFinite.smallEuler ⌊w⌋₊)⁻¹ ≤ 2*Real.exp Real.eulerMascheroniConstant*Real.log w := by
  have hnorm := (tendsto_order.mp ReferenceMertens.normalization_tendsto_one).2 2 (by norm_num)
  filter_upwards [hnorm,eventually_ge_atTop (2 : ℝ)] with w hn hw
  have hw0 : 0 < w := by linarith
  have hL : 0 < Real.log w := Real.log_pos (by linarith)
  have hV : 0 < SmallSieveFinite.smallEuler ⌊w⌋₊ :=
    (inv_pos.mpr hw0).trans_le (SmallSieveFinite.smallEuler_floor_ge_inv w hw)
  have hn' : Real.exp (-Real.eulerMascheroniConstant)/
      (Real.log w*SmallSieveFinite.smallEuler ⌊w⌋₊) ≤ 2 := by
    simpa only [ReferenceMertens.normalization,← smallEuler_eq_primeProduct] using hn.le
  have hprod := (div_le_iff₀ (mul_pos hL hV)).mp hn'
  have hlo : Real.exp (-Real.eulerMascheroniConstant)/(2*Real.log w) ≤ SmallSieveFinite.smallEuler ⌊w⌋₊ := by
    apply (div_le_iff₀ (by positivity : 0 < 2*Real.log w)).mpr
    nlinarith
  have hlowpos : 0 < Real.exp (-Real.eulerMascheroniConstant)/(2*Real.log w) := by positivity
  have hi := (inv_le_inv₀ hV hlowpos).mpr hlo
  refine ⟨hw,hV,hlo,?_⟩
  calc
    _ ≤ (Real.exp (-Real.eulerMascheroniConstant)/(2*Real.log w))⁻¹ := hi
    _ = 2*Real.exp Real.eulerMascheroniConstant*Real.log w := by
      rw [inv_div,Real.exp_neg,div_inv_eq_mul]
      ring

end ErdosInverseEuler

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SmallModelSourceScales
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseEuler
open NumberTheoryLean

theorem log_smallModulus_eq_theta (w : ℝ) : Real.log (smallModulus w : ℝ) = Chebyshev.theta w := by
  have hn : ∀ p ∈ LargePrimeDeletion.cutoffPrimes ⌊w⌋₊,(p : ℝ) ≠ 0 := by
    intro p hp
    exact_mod_cast (LargePrimeDeletion.mem_cutoffPrimes.mp hp).1.ne_zero
  unfold smallModulus IntervalBoundingSieve.cutoffProduct
  rw [Nat.cast_prod,Real.log_prod hn,cutoffPrimes_eq_filtered_Ioc]
  rfl

theorem log_smallModulus_le (w : ℝ) (hw : 0 ≤ w) :
    Real.log (smallModulus w : ℝ) ≤ Real.log 4*w := by
  rw [log_smallModulus_eq_theta]
  exact Chebyshev.theta_le_log4_mul_x hw

theorem smallModulus_le_exp (w : ℝ) (hw : 0 ≤ w) :
    (smallModulus w : ℝ) ≤ Real.exp (Real.log 4*w) := by
  have hp : (0 : ℝ) < smallModulus w := by exact_mod_cast smallModulus_pos w
  calc
    (smallModulus w : ℝ) = Real.exp (Real.log (smallModulus w : ℝ)) := (Real.exp_log hp).symm
    _ ≤ _ := Real.exp_le_exp.mpr (log_smallModulus_le w hw)

end ErdosInverseEuler

end

section

namespace ErdosInverseFrozen
open NumberTheoryLean ErdosInverseHits ErdosInverseEuler ErdosInverseCounts

theorem cutoffPrime_dvd_smallModulus (w : ℝ) (t : ℕ)
    (ht : t ∈ LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) : t ∣ smallModulus w := by
  unfold smallModulus IntervalBoundingSieve.cutoffProduct
  exact Finset.dvd_prod_of_mem id ht

end ErdosInverseFrozen

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseEuler
open ErdosInverseBoxHeight

theorem sourceW_tendsto_atTop : Tendsto sourceW atTop atTop := by
  have hs := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1/2)).bound zero_lt_one
  have hlow : (fun z : ℝ => (Real.log z)^((1 : ℝ)/2)) ≤ᶠ[atTop] sourceW := by
    filter_upwards [Real.tendsto_log_atTop.eventually hs,
      Real.tendsto_log_atTop.eventually_gt_atTop 1] with z hz hL
    have hL0 : 0 < Real.log z := by linarith
    have hLL : 0 < Real.log (Real.log z) := Real.log_pos hL
    have hh : (Real.log (Real.log z))^2 ≤ (Real.log z)^((1 : ℝ)/2) := by
      simpa only [Real.norm_eq_abs,Real.rpow_two,abs_of_nonneg (sq_nonneg (Real.log (Real.log z))),
        abs_of_nonneg (Real.rpow_nonneg hL0.le ((1 : ℝ)/2)),one_mul] using hz
    have hp : (Real.log z)^((1 : ℝ)/2)*(Real.log z)^((1 : ℝ)/2) = Real.log z := by
      rw [← Real.rpow_add hL0]
      norm_num
    apply (le_div_iff₀ (sq_pos_of_pos hLL)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hL0.le ((1 : ℝ)/2))]
  exact tendsto_atTop_mono' atTop hlow ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).comp Real.tendsto_log_atTop)

theorem sourceZ_le_rpow (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop, 1 < z ∧ sourceZ z ≤ z^eps := by
  have hh := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (max 1 (1/eps))
  filter_upwards [hh,eventually_gt_atTop (1 : ℝ)] with z hLL hz
  have hL0 : 0 < Real.log z := Real.log_pos hz
  have hLL1 : 1 ≤ Real.log (Real.log z) := (le_max_left _ _).trans hLL
  have hLL0 : 0 < Real.log (Real.log z) := by linarith
  have hpay : 1 ≤ Real.log (Real.log z)*eps := (div_le_iff₀ heps).mp ((le_max_right _ _).trans hLL)
  refine ⟨hz,?_⟩
  rw [sourceZ,Real.rpow_def_of_pos (by linarith : 0 < z)]
  apply Real.exp_le_exp.mpr
  apply (div_le_iff₀ hLL0).mpr
  nlinarith [mul_le_mul_of_nonneg_left hpay hL0.le]

theorem smallModulus_source_power (k : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop, (smallModulus (sourceW z) : ℝ)^k ≤ (sourceZ z)^eps := by
  have hh := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop
    (max 1 ((k : ℝ)*Real.log 4/eps))
  filter_upwards [hh,Real.tendsto_log_atTop.eventually_gt_atTop 1] with z hLL hL
  have hL0 : 0 < Real.log z := by linarith
  have hLL1 : 1 ≤ Real.log (Real.log z) := (le_max_left _ _).trans hLL
  have hLL0 : 0 < Real.log (Real.log z) := by linarith
  have hW0 : 0 ≤ sourceW z := div_nonneg hL0.le (sq_nonneg _)
  have hpay : (k : ℝ)*Real.log 4 ≤ Real.log (Real.log z)*eps :=
    (div_le_iff₀ heps).mp ((le_max_right _ _).trans hLL)
  have hscale : (k : ℝ)*(Real.log 4*sourceW z) ≤ (Real.log z/Real.log (Real.log z))*eps := by
    calc
      _ = ((k : ℝ)*Real.log 4*Real.log z)/(Real.log (Real.log z))^2 := by unfold sourceW;ring
      _ ≤ (Real.log (Real.log z)*eps*Real.log z)/(Real.log (Real.log z))^2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hpay hL0.le) (sq_nonneg _)
      _ = _ := by field_simp
  calc
    _ ≤ (Real.exp (Real.log 4*sourceW z))^k := pow_le_pow_left₀ (Nat.cast_nonneg _) (smallModulus_le_exp _ hW0) k
    _ = Real.exp ((k : ℝ)*(Real.log 4*sourceW z)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp ((Real.log z/Real.log (Real.log z))*eps) := Real.exp_le_exp.mpr hscale
    _ = (sourceZ z)^eps := Real.exp_mul _ _

end ErdosInverseEuler

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceExtensionScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseSampleCost
open ErdosInverseBoxHeight ErdosInverseEuler

theorem sourceW_log_bounds : ∀ᶠ z : ℝ in atTop,
    1 < z ∧ 0 < Real.log z ∧ (Real.log z)^((1 : ℝ)/2) ≤ sourceW z ∧ sourceW z ≤ Real.log z := by
  have hs := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1/2)).bound zero_lt_one
  filter_upwards [Real.tendsto_log_atTop.eventually hs,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1,
    eventually_gt_atTop (1 : ℝ)] with z hh hLL hz
  have hL : 0 < Real.log z := Real.log_pos hz
  have hLL1 : 1 ≤ Real.log (Real.log z) := hLL
  have hLLpos : 0 < Real.log (Real.log z) := by linarith
  have hbound : (Real.log (Real.log z))^2 ≤ (Real.log z)^((1 : ℝ)/2) := by
    simpa only [Real.norm_eq_abs,Real.rpow_two,abs_of_nonneg (sq_nonneg (Real.log (Real.log z))),
      abs_of_nonneg (Real.rpow_nonneg hL.le ((1 : ℝ)/2)),one_mul] using hh
  have heq : (Real.log z)^((1 : ℝ)/2)*(Real.log z)^((1 : ℝ)/2) = Real.log z := by
    rw [← Real.rpow_add hL]
    norm_num
  refine ⟨hz,hL,?_,?_⟩
  · apply (le_div_iff₀ (sq_pos_of_pos hLLpos)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hL.le ((1 : ℝ)/2))]
  · exact div_le_self hL.le (by nlinarith)

theorem sourceW_le_power (alpha : ℝ) (ha : 0 < alpha) :
    ∀ᶠ z : ℝ in atTop,sourceW z ≤ z^alpha := by
  have hs := (isLittleO_log_rpow_rpow_atTop (1 : ℝ) ha).bound zero_lt_one
  filter_upwards [sourceW_log_bounds,hs] with z hz hh
  have hlog : Real.log z ≤ z^alpha := by
    simpa only [Real.norm_eq_abs,Real.rpow_one,abs_of_pos hz.2.1,
      abs_of_nonneg (Real.rpow_nonneg (by linarith [hz.1] : 0 ≤ z) alpha),one_mul] using hh
  exact hz.2.2.2.trans hlog

theorem source_inverse_power_log_tendsto (t : ℝ) (ht : 12 < t) :
    Tendsto (fun z : ℝ => (Real.log z)^6*(sourceW z)^(-t)) atTop (𝓝 0) := by
  have heps : 0 < t/2-6 := by linarith
  have hT := (tendsto_rpow_neg_atTop heps).comp Real.tendsto_log_atTop
  have hnonneg : ∀ᶠ z : ℝ in atTop,0 ≤ (Real.log z)^6*(sourceW z)^(-t) := by
    filter_upwards [sourceW_log_bounds] with z hz
    have hWpos : 0 < sourceW z := (Real.rpow_pos_of_pos hz.2.1 _).trans_le hz.2.2.1
    exact mul_nonneg (pow_nonneg hz.2.1.le 6) (Real.rpow_nonneg hWpos.le _)
  have hbound : ∀ᶠ z : ℝ in atTop,
      (Real.log z)^6*(sourceW z)^(-t) ≤ (Real.log z)^(-(t/2-6)) := by
    filter_upwards [sourceW_log_bounds] with z hz
    have hpow := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hz.2.1 ((1 : ℝ)/2))
      hz.2.2.1 (show -t ≤ 0 by linarith)
    calc
      _ ≤ (Real.log z)^6*((Real.log z)^((1 : ℝ)/2))^(-t) :=
        mul_le_mul_of_nonneg_left hpow (pow_nonneg hz.2.1.le 6)
      _ = _ := by
        rw [← Real.rpow_mul hz.2.1.le,← Real.rpow_natCast (Real.log z) 6,← Real.rpow_add hz.2.1]
        congr 1
        norm_num
        ring
  exact squeeze_zero' hnonneg hbound hT

end ErdosInverseSampleCost

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseSampleCost
open ErdosInverseBoxHeight ErdosInverseEuler

theorem source_rounding_log_tendsto (K alpha : ℝ) (h : ℕ) (hK : 0 ≤ K) (ha : 0 < alpha) :
    Tendsto (fun z : ℝ => (Real.log z)^6*(smallModulus (sourceW z) : ℝ)*
      (2*(sourceW z)^K)^h/z^alpha) atTop (𝓝 0) := by
  have hcoef : 0 < (2 : ℝ)^h := by positivity
  have hs := (isLittleO_log_rpow_rpow_atTop (6+K*(h : ℝ)) (by positivity : 0 < alpha/4)).bound (inv_pos.mpr hcoef)
  have hbound : ∀ᶠ z : ℝ in atTop,
      (Real.log z)^6*(smallModulus (sourceW z) : ℝ)*(2*(sourceW z)^K)^h/z^alpha ≤ z^(-(alpha/2)) := by
    filter_upwards [sourceW_log_bounds,smallModulus_source_power 1 1 zero_lt_one,
      sourceZ_le_rpow (alpha/4) (by positivity),hs] with z hz hM hZ hh
    have hzpos : 0 < z := by linarith [hz.1]
    have hWpos : 0 < sourceW z := (Real.rpow_pos_of_pos hz.2.1 _).trans_le hz.2.2.1
    have hMbound : (smallModulus (sourceW z) : ℝ) ≤ z^(alpha/4) := by
      have hm : (smallModulus (sourceW z) : ℝ) ≤ sourceZ z := by simpa only [pow_one,Real.rpow_one] using hM
      exact hm.trans hZ.2
    have hlogbound : (2 : ℝ)^h*(Real.log z)^(6+K*(h : ℝ)) ≤ z^(alpha/4) := by
      have hsimp : (Real.log z)^(6+K*(h : ℝ)) ≤ ((2 : ℝ)^h)⁻¹*z^(alpha/4) := by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hz.2.1.le _),
          abs_of_nonneg (Real.rpow_nonneg hzpos.le _)] using hh
      have hm := mul_le_mul_of_nonneg_left hsimp hcoef.le
      have heq : (2 : ℝ)^h*(((2 : ℝ)^h)⁻¹*z^(alpha/4)) = z^(alpha/4) := by field_simp
      rwa [heq] at hm
    have hsmall : (Real.log z)^6*(2*(sourceW z)^K)^h ≤ z^(alpha/4) := by
      calc
        _ ≤ (Real.log z)^6*(2*(Real.log z)^K)^h :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hWpos.le hz.2.2.2 hK) (by norm_num)) h)
            (pow_nonneg hz.2.1.le 6)
        _ = (2 : ℝ)^h*(Real.log z)^(6+K*(h : ℝ)) := by
          rw [mul_pow,← Real.rpow_natCast ((Real.log z)^K) h,← Real.rpow_mul hz.2.1.le,
            ← Real.rpow_natCast (Real.log z) 6]
          norm_num only [Nat.cast_ofNat]
          calc
            _ = (2 : ℝ)^h*((Real.log z)^(6 : ℝ)*(Real.log z)^(K*(h : ℝ))) := by ring
            _ = _ := by rw [← Real.rpow_add hz.2.1]
        _ ≤ _ := hlogbound
    calc
      _ = (smallModulus (sourceW z) : ℝ)*((Real.log z)^6*(2*(sourceW z)^K)^h)/z^alpha := by ring
      _ ≤ z^(alpha/4)*z^(alpha/4)/z^alpha := by
        apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hzpos.le _)
        exact mul_le_mul hMbound hsmall (by positivity) (Real.rpow_nonneg hzpos.le _)
      _ = z^(-(alpha/2)) := by
        rw [← Real.rpow_add hzpos,← Real.rpow_sub hzpos]
        congr 1
        ring
  have hnonneg : ∀ᶠ z : ℝ in atTop,0 ≤
      (Real.log z)^6*(smallModulus (sourceW z) : ℝ)*(2*(sourceW z)^K)^h/z^alpha := by
    filter_upwards [sourceW_log_bounds] with z hz
    have hzpos : 0 < z := by linarith [hz.1]
    have hWpos : 0 < sourceW z := (Real.rpow_pos_of_pos hz.2.1 _).trans_le hz.2.2.1
    positivity
  exact squeeze_zero' hnonneg hbound (tendsto_rpow_neg_atTop (by positivity : 0 < alpha/2))

end ErdosInverseSampleCost

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseSampleCost
open ErdosInverseBoxHeight ErdosInverseEuler

theorem source_cost_budget (aStar K alpha eps : ℝ) (h : ℕ) (hK : 0 ≤ K)
    (ha : 0 < alpha) (heps : 0 < eps) (hh : 12 < aStar*(h : ℝ)/2) :
    ∀ᶠ z : ℝ in atTop,1 < z ∧ ∀ R U : ℝ,z^alpha ≤ R → 0 ≤ U → U ≤ (sourceW z)^K →
      (Real.log z)^6*(4*R*((sourceW z)^(-aStar/2))^h+
        (smallModulus (sourceW z) : ℝ)*(2*U)^h)/R ≤ eps := by
  have hmain := source_inverse_power_log_tendsto (aStar*(h : ℝ)/2) hh
  have hround := source_rounding_log_tendsto K alpha h hK ha
  have hsum : Tendsto (fun z : ℝ => 4*((Real.log z)^6*(sourceW z)^(-(aStar*(h : ℝ)/2)))+
      (Real.log z)^6*(smallModulus (sourceW z) : ℝ)*(2*(sourceW z)^K)^h/z^alpha) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_add] using (hmain.const_mul 4).add hround
  have hs := (tendsto_order.mp hsum).2 eps heps
  filter_upwards [hs,sourceW_log_bounds] with z hsumsmall hz
  refine ⟨hz.1,?_⟩
  intro R U hR hU hUtop
  have hzpos : 0 < z := by linarith [hz.1]
  have hWpos : 0 < sourceW z := (Real.rpow_pos_of_pos hz.2.1 _).trans_le hz.2.2.1
  have hRpos : 0 < R := (Real.rpow_pos_of_pos hzpos alpha).trans_le hR
  have htau : ((sourceW z)^(-aStar/2))^h = (sourceW z)^(-(aStar*(h : ℝ)/2)) := by
    rw [← Real.rpow_natCast ((sourceW z)^(-aStar/2)) h,← Real.rpow_mul hWpos.le]
    congr 1
    ring
  have hURound : (2*U)^h ≤ (2*(sourceW z)^K)^h :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hUtop (by norm_num)) h
  have hroundle : (Real.log z)^6*(smallModulus (sourceW z) : ℝ)*(2*U)^h/R ≤
      (Real.log z)^6*(smallModulus (sourceW z) : ℝ)*(2*(sourceW z)^K)^h/z^alpha := by
    calc
      _ ≤ (Real.log z)^6*(smallModulus (sourceW z) : ℝ)*(2*(sourceW z)^K)^h/R :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hURound (by positivity)) hRpos.le
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hzpos _) hR
  calc
    _ = 4*((Real.log z)^6*(sourceW z)^(-(aStar*(h : ℝ)/2)))+
        (Real.log z)^6*(smallModulus (sourceW z) : ℝ)*(2*U)^h/R := by
      rw [htau]
      field_simp
    _ ≤ 4*((Real.log z)^6*(sourceW z)^(-(aStar*(h : ℝ)/2)))+
        (Real.log z)^6*(smallModulus (sourceW z) : ℝ)*(2*(sourceW z)^K)^h/z^alpha :=
      add_le_add le_rfl hroundle
    _ ≤ eps := hsumsmall.le

end ErdosInverseSampleCost

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_EdgeBinBounds
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseSaving
open ErdosInversePrimeBin

theorem edgeFrequencyCap_le (U : ℝ) (hU : 1 ≤ U) : (edgeFrequencyCap U : ℝ) ≤ 3*U := by
  have hh := Nat.ceil_lt_add_one (show 0 ≤ 2*U by linarith)
  change (⌈2*U⌉₊ : ℝ) ≤ 3*U
  linarith

theorem edge_prime_le_cap (U theta : ℝ) (hU : 0 ≤ U) (htheta : 0 ≤ theta)
    (htheta1 : theta ≤ 1) (u : ℕ) (hu : u ∈ primeBin U theta) : u ≤ edgeFrequencyCap U := by
  have htop := ((mem_primeBin hU htheta u).mp hu).2.2
  have huR : (u : ℝ) ≤ 2*U := htop.trans (by nlinarith)
  exact_mod_cast huR.trans (Nat.le_ceil (2*U))

theorem uniform_edge_bin_count (xi : ℝ) (hxi : 0 < xi) (hxi1 : xi ≤ 1) :
    ∀ᶠ w : ℝ in atTop,2 ≤ w ∧ ∀ U theta : ℝ,w ≤ U → xi/4 ≤ theta → theta ≤ xi →
      xi*U/(16*Real.log U) ≤ ((primeBin U theta).card : ℝ) ∧ 0 < (primeBin U theta).card := by
  obtain ⟨U0,hU0⟩ := eventually_atTop.mp (uniform_prime_bin_count (by positivity : 0 < xi/4))
  filter_upwards [eventually_ge_atTop (max 2 U0)] with w hw
  have hw2 : 2 ≤ w := (le_max_left _ _).trans hw
  refine ⟨hw2,?_⟩
  intro U theta hwU htlow hthigh
  have hU2 : 2 ≤ U := hw2.trans hwU
  have hUpos : 0 < U := by linarith
  have hlog : 0 < Real.log U := Real.log_pos (by linarith)
  have hc := ((hU0 U (((le_max_right _ _).trans hw).trans hwU)).2 theta htlow (hthigh.trans hxi1)).1
  have hlow : xi*U/(16*Real.log U) ≤ ((primeBin U theta).card : ℝ) := by
    calc
      _ = (xi/4)*U/(4*Real.log U) := by ring
      _ ≤ theta*U/(4*Real.log U) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right htlow hUpos.le) (by positivity)
      _ ≤ _ := hc
  refine ⟨hlow,?_⟩
  have hh : (0 : ℝ) < (primeBin U theta).card := (by positivity : 0 < xi*U/(16*Real.log U)).trans_le hlow
  exact_mod_cast hh

end ErdosInverseSaving

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_SourceIntervalReplacement
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseFrozen
open NumberTheoryLean ErdosInverseEuler

theorem center_step_coprime (w : ℝ) (p q q0 t : ℕ) (ht : t.Prime) (htw : (t : ℝ) ≤ w)
    (hqq : Int.ModEq (smallModulus w : ℤ) (q : ℤ) (q0 : ℤ))
    (hactual : (p*q).Coprime t) : (p*q0).Coprime t := by
  have htmem : t ∈ LargePrimeDeletion.cutoffPrimes ⌊w⌋₊ :=
    LargePrimeDeletion.mem_cutoffPrimes.mpr ⟨ht,(Nat.le_floor_iff ((Nat.cast_nonneg t).trans htw)).mpr htw⟩
  have hdiv : (t : ℤ) ∣ (smallModulus w : ℤ) := by
    exact_mod_cast cutoffPrime_dvd_smallModulus w t htmem
  have hqt : Nat.ModEq t q q0 := Int.natCast_modEq_iff.mp (hqq.of_dvd hdiv)
  have hprod : Nat.ModEq t (p*q) (p*q0) := hqt.mul_left p
  have hn := ht.coprime_iff_not_dvd.mp hactual.symm
  apply Nat.Coprime.symm
  apply ht.coprime_iff_not_dvd.mpr
  intro hd
  apply hn
  change (p*q)%t = (p*q0)%t at hprod
  exact Nat.dvd_of_mod_eq_zero (hprod.trans (Nat.mod_eq_zero_of_dvd hd))

end ErdosInverseFrozen

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_FiniteSampleSpace
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseSampling
attribute [local instance] Classical.decEq

theorem sample_card {α : Type*} (U : Finset α) (h : ℕ) :
    Fintype.card (Sample U h) = U.card.descFactorial h := by
  classical
  simp only [Sample,Fintype.card_embedding_eq,Fintype.card_fin,Fintype.card_coe]

theorem goodSamples_card {α : Type*} (U W : Finset α) (hWU : W ⊆ U) (h : ℕ) :
    (goodSamples U W h).card = W.card.descFactorial h := by
  classical
  have hh := Fintype.card_congr (goodSampleEquiv U W hWU h)
  simpa only [Fintype.card_coe,sample_card] using hh

theorem sampleFrequency_eq {α : Type*} (U W : Finset α) (hWU : W ⊆ U) (h : ℕ) :
    sampleFrequency U W h = (W.card.descFactorial h : ℝ)/(U.card.descFactorial h : ℝ) := by
  rw [sampleFrequency,goodSamples_card U W hWU,sample_card]

end ErdosInverseSampling

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_FallingFactorialProbability
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseSampling
attribute [local instance] Classical.decEq

theorem sample_length_le (n h : ℕ) (beta : ℝ) (hb : 0 < beta) (hb1 : beta ≤ 1)
    (hsize : 4*(h : ℝ)/beta ≤ (n : ℝ)) : h ≤ n := by
  have hh := (div_le_iff₀ hb).mp hsize
  have hbmul := mul_le_mul_of_nonneg_right hb1 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hr : (h : ℝ) ≤ n := by nlinarith [show (0 : ℝ) ≤ h from Nat.cast_nonneg h]
  exact_mod_cast hr

theorem falling_ratio_lower (n m h : ℕ) (beta : ℝ) (hb : 0 < beta) (hb1 : beta ≤ 1)
    (hgood : (beta/2)*(n : ℝ) ≤ (m : ℝ))
    (hsize : 4*(h : ℝ)/beta ≤ (n : ℝ)) :
    (beta/4)^h ≤ (m.descFactorial h : ℝ)/(n.descFactorial h : ℝ) := by
  have hhn := sample_length_le n h beta hb hb1 hsize
  have hpay := (div_le_iff₀ hb).mp hsize
  have hhm : h ≤ m := by
    have hh : (h : ℝ) ≤ m := by nlinarith [show (0 : ℝ) ≤ h from Nat.cast_nonneg h]
    exact_mod_cast hh
  have hnum : ((beta/4)*(n : ℝ))^h ≤ (m.descFactorial h : ℝ) := by
    rw [Nat.descFactorial_eq_prod_range,Nat.cast_prod]
    calc
      _ = ∏ _i ∈ Finset.range h,(beta/4)*(n : ℝ) := by simp
      _ ≤ ∏ i ∈ Finset.range h,((m-i : ℕ) : ℝ) := by
        apply Finset.prod_le_prod (fun _ _ => by positivity)
        intro i hi
        have hih : i < h := Finset.mem_range.mp hi
        have him : i ≤ m := by omega
        rw [Nat.cast_sub him]
        have hiR : (i : ℝ) ≤ h := by exact_mod_cast hih.le
        nlinarith
  have hden : (n.descFactorial h : ℝ) ≤ (n : ℝ)^h := by
    exact_mod_cast Nat.descFactorial_le_pow n h
  have hdenpos : (0 : ℝ) < n.descFactorial h := by exact_mod_cast Nat.descFactorial_pos.mpr hhn
  apply (le_div_iff₀ hdenpos).mpr
  calc
    _ ≤ (beta/4)^h*(n : ℝ)^h := mul_le_mul_of_nonneg_left hden (by positivity)
    _ = ((beta/4)*(n : ℝ))^h := by rw [mul_pow]
    _ ≤ _ := hnum

theorem sampleFrequency_lower {α : Type*} (U W : Finset α) (hWU : W ⊆ U) (h : ℕ)
    (beta : ℝ) (hb : 0 < beta) (hb1 : beta ≤ 1)
    (hgood : (beta/2)*(U.card : ℝ) ≤ (W.card : ℝ))
    (hsize : 4*(h : ℝ)/beta ≤ (U.card : ℝ)) :
    (beta/4)^h ≤ sampleFrequency U W h := by
  rw [sampleFrequency_eq U W hWU h]
  exact falling_ratio_lower U.card W.card h beta hb hb1 hgood hsize

theorem sample_nonempty_of_length {α : Type*} (U : Finset α) (h : ℕ) (hh : h ≤ U.card) :
    Nonempty (Sample U h) := by
  apply Fintype.card_pos_iff.mp
  rw [sample_card]
  exact Nat.descFactorial_pos.mpr hh

end ErdosInverseSampling

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceSamplePopulation
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseSampling
attribute [local instance] Classical.decEq

theorem sample_product_sum_le {α : Type*} (U : Finset α) (h : ℕ) (t : U → ℝ)
    (ht : ∀ u,0 ≤ t u) :
    (∑ e : Sample U h,∏ i : Fin h,t (e i)) ≤ (∑ u : U,t u)^h := by
  classical
  let E : Finset (Fin h → U) := Finset.univ.image (fun e : Sample U h => (e : Fin h → U))
  have he : (∑ e : Sample U h,∏ i : Fin h,t (e i)) = ∑ f ∈ E,∏ i : Fin h,t (f i) := by
    dsimp only [E]
    rw [Finset.sum_image (fun _ _ _ _ he => Function.Embedding.coe_injective he)]
  have hall : (∑ f : Fin h → U,∏ i : Fin h,t (f i)) = (∑ u : U,t u)^h := by
    have hh := (Fintype.prod_sum (fun _i : Fin h => fun u : U => t u)).symm
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hh
  calc
    _ = ∑ f ∈ E,∏ i : Fin h,t (f i) := he
    _ ≤ ∑ f : Fin h → U,∏ i : Fin h,t (f i) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
        (fun f _ _ => Finset.prod_nonneg (fun i _ => ht (f i)))
    _ = _ := hall

theorem sample_product_average_le {α : Type*} (U : Finset α) (h : ℕ) (t : U → ℝ)
    (ht : ∀ u,0 ≤ t u) (hU : 0 < U.card) (hh : h ≤ U.card) :
    sampleAverage U h (fun e => ∏ i : Fin h,t (e i)) ≤
      ((U.card : ℝ)^h/(U.card.descFactorial h : ℝ))*((∑ u : U,t u)/(U.card : ℝ))^h := by
  have hn : (0 : ℝ) < U.card := by exact_mod_cast hU
  have hd : (0 : ℝ) < U.card.descFactorial h := by exact_mod_cast Nat.descFactorial_pos.mpr hh
  unfold sampleAverage
  rw [sample_card]
  calc
    _ ≤ (∑ u : U,t u)^h/(U.card.descFactorial h : ℝ) :=
      div_le_div_of_nonneg_right (sample_product_sum_le U h t ht) hd.le
    _ = _ := by rw [div_pow];field_simp

end ErdosInverseSampling

end

section

open _root_.Filter _root_.Erdos970.Filter
open scoped Topology
namespace ErdosInverseSampling

theorem normalized_falling_eq_product (n h : ℕ) (hh : h ≤ n) (hn : 0 < n) :
    (n.descFactorial h : ℝ)/(n : ℝ)^h = ∏ i ∈ Finset.range h,(1-(i : ℝ)/(n : ℝ)) := by
  rw [Nat.descFactorial_eq_prod_range,Nat.cast_prod]
  have hden : (n : ℝ)^h = ∏ _i ∈ Finset.range h,(n : ℝ) := by simp
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [hden,← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hin : i ≤ n := (Finset.mem_range.mp hi).le.trans hh
  rw [Nat.cast_sub hin]
  field_simp

theorem normalized_falling_tendsto (h : ℕ) :
    Tendsto (fun n : ℕ => (n.descFactorial h : ℝ)/(n : ℝ)^h) atTop (𝓝 1) := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hprod : Tendsto (fun n : ℕ => ∏ i ∈ Finset.range h,(1-(i : ℝ)/(n : ℝ))) atTop (𝓝 1) := by
    have hh := tendsto_finsetProd (Finset.range h) (fun i _ =>
      (tendsto_const_nhds : Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
        (hcast.const_div_atTop (i : ℝ)))
    simpa only [sub_zero,Finset.prod_const_one] using hh
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop h,eventually_ge_atTop (1 : ℕ)] with n hhn hn
  exact (normalized_falling_eq_product n h hhn (by omega)).symm

theorem sampling_prefactor_tendsto (h : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ)^h/(n.descFactorial h : ℝ)) atTop (𝓝 1) := by
  have hh := (normalized_falling_tendsto h).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simpa only [inv_div,inv_one] using hh

theorem sampling_prefactor_eventually_le_two (h : ℕ) :
    ∀ᶠ n : ℕ in atTop,(n : ℝ)^h/(n.descFactorial h : ℝ) ≤ 2 := by
  have hh := (tendsto_order.mp (sampling_prefactor_tendsto h)).2 2 (by norm_num)
  exact hh.mono (fun _ hn => hn.le)

end ErdosInverseSampling

end

section

namespace ErdosInverseSampleCost
open ErdosInverseSampling
attribute [local instance] Classical.decEq

theorem sampleAverage_mono {α : Type*} (U : Finset α) (h : ℕ)
    (f g : Sample U h → ℝ) (hfg : ∀ s,f s ≤ g s) : sampleAverage U h f ≤ sampleAverage U h g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum (fun s _ => hfg s)) (Nat.cast_nonneg _)

theorem sampleAverage_add {α : Type*} (U : Finset α) (h : ℕ) (f g : Sample U h → ℝ) :
    sampleAverage U h (fun s => f s+g s) = sampleAverage U h f+sampleAverage U h g := by
  unfold sampleAverage
  rw [Finset.sum_add_distrib,add_div]

theorem sampleAverage_mul {α : Type*} (U : Finset α) (h : ℕ) (c : ℝ) (f : Sample U h → ℝ) :
    sampleAverage U h (fun s => c*f s) = c*sampleAverage U h f := by
  unfold sampleAverage
  rw [← Finset.mul_sum,mul_div_assoc]

theorem sampleAverage_div {α : Type*} (U : Finset α) (h : ℕ) (c : ℝ) (f : Sample U h → ℝ) :
    sampleAverage U h (fun s => f s/c) = sampleAverage U h f/c := by
  unfold sampleAverage
  rw [← Finset.sum_div,div_right_comm]

theorem sampleAverage_sum {α ι : Type*} (U : Finset α) (h : ℕ) (I : Finset ι)
    (f : ι → Sample U h → ℝ) :
    sampleAverage U h (fun s => ∑ i ∈ I,f i s) = ∑ i ∈ I,sampleAverage U h (f i) := by
  unfold sampleAverage
  rw [Finset.sum_comm,Finset.sum_div]

theorem sampleAverage_const {α : Type*} (U : Finset α) (h : ℕ) (hh : h ≤ U.card) (c : ℝ) :
    sampleAverage U h (fun _ => c) = c := by
  have hcard : (0 : ℝ) < Fintype.card (Sample U h) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (sample_nonempty_of_length U h hh)
  unfold sampleAverage
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  field_simp

theorem sampleAverage_product_bound {α : Type*} (U : Finset α) (h : ℕ) (hh : h ≤ U.card)
    (t : U → ℝ) (T : ℝ) (ht : ∀ u,0 ≤ t u) (hT : ∀ u,t u ≤ T) :
    sampleAverage U h (fun s => ∏ i : Fin h,t (s i)) ≤ T^h := by
  have hprod : ∀ s : Sample U h,(∏ i : Fin h,t (s i)) ≤ T^h := by
    intro s
    have hh := Finset.prod_le_prod (s := Finset.univ) (fun i _ => ht (s i)) (fun i _ => hT (s i))
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hh
  exact (sampleAverage_mono U h _ _ hprod).trans_eq (sampleAverage_const U h hh (T^h))

end ErdosInverseSampleCost

end

section

open _root_.Filter _root_.Erdos970.Filter
open scoped Topology
namespace ErdosInverseSampleCost
open ErdosInverseSampling ErdosInversePrimeBin ErdosInverseEuler ErdosInverseBoxHeight

theorem source_sample_population (xi beta : ℝ) (h : ℕ) (hxi : 0 < xi) (hxi1 : xi ≤ 1) :
    ∀ᶠ z : ℝ in atTop,∀ U theta : ℝ,sourceW z ≤ U → xi/4 ≤ theta → theta ≤ xi →
      0 < (primeBin U theta).card ∧ h ≤ (primeBin U theta).card ∧
      4*(h : ℝ)/beta ≤ ((primeBin U theta).card : ℝ) ∧
      ((primeBin U theta).card : ℝ)^h/((primeBin U theta).card.descFactorial h : ℝ) ≤ 2 := by
  obtain ⟨n0,hn0⟩ := eventually_atTop.mp (sampling_prefactor_eventually_le_two h)
  let M : ℕ := n0+h+⌈4*(h : ℝ)/beta⌉₊+1
  obtain ⟨U0,hU0⟩ := eventually_atTop.mp (uniform_prime_bin_many (by positivity : 0 < xi/4) M)
  filter_upwards [sourceW_tendsto_atTop.eventually_ge_atTop U0] with z hz
  intro U theta hWU htlow hthigh
  have hmany := (hU0 U (hz.trans hWU)).2 theta htlow (hthigh.trans hxi1)
  have hM0 : n0 ≤ M := by dsimp [M];omega
  have hMh : h ≤ M := by dsimp [M];omega
  have hM1 : 1 ≤ M := by dsimp [M];omega
  have hMc : ⌈4*(h : ℝ)/beta⌉₊ ≤ M := by dsimp [M];omega
  refine ⟨by omega,hMh.trans hmany,?_,hn0 _ (hM0.trans hmany)⟩
  exact (Nat.le_ceil (4*(h : ℝ)/beta)).trans (by exact_mod_cast hMc.trans hmany)

end ErdosInverseSampleCost

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_CRTPrimeCost
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseSampleCost
open ErdosInverseSampling
attribute [local instance] Classical.decEq

theorem primeCost_nonneg (U : Finset ℕ) (h M0 : ℕ) [NeZero M0]
    (E : ℕ → ZMod M0 → ∀ u : U,Finset (ZMod u.val)) (p : ℕ) (s : Sample U h) :
    0 ≤ primeCost U h M0 E p s := by unfold primeCost;positivity

theorem primeCost_average_bound (U : Finset ℕ) (h M0 : ℕ) [NeZero M0]
    (E : ℕ → ZMod M0 → ∀ u : U,Finset (ZMod u.val)) (p : ℕ) (tau T : ℝ)
    (hU : 0 < U.card) (hh : h ≤ U.card)
    (hPref : (U.card : ℝ)^h/(U.card.descFactorial h : ℝ) ≤ 2)
    (hMean : ∀ v : ZMod M0,(∑ u : U,((E p v u).card : ℝ)/(u.val : ℝ))/(U.card : ℝ) ≤ tau)
    (hCap : ∀ u : U,(u.val : ℝ) ≤ T) :
    sampleAverage U h (primeCost U h M0 E p) ≤ 2*(p : ℝ)*tau^h+(M0 : ℝ)*T^h := by
  have hRatio : ∀ (v : ZMod M0) (u : U),0 ≤ ((E p v u).card : ℝ)/(u.val : ℝ) := by
    intro v u
    positivity
  have hProduct : ∀ v : ZMod M0,
      sampleAverage U h (fun s => ∏ i : Fin h,((E p v (s i)).card : ℝ)/((s i).val : ℝ)) ≤ 2*tau^h := by
    intro v
    have hm0 : 0 ≤ (∑ u : U,((E p v u).card : ℝ)/(u.val : ℝ))/(U.card : ℝ) :=
      div_nonneg (Finset.sum_nonneg (fun u _ => hRatio v u)) (Nat.cast_nonneg _)
    calc
      _ ≤ ((U.card : ℝ)^h/(U.card.descFactorial h : ℝ))*
          ((∑ u : U,((E p v u).card : ℝ)/(u.val : ℝ))/(U.card : ℝ))^h :=
        sample_product_average_le U h (fun u => ((E p v u).card : ℝ)/(u.val : ℝ)) (hRatio v) hU hh
      _ ≤ 2*tau^h := mul_le_mul hPref (pow_le_pow_left₀ hm0 (hMean v) h)
        (pow_nonneg hm0 h) (by norm_num)
  have hRound : sampleAverage U h (fun s => ∏ i : Fin h,((s i).val : ℝ)) ≤ T^h :=
    sampleAverage_product_bound U h hh (fun u => (u.val : ℝ)) T (fun u => Nat.cast_nonneg _) hCap
  have hM : (M0 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M0)
  unfold primeCost
  rw [sampleAverage_add,sampleAverage_mul,sampleAverage_mul,sampleAverage_sum]
  calc
    _ ≤ ((p : ℝ)/(M0 : ℝ))*(∑ _v : ZMod M0,2*tau^h)+(M0 : ℝ)*T^h :=
      add_le_add (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun v _ => hProduct v)) (by positivity))
        (mul_le_mul_of_nonneg_left hRound (Nat.cast_nonneg _))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]
      field_simp

end ErdosInverseSampleCost

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_SampleWitnessAverage
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseSampling
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem many_large_weights {α : Type*} (A : Finset α) (f : α → ℝ) (beta : ℝ)
    (hb : 0 ≤ beta) (hf : ∀ a ∈ A,f a ≤ 1) (hmean : beta*(A.card : ℝ) ≤ ∑ a ∈ A,f a) :
    (beta/2)*(A.card : ℝ) ≤ ((A.filter (fun a => beta/2 ≤ f a)).card : ℝ) := by
  have hup : (∑ a ∈ A,f a) ≤
      ((A.filter (fun a => beta/2 ≤ f a)).card : ℝ)+(A.card : ℝ)*(beta/2) := by
    calc
      _ ≤ ∑ a ∈ A,((if beta/2 ≤ f a then (1 : ℝ) else 0)+beta/2) := by
        apply Finset.sum_le_sum
        intro a ha
        by_cases hh : beta/2 ≤ f a
        · rw [ite_eq_left hh]
          linarith [hf a ha]
        · rw [ite_eq_right hh,zero_add]
          exact (lt_of_not_ge hh).le
      _ = _ := by
        rw [Finset.sum_add_distrib,Finset.sum_boole]
        simp
  linarith

theorem witnessPairs_card {α β : Type*} (A : Finset α) (U : Finset β) (witness : α → β → Prop) :
    (witnessPairs A U witness).card = ∑ a ∈ A,(U.filter (witness a)).card := by
  simp only [witnessPairs,Finset.card_eq_sum_ones,Finset.sum_filter]
  exact Finset.sum_product A U (fun v : α × β => if witness v.1 v.2 then (1 : ℕ) else 0)

end ErdosInverseSampling

end

section

namespace ErdosInverseSampling
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem goodSamples_filter {β : Type*} (U : Finset β) (good : β → Prop) (h : ℕ) :
    goodSamples U (U.filter good) h = Finset.univ.filter (fun e : Sample U h => ∀ i,good (e i).val) := by
  ext e
  simp only [goodSamples,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨fun he i => (he i).2,fun he i => ⟨(e i).property,he i⟩⟩

theorem sample_incidence_average_eq {α β : Type*} (A : Finset α) (U : Finset β)
    (witness : α → β → Prop) (h : ℕ) :
    sampleAverage U h (selectedFraction A U witness h) =
      (∑ a ∈ A,sampleFrequency U (U.filter (witness a)) h)/(A.card : ℝ) := by
  have hh := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun e : Sample U h => fun a : α => ∀ i,witness a (e i).val) (s := Finset.univ) (t := A)
  have hc : (∑ e : Sample U h,((selectedPairs A U witness h e).card : ℝ)) =
      ∑ a ∈ A,((goodSamples U (U.filter (witness a)) h).card : ℝ) := by
    have hn : (∑ e : Sample U h,(selectedPairs A U witness h e).card) =
        ∑ a ∈ A,(goodSamples U (U.filter (witness a)) h).card := by
      simpa only [selectedPairs,Finset.bipartiteAbove,Finset.bipartiteBelow,goodSamples_filter] using hh
    exact_mod_cast hn
  unfold sampleAverage selectedFraction sampleFrequency
  simp_rw [← Finset.sum_div]
  rw [hc]
  ring

theorem sample_incidence_average_lower {α β : Type*} (A : Finset α) (U : Finset β)
    (witness : α → β → Prop) (h : ℕ) (beta : ℝ) (hb : 0 < beta) (hb1 : beta ≤ 1)
    (hA : 0 < A.card) (hU : 0 < U.card)
    (hdense : beta*(A.card : ℝ)*(U.card : ℝ) ≤ ((witnessPairs A U witness).card : ℝ))
    (hsize : 4*(h : ℝ)/beta ≤ (U.card : ℝ)) :
    (beta/2)*(beta/4)^h ≤ sampleAverage U h (selectedFraction A U witness h) := by
  have hAR : (0 : ℝ) < A.card := by exact_mod_cast hA
  have hUR : (0 : ℝ) < U.card := by exact_mod_cast hU
  let f : α → ℝ := fun a => ((U.filter (witness a)).card : ℝ)/(U.card : ℝ)
  let G := A.filter (fun a => beta/2 ≤ f a)
  have hf (a : α) (_ha : a ∈ A) : f a ≤ 1 := by
    apply (div_le_iff₀ hUR).mpr
    simpa only [one_mul] using (Nat.cast_le.mpr (Finset.card_filter_le U (witness a)) :
      ((U.filter (witness a)).card : ℝ) ≤ U.card)
  have hmean : beta*(A.card : ℝ) ≤ ∑ a ∈ A,f a := by
    change beta*(A.card : ℝ) ≤ ∑ a ∈ A,((U.filter (witness a)).card : ℝ)/(U.card : ℝ)
    rw [← Finset.sum_div]
    apply (le_div_iff₀ hUR).mpr
    have he : ((witnessPairs A U witness).card : ℝ) = ∑ a ∈ A,((U.filter (witness a)).card : ℝ) := by
      exact_mod_cast witnessPairs_card A U witness
    rwa [← he]
  have hG : (beta/2)*(A.card : ℝ) ≤ (G.card : ℝ) := many_large_weights A f beta hb.le hf hmean
  have hfreq (a : α) (ha : a ∈ G) : (beta/4)^h ≤ sampleFrequency U (U.filter (witness a)) h := by
    have hh := (Finset.mem_filter.mp ha).2
    have hgood : (beta/2)*(U.card : ℝ) ≤ ((U.filter (witness a)).card : ℝ) := (le_div_iff₀ hUR).mp hh
    exact sampleFrequency_lower U (U.filter (witness a)) (Finset.filter_subset _ _) h beta hb hb1 hgood hsize
  have hnonneg (a : α) : 0 ≤ sampleFrequency U (U.filter (witness a)) h := by
    unfold sampleFrequency
    positivity
  rw [sample_incidence_average_eq]
  apply (le_div_iff₀ hAR).mpr
  calc
    _ ≤ (G.card : ℝ)*(beta/4)^h := by
      have hh := mul_le_mul_of_nonneg_right hG (show 0 ≤ (beta/4)^h by positivity)
      nlinarith only [hh]
    _ = ∑ _a ∈ G,(beta/4)^h := by simp
    _ ≤ ∑ a ∈ G,sampleFrequency U (U.filter (witness a)) h := Finset.sum_le_sum hfreq
    _ ≤ ∑ a ∈ A,sampleFrequency U (U.filter (witness a)) h :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun a _ _ => hnonneg a)

end ErdosInverseSampling

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_GoodSampleSelection
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseSampling
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem exists_reward_cost_sample {Ω : Type*} (S : Finset Ω) (hS : S.Nonempty)
    (reward cost : Ω → ℝ) (gamma tau : ℝ) (hg : 0 < gamma) (ht : 0 < tau)
    (hr : ∀ s ∈ S,reward s ≤ 1) (hc : ∀ s ∈ S,0 ≤ cost s)
    (hreward : gamma*(S.card : ℝ) ≤ ∑ s ∈ S,reward s)
    (hcost : (∑ s ∈ S,cost s) ≤ (gamma*tau/4)*(S.card : ℝ)) :
    ∃ s ∈ S,gamma/2 ≤ reward s ∧ cost s ≤ tau := by
  by_contra h
  push Not at h
  have hpoint (s : Ω) (hs : s ∈ S) : reward s ≤ gamma/2+cost s/tau := by
    by_cases hh : gamma/2 ≤ reward s
    · have hct : tau < cost s := h s hs hh
      have hone : (1 : ℝ) < cost s/tau := (lt_div_iff₀ ht).mpr (by simpa using hct)
      linarith [hr s hs]
    · have hcn : 0 ≤ cost s/tau := div_nonneg (hc s hs) ht.le
      linarith
  have hupper : (∑ s ∈ S,reward s) ≤ (S.card : ℝ)*(gamma/2)+(∑ s ∈ S,cost s)/tau := by
    calc
      _ ≤ ∑ s ∈ S,(gamma/2+cost s/tau) := Finset.sum_le_sum hpoint
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const,nsmul_eq_mul,← Finset.sum_div]
  have hsmall : (∑ s ∈ S,cost s)/tau ≤ (gamma/4)*(S.card : ℝ) := by
    apply (div_le_iff₀ ht).mpr
    nlinarith only [hcost]
  have hN : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hpos : 0 < gamma*(S.card : ℝ) := mul_pos hg hN
  nlinarith only [hreward,hupper,hsmall,hpos]

theorem selectedFraction_le_one {α β : Type*} (A : Finset α) (U : Finset β)
    (witness : α → β → Prop) (h : ℕ) (e : Sample U h) (hA : 0 < A.card) :
    selectedFraction A U witness h e ≤ 1 := by
  have hAR : (0 : ℝ) < A.card := by exact_mod_cast hA
  apply (div_le_iff₀ hAR).mpr
  have hh : (selectedPairs A U witness h e).card ≤ A.card := Finset.card_filter_le A _
  simpa only [one_mul] using (Nat.cast_le.mpr hh : ((selectedPairs A U witness h e).card : ℝ) ≤ A.card)

theorem exists_good_distinct_sample {α β : Type*} (A : Finset α) (U : Finset β)
    (witness : α → β → Prop) (h : ℕ) (beta tau : ℝ) (hb : 0 < beta) (hb1 : beta ≤ 1)
    (ht : 0 < tau) (hA : 0 < A.card) (hU : 0 < U.card)
    (hdense : beta*(A.card : ℝ)*(U.card : ℝ) ≤ ((witnessPairs A U witness).card : ℝ))
    (hsize : 4*(h : ℝ)/beta ≤ (U.card : ℝ)) (cost : Sample U h → ℝ)
    (hc : ∀ e,0 ≤ cost e)
    (hcost : sampleAverage U h cost ≤ (((beta/2)*(beta/4)^h)*tau/4)) :
    ∃ e : Sample U h,((beta/2)*(beta/4)^h)/2 ≤ selectedFraction A U witness h e ∧ cost e ≤ tau := by
  let gamma := (beta/2)*(beta/4)^h
  have hg : 0 < gamma := by dsimp [gamma] <;> positivity
  have hlen := sample_length_le U.card h beta hb hb1 hsize
  have hn : 0 < Fintype.card (Sample U h) := by rw [sample_card];exact Nat.descFactorial_pos.mpr hlen
  have hnR : (0 : ℝ) < Fintype.card (Sample U h) := by exact_mod_cast hn
  have hreward := sample_incidence_average_lower A U witness h beta hb hb1 hA hU hdense hsize
  have hreward' : gamma*(Fintype.card (Sample U h) : ℝ) ≤
      ∑ e : Sample U h,selectedFraction A U witness h e := (le_div_iff₀ hnR).mp hreward
  have hcost' : (∑ e : Sample U h,cost e) ≤ (gamma*tau/4)*(Fintype.card (Sample U h) : ℝ) :=
    (div_le_iff₀ hnR).mp hcost
  obtain ⟨e,_he,her,hec⟩ := exists_reward_cost_sample (Finset.univ : Finset (Sample U h))
    (Finset.card_pos.mp (by simpa only [Finset.card_univ] using hn))
    (selectedFraction A U witness h) cost gamma tau hg ht
    (fun e _ => selectedFraction_le_one A U witness h e hA) (fun e _ => hc e)
    (by simpa only [Finset.card_univ] using hreward') (by simpa only [Finset.card_univ] using hcost')
  exact ⟨e,her,hec⟩

end ErdosInverseSampling

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ActualPointSlopes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseSaving

theorem mean_envelope (N Q n : ℕ) (hN : 0 < N) (w U K xi delta C V : ℝ)
    (hw : 1 < w) (hU : 1 < U) (hK : 0 ≤ K) (hxi : 0 < xi) (hd : 0 < delta)
    (hC : 0 ≤ C) (hV : 0 < V)
    (hcount : xi*U/(16*Real.log U) ≤ (n : ℝ))
    (hEuler : V⁻¹ ≤ 2*Real.exp Real.eulerMascheroniConstant*Real.log w)
    (hQ : (Q : ℝ) ≤ 3*U) (hlogU : Real.log U ≤ K*Real.log w) :
    (4+8*Real.pi^2)*C*((N : ℝ)+(Q : ℝ)^2)/((n : ℝ)*delta^2*(N : ℝ)*V) ≤
      (32*(4+8*Real.pi^2)*C*K*Real.exp Real.eulerMascheroniConstant/(xi*delta^2))*(Real.log w)^2*
        (1/U+9*U/(N : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hUpos : 0 < U := by linarith
  have hlogw : 0 < Real.log w := Real.log_pos hw
  have hlogUpos : 0 < Real.log U := Real.log_pos hU
  have hlo : 0 < xi*U/(16*Real.log U) := by positivity
  have hn : (0 : ℝ) < n := hlo.trans_le hcount
  have hni : (n : ℝ)⁻¹ ≤ 16*Real.log U/(xi*U) := by
    have hh := (inv_le_inv₀ hn hlo).mpr hcount
    simpa only [inv_div] using hh
  have hnK : (n : ℝ)⁻¹ ≤ 16*K*Real.log w/(xi*U) := by
    apply hni.trans
    apply div_le_div_of_nonneg_right _ (mul_pos hxi hUpos).le
    nlinarith
  have hQsq : (Q : ℝ)^2 ≤ 9*U^2 := by nlinarith [show (0 : ℝ) ≤ Q from Nat.cast_nonneg Q]
  calc
    _ = ((4+8*Real.pi^2)*C/delta^2)*(((N : ℝ)+(Q : ℝ)^2)/(N : ℝ))*(n : ℝ)⁻¹*V⁻¹ := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ ≤ ((4+8*Real.pi^2)*C/delta^2)*(((N : ℝ)+9*U^2)/(N : ℝ))*
        (16*K*Real.log w/(xi*U))*(2*Real.exp Real.eulerMascheroniConstant*Real.log w) := by
      gcongr
    _ = _ := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      field_simp
      ring

theorem spectral_factor_bound (N : ℕ) (hN : 0 < N) (U rho : ℝ) (_hU : 0 < U)
    (hrho : 0 < rho) (hrhoU : rho ≤ U) (hNlower : U*rho/4 ≤ (N : ℝ)) :
    1/U+9*U/(N : ℝ) ≤ 37/rho := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : 1/U ≤ 1/rho := one_div_le_one_div_of_le hrho hrhoU
  have h2 : U/(N : ℝ) ≤ 4/rho := by
    apply (div_le_div_iff₀ hNR hrho).mpr
    nlinarith
  calc
    _ = 1/U+9*(U/(N : ℝ)) := by ring
    _ ≤ 1/rho+9*(4/rho) := add_le_add h1 (mul_le_mul_of_nonneg_left h2 (by norm_num))
    _ = _ := by ring

end ErdosInverseSaving

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseSaving

theorem log_square_absorption (A eps : ℝ) (hA : 0 ≤ A) (heps : 0 < eps) :
    ∀ᶠ w : ℝ in atTop,A*(Real.log w)^2 ≤ w^eps := by
  have hA1 : 0 < A+1 := by linarith
  have hs := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) heps).bound (inv_pos.mpr hA1)
  filter_upwards [hs,eventually_gt_atTop (1 : ℝ)] with w hw hw1
  have hw0 : 0 < w := by linarith
  have hh : (Real.log w)^2 ≤ (A+1)⁻¹*w^eps := by
    simpa only [Real.norm_eq_abs,Real.rpow_two,abs_of_nonneg (sq_nonneg (Real.log w)),
      abs_of_nonneg (Real.rpow_nonneg hw0.le eps)] using hw
  have hp := mul_le_mul_of_nonneg_left hh hA1.le
  have hcancel : (A+1)*((A+1)⁻¹*w^eps) = w^eps := by field_simp
  rw [hcancel] at hp
  nlinarith [sq_nonneg (Real.log w)]

end ErdosInverseSaving

end

section

namespace ErdosInverseSaving
open ErdosInverseTail ErdosInversePrimeBin

theorem common_length_bin_lower (Y p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (Qplus xi w aStar U theta : ℝ) (hqQ : (q : ℝ) ≤ Qplus)
    (hQq : Qplus ≤ (1+xi)*(q : ℝ)) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (hw : 1 < w) (ha : 0 < aStar) (hwU : w ≤ U) (htheta : 0 ≤ theta)
    (hlarge : 4 ≤ w^(3*aStar/4)) (hne : (primeBin U theta).Nonempty)
    (hlen : ∀ u ∈ primeBin U theta,
      3*aStar/4 ≤ Real.log ((Y : ℝ)/((p : ℝ)*q*u))/Real.log w) :
    U*w^(3*aStar/4)/4 ≤ (commonParentLength Y p Qplus : ℝ) := by
  obtain ⟨u,hu⟩ := hne
  have hUpos : 0 < U := (by linarith : 0 < w).trans_le hwU
  have humem := (mem_primeBin hUpos.le htheta u).mp hu
  have huR : (0 : ℝ) < u := hUpos.trans humem.2.1
  have hgeo := common_length_from_log Y p q u hp hq humem.1.pos Qplus xi w aStar hqQ hQq
    hxi hxi1 hw ha (hlen u hu)
  rw [mul_div_assoc (2 : ℝ) (commonParentLength Y p Qplus : ℝ) (u : ℝ)] at hgeo
  have hlow : w^(3*aStar/4)/4 ≤ (commonParentLength Y p Qplus : ℝ)/(u : ℝ) := by nlinarith
  have hprod := (le_div_iff₀ huR).mp hlow
  have hpow : 0 ≤ w^(3*aStar/4)/4 := by positivity
  calc
    _ = (w^(3*aStar/4)/4)*U := by ring
    _ ≤ (w^(3*aStar/4)/4)*(u : ℝ) := mul_le_mul_of_nonneg_left humem.2.1.le hpow
    _ ≤ _ := hprod

end ErdosInverseSaving

end

section

namespace ErdosInverseSampleCost
open ErdosInverseSampling
attribute [local instance] Classical.decEq

theorem totalCost_nonneg (P U : Finset ℕ) (h M0 : ℕ) [NeZero M0]
    (E : ℕ → ZMod M0 → ∀ u : U,Finset (ZMod u.val)) (s : Sample U h) :
    0 ≤ totalCost P U h M0 E s := by
  exact div_nonneg (Finset.sum_nonneg (fun p _ => primeCost_nonneg U h M0 E p s)) (Nat.cast_nonneg _)

theorem totalCost_average_bound (P U : Finset ℕ) (h M0 : ℕ) [NeZero M0]
    (E : ℕ → ZMod M0 → ∀ u : U,Finset (ZMod u.val)) (R tau T : ℝ)
    (hP : 0 < P.card) (hU : 0 < U.card) (hh : h ≤ U.card) (htau : 0 ≤ tau)
    (hPref : (U.card : ℝ)^h/(U.card.descFactorial h : ℝ) ≤ 2)
    (hMean : ∀ p ∈ P,∀ v : ZMod M0,
      (∑ u : U,((E p v u).card : ℝ)/(u.val : ℝ))/(U.card : ℝ) ≤ tau)
    (hR : ∀ p ∈ P,(p : ℝ) ≤ 2*R) (hCap : ∀ u : U,(u.val : ℝ) ≤ T) :
    sampleAverage U h (totalCost P U h M0 E) ≤ 4*R*tau^h+(M0 : ℝ)*T^h := by
  have hPnz : (P.card : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  unfold totalCost
  rw [sampleAverage_div,sampleAverage_sum]
  calc
    _ ≤ (∑ p ∈ P,(2*(p : ℝ)*tau^h+(M0 : ℝ)*T^h))/(P.card : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun p hp =>
        primeCost_average_bound U h M0 E p tau T hU hh hPref (hMean p hp) hCap)) (Nat.cast_nonneg _)
    _ ≤ (∑ _p ∈ P,(4*R*tau^h+(M0 : ℝ)*T^h))/(P.card : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro p hp
      have hh := mul_le_mul_of_nonneg_right (hR p hp) (pow_nonneg htau h)
      nlinarith
    _ = _ := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      field_simp

end ErdosInverseSampleCost

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseSaving
open NumberTheoryLean ErdosInversePrimeBin ErdosInverseFrozen ErdosInverseEuler

theorem actual_mean_envelope (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ,0 < C ∧ ∀ xi K delta : ℝ,0 < xi → xi ≤ 1 → 0 ≤ K → 0 < delta →
      ∀ᶠ w : ℝ in atTop,2 ≤ w ∧ ∀ (N : ℕ) (p q : ℕ) (b v : ℤ) (a : ℕ → ℕ) (U theta : ℝ),
        w ≤ U → U ≤ w^K → xi/4 ≤ theta → theta ≤ xi → w^eta ≤ (N : ℝ) →
        (∀ t : ℕ,t.Prime → (t : ℝ) ≤ w → (p*q).Coprime t) →
        frozenPrimeMean N w p q b v a delta U theta ≤
          meanCoefficient C K xi delta*(Real.log w)^2*(1/U+9*U/(N : ℝ)) := by
  obtain ⟨C,hC,w0,_hw0,hmean⟩ := frozen_exceptional_mean_jb247 eta heta
  refine ⟨C,hC,?_⟩
  intro xi K delta hxi hxi1 hK hd
  filter_upwards [eventually_ge_atTop w0,uniform_edge_bin_count xi hxi hxi1,smallEuler_log_bounds]
    with w hw hb hEuler
  refine ⟨hb.1,?_⟩
  intro N p q b v a U theta hwU hUmax htlow hthigh hN hcop
  have hwpos : 0 < w := by linarith [hb.1]
  have hUpos : 0 < U := hwpos.trans_le hwU
  have hU2 : 2 ≤ U := hb.1.trans hwU
  have htpos : 0 ≤ theta := (by positivity : (0 : ℝ) ≤ xi/4).trans htlow
  have ht1 : theta ≤ 1 := hthigh.trans hxi1
  have hNpos : 0 < N := by exact_mod_cast (Real.rpow_pos_of_pos hwpos eta).trans_le hN
  have hlogU : Real.log U ≤ K*Real.log w := by
    have hh := Real.log_le_log hUpos hUmax
    rwa [Real.log_rpow hwpos] at hh
  have hbin := hb.2 U theta hwU htlow hthigh
  have hprimes : ∀ u ∈ primeBin U theta,u.Prime := fun u hu => ((mem_primeBin hUpos.le htpos u).mp hu).1
  have hcapped : ∀ u ∈ primeBin U theta,u ≤ edgeFrequencyCap U :=
    edge_prime_le_cap U theta hUpos.le htpos ht1
  have hspec := hmean N (edgeFrequencyCap U) w p q b v a (primeBin U theta) delta
    hw hN hcop hprimes hcapped hbin.2 hd
  exact hspec.trans (mean_envelope N (edgeFrequencyCap U) (primeBin U theta).card hNpos
    w U K xi delta C (SmallSieveFinite.smallEuler ⌊w⌋₊) (by linarith [hb.1]) (by linarith)
    hK hxi hd hC.le hEuler.2.1 hbin.1 hEuler.2.2.2 (edgeFrequencyCap_le U (by linarith)) hlogU)

end ErdosInverseSaving

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseSaving
open NumberTheoryLean ErdosInversePrimeBin ErdosInverseFrozen ErdosInverseEuler ErdosInverseTail

theorem uniform_mean_power (aStar K xi delta : ℝ) (ha : 0 < aStar) (ha1 : aStar ≤ 1)
    (hK : 0 ≤ K) (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hd : 0 < delta) :
    ∀ᶠ w : ℝ in atTop,4 ≤ w ∧
      ∀ (Y p q q0 : ℕ) (Qplus U theta : ℝ) (b v : ℤ) (a : ℕ → ℕ),
        0 < p → 0 < q → (q : ℝ) ≤ Qplus → Qplus ≤ (1+xi)*(q : ℝ) →
        w ≤ U → U ≤ w^K → xi/4 ≤ theta → theta ≤ xi →
        Int.ModEq (smallModulus w : ℤ) (q : ℤ) (q0 : ℤ) →
        (∀ t : ℕ,t.Prime → (t : ℝ) ≤ w → (p*q).Coprime t) →
        (∀ u ∈ primeBin U theta,
          3*aStar/4 ≤ Real.log ((Y : ℝ)/((p : ℝ)*q*u))/Real.log w) →
        frozenPrimeMean (commonParentLength Y p Qplus) w p q0 b v a delta U theta ≤ w^(-aStar/2) := by
  obtain ⟨C,hC,hmean⟩ := actual_mean_envelope (aStar/2) (by positivity)
  have hA : 0 ≤ meanCoefficient C K xi delta := by unfold meanCoefficient;positivity
  filter_upwards [hmean xi K delta hxi hxi1 hK hd,uniform_edge_bin_count xi hxi hxi1,
    log_square_absorption (37*meanCoefficient C K xi delta) (aStar/4) (by positivity) (by positivity),
    eventually_ge_atTop (4 : ℝ),(tendsto_rpow_atTop (by linarith : 0 < 3*aStar/4)).eventually_ge_atTop 4]
    with w hm hb habs hw hlarge
  refine ⟨hw,?_⟩
  intro Y p q q0 Qplus U theta b v a hp hq hqQ hQq hwU hUmax htlow hthigh hqq hcop hlog
  have hwpos : 0 < w := by linarith
  have hw1 : 1 ≤ w := by linarith
  have hUpos : 0 < U := hwpos.trans_le hwU
  have htpos : 0 ≤ theta := (by positivity : (0 : ℝ) ≤ xi/4).trans htlow
  have hcard := (hb.2 U theta hwU htlow hthigh).2
  have hNlower := common_length_bin_lower Y p q hp hq Qplus xi w aStar U theta hqQ hQq
    hxi.le hxi1 (by linarith) ha hwU htpos hlarge (Finset.card_pos.mp hcard) hlog
  have hrho : 0 < w^(3*aStar/4) := Real.rpow_pos_of_pos hwpos _
  have hNpos : 0 < commonParentLength Y p Qplus := by
    exact_mod_cast (div_pos (mul_pos hUpos hrho) (by norm_num : (0 : ℝ) < 4)).trans_le hNlower
  have hrhoN : w^(3*aStar/4) ≤ (commonParentLength Y p Qplus : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right (hw.trans hwU) hrho.le
    nlinarith
  have hEta : w^(aStar/2) ≤ (commonParentLength Y p Qplus : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hw1 (by linarith : aStar/2 ≤ 3*aStar/4)).trans hrhoN
  have hrhoU : w^(3*aStar/4) ≤ U := by
    have hh := Real.rpow_le_rpow_of_exponent_le hw1 (show 3*aStar/4 ≤ 1 by linarith)
    have hwr : w^(3*aStar/4) ≤ w := by simpa only [Real.rpow_one] using hh
    exact hwr.trans hwU
  have hcenter : ∀ t : ℕ,t.Prime → (t : ℝ) ≤ w → (p*q0).Coprime t :=
    fun t ht htw => center_step_coprime w p q q0 t ht htw hqq (hcop t ht htw)
  have hEnv := hm.2 (commonParentLength Y p Qplus) p q0 b v a U theta hwU hUmax htlow hthigh hEta hcenter
  have hFactor := spectral_factor_bound (commonParentLength Y p Qplus) hNpos U (w^(3*aStar/4))
    hUpos hrho hrhoU hNlower
  calc
    _ ≤ meanCoefficient C K xi delta*(Real.log w)^2*(1/U+9*U/(commonParentLength Y p Qplus : ℝ)) := hEnv
    _ ≤ meanCoefficient C K xi delta*(Real.log w)^2*(37/w^(3*aStar/4)) :=
      mul_le_mul_of_nonneg_left hFactor (mul_nonneg hA (sq_nonneg _))
    _ = (37*meanCoefficient C K xi delta*(Real.log w)^2)/w^(3*aStar/4) := by ring
    _ ≤ w^(aStar/4)/w^(3*aStar/4) := div_le_div_of_nonneg_right habs hrho.le
    _ = w^(-aStar/2) := by
      rw [← Real.rpow_sub hwpos]
      congr 1
      ring

end ErdosInverseSaving

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseSaving
open ErdosInverseBoxHeight ErdosInverseEuler ErdosInversePrimeBin ErdosInverseTail

theorem source_mean_power (aStar K xi delta : ℝ) (ha : 0 < aStar) (ha1 : aStar ≤ 1)
    (hK : 0 ≤ K) (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hd : 0 < delta) :
    ∀ᶠ z : ℝ in atTop,4 ≤ sourceW z ∧
      ∀ (p q q0 : ℕ) (Qplus U theta : ℝ) (b v : ℤ) (a : ℕ → ℕ),
        0 < p → 0 < q → (q : ℝ) ≤ Qplus → Qplus ≤ (1+xi)*(q : ℝ) →
        sourceW z ≤ U → U ≤ (sourceW z)^K → xi/4 ≤ theta → theta ≤ xi →
        Int.ModEq (smallModulus (sourceW z) : ℤ) (q : ℤ) (q0 : ℤ) →
        (∀ t : ℕ,t.Prime → (t : ℝ) ≤ sourceW z → (p*q).Coprime t) →
        (∀ u ∈ primeBin U theta,
          3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*q*u))/Real.log (sourceW z)) →
        frozenPrimeMean (commonParentLength (sourceY z) p Qplus) (sourceW z) p q0 b v a delta U theta ≤
          (sourceW z)^(-aStar/2) := by
  filter_upwards [sourceW_tendsto_atTop.eventually (uniform_mean_power aStar K xi delta ha ha1 hK hxi hxi1 hd)] with z hz
  exact ⟨hz.1,hz.2 (sourceY z)⟩

end ErdosInverseSaving

end

section

namespace ErdosInverseSampleCost
open NumberTheoryLean ErdosInverseSampling ErdosInverseSaving ErdosInverseFrozen ErdosInverseTail ErdosInverseEuler ErdosInversePrimeBin
attribute [local instance] Classical.decEq

theorem actual_family_mean_eq (Y : ℕ) (w Qplus : ℝ) (q0 : ℕ) (b0 : ℤ) (a : ℕ → ℕ)
    (delta U theta : ℝ) (M0 p : ℕ) (v : ZMod M0) :
    (∑ u : primeBin U theta,((actualFamily Y w Qplus q0 b0 a delta (primeBin U theta) M0 p v u).card : ℝ)/(u.val : ℝ))/
        ((primeBin U theta).card : ℝ) =
      frozenPrimeMean (commonParentLength Y p Qplus) w p q0 b0 (v.val : ℤ) a delta U theta := by
  unfold actualFamily frozenPrimeMean
  rw [Finset.sum_coe_sort (primeBin U theta) (fun u : ℕ =>
    ((frozenExceptional (commonParentLength Y p Qplus) w p q0 b0 (v.val : ℤ) a u delta
      (SmallSieveFinite.smallEuler ⌊w⌋₊)).card : ℝ)/(u : ℝ))]

theorem actualCost_nonneg (Y : ℕ) (w Qplus R : ℝ) (q0 : ℕ) (b0 : ℤ) (a : ℕ → ℕ)
    (delta : ℝ) (P U : Finset ℕ) (h : ℕ) (s : Sample U h) (hR : 0 ≤ R) :
    0 ≤ actualCost Y w Qplus R q0 b0 a delta P U h s := by
  let : NeZero (smallModulus w) := ⟨(smallModulus_pos w).ne'⟩
  unfold actualCost
  exact div_nonneg (totalCost_nonneg P U h _ _ s) hR

theorem actualCost_average_bound (Y : ℕ) (w Qplus R : ℝ) (q0 : ℕ) (b0 : ℤ) (a : ℕ → ℕ)
    (delta : ℝ) (P U : Finset ℕ) (h : ℕ) (tau T : ℝ) (hR0 : 0 ≤ R)
    (hP : 0 < P.card) (hU : 0 < U.card) (hh : h ≤ U.card) (htau : 0 ≤ tau)
    (hPref : (U.card : ℝ)^h/(U.card.descFactorial h : ℝ) ≤ 2)
    (hMean : ∀ p ∈ P,∀ v : ZMod (smallModulus w),
      (∑ u : U,((actualFamily Y w Qplus q0 b0 a delta U (smallModulus w) p v u).card : ℝ)/(u.val : ℝ))/(U.card : ℝ) ≤ tau)
    (hR : ∀ p ∈ P,(p : ℝ) ≤ 2*R) (hCap : ∀ u : U,(u.val : ℝ) ≤ T) :
    sampleAverage U h (actualCost Y w Qplus R q0 b0 a delta P U h) ≤
      (4*R*tau^h+(smallModulus w : ℝ)*T^h)/R := by
  let : NeZero (smallModulus w) := ⟨(smallModulus_pos w).ne'⟩
  unfold actualCost
  rw [sampleAverage_div]
  exact div_le_div_of_nonneg_right (totalCost_average_bound P U h _ _ R tau T
    hP hU hh htau hPref hMean hR hCap) hR0

end ErdosInverseSampleCost

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseSampleCost
open NumberTheoryLean ErdosInverseSampling ErdosInverseSaving ErdosInversePrimeBin ErdosInverseEuler ErdosInverseBoxHeight

theorem source_expected_cost (aStar K alpha xi delta beta : ℝ) (h : ℕ)
    (ha : 0 < aStar) (ha1 : aStar ≤ 1) (hK : 0 ≤ K) (halpha : 0 < alpha)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hd : 0 < delta) :
    ∀ᶠ z : ℝ in atTop,1 < z ∧ ∀ R thetaP U thetaU Qplus : ℝ,∀ (q0 : ℕ) (b0 : ℤ) (a : ℕ → ℕ),
      z^alpha ≤ R → sourceW z ≤ U → U ≤ (sourceW z)^K →
      xi/4 ≤ thetaP → thetaP ≤ xi → xi/4 ≤ thetaU → thetaU ≤ xi →
      0 < q0 → (q0 : ℝ) ≤ Qplus → Qplus ≤ (1+xi)*(q0 : ℝ) →
      (∀ p ∈ primeBin R thetaP,∀ t : ℕ,t.Prime → (t : ℝ) ≤ sourceW z → (p*q0).Coprime t) →
      (∀ p ∈ primeBin R thetaP,∀ u ∈ primeBin U thetaU,
        3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*q0*u))/Real.log (sourceW z)) →
      0 < (primeBin R thetaP).card ∧ 0 < (primeBin U thetaU).card ∧ h ≤ (primeBin U thetaU).card ∧
      4*(h : ℝ)/beta ≤ ((primeBin U thetaU).card : ℝ) ∧
      sampleAverage (primeBin U thetaU) h
        (actualCost (sourceY z) (sourceW z) Qplus R q0 b0 a delta (primeBin R thetaP) (primeBin U thetaU) h) ≤
          (4*R*((sourceW z)^(-aStar/2))^h+(smallModulus (sourceW z) : ℝ)*(2*U)^h)/R := by
  filter_upwards [source_mean_power aStar K xi delta ha ha1 hK hxi hxi1 hd,
    source_sample_population xi beta h hxi hxi1,source_sample_population xi 1 0 hxi hxi1,
    sourceW_le_power alpha halpha,eventually_gt_atTop (1 : ℝ)] with z hmean hpop hpopP hWR hz
  refine ⟨hz,?_⟩
  intro R thetaP U thetaU Qplus q0 b0 a hR hWU hUtop hPlow hPhigh hUlow hUhigh hq0 hqQ hQq hcop hlog
  have hzpos : 0 < z := by linarith
  have hRpos : 0 < R := (Real.rpow_pos_of_pos hzpos alpha).trans_le hR
  have hWpos : 0 < sourceW z := by linarith [hmean.1]
  have hUpos : 0 < U := hWpos.trans_le hWU
  have hthetaP : 0 ≤ thetaP := (by positivity : (0 : ℝ) ≤ xi/4).trans hPlow
  have hthetaU : 0 ≤ thetaU := (by positivity : (0 : ℝ) ≤ xi/4).trans hUlow
  have hPo := hpopP R thetaP (hWR.trans hR) hPlow hPhigh
  have hUo := hpop U thetaU hWU hUlow hUhigh
  refine ⟨hPo.1,hUo.1,hUo.2.1,hUo.2.2.1,?_⟩
  apply actualCost_average_bound (sourceY z) (sourceW z) Qplus R q0 b0 a delta
    (primeBin R thetaP) (primeBin U thetaU) h ((sourceW z)^(-aStar/2)) (2*U) hRpos.le
    hPo.1 hUo.1 hUo.2.1 (Real.rpow_nonneg hWpos.le _) hUo.2.2.2
  · intro p hp v
    rw [actual_family_mean_eq]
    have hprime := ((mem_primeBin hRpos.le hthetaP p).mp hp).1
    exact hmean.2 p q0 q0 Qplus U thetaU b0 (v.val : ℤ) a hprime.pos hq0 hqQ hQq hWU hUtop
      hUlow hUhigh (Int.ModEq.refl _) (hcop p hp) (hlog p hp)
  · intro p hp
    have hh := ((mem_primeBin hRpos.le hthetaP p).mp hp).2.2
    have htheta1 := hPhigh.trans hxi1
    nlinarith
  · intro u
    have hh := ((mem_primeBin hUpos.le hthetaU u.val).mp u.property).2.2
    have htheta1 := hUhigh.trans hxi1
    nlinarith

end ErdosInverseSampleCost

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseSampleCost
open NumberTheoryLean ErdosInverseSampling ErdosInverseSaving ErdosInversePrimeBin ErdosInverseEuler ErdosInverseBoxHeight

theorem source_expected_cost_small (aStar K alpha xi delta beta eps : ℝ) (h : ℕ)
    (ha : 0 < aStar) (ha1 : aStar ≤ 1) (hK : 0 ≤ K) (halpha : 0 < alpha)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hd : 0 < delta)
    (heps : 0 < eps) (hh : 12 < aStar*(h : ℝ)/2) :
    ∀ᶠ z : ℝ in atTop,1 < z ∧ ∀ R thetaP U thetaU Qplus : ℝ,∀ (q0 : ℕ) (b0 : ℤ) (a : ℕ → ℕ),
      z^alpha ≤ R → sourceW z ≤ U → U ≤ (sourceW z)^K →
      xi/4 ≤ thetaP → thetaP ≤ xi → xi/4 ≤ thetaU → thetaU ≤ xi →
      0 < q0 → (q0 : ℝ) ≤ Qplus → Qplus ≤ (1+xi)*(q0 : ℝ) →
      (∀ p ∈ primeBin R thetaP,∀ t : ℕ,t.Prime → (t : ℝ) ≤ sourceW z → (p*q0).Coprime t) →
      (∀ p ∈ primeBin R thetaP,∀ u ∈ primeBin U thetaU,
        3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*q0*u))/Real.log (sourceW z)) →
      0 < (primeBin R thetaP).card ∧ 0 < (primeBin U thetaU).card ∧ h ≤ (primeBin U thetaU).card ∧
      4*(h : ℝ)/beta ≤ ((primeBin U thetaU).card : ℝ) ∧
      sampleAverage (primeBin U thetaU) h
        (actualCost (sourceY z) (sourceW z) Qplus R q0 b0 a delta (primeBin R thetaP) (primeBin U thetaU) h) ≤
          eps/(Real.log z)^6 := by
  filter_upwards [source_expected_cost aStar K alpha xi delta beta h ha ha1 hK halpha hxi hxi1 hd,
    source_cost_budget aStar K alpha eps h hK halpha heps hh] with z hexp hbudget
  refine ⟨hexp.1,?_⟩
  intro R thetaP U thetaU Qplus q0 b0 a hR hWU hUtop hPlow hPhigh hUlow hUhigh hq0 hqQ hQq hcop hlog
  have hv := hexp.2 R thetaP U thetaU Qplus q0 b0 a hR hWU hUtop hPlow hPhigh hUlow hUhigh hq0 hqQ hQq hcop hlog
  have hL : 0 < Real.log z := Real.log_pos hexp.1
  have hW : 0 ≤ sourceW z := div_nonneg hL.le (sq_nonneg _)
  have hs := hbudget.2 R U hR (hW.trans hWU) hUtop
  have hL6 : 0 < (Real.log z)^6 := pow_pos hL 6
  refine ⟨hv.1,hv.2.1,hv.2.2.1,hv.2.2.2.1,?_⟩
  apply (le_div_iff₀ hL6).mpr
  calc
    _ ≤ ((4*R*((sourceW z)^(-aStar/2))^h+(smallModulus (sourceW z) : ℝ)*(2*U)^h)/R)*(Real.log z)^6 :=
      mul_le_mul_of_nonneg_right hv.2.2.2.2 hL6.le
    _ = (Real.log z)^6*(4*R*((sourceW z)^(-aStar/2))^h+
        (smallModulus (sourceW z) : ℝ)*(2*U)^h)/R := by ring
    _ ≤ eps := hs

end ErdosInverseSampleCost

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseSampleCost
open NumberTheoryLean ErdosInverseSampling ErdosInverseSaving ErdosInversePrimeBin ErdosInverseEuler ErdosInverseBoxHeight

theorem sampleGamma_pos (beta : ℝ) (h : ℕ) (hb : 0 < beta) : 0 < sampleGamma beta h := by
  unfold sampleGamma
  positivity

theorem source_good_sample_jb247_oai (aStar K alpha xi delta beta : ℝ) (h : ℕ)
    (ha : 0 < aStar) (ha1 : aStar ≤ 1) (hK : 0 ≤ K) (halpha : 0 < alpha)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hd : 0 < delta) (hb : 0 < beta) (hb1 : beta ≤ 1)
    (hh : 12 < aStar*(h : ℝ)/2) :
    ∀ᶠ z : ℝ in atTop,1 < z ∧ ∀ R thetaP U thetaU Qplus S : ℝ,
      ∀ (C : Finset ℕ) (q0 : ℕ) (b0 : ℤ) (a : ℕ → ℕ),
      z^alpha ≤ R → sourceW z ≤ U → U ≤ (sourceW z)^K →
      xi/4 ≤ thetaP → thetaP ≤ xi → xi/4 ≤ thetaU → thetaU ≤ xi →
      q0 ∈ C → 0 < q0 → (q0 : ℝ) ≤ Qplus → Qplus ≤ (1+xi)*(q0 : ℝ) →
      (∀ p ∈ primeBin R thetaP,∀ t : ℕ,t.Prime → (t : ℝ) ≤ sourceW z → (p*q0).Coprime t) →
      (∀ p ∈ primeBin R thetaP,∀ u ∈ primeBin U thetaU,
        3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*q0*u))/Real.log (sourceW z)) →
      let P := primeBin R thetaP
      let Uset := primeBin U thetaU
      let witness := actualWitness (sourceY z) (LargePrimeDeletion.cutoffPrimes ⌊sourceW z⌋₊) a delta
        (SmallSieveFinite.smallEuler ⌊sourceW z⌋₊) P S R (sourceZ z) (sampleGamma beta h/32)
      beta*((P.product C).card : ℝ)*(Uset.card : ℝ) ≤ ((witnessPairs (P.product C) Uset witness).card : ℝ) →
      ∃ s : Sample Uset h,0 < P.card ∧ 0 < Uset.card ∧ 0 < h ∧
        sampleGamma beta h/2 ≤ selectedFraction (P.product C) Uset witness h s ∧
        actualCost (sourceY z) (sourceW z) Qplus R q0 b0 a (delta/4) P Uset h s ≤ 1/(Real.log z)^6 := by
  have hg := sampleGamma_pos beta h hb
  have hpos : 0 < h := by
    by_contra hn
    have hh0 : h = 0 := by omega
    rw [hh0] at hh
    norm_num at hh
  filter_upwards [source_expected_cost_small aStar K alpha xi (delta/4) beta (sampleGamma beta h/4) h
    ha ha1 hK halpha hxi hxi1 (by positivity) (by positivity) hh] with z hz
  refine ⟨hz.1,?_⟩
  intro R thetaP U thetaU Qplus S C q0 b0 a hR hWU hUtop hPlow hPhigh hUlow hUhigh
    hqC hq0 hqQ hQq hcop hlog
  dsimp only
  intro hdense
  have hv := hz.2 R thetaP U thetaU Qplus q0 b0 a hR hWU hUtop hPlow hPhigh hUlow hUhigh hq0 hqQ hQq hcop hlog
  have hC : 0 < C.card := Finset.card_pos.mpr ⟨q0,hqC⟩
  have hA : 0 < ((primeBin R thetaP).product C).card := by
    rw [Finset.product_eq_sprod,Finset.card_product]
    exact Nat.mul_pos hv.1 hC
  have hL : 0 < Real.log z := Real.log_pos hz.1
  have hzpos : 0 < z := by linarith [hz.1]
  have hRpos : 0 < R := (Real.rpow_pos_of_pos hzpos alpha).trans_le hR
  let witness := actualWitness (sourceY z) (LargePrimeDeletion.cutoffPrimes ⌊sourceW z⌋₊) a delta
    (SmallSieveFinite.smallEuler ⌊sourceW z⌋₊) (primeBin R thetaP) S R (sourceZ z) (sampleGamma beta h/32)
  let cost := actualCost (sourceY z) (sourceW z) Qplus R q0 b0 a (delta/4) (primeBin R thetaP) (primeBin U thetaU) h
  have hc : ∀ s : Sample (primeBin U thetaU) h,0 ≤ cost s :=
    fun s => actualCost_nonneg _ _ _ _ _ _ _ _ _ _ _ s hRpos.le
  have hcost : sampleAverage (primeBin U thetaU) h cost ≤
      (((beta/2)*(beta/4)^h)*(1/(Real.log z)^6)/4) := by
    calc
      _ ≤ (sampleGamma beta h/4)/(Real.log z)^6 := hv.2.2.2.2
      _ = _ := by unfold sampleGamma;ring
  obtain ⟨s,hs,hcs⟩ := exists_good_distinct_sample ((primeBin R thetaP).product C) (primeBin U thetaU)
    witness h beta (1/(Real.log z)^6) hb hb1 (by positivity) hA hv.2.1 hdense hv.2.2.2.1 cost hc hcost
  exact ⟨s,hv.1,hv.2.1,hpos,hs,hcs⟩

end ErdosInverseSampleCost

end

end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.ErdosInverseSampleCost.source_good_sample_jb247_oai := @OAI.Erdos970.ErdosInverseSampleCost.source_good_sample_jb247_oai
