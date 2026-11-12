-- Prove2me | solution 1 for OAI.Erdos970.ErdosVarianceLargeMap.source_full_pattern_domination_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:57:35.797809+00:00
-- url     : https://prove2.me/submissions/6b4aa477-10c7-445d-a271-32493dcd07ef

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
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Basic
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
import Theorems.Thm_OAI_Erdos970_ErdosVarianceLargeCount_source_pair_sieve_upper_jb247

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_UnitCyclicBounds
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosHyperbola

theorem harmonicConstant_pos : 0 < harmonicConstant := by
  have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold harmonicConstant
  positivity

end ErdosHyperbola

end

section

namespace ErdosHyperbolaWeighted

theorem log_two_mul_le_power {eps x : ℝ} (heps : 0 < eps) (hx : 0 < x) :
    Real.log (2*x) ≤ ((2 : ℝ)^eps/eps)*x^eps := by
  have h := Real.add_one_le_exp (eps*Real.log (2*x))
  have he : Real.exp (eps*Real.log (2*x)) = (2*x)^eps := by
    rw [Real.rpow_def_of_pos (by positivity)]
    congr 1
    ring
  rw [he, Real.mul_rpow (by norm_num) hx.le] at h
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ heps).mpr
  nlinarith

end ErdosHyperbolaWeighted

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimePowerGrowth
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosDivisorBounds

theorem local_power_bound {eps : ℝ} (heps : 0 < eps) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ p : ℕ, 2 ≤ p → ∀ k : ℕ,
      (k : ℝ) + 1 ≤ B * ((p : ℝ)^eps)^k := by
  let a : ℝ := (2 : ℝ)^eps - 1
  have ha : 0 < a := sub_pos.mpr (Real.one_lt_rpow (by norm_num) heps)
  let B : ℝ := 1 + a⁻¹
  have hB : 1 ≤ B := by
    dsimp [B]
    exact le_add_of_nonneg_right (inv_nonneg.mpr ha.le)
  have hBa : B*a = a+1 := by dsimp [B]; field_simp
  refine ⟨B,hB,?_⟩
  intro p hp k
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hlin : (k : ℝ)+1 ≤ B*(1+(k : ℝ)*a) := by
    have hm := mul_le_mul_of_nonneg_right (show 1 ≤ B*a by rw [hBa]; linarith) hk
    nlinarith
  have hbern := one_add_mul_le_pow (a:=a) (by linarith : -2 ≤ a) k
  have heq : 1+a = (2 : ℝ)^eps := by dsimp [a] <;> ring
  have hpp : (2 : ℝ)^eps ≤ (p : ℝ)^eps :=
    Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hp) heps.le
  calc
    _ ≤ B*(1+(k : ℝ)*a) := hlin
    _ ≤ B*(1+a)^k := mul_le_mul_of_nonneg_left hbern (by linarith)
    _ = B*((2 : ℝ)^eps)^k := by rw [heq]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hpp k) (by linarith)

theorem large_prime_power_bound {eps : ℝ} (heps : 0 < eps) :
    ∃ P : ℕ, ∀ p : ℕ, P ≤ p → ∀ k : ℕ,
      (k : ℝ)+1 ≤ ((p : ℝ)^eps)^k := by
  obtain ⟨P,hP⟩ := exists_nat_ge ((2 : ℝ)^(1/eps))
  refine ⟨P,?_⟩
  intro p hp k
  have hpp : (2 : ℝ)^(1/eps) ≤ (p : ℝ) := hP.trans (by exact_mod_cast hp)
  have hr := Real.rpow_le_rpow (by positivity : 0 ≤ (2 : ℝ)^(1/eps)) hpp heps.le
  have he : ((2 : ℝ)^(1/eps))^eps = 2 := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
    norm_num
  rw [he] at hr
  have hb := one_add_mul_le_pow (a:=(1 : ℝ)) (by norm_num) k
  have hlin : (k : ℝ)+1 ≤ (2 : ℝ)^k := by simpa only [mul_one, one_add_one_eq_two, add_comm] using hb
  exact hlin.trans (pow_le_pow_left₀ (by norm_num) hr k)

end ErdosDivisorBounds

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_DivisorLogGrowth
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
namespace ErdosDivisorBounds

theorem prime_factor_product (n : ℕ) (hn : n ≠ 0) (eps : ℝ) :
    (∏ p ∈ n.primeFactors, ((p : ℝ)^eps)^(n.factorization p)) = (n : ℝ)^eps := by
  calc
    _ = ∏ p ∈ n.primeFactors, ((p : ℝ)^(n.factorization p))^eps := by
      apply Finset.prod_congr rfl
      intro p _
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p),
        ← Real.rpow_natCast_mul (Nat.cast_nonneg p)]
      congr 1
      ring
    _ = (∏ p ∈ n.primeFactors, (p : ℝ)^(n.factorization p))^eps :=
      Real.finsetProd_rpow _ _ (fun p _ => by positivity) eps
    _ = _ := by
      have h : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ)^(n.factorization p) := by
        exact_mod_cast Nat.prod_primeFactors_pow_factorization hn
      rw [← h]

theorem small_factor_product (s : Finset ℕ) (P : ℕ) {B : ℝ} (hB : 1 ≤ B) :
    (∏ p ∈ s, if p < P then B else 1) ≤ B^P := by
  classical
  have hcard : (s.filter (fun p => p < P)).card ≤ P := by
    calc
      _ ≤ (Finset.range P).card := Finset.card_le_card (by
        intro p hp
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
      _ = P := Finset.card_range P
  rw [Finset.prod_ite]
  simpa using pow_le_pow_right₀ hB hcard

theorem divisor_subpower {eps : ℝ} (heps : 0 < eps) :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ A*(n : ℝ)^eps := by
  classical
  obtain ⟨B,hB,hsmall⟩ := local_power_bound heps
  obtain ⟨P,hlarge⟩ := large_prime_power_bound heps
  refine ⟨B^P, pow_pos (by linarith) _, ?_⟩
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hcard : (n.divisors.card : ℝ) =
      ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ)+1) := by
    exact_mod_cast Nat.card_divisors hn0
  have hlocal (p : ℕ) (hp : p ∈ n.primeFactors) :
      (n.factorization p : ℝ)+1 ≤
        (if p < P then B else 1)*((p : ℝ)^eps)^(n.factorization p) := by
    by_cases h : p < P
    · simpa only [h,ite_true, if_true] using hsmall p (Nat.prime_of_mem_primeFactors hp).two_le (n.factorization p)
    · simpa only [h,ite_false, if_false,one_mul] using hlarge p (by omega) (n.factorization p)
  calc
    _ = _ := hcard
    _ ≤ ∏ p ∈ n.primeFactors,
        (if p < P then B else 1)*((p : ℝ)^eps)^(n.factorization p) :=
      Finset.prod_le_prod (fun p _ => by positivity) hlocal
    _ = (∏ p ∈ n.primeFactors, if p < P then B else 1) *
        (∏ p ∈ n.primeFactors, ((p : ℝ)^eps)^(n.factorization p)) := Finset.prod_mul_distrib
    _ ≤ B^P*(∏ p ∈ n.primeFactors, ((p : ℝ)^eps)^(n.factorization p)) :=
      mul_le_mul_of_nonneg_right (small_factor_product _ P hB) (by positivity)
    _ = _ := by rw [prime_factor_product n hn0 eps]

theorem divisor_power_subpower (C : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ)^C ≤ A*(n : ℝ)^eps := by
  let delta : ℝ := eps/((C : ℝ)+1)
  have hden : 0 < (C : ℝ)+1 := by positivity
  have hd : 0 < delta := div_pos heps hden
  obtain ⟨A,hA,hbound⟩ := divisor_subpower hd
  refine ⟨A^C,pow_pos hA _,?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hde : delta*(C : ℝ) ≤ eps := by
    have he : delta*((C : ℝ)+1) = eps := by dsimp [delta]; field_simp
    nlinarith

  calc
    _ ≤ (A*(n : ℝ)^delta)^C := pow_le_pow_left₀ (Nat.cast_nonneg _) (hbound n hn) C
    _ = A^C*(n : ℝ)^(delta*(C : ℝ)) := by
      rw [mul_pow,Real.rpow_mul_natCast (Nat.cast_nonneg n)]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn1 hde) (pow_nonneg hA.le _)

end ErdosDivisorBounds

end

section

namespace ErdosHyperbolaWeighted

theorem divisor_log_square_subpower (C : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∃ A : ℝ, 0 < A ∧ ∀ N : ℕ, 1 ≤ N →
      (N.divisors.card : ℝ)^C*(Real.log (2*(N : ℝ)))^2 ≤ A*(N : ℝ)^eps := by
  let alpha := eps/2
  let beta := eps/4
  have ha : 0 < alpha := by dsimp [alpha] <;> positivity
  have hb : 0 < beta := by dsimp [beta] <;> positivity
  obtain ⟨A, hA, hdiv⟩ := ErdosDivisorBounds.divisor_power_subpower C ha
  let L := (2 : ℝ)^beta/beta
  have hL : 0 < L := by dsimp [L] <;> positivity
  refine ⟨A*L^2, by positivity, ?_⟩
  intro N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlog : 0 ≤ Real.log (2*(N : ℝ)) := Real.log_nonneg (by linarith)
  have hlogbound : (Real.log (2*(N : ℝ)))^2 ≤ L^2*(N : ℝ)^(beta*2) := by
    calc
      _ ≤ (L*(N : ℝ)^beta)^2 := pow_le_pow_left₀ hlog (log_two_mul_le_power hb hNpos) 2
      _ = _ := by
        rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg N)]
        norm_num
  calc
    _ ≤ (A*(N : ℝ)^alpha)*(L^2*(N : ℝ)^(beta*2)) :=
      mul_le_mul (hdiv N hN) hlogbound (sq_nonneg _) (by positivity)
    _ = A*L^2*(N : ℝ)^eps := by
      have he : alpha+beta*2 = eps := by dsimp [alpha,beta] <;> ring
      rw [← he, Real.rpow_add hNpos]
      ring

end ErdosHyperbolaWeighted

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_EulerProductRatio
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceMoments
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem cast_int_residue (M t : ℕ) [NeZero M] (htM : t ∣ M) (n : ℤ) :
    (((n : ZMod M).val : ℕ) : ZMod t) = (n : ZMod t) := by
  have hh := congrArg (ZMod.castHom htM (ZMod t)) (ZMod.natCast_zmod_val (n : ZMod M))
  simpa only [map_natCast,map_intCast] using hh

end ErdosVarianceMoments

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourcePairRemainder
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosHyperbolaError

theorem source_restriction_divides (H T : ℕ) (hH : 0 < H) (hT : Squarefree T)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ T → p ∣ H) : T ∣ H := by
  apply (Nat.factorization_le_iff_dvd hT.ne_zero hH.ne').mp
  intro p
  by_cases hp : p.Prime
  · by_cases hz : T.factorization p = 0
    · rw [hz]
      exact Nat.zero_le _
    · have hpd : p ∣ T := (hp.dvd_iff_one_le_factorization hT.ne_zero).mpr (Nat.pos_of_ne_zero hz)
      exact (hT.natFactorization_le_one p).trans
        ((hp.dvd_iff_one_le_factorization hH.ne').mp (hsupport p hp hpd))
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

theorem source_totient_product (H T : ℕ) (hTH : T ∣ H) (hT : 0 < T) :
    (H*T).totient = T*H.totient := by
  have h := Nat.totient_gcd_mul_totient_mul H T
  rw [Nat.gcd_eq_right_iff_dvd.mpr hTH] at h
  have he : T.totient*(H*T).totient = T.totient*(T*H.totient) := by
    calc
      _ = H.totient*T.totient*T := h
      _ = _ := by ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.totient_pos.mpr hT) he

end ErdosHyperbolaError

end

section

open scoped BigOperators
namespace ErdosHyperbolaError

open ErdosHyperbolaIdentities

theorem completionConstant_pos : 0 < completionConstant := by
  have h := ErdosHyperbola.harmonicConstant_pos
  unfold completionConstant
  positivity

end ErdosHyperbolaError

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_HarmonicLevelBound
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceLargeCount
open NumberTheoryLean ErdosHyperbolaError
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem real_level_card_bound (P : Finset ℕ) (v s : ℝ) (hD : 1 ≤ v^s) :
    ((RealFundamentalSieve.levelDivisors P v s).card : ℝ) ≤ 2*(v^s) := by
  have hsub : RealFundamentalSieve.levelDivisors P v s ⊆ Finset.range (⌊v^s⌋₊+1) := by
    intro d hd
    have hb := (Finset.mem_filter.mp hd).2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_floor_iff (by linarith)).mpr hb))
  have hc : ((RealFundamentalSieve.levelDivisors P v s).card : ℝ) ≤ ((⌊v^s⌋₊+1 : ℕ) : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_range _)
  have hf := Nat.floor_le (show 0 ≤ v^s by linarith)
  push_cast at hc
  linarith

theorem real_level_reciprocal_bound (P : Finset ℕ) (v s : ℝ) (hD : 1 ≤ v^s) :
    (∑ d ∈ RealFundamentalSieve.levelDivisors P v s,1/(d : ℝ)) ≤ 1+Real.log (v^s) := by
  have hsub : RealFundamentalSieve.levelDivisors P v s ⊆ Finset.Icc 1 ⌊v^s⌋₊ := by
    intro d hd
    obtain ⟨hddiv,hdlev⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hddiv,(Nat.le_floor_iff (by linarith)).mpr hdlev⟩
  have hh := harmonic_floor_le_one_add_log (v^s) hD
  have hh' : (∑ d ∈ Finset.Icc 1 ⌊v^s⌋₊,1/(d : ℝ)) ≤ 1+Real.log (v^s) := by
    simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div] using hh
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans hh'

theorem hyperbolaEnvelope_nonneg (H T0 : ℕ) : 0 ≤ hyperbolaEnvelope H T0 := by
  have hC := completionConstant_pos.le
  dsimp [hyperbolaEnvelope]
  positivity

theorem hyperbola_level_sum_bound (H T0 : ℕ) (P : Finset ℕ) (v s U V : ℝ)
    (hD : 1 ≤ v^s) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    (∑ d ∈ RealFundamentalSieve.levelDivisors P v s,
      hyperbolaEnvelope H T0*(1+U/((d : ℝ)*((H*T0 : ℕ) : ℝ))+V/((H*T0 : ℕ) : ℝ))) ≤
        hyperbolaEnvelope H T0*(2*(v^s)*(1+V/((H*T0 : ℕ) : ℝ))+
          (U/((H*T0 : ℕ) : ℝ))*(1+Real.log (v^s))) := by
  let F := RealFundamentalSieve.levelDivisors P v s
  let N : ℝ := (H*T0 : ℕ)
  have he (d : ℕ) : 1+U/((d : ℝ)*N)+V/N = (1+V/N)+(U/N)*(1/(d : ℝ)) := by ring
  have hsum : (∑ d ∈ F,hyperbolaEnvelope H T0*(1+U/((d : ℝ)*N)+V/N)) =
      hyperbolaEnvelope H T0*((F.card : ℝ)*(1+V/N)+(U/N)*(∑ d ∈ F,1/(d : ℝ))) := by
    rw [← Finset.mul_sum]
    simp_rw [he]
    rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum]
  rw [hsum]
  apply mul_le_mul_of_nonneg_left _ (hyperbolaEnvelope_nonneg H T0)
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (real_level_card_bound P v s hD) (by positivity)
  · exact mul_le_mul_of_nonneg_left (real_level_reciprocal_bound P v s hD) (by positivity)

end ErdosVarianceLargeCount

end

end Erdos970

end OAI
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

end ErdosInversePrimeBin

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ResidueCountDifference
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970



namespace ErdosPrimeInputs.SubsetPrimeSieve

open Finset
open NumberTheoryLean
open SmallSieveFinite IntervalBoundingSieve

theorem euler_pos {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime) : 0 < euler P := by
  apply prod_pos
  intro p hp
  have hp1 : (1:ℝ) < p := by exact_mod_cast (hprime p hp).one_lt
  exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1)

end ErdosPrimeInputs.SubsetPrimeSieve



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

open _root_.Filter
open scoped Topology

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

namespace ErdosVarianceSmallModel
open NumberTheoryLean ErdosInverseEuler ErdosHyperbolaError
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem pattern_moduli_product (w : ℝ) (H : ℕ) :
    divisorModulus w H*coprimeModulus w H = smallModulus w := by
  unfold divisorModulus coprimeModulus divisorPrimes coprimePrimes
  rw [Finset.prod_filter_mul_prod_filter_not]
  rfl

end ErdosVarianceSmallModel

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

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseEuler
open ErdosInverseBoxHeight

theorem exp_loglog_sq_le_sourceZ (C eps : ℝ) (hC : 0 ≤ C) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop,
      Real.exp (C*(Real.log (Real.log z))^2) ≤ (sourceZ z)^eps := by
  have hC1 : 0 < C+1 := by linarith
  have hs := (isLittleO_log_rpow_rpow_atTop (3 : ℝ) zero_lt_one).bound
    (div_pos heps hC1)
  filter_upwards [Real.tendsto_log_atTop.eventually hs,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_gt_atTop 1]
    with z hz hLL hL
  have hLL0 : 0 < Real.log (Real.log z) := by change 1 ≤ Real.log (Real.log z) at hLL;linarith
  have hL0 : 0 < Real.log z := by linarith
  have hcube : (Real.log (Real.log z))^3 ≤ (eps/(C+1))*Real.log z := by
    simpa only [Real.norm_eq_abs,Real.rpow_ofNat,Real.rpow_one,
      abs_of_nonneg (pow_nonneg hLL0.le 3),abs_of_nonneg hL0.le] using hz
  have hpay : C*(Real.log (Real.log z))^3 ≤ eps*Real.log z := by
    have hm := (le_div_iff₀ hC1).mp (show (Real.log (Real.log z))^3 ≤ (eps*Real.log z)/(C+1) by
      simpa only [div_mul_eq_mul_div] using hcube)
    nlinarith [pow_nonneg hLL0.le 3]
  rw [sourceZ,← Real.exp_mul]
  apply Real.exp_le_exp.mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hLL0).mpr
  nlinarith only [hpay]

theorem log_pow_le_sourceZ (r : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop, (Real.log z)^r ≤ (sourceZ z)^eps := by
  filter_upwards [exp_loglog_sq_le_sourceZ r eps (Nat.cast_nonneg _) heps,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_gt_atTop 1]
    with z hz hLL hL
  have hLL1 : 1 ≤ Real.log (Real.log z) := hLL
  have hLL0 : 0 < Real.log (Real.log z) := by linarith
  have hL0 : 0 < Real.log z := by linarith
  calc
    (Real.log z)^r = (Real.exp (Real.log (Real.log z)))^r := by rw [Real.exp_log hL0]
    _ = Real.exp ((r : ℝ)*Real.log (Real.log z)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp ((r : ℝ)*(Real.log (Real.log z))^2) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (by nlinarith) (Nat.cast_nonneg _)
    _ ≤ _ := hz

theorem sourceZ_tendsto_atTop : Tendsto sourceZ atTop atTop := by
  have hlow : (fun z : ℝ => Real.log z) ≤ᶠ[atTop] sourceZ := by
    filter_upwards [log_pow_le_sourceZ 1 1 zero_lt_one] with z hz
    simpa only [pow_one,Real.rpow_one] using hz
  exact tendsto_atTop_mono' atTop hlow Real.tendsto_log_atTop

end ErdosInverseEuler

end

section

open _root_.Filter
open scoped Topology
namespace ErdosVarianceSmallModel
open ErdosInverseBoxHeight ErdosInverseEuler

theorem source_Z_power_R (alpha beta : ℝ) (n : ℕ) (ha : 0 < alpha) (hb : 0 < beta) (hn : 0 < n) :
    ∀ᶠ z : ℝ in atTop,1 < z ∧ ∀ R : ℝ,z^alpha ≤ R → (sourceZ z)^n ≤ R^beta := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  filter_upwards [sourceZ_le_rpow (alpha*beta/(n : ℝ)) (by positivity)] with z hz
  refine ⟨hz.1,?_⟩
  intro R hR
  have hz0 : 0 < z := by linarith [hz.1]
  calc
    _ ≤ (z^(alpha*beta/(n : ℝ)))^n := pow_le_pow_left₀ (Real.exp_pos _).le hz.2 n
    _ = z^(alpha*beta) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hz0.le]
      congr 1
      field_simp
    _ ≤ _ := by
      have hh := Real.rpow_le_rpow (Real.rpow_nonneg hz0.le alpha) hR hb.le
      simpa only [← Real.rpow_mul hz0.le] using hh

end ErdosVarianceSmallModel

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ConditionalPatternCounts
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosLargePatternLaw
open ErdosVarianceSmallModel

attribute [local instance] Classical.propDecidable

theorem pattern_card (w : ℝ) (H : ℕ) : Fintype.card (FullPattern w H) =
    (divisorModulus w H).totient*divisorModulus w H*(coprimeModulus w H).totient*coprimeModulus w H := by
  simp only [FullPattern,Fintype.card_prod,ZMod.card_units_eq_totient,ZMod.card]
  ring

theorem weight_positive (w : ℝ) (H : ℕ) : 0 < weight w H := by
  have hT0 := divisorModulus_pos w H
  have hT1 := coprimeModulus_pos w H
  have hP0 := Nat.totient_pos.mpr hT0
  have hP1 := Nat.totient_pos.mpr hT1
  unfold weight
  positivity

end ErdosLargePatternLaw



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_TagSubbinWidths
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosTagSubbins

theorem left_lt_right {R theta : ℝ} {N i : ℕ} (hR : 0 < R) (ht : 0 < theta)
    (hN : 0 < N) : left R theta N i < right R theta N i := by
  rw [right_eq_left_add]; linarith [step_pos hR ht hN]

end ErdosTagSubbins

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_HeightBlockCount
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosLargeHeightBlocks

theorem blockCount_lower (C0 : ℤ) (R xi : ℝ) (H : ℕ) :
    xi*|(C0 : ℝ)|/(R*(H : ℝ)) ≤ (blockCount C0 R xi H : ℝ) := by
  apply (Nat.le_ceil _).trans
  unfold blockCount
  exact_mod_cast le_max_right 1 ⌈xi*|(C0 : ℝ)|/(R*(H : ℝ))⌉₊

theorem blockCount_upper (C0 : ℤ) (R xi : ℝ) (H : ℕ)
    (hR : 0 < R) (hxi : 0 ≤ xi) (hH : 0 < H) :
    (blockCount C0 R xi H : ℝ) ≤ 1+xi*|(C0 : ℝ)|/(R*(H : ℝ)) := by
  have hx : 0 ≤ xi*|(C0 : ℝ)|/(R*(H : ℝ)) := by positivity
  have hc := Nat.ceil_lt_add_one hx
  rw [blockCount,Nat.cast_max,Nat.cast_one]
  apply max_le <;> linarith

theorem blockCount_source_bound (C0 : ℤ) (R xi Z : ℝ) (H : ℕ)
    (hR : 0 < R) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1) (hH : 0 < H) (hZ : 2 ≤ Z)
    (hsize : max (H : ℝ) (|(C0 : ℝ)|/R)/(H : ℝ) ≤ Z^12) :
    (blockCount C0 R xi H : ℝ) ≤ Z^13 := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hc : |(C0 : ℝ)|/(R*(H : ℝ)) ≤ Z^12 := by
    have h := (div_le_div_of_nonneg_right (le_max_right (H : ℝ) (|(C0 : ℝ)|/R)) hHr.le).trans hsize
    simpa only [div_div] using h
  have hx : xi*|(C0 : ℝ)|/(R*(H : ℝ)) ≤ Z^12 := by
    have h := mul_le_mul_of_nonneg_right hxi1 (show 0 ≤ |(C0 : ℝ)|/(R*(H : ℝ)) by positivity)
    have he : xi*|(C0 : ℝ)|/(R*(H : ℝ))=xi*(|(C0 : ℝ)|/(R*(H : ℝ))) := by ring
    rw [he]
    exact h.trans (by simpa only [one_mul] using hc)
  have hz0 : 0 ≤ Z := by linarith
  have hpow : 1 ≤ Z^12 := one_le_pow₀ (by linarith)
  have hzstep : 1+Z^12 ≤ Z^13 := by
    have hh := mul_le_mul_of_nonneg_right hZ (pow_nonneg hz0 12)
    rw [show Z*Z^12=Z^13 by ring] at hh
    linarith
  calc
    _ ≤ 1+xi*|(C0 : ℝ)|/(R*(H : ℝ)) := blockCount_upper C0 R xi H hR hxi hH
    _ ≤ 1+Z^12 := by linarith
    _ ≤ _ := hzstep

end ErdosLargeHeightBlocks


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_CommonSliceGeometry
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosCommonParameterInterval

theorem div_between_endpoints (a : ℝ) {R p T : ℝ} (hR : 0 < R)
    (hRp : R ≤ p) (hpT : p ≤ T) :
    min (a/R) (a/T) ≤ a/p ∧ a/p ≤ max (a/R) (a/T) := by
  have hp : 0 < p := hR.trans_le hRp
  have hT : 0 < T := hp.trans_le hpT
  by_cases ha : 0 ≤ a
  · exact ⟨(min_le_right _ _).trans (div_le_div_of_nonneg_left ha hp hpT),
      (div_le_div_of_nonneg_left ha hR hRp).trans (le_max_left _ _)⟩
  · have han : 0 ≤ -a := by linarith
    have h1 := div_le_div_of_nonneg_left han hp hpT
    have h2 := div_le_div_of_nonneg_left han hR hRp
    simp only [neg_div] at h1 h2
    exact ⟨(min_le_left _ _).trans (by linarith),
      (show a/p ≤ a/T by linarith).trans (le_max_right _ _)⟩

end ErdosCommonParameterInterval



namespace ErdosLargeHeightBlocks

theorem block_reciprocal_variation (C0 : ℤ) (R xi : ℝ) (H i : ℕ)
    (hR : 0 < R) (hxi : 0 < xi) (hH : 0 < H) :
    |(C0 : ℝ)/blockLeft C0 R xi H i-(C0 : ℝ)/blockRight C0 R xi H i| ≤ (H : ℝ) := by
  let N := blockCount C0 R xi H
  let a := blockLeft C0 R xi H i
  let b := blockRight C0 R xi H i
  have hN : 0 < N := blockCount_pos C0 R xi H
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hs := ErdosTagSubbins.step_pos hR hxi hN
  have ha : R ≤ a := ErdosTagSubbins.left_lower hs.le
  have hab : a < b := ErdosTagSubbins.left_lt_right hR hxi hN
  have hb : R ≤ b := ha.trans hab.le
  have ha0 : 0 < a := hR.trans_le ha
  have hb0 : 0 < b := hR.trans_le hb
  have hd : b-a = ErdosTagSubbins.step R xi N := ErdosTagSubbins.right_sub_left R xi N i
  have hden : R^2 ≤ a*b := by
    simpa only [pow_two] using mul_le_mul ha hb hR.le ha0.le
  have he : (C0 : ℝ)/a-(C0 : ℝ)/b=(C0 : ℝ)*(b-a)/(a*b) := by
    field_simp
  have hcount := (div_le_iff₀ (mul_pos hR hHr)).mp (blockCount_lower C0 R xi H)
  change |(C0 : ℝ)/a-(C0 : ℝ)/b| ≤ (H : ℝ)
  rw [he,abs_div,abs_mul,abs_of_nonneg (sub_nonneg.mpr hab.le),abs_of_pos (mul_pos ha0 hb0)]
  calc
    _ ≤ |(C0 : ℝ)| * (b-a)/R^2 :=
      div_le_div_of_nonneg_left (mul_nonneg (abs_nonneg _) (sub_nonneg.mpr hab.le)) (sq_pos_of_pos hR) hden
    _ = xi*|(C0 : ℝ)|/(R*(N : ℝ)) := by
      rw [hd]
      dsimp [ErdosTagSubbins.step]
      field_simp
    _ ≤ _ := by
      apply (div_le_iff₀ (mul_pos hR hNr)).mpr
      change xi*|(C0 : ℝ)| ≤ (N : ℝ)*(R*(H : ℝ)) at hcount
      nlinarith

theorem block_coordinate_containment (C0 : ℤ) (R xi : ℝ) (H i : ℕ)
    (hR : 0 < R) (hxi : 0 < xi) (p m : ℝ)
    (hpL : blockLeft C0 R xi H i ≤ p) (hpU : p ≤ blockRight C0 R xi H i)
    (hmL : (C0 : ℝ)/p ≤ m) (hmU : m < (C0 : ℝ)/p+(H : ℝ)) :
    m ∈ Set.Ico (coordinateLower C0 R xi H i) (coordinateUpper C0 R xi H i) := by
  have hL : 0 < blockLeft C0 R xi H i :=
    ErdosTagSubbins.left_pos hR hxi (blockCount_pos C0 R xi H)
  have hb := ErdosCommonParameterInterval.div_between_endpoints (C0 : ℝ) hL hpL hpU
  refine ⟨hb.1.trans hmL,?_⟩
  dsimp only [coordinateUpper]
  linarith [hb.2]

theorem block_coordinate_width (C0 : ℤ) (R xi : ℝ) (H i : ℕ)
    (hR : 0 < R) (hxi : 0 < xi) (hH : 0 < H) :
    coordinateUpper C0 R xi H i-coordinateLower C0 R xi H i ≤ 2*(H : ℝ) := by
  have hv := block_reciprocal_variation C0 R xi H i hR hxi hH
  have he (x y : ℝ) : max x y-min x y=|x-y| := by
    rw [max_sub_min_eq_abs,abs_sub_comm]
  dsimp [coordinateUpper,coordinateLower]
  rw [show max ((C0 : ℝ)/blockLeft C0 R xi H i) ((C0 : ℝ)/blockRight C0 R xi H i)+(H : ℝ)-
      min ((C0 : ℝ)/blockLeft C0 R xi H i) ((C0 : ℝ)/blockRight C0 R xi H i) =
      (max ((C0 : ℝ)/blockLeft C0 R xi H i) ((C0 : ℝ)/blockRight C0 R xi H i)-
      min ((C0 : ℝ)/blockLeft C0 R xi H i) ((C0 : ℝ)/blockRight C0 R xi H i))+(H : ℝ) by ring,
    he]
  linarith

end ErdosLargeHeightBlocks



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_OriginalPrimeBlocks
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosLargeHeightBlocks


theorem mem_blockPrimes (C0 : ℤ) (R xi : ℝ) (H i p : ℕ)
    (hR : 0 < R) (hxi : 0 < xi) :
    p ∈ blockPrimes C0 R xi H i ↔ p.Prime ∧
      blockLeft C0 R xi H i < (p : ℝ) ∧ (p : ℝ) ≤ blockRight C0 R xi H i :=
  ErdosTagSubbins.mem_subbin hR hxi (blockCount_pos C0 R xi H)

theorem block_width_sum (C0 : ℤ) (R xi : ℝ) (H : ℕ) :
    (∑ i : Fin (blockCount C0 R xi H),
      (blockRight C0 R xi H i-blockLeft C0 R xi H i)) = xi*R := by
  simp only [blockRight,blockLeft,ErdosTagSubbins.right_sub_left,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [ErdosTagSubbins.total_step (blockCount_pos C0 R xi H)]
  ring

end ErdosLargeHeightBlocks


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_ActualCoordinateBlocks
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosVarianceEffective

theorem intervalK_lt (p H : ℕ) [NeZero p] (hHp : H.Coprime p) (C0 : ℤ) :
    intervalK p H hHp C0 < p := ZMod.val_lt _

theorem interval_numerator_dvd (p H : ℕ) [NeZero p] (hHp : H.Coprime p) (C0 : ℤ) :
    (p : ℤ) ∣ C0+(H : ℤ)*(intervalK p H hHp C0 : ℤ) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simp only [Int.cast_add,Int.cast_mul,Int.cast_natCast,intervalK,ZMod.natCast_zmod_val]
  have hu : (H : ZMod p)*(↑((ZMod.unitOfCoprime H hHp)⁻¹) : ZMod p) = 1 := by
    simpa only [ZMod.coe_unitOfCoprime] using (ZMod.unitOfCoprime H hHp).mul_inv
  calc
    _ = (C0 : ZMod p)-(C0 : ZMod p)*((H : ZMod p)*↑((ZMod.unitOfCoprime H hHp)⁻¹)) := by ring
    _ = 0 := by rw [hu];ring

theorem intervalM0_identity (p H : ℕ) [NeZero p] (hHp : H.Coprime p) (C0 : ℤ) :
    (p : ℤ)*intervalM0 p H hHp C0 = C0+(H : ℤ)*(intervalK p H hHp C0 : ℤ) := by
  rw [intervalM0,mul_comm]
  exact Int.ediv_mul_cancel (interval_numerator_dvd p H hHp C0)

theorem intervalM0_bounds (p H : ℕ) [NeZero p] (hHp : H.Coprime p) (C0 : ℤ) (hH : 0 < H) :
    (C0 : ℝ)/(p : ℝ) ≤ (intervalM0 p H hHp C0 : ℝ) ∧
      (intervalM0 p H hHp C0 : ℝ) < (C0 : ℝ)/(p : ℝ)+(H : ℝ) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  have hk0 : (0 : ℝ) ≤ intervalK p H hHp C0 := Nat.cast_nonneg _
  have hkp : (intervalK p H hHp C0 : ℝ) < p := by exact_mod_cast intervalK_lt p H hHp C0
  have he : (p : ℝ)*(intervalM0 p H hHp C0 : ℝ) = (C0 : ℝ)+(H : ℝ)*(intervalK p H hHp C0 : ℝ) := by
    exact_mod_cast intervalM0_identity p H hHp C0
  have hd : (C0 : ℝ)/(p : ℝ)*(p : ℝ) = C0 := div_mul_cancel₀ _ hp.ne'
  constructor
  · apply (div_le_iff₀ hp).mpr
    nlinarith
  · have hmul := mul_lt_mul_of_pos_left hkp hH'
    nlinarith

end ErdosVarianceEffective



namespace ErdosLargeHeightBlocks


theorem actual_m0_block_interval (C0 : ℤ) (R xi : ℝ) (H i p : ℕ) [NeZero p]
    (hR : 0 < R) (hxi : 0 < xi) (hH : 0 < H) (hHp : H.Coprime p)
    (hp : p ∈ blockPrimes C0 R xi H i) :
    (ErdosVarianceEffective.intervalM0 p H hHp C0 : ℝ) ∈
      Set.Ico (coordinateLower C0 R xi H i) (coordinateUpper C0 R xi H i) ∧
      coordinateUpper C0 R xi H i-coordinateLower C0 R xi H i ≤ 2*(H : ℝ) := by
  have hb := (mem_blockPrimes C0 R xi H i p hR hxi).mp hp
  have hm := ErdosVarianceEffective.intervalM0_bounds p H hHp C0 hH
  exact ⟨block_coordinate_containment C0 R xi H i hR hxi p _ hb.2.1.le hb.2.2 hm.1 hm.2,
    block_coordinate_width C0 R xi H i hR hxi hH⟩

end ErdosLargeHeightBlocks


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeProductOmissions
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosPrimeInputs.PrimeProductOmissions

open _root_.Finset
open NumberTheoryLean.LargePrimeDeletion SubsetPrimeSieve MertensStrong

lemma factor_bounds {p : ℕ} (hp : p.Prime) :
    0 < 1 - (p : ℝ)⁻¹ ∧ 1 - (p : ℝ)⁻¹ ≤ 1 := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  exact ⟨sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1), sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg _))⟩

lemma totient_euler (q : ℕ) : (q.totient : ℝ) = (q : ℝ) * euler q.primeFactors := by
  unfold euler
  have h := congrArg (fun r : ℚ => (r : ℝ)) (Nat.totient_eq_mul_prod_factors q)
  push_cast at h
  exact h

theorem euler_omissions_le (P : Finset ℕ) (q : ℕ) (hq : 0 < q)
    (hP : ∀ p ∈ P, p.Prime) : euler (P \ q.primeFactors) ≤ euler P * q / q.totient := by
  have hQ : ∀ p ∈ q.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hsmall : euler q.primeFactors ≤ euler (P ∩ q.primeFactors) := by
    apply prod_le_prod_of_subset_of_le_one inter_subset_right
    · intro p hp
      exact (factor_bounds (hQ p hp)).1.le
    · intro p hp _
      exact (factor_bounds (hQ p hp)).2
  have hdiff : P \ (P ∩ q.primeFactors) = P \ q.primeFactors := by
    ext p
    simp
  have hprod : euler (P \ q.primeFactors) * euler (P ∩ q.primeFactors) = euler P := by
    unfold euler
    rw [← hdiff]
    exact prod_sdiff inter_subset_left
  have he : euler (P \ q.primeFactors) * euler q.primeFactors ≤ euler P :=
    (mul_le_mul_of_nonneg_left hsmall
      (euler_pos (fun p hp => hP p (mem_sdiff.mp hp).1)).le).trans_eq hprod
  have hqR : 0 < (q:ℝ) := by exact_mod_cast hq
  have htR : 0 < (q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  apply (le_div_iff₀ htR).mpr
  rw [totient_euler q]
  nlinarith [mul_le_mul_of_nonneg_right he hqR.le]

lemma cutoff_euler_eq (x : ℝ) : euler (cutoffPrimes ⌊x⌋₊) = primeProduct x := by
  have hs : cutoffPrimes ⌊x⌋₊ = (Ioc 0 ⌊x⌋₊).filter Nat.Prime := by
    ext p
    simp only [mem_cutoffPrimes,mem_filter,mem_Ioc]
    constructor
    · rintro ⟨hp,hle⟩
      exact ⟨⟨hp.pos,hle⟩,hp⟩
    · rintro ⟨⟨_,hle⟩,hp⟩
      exact ⟨hp,hle⟩
  unfold euler primeProduct
  rw [hs]
  simp only [one_div]

theorem prime_product_upper : ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧
    ∀ x : ℝ, x₀ ≤ x → primeProduct x ≤ C / Real.log x := by
  obtain ⟨c,K,x₀,hc,hK,hx₀,h⟩ := prime_product_strong
  refine ⟨(K+1)*Real.exp (-Real.eulerMascheroniConstant),x₀,by positivity,hx₀,?_⟩
  intro x hx
  have hx1 : 1 < x := by linarith [hx₀.trans hx]
  have hl := Real.log_pos hx1
  have hd : Real.exp (-c * Real.sqrt (Real.log x)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have := Real.sqrt_nonneg (Real.log x)
    nlinarith)
  have hh := (abs_le.mp (h x hx)).2
  have hu : primeProduct x / (Real.exp (-Real.eulerMascheroniConstant) / Real.log x) ≤ K+1 := by
    nlinarith [mul_le_mul_of_nonneg_left hd hK.le]
  have hmul := (div_le_iff₀ (div_pos (Real.exp_pos _) hl)).mp hu
  simpa only [mul_div_assoc] using hmul

theorem reduced_product_upper : ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧
    ∀ x : ℝ, x₀ ≤ x → ∀ q : ℕ, 0 < q →
      euler (reducedPrimes ⌊x⌋₊ q) ≤ C * ((q : ℝ) / q.totient) / Real.log x := by
  obtain ⟨C,x₀,hC,hx₀,h⟩ := prime_product_upper
  refine ⟨C,x₀,hC,hx₀,?_⟩
  intro x hx q hq
  have ht0 : 0 ≤ (q.totient : ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ euler (cutoffPrimes ⌊x⌋₊) * q / q.totient :=
      euler_omissions_le _ q hq (fun p hp => (mem_cutoffPrimes.mp hp).1)
    _ = primeProduct x * q / q.totient := by rw [cutoff_euler_eq]
    _ ≤ (C / Real.log x) * q / q.totient := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (h x hx) (Nat.cast_nonneg _)) ht0
    _ = _ := by ring

end ErdosPrimeInputs.PrimeProductOmissions

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeEventCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceSmallModel
open ErdosVarianceEffective
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem primeMK_identity (P : Finset ℕ) (H : ℕ) (C0 : ℤ) (hP : ∀ p ∈ P,p.Prime)
    (p : goodPrimes P H) :
    (p.val : ℤ)*primeM P H C0 hP p = C0+(H : ℤ)*(primeK P H C0 hP p : ℤ) := by
  let : NeZero p.val := ⟨(hP _ (Finset.mem_filter.mp p.property).1).ne_zero⟩
  exact intervalM0_identity p.val H (Finset.mem_filter.mp p.property).2 C0

end ErdosVarianceSmallModel

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ResidueProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceMoments
open ErdosVarianceSmallModel

theorem cast_nat_residue (M t n : ℕ) [NeZero M] (htM : t ∣ M) :
    (((n : ZMod M).val : ℕ) : ZMod t) = (n : ZMod t) := by
  have hh : Nat.ModEq M (n : ZMod M).val n := (ZMod.natCast_eq_natCast_iff _ _ _).mp
    (ZMod.natCast_zmod_val (n : ZMod M))
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.ModEq.of_dvd htM hh)

theorem primePoint_pValue (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (p : goodPrimes P H) (t : ℕ) (ht : t ∣ coprimeModulus w H) :
    patternPValue w H (primePoint P w H C0 hw hP hlarge p).2 t = (p.val : ZMod t) := by
  exact cast_nat_residue (coprimeModulus w H) t p.val ht

end ErdosVarianceMoments

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_FullPatternCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceLargeMap
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceMoments
attribute [local instance] Classical.propDecidable

theorem full_p0_projection (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (p : goodPrimes P H) (t : ℕ) (ht : t ∣ divisorModulus w H) :
    ((actualFullPattern P w H C0 hw hP hlarge p).1.val.val : ZMod t) = (p.val : ZMod t) :=
  cast_nat_residue (divisorModulus w H) t p.val ht

theorem full_k0_projection (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (p : goodPrimes P H) (t : ℕ) (ht : t ∣ divisorModulus w H) :
    ((actualFullPattern P w H C0 hw hP hlarge p).2.1.val : ZMod t) = (primeK P H C0 hP p : ZMod t) :=
  cast_nat_residue (divisorModulus w H) t (primeK P H C0 hP p) ht

theorem full_p1_projection (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (p : goodPrimes P H) (t : ℕ) (ht : t ∣ coprimeModulus w H) :
    ((actualFullPattern P w H C0 hw hP hlarge p).2.2.1.val.val : ZMod t) = (p.val : ZMod t) :=
  primePoint_pValue P w H C0 hw hP hlarge p t ht

theorem full_m1_projection (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (p : goodPrimes P H) (t : ℕ) (ht : t ∣ coprimeModulus w H) :
    ((actualFullPattern P w H C0 hw hP hlarge p).2.2.2.val : ZMod t) = (primeM P H C0 hP p : ZMod t) :=
  cast_int_residue (coprimeModulus w H) t ht (primeM P H C0 hP p)

end ErdosVarianceLargeMap

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_FullPatternCongruences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceLargeMap
open ErdosVarianceSmallModel ErdosVarianceMoments
attribute [local instance] Classical.propDecidable

theorem full_pattern_units (w : ℝ) (H : ℕ) (v : ErdosLargePatternLaw.FullPattern w H) :
    Int.gcd (v.1.val.val : ℤ) (divisorModulus w H : ℤ) = 1 ∧
      Int.gcd (v.2.2.1.val.val : ℤ) (coprimeModulus w H : ℤ) = 1 := by
  constructor
  · simpa only [Int.gcd_def,Int.natAbs_natCast] using (ZMod.val_coe_unit_coprime v.1).gcd_eq_one
  · simpa only [Int.gcd_def,Int.natAbs_natCast] using (ZMod.val_coe_unit_coprime v.2.2.1).gcd_eq_one

theorem full_pattern_residue_congruences (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ)) (p : goodPrimes P H) :
    let v := actualFullPattern P w H C0 hw hP hlarge p
    Int.ModEq (divisorModulus w H : ℤ) (p.val : ℤ) (v.1.val.val : ℤ) ∧
    Int.ModEq (coprimeModulus w H : ℤ) (p.val : ℤ) (v.2.2.1.val.val : ℤ) ∧
    Int.ModEq (coprimeModulus w H : ℤ) (primeM P H C0 hP p) (v.2.2.2.val : ℤ) := by
  dsimp only
  constructor
  · rw [← ZMod.intCast_eq_intCast_iff]
    simpa only [Int.cast_natCast] using (full_p0_projection P w H C0 hw hP hlarge p _ dvd_rfl).symm
  · constructor
    · rw [← ZMod.intCast_eq_intCast_iff]
      simpa only [Int.cast_natCast] using (full_p1_projection P w H C0 hw hP hlarge p _ dvd_rfl).symm
    · rw [← ZMod.intCast_eq_intCast_iff]
      simpa only [Int.cast_natCast] using (full_m1_projection P w H C0 hw hP hlarge p _ dvd_rfl).symm

theorem full_pattern_product_congruence (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ)) (p : goodPrimes P H) :
    let v := actualFullPattern P w H C0 hw hP hlarge p
    Int.ModEq ((H*divisorModulus w H : ℕ) : ℤ) ((p.val : ℤ)*primeM P H C0 hP p)
      (C0+(H : ℤ)*(v.2.1.val : ℤ)) := by
  dsimp only
  have hk : Int.ModEq (divisorModulus w H : ℤ)
      ((actualFullPattern P w H C0 hw hP hlarge p).2.1.val : ℤ) (primeK P H C0 hP p : ℤ) := by
    rw [← ZMod.intCast_eq_intCast_iff]
    simpa only [Int.cast_natCast] using full_k0_projection P w H C0 hw hP hlarge p _ dvd_rfl
  obtain ⟨u,hu⟩ := Int.modEq_iff_add_fac.mp hk
  apply Int.ModEq.symm
  apply Int.modEq_iff_add_fac.mpr
  refine ⟨u,?_⟩
  rw [primeMK_identity,hu]
  push_cast
  ring

end ErdosVarianceLargeMap

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_OriginalPairMembership
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceLargeMap
open ErdosVarianceSmallModel ErdosHyperbolaError
attribute [local instance] Classical.propDecidable

theorem mem_open_closed_integer_interval (x y : ℝ) (n : ℤ) :
    n ∈ realIntervalIntegers x y false true ↔ x < (n : ℝ) ∧ (n : ℝ) ≤ y := by
  simp only [realIntervalIntegers,Finset.mem_filter,Finset.mem_Icc,Int.ceil_le,Int.le_floor,
    Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨⟨h.1.le,h.2⟩,h⟩

theorem mem_closed_open_integer_interval (x y : ℝ) (n : ℤ) :
    n ∈ realIntervalIntegers x y true false ↔ x ≤ (n : ℝ) ∧ (n : ℝ) < y := by
  simp only [realIntervalIntegers,Finset.mem_filter,Finset.mem_Icc,Int.ceil_le,Int.le_floor,
    Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨⟨h.1,h.2.le⟩,h⟩

theorem original_pair_mem_sourcePairs (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ)) (p : goodPrimes P H)
    (x0 x1 y0 y1 : ℝ) (hp : x0 < (p.val : ℝ) ∧ (p.val : ℝ) ≤ x1)
    (hm : y0 ≤ (primeM P H C0 hP p : ℝ) ∧ (primeM P H C0 hP p : ℝ) < y1) :
    let v := actualFullPattern P w H C0 hw hP hlarge p
    ((p.val : ℤ),primeM P H C0 hP p) ∈
      sourcePairs H (divisorModulus w H) (coprimeModulus w H) C0 (v.2.1.val : ℤ)
        (v.1.val.val : ℤ) (v.2.2.1.val.val : ℤ) (v.2.2.2.val : ℤ) 1 x0 x1 y0 y1 false true true false := by
  dsimp only
  have hres := full_pattern_residue_congruences P w H C0 hw hP hlarge p
  have hprod := full_pattern_product_congruence P w H C0 hw hP hlarge p
  unfold sourcePairs
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,by simp only [Nat.cast_one,one_dvd,true_and];exact ⟨hres.1,hres.2.1,hres.2.2,hprod⟩⟩
  · exact (mem_open_closed_integer_interval x0 x1 (p.val : ℤ)).mpr (by exact_mod_cast hp)
  · exact (mem_closed_open_integer_interval y0 y1 (primeM P H C0 hP p)).mpr hm

theorem original_prime_pair_injective (P : Finset ℕ) (H : ℕ) (C0 : ℤ) (hP : ∀ p ∈ P,p.Prime) :
    Function.Injective (fun p : goodPrimes P H => ((p.val : ℤ),primeM P H C0 hP p)) := by
  intro p q he
  apply Subtype.ext
  have hh : (p.val : ℤ) = (q.val : ℤ) := congrArg Prod.fst he
  exact Int.ofNat.inj hh

end ErdosVarianceLargeMap

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_PatternMainTerm
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
namespace ErdosVarianceLargeCount
open NumberTheoryLean ErdosHyperbolaError ErdosPrimeInputs.PrimeProductOmissions
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem patternCard_pos (T0 T1 : ℕ) (hT0 : 0 < T0) (hT1 : 0 < T1) : 0 < patternCard T0 T1 := by
  unfold patternCard
  exact mul_pos (mul_pos (mul_pos hT0 (Nat.totient_pos.mpr hT0)) hT1) (Nat.totient_pos.mpr hT1)

theorem sourceMain_totient_cancellation (H T0 T1 : ℕ) (hH : 0 < H) (hT0 : 0 < T0) (hT1 : 0 < T1)
    (hT0H : T0 ∣ H) (hcop : H.Coprime T1) (U V : ℝ) :
    sourceMain H T0 T1 U V*((H*T1 : ℕ) : ℝ)/((H*T1).totient : ℝ) =
      U*(V/(H : ℝ))/(patternCard T0 T1 : ℝ) := by
  have hHN : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  have h0N : (T0 : ℝ) ≠ 0 := by exact_mod_cast hT0.ne'
  have h1N : (T1 : ℝ) ≠ 0 := by exact_mod_cast hT1.ne'
  have hph : (H.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hH).ne'
  have hp0 : (T0.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hT0).ne'
  have hp1 : (T1.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hT1).ne'
  unfold sourceMain patternCard
  rw [source_totient_product H T0 hT0H hT0,Nat.totient_mul hcop]
  push_cast
  field_simp

theorem source_main_uniform_upper : ∃ C v0 : ℝ,0 < C ∧ 2 ≤ v0 ∧
    ∀ v : ℝ,v0 ≤ v → ∀ (H T0 T1 : ℕ),0 < H → 0 < T0 → 0 < T1 →
      T0 ∣ H → H.Coprime T1 → ∀ (U V s : ℝ),0 ≤ U → 0 ≤ V → V ≤ 2*(H : ℝ) → 0 ≤ s →
      sourceMain H T0 T1 U V*
        (∏ t ∈ reducedPrimes ⌊v⌋₊ (H*T1),(1-1/(t : ℝ)))*
          (1+Real.exp (-s/96)) ≤ C*U/((patternCard T0 T1 : ℝ)*Real.log v) := by
  obtain ⟨C,v0,hC,hv0,hEuler⟩ := reduced_product_upper
  refine ⟨4*C,v0,by positivity,hv0,?_⟩
  intro v hv H T0 T1 hH hT0 hT1 hT0H hcop U V s hU hV hVH hs
  have hv1 : 1 < v := by linarith
  have hlog : 0 < Real.log v := Real.log_pos hv1
  have hHN : (0 : ℝ) < H := by exact_mod_cast hH
  have hpat : (0 : ℝ) < patternCard T0 T1 := by exact_mod_cast patternCard_pos T0 T1 hT0 hT1
  have hX : 0 ≤ sourceMain H T0 T1 U V := by dsimp [sourceMain] <;> positivity
  have he := hEuler v hv (H*T1) (mul_pos hH hT1)
  have hmul := mul_le_mul_of_nonneg_left he hX
  have heq : sourceMain H T0 T1 U V*(C*(((H*T1 : ℕ) : ℝ)/((H*T1).totient : ℝ))/Real.log v) =
      C*(U*(V/(H : ℝ))/(patternCard T0 T1 : ℝ))/Real.log v := by
    rw [show sourceMain H T0 T1 U V*(C*(((H*T1 : ℕ) : ℝ)/((H*T1).totient : ℝ))/Real.log v) =
      C*(sourceMain H T0 T1 U V*((H*T1 : ℕ) : ℝ)/((H*T1).totient : ℝ))/Real.log v by ring,
      sourceMain_totient_cancellation H T0 T1 hH hT0 hT1 hT0H hcop]
  have hEuler' : sourceMain H T0 T1 U V*
      (∏ t ∈ reducedPrimes ⌊v⌋₊ (H*T1),(1-1/(t : ℝ))) ≤
        C*(U*(V/(H : ℝ))/(patternCard T0 T1 : ℝ))/Real.log v := by
    simpa only [ErdosPrimeInputs.SubsetPrimeSieve.euler,one_div] using hmul.trans_eq heq
  have hVdiv : V/(H : ℝ) ≤ 2 := (div_le_iff₀ hHN).mpr hVH
  have hEexp : 1+Real.exp (-s/96) ≤ 2 := by
    have hh : Real.exp (-s/96) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have hm1 := mul_le_mul_of_nonneg_right hEuler' (show 0 ≤ 1+Real.exp (-s/96) by positivity)
  have hm2 := mul_le_mul_of_nonneg_left hEexp
    (show 0 ≤ C*(U*(V/(H : ℝ))/(patternCard T0 T1 : ℝ))/Real.log v by positivity)
  have hlast : (C*(U*(V/(H : ℝ))/(patternCard T0 T1 : ℝ))/Real.log v)*2 ≤
      (4*C)*U/((patternCard T0 T1 : ℝ)*Real.log v) := by
    calc
      _ = (2*C*U/((patternCard T0 T1 : ℝ)*Real.log v))*(V/(H : ℝ)) := by ring
      _ ≤ (2*C*U/((patternCard T0 T1 : ℝ)*Real.log v))*2 :=
        mul_le_mul_of_nonneg_left hVdiv (by positivity)
      _ = _ := by ring
  exact hm1.trans (hm2.trans hlast)

end ErdosVarianceLargeCount

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_OriginalPairSieve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
namespace ErdosVarianceLargeCount
open NumberTheoryLean ErdosHyperbolaError ErdosPrimeInputs.PrimeProductOmissions
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem largeSieveExponent_bounds : 0 < largeSieveExponent ∧ largeSieveExponent < 1 := by
  norm_num [largeSieveExponent,largeSieveLevel]

theorem largeSieveCutoff_level (R : ℝ) (hR : 0 < R) :
    (largeSieveCutoff R)^largeSieveLevel = R^((1 : ℝ)/10) := by
  unfold largeSieveCutoff
  rw [← Real.rpow_mul hR.le]
  norm_num [largeSieveExponent,largeSieveLevel]

theorem largeSieveCutoff_log (R : ℝ) (hR : 0 < R) :
    Real.log (largeSieveCutoff R) = largeSieveExponent*Real.log R := Real.log_rpow hR _

theorem largeSieveCutoff_tendsto : Tendsto largeSieveCutoff atTop atTop :=
  tendsto_rpow_atTop largeSieveExponent_bounds.1

theorem largeSieveCutoff_lt (R : ℝ) (hR : 1 < R) : largeSieveCutoff R < R := by
  simpa only [largeSieveCutoff,Real.rpow_one] using
    Real.rpow_lt_rpow_of_exponent_lt hR largeSieveExponent_bounds.2

theorem source_main_R_upper : ∃ C : ℝ,0 < C ∧ ∀ᶠ R : ℝ in atTop,1 < R ∧ 2 ≤ largeSieveCutoff R ∧
    ∀ (H T0 T1 : ℕ),0 < H → 0 < T0 → 0 < T1 → T0 ∣ H → H.Coprime T1 →
      ∀ (U V : ℝ),0 ≤ U → 0 ≤ V → V ≤ 2*(H : ℝ) →
      sourceMain H T0 T1 U V*
        (∏ t ∈ reducedPrimes ⌊largeSieveCutoff R⌋₊ (H*T1),(1-1/(t : ℝ)))*
          (1+Real.exp (-largeSieveLevel/96)) ≤
            C*U/((patternCard T0 T1 : ℝ)*Real.log R) := by
  obtain ⟨C,v0,hC,hv0,hmain⟩ := source_main_uniform_upper
  refine ⟨C/largeSieveExponent,div_pos hC largeSieveExponent_bounds.1,?_⟩
  filter_upwards [largeSieveCutoff_tendsto.eventually_ge_atTop v0,eventually_gt_atTop (1 : ℝ)]
    with R hv hR
  refine ⟨hR,hv0.trans hv,?_⟩
  intro H T0 T1 hH hT0 hT1 hT0H hcop U V hU hV hVH
  have hh := hmain (largeSieveCutoff R) hv H T0 T1 hH hT0 hT1 hT0H hcop U V largeSieveLevel hU hV hVH
    (by norm_num [largeSieveLevel])
  rw [largeSieveCutoff_log R (by linarith)] at hh
  calc
    _ ≤ C*U/((patternCard T0 T1 : ℝ)*(largeSieveExponent*Real.log R)) := hh
    _ = _ := by ring

end ErdosVarianceLargeCount

end

section

namespace ErdosVarianceLargeMap
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceLargeCount ErdosHyperbolaError
  ErdosPrimeInputs.PrimeProductOmissions
attribute [local instance] Classical.propDecidable

theorem prime_avoids_cutoff (p : ℕ) (hp : p.Prime) (v : ℝ) (hvp : v < (p : ℝ))
    (t : ℕ) (ht : t.Prime) (htv : (t : ℝ) ≤ v) : ¬(t : ℤ) ∣ (p : ℤ) := by
  intro hdiv
  have hd : t ∣ p := by exact_mod_cast hdiv
  rcases (Nat.dvd_prime hp).mp hd with he|he
  · exact ht.ne_one he
  · subst t
    linarith

theorem original_pair_mem_sifted (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ)) (p : goodPrimes P H)
    (R : ℝ) (hR : 1 < R) (hpR : R < (p.val : ℝ))
    (x0 x1 y0 y1 : ℝ) (hp : x0 < (p.val : ℝ) ∧ (p.val : ℝ) ≤ x1)
    (hm : y0 ≤ (primeM P H C0 hP p : ℝ) ∧ (primeM P H C0 hP p : ℝ) < y1) :
    let v := actualFullPattern P w H C0 hw hP hlarge p
    ((p.val : ℤ),primeM P H C0 hP p) ∈
      siftedSourcePairs H (divisorModulus w H) (coprimeModulus w H) C0 (v.2.1.val : ℤ)
        (v.1.val.val : ℤ) (v.2.2.1.val.val : ℤ) (v.2.2.2.val : ℤ) x0 x1 y0 y1 false true true false
          (reducedPrimes ⌊largeSieveCutoff R⌋₊ (H*coprimeModulus w H)) := by
  dsimp only
  apply Finset.mem_filter.mpr
  refine ⟨original_pair_mem_sourcePairs P w H C0 hw hP hlarge p x0 x1 y0 y1 hp hm,?_⟩
  intro t ht
  have hc := LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_sdiff.mp ht).1
  have hcut0 : 0 ≤ largeSieveCutoff R := Real.rpow_nonneg (by linarith) _
  have htv := (Nat.le_floor_iff hcut0).mp hc.2
  exact prime_avoids_cutoff p.val (hP p.val (Finset.mem_filter.mp p.property).1) (largeSieveCutoff R)
    ((largeSieveCutoff_lt R hR).trans hpR) t hc.1 htv

theorem original_prime_fibre_le_pairs (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (A : Finset (goodPrimes P H)) (v : ErdosLargePatternLaw.FullPattern w H)
    (R : ℝ) (hR : 1 < R) (x0 x1 y0 y1 : ℝ)
    (hA : ∀ p ∈ A,actualFullPattern P w H C0 hw hP hlarge p = v ∧ R < (p.val : ℝ) ∧
      (x0 < (p.val : ℝ) ∧ (p.val : ℝ) ≤ x1) ∧
      (y0 ≤ (primeM P H C0 hP p : ℝ) ∧ (primeM P H C0 hP p : ℝ) < y1)) :
    A.card ≤ (siftedSourcePairs H (divisorModulus w H) (coprimeModulus w H) C0 (v.2.1.val : ℤ)
      (v.1.val.val : ℤ) (v.2.2.1.val.val : ℤ) (v.2.2.2.val : ℤ) x0 x1 y0 y1 false true true false
        (reducedPrimes ⌊largeSieveCutoff R⌋₊ (H*coprimeModulus w H))).card := by
  apply Finset.card_le_card_of_injOn (fun p => ((p.val : ℤ),primeM P H C0 hP p))
  · intro p hp
    obtain ⟨he,hpR,hpI,hmI⟩ := hA p hp
    have hm := original_pair_mem_sifted P w H C0 hw hP hlarge p R hR hpR x0 x1 y0 y1 hpI hmI
    dsimp only at hm
    rwa [he] at hm
  · exact (original_prime_pair_injective P H C0 hP).injOn

end ErdosVarianceLargeMap

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceLargePairBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
namespace ErdosVarianceLargeCount
open NumberTheoryLean ErdosHyperbolaError ErdosPrimeInputs.PrimeProductOmissions
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem finite_large_pair_bound : ∃ C : ℝ,0 < C ∧ ∀ᶠ R : ℝ in atTop,1 < R ∧
    ∀ (H T0 T1 : ℕ),2 ≤ H → 0 < T0 → 0 < T1 → Squarefree T0 →
      (∀ t : ℕ,t.Prime → t ∣ T0 → t ∣ H) → T1.Coprime (H*T0) →
      ∀ (C0 k0 p0 p1 m1 : ℤ),Int.gcd C0 (H : ℤ) = 1 → Int.gcd p0 (T0 : ℤ) = 1 →
        Int.gcd p1 (T1 : ℤ) = 1 →
      ∀ (x0 x1 y0 y1 : ℝ),x0 ≤ x1 → y0 ≤ y1 → y1-y0 ≤ 2*(H : ℝ) →
      ∀ (lcI rcI lcJ rcJ : Bool),
      ((siftedSourcePairs H T0 T1 C0 k0 p0 p1 m1 x0 x1 y0 y1 lcI rcI lcJ rcJ
        (reducedPrimes ⌊largeSieveCutoff R⌋₊ (H*T1))).card : ℝ) ≤
        C*(x1-x0)/((patternCard T0 T1 : ℝ)*Real.log R)+
        hyperbolaEnvelope H T0*(2*R^((1 : ℝ)/10)*(1+(y1-y0)/((H*T0 : ℕ) : ℝ))+
          ((x1-x0)/((H*T0 : ℕ) : ℝ))*(1+Real.log (R^((1 : ℝ)/10)))) := by
  obtain ⟨C,hC,hmain⟩ := source_main_R_upper
  refine ⟨C,hC,?_⟩
  filter_upwards [hmain] with R hR
  refine ⟨hR.1,?_⟩
  intro H T0 T1 hH hT0 hT1 hSF hsupport hT1N C0 k0 p0 p1 m1 hC0 hp0 hp1
    x0 x1 y0 y1 hx hy hVH lcI rcI lcJ rcJ
  have hH0 : 0 < H := by omega
  have hq : 0 < H*T1 := mul_pos hH0 hT1
  let P := reducedPrimes ⌊largeSieveCutoff R⌋₊ (H*T1)
  have hP (t : ℕ) (ht : t ∈ P) : t.Prime :=
    (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_sdiff.mp ht).1).1
  have hPv (t : ℕ) (ht : t ∈ P) : (t : ℝ) ≤ largeSieveCutoff R :=
    (Nat.le_floor_iff (by linarith [hR.2.1])).mp
      (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_sdiff.mp ht).1).2
  have hPcop (t : ℕ) (ht : t ∈ P) : t.Coprime (H*T1) := by
    apply (hP t ht).coprime_iff_not_dvd.mpr
    intro hdiv
    exact (Finset.mem_sdiff.mp ht).2 (Nat.mem_primeFactors.mpr ⟨hP t ht,hdiv,hq.ne'⟩)
  have hb := source_pair_sieve_upper_jb247 H T0 T1 hH hT0 hT1 hSF hsupport hT1N C0 k0 p0 p1 m1
    hC0 hp0 hp1 P hP hPcop (largeSieveCutoff R) largeSieveLevel hR.2.1 (by norm_num [largeSieveLevel]) hPv
    x0 x1 y0 y1 hx hy lcI rcI lcJ rcJ
  have hT0H := source_restriction_divides H T0 hH0 hSF hsupport
  have hcop : H.Coprime T1 := hT1N.symm.of_dvd_left (dvd_mul_right H T0)
  have hm := hR.2.2 H T0 T1 hH0 hT0 hT1 hT0H hcop (x1-x0) (y1-y0)
    (sub_nonneg.mpr hx) (sub_nonneg.mpr hy) hVH
  have hD : 1 ≤ (largeSieveCutoff R)^largeSieveLevel :=
    Real.one_le_rpow (by linarith [hR.2.1]) (by norm_num [largeSieveLevel])
  have he := hyperbola_level_sum_bound H T0 P (largeSieveCutoff R) largeSieveLevel
    (x1-x0) (y1-y0) hD (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)
  rw [largeSieveCutoff_level R (by linarith [hR.1])] at he
  exact hb.trans (add_le_add hm he)

end ErdosVarianceLargeCount

end

section

open _root_.Filter
namespace ErdosVarianceLargeScale
open NumberTheoryLean ErdosHyperbolaError ErdosHyperbolaWeighted ErdosVarianceLargeCount
  ErdosInverseBoxHeight ErdosInverseEuler ErdosVarianceSmallModel

theorem hyperbolaEnvelope_factor (H T0 : ℕ) :
    hyperbolaEnvelope H T0 = slowHyperbolaFactor (H*T0) T0*((H*T0 : ℕ) : ℝ)^((3 : ℝ)/4) := by
  unfold hyperbolaEnvelope slowHyperbolaFactor
  ring

theorem source_hyperbola_scales (alpha : ℝ) (halpha : 0 < alpha) :
    ∀ᶠ z : ℝ in atTop,1 < z ∧ ∀ (R : ℝ),z^alpha ≤ R →
      ∀ (H T0 : ℕ),1 ≤ H → 1 ≤ T0 →
        (H : ℝ) ≤ R*(sourceZ z)^11 → T0 ≤ smallModulus (sourceW z) →
        1 < R ∧ ((H*T0 : ℕ) : ℝ) ≤ R^((101 : ℝ)/100) ∧
          slowHyperbolaFactor (H*T0) T0 ≤ R^((1 : ℝ)/100) := by
  obtain ⟨A,hA,hdiv⟩ := divisor_log_square_subpower 3 (by norm_num : (0 : ℝ) < 1/1000)
  let C := completionConstant*A
  have hconst := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3/1000)).comp
    (tendsto_rpow_atTop halpha)).eventually_ge_atTop C
  filter_upwards [source_Z_power_R alpha (1/100) 12 halpha (by norm_num) (by decide),
    source_Z_power_R alpha (1/100) 1 halpha (by norm_num) (by decide),
    smallModulus_source_power 1 1 zero_lt_one,hconst]
    with z hZ12 hZ1 hM hconstz
  refine ⟨hZ12.1,?_⟩
  intro R hRlo H T0 hH hT0 hHhi hT0M
  have hz0 : 0 < z := by linarith [hZ12.1]
  have hR1 : 1 < R := (Real.one_lt_rpow hZ12.1 halpha).trans_le hRlo
  have hR : 0 < R := by linarith
  have hZ : 0 < sourceZ z := Real.exp_pos _
  have hMZ : (smallModulus (sourceW z) : ℝ) ≤ sourceZ z := by
    simpa only [pow_one,Real.rpow_one] using hM
  have hT0Z : (T0 : ℝ) ≤ sourceZ z := (by exact_mod_cast hT0M : (T0 : ℝ) ≤ smallModulus (sourceW z)).trans hMZ
  have hT0R : (T0 : ℝ) ≤ R^((1 : ℝ)/100) := hT0Z.trans (by
    simpa only [pow_one] using hZ1.2 R hRlo)
  have hN : ((H*T0 : ℕ) : ℝ) ≤ R^((101 : ℝ)/100) := by
    calc
      _ = (H : ℝ)*(T0 : ℝ) := Nat.cast_mul _ _
      _ ≤ (R*(sourceZ z)^11)*sourceZ z := mul_le_mul hHhi hT0Z (Nat.cast_nonneg _) (by positivity)
      _ = R*(sourceZ z)^12 := by ring
      _ ≤ R*R^((1 : ℝ)/100) := mul_le_mul_of_nonneg_left (hZ12.2 R hRlo) hR.le
      _ = R^(1 : ℝ)*R^((1 : ℝ)/100) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hR];norm_num
  have hN1 : 1 ≤ H*T0 := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))
  have hN2 : ((H*T0 : ℕ) : ℝ) ≤ R^(2 : ℝ) :=
    hN.trans (Real.rpow_le_rpow_of_exponent_le hR1.le (by norm_num))
  have hNp : (((H*T0 : ℕ) : ℝ)^((1 : ℝ)/1000)) ≤ R^((1 : ℝ)/500) := by
    calc
      _ ≤ (R^(2 : ℝ))^((1 : ℝ)/1000) := Real.rpow_le_rpow (Nat.cast_nonneg _) hN2 (by norm_num)
      _ = _ := by rw [← Real.rpow_mul hR.le];norm_num
  have hsqrt : Real.sqrt T0 ≤ R^((1 : ℝ)/200) := by
    calc
      _ ≤ Real.sqrt (R^((1 : ℝ)/100)) := Real.sqrt_le_sqrt hT0R
      _ = _ := by rw [Real.sqrt_eq_rpow,← Real.rpow_mul hR.le];norm_num
  have hC : C ≤ R^((3 : ℝ)/1000) :=
    hconstz.trans (Real.rpow_le_rpow (Real.rpow_nonneg hz0.le alpha) hRlo (by norm_num))
  have hfactor : slowHyperbolaFactor (H*T0) T0 ≤ R^((1 : ℝ)/100) := by
    calc
      _ = completionConstant*((H*T0).divisors.card : ℝ)^3*
          (Real.log (2*((H*T0 : ℕ) : ℝ)))^2*Real.sqrt T0 := rfl
      _ ≤ completionConstant*(A*(((H*T0 : ℕ) : ℝ)^((1 : ℝ)/1000)))*Real.sqrt T0 := by
        exact mul_le_mul_of_nonneg_right (by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hdiv (H*T0) hN1) completionConstant_pos.le)
          (Real.sqrt_nonneg _)
      _ = C*(((H*T0 : ℕ) : ℝ)^((1 : ℝ)/1000))*Real.sqrt T0 := by dsimp [C] <;> ring
      _ ≤ R^((3 : ℝ)/1000)*R^((1 : ℝ)/500)*R^((1 : ℝ)/200) := by
        exact mul_le_mul (mul_le_mul hC hNp (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity))
          hsqrt (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by rw [← Real.rpow_add hR,← Real.rpow_add hR];norm_num
  exact ⟨hR1,hN,hfactor⟩

end ErdosVarianceLargeScale

end


namespace ErdosVarianceLargeScale

theorem large_error_algebra (R N F U V : ℝ) (hR : 1 < R) (hN : 0 < N)
    (_hFlow : 0 ≤ F) (hF : F ≤ R^((1 : ℝ)/100))
    (hNlo : R^((4 : ℝ)/5) ≤ N) (hNhi : N ≤ R^((101 : ℝ)/100))
    (hU : 0 ≤ U) (hUR : U ≤ R) (hV : 0 ≤ V) (hVN : V ≤ 2*N)
    (hlog : 1+Real.log (R^((1 : ℝ)/10)) ≤ 2*R^((1 : ℝ)/20))
    (hconstant : 8 ≤ R^((1 : ℝ)/40)) :
    F*N^((3 : ℝ)/4)*(2*R^((1 : ℝ)/10)*(1+V/N)+(U/N)*(1+Real.log (R^((1 : ℝ)/10)))) ≤
      R^((9 : ℝ)/10) := by
  have hR0 : 0 < R := by linarith
  have hNp : N^((3 : ℝ)/4) ≤ R^((303 : ℝ)/400) := by
    calc
      _ ≤ (R^((101 : ℝ)/100))^((3 : ℝ)/4) := Real.rpow_le_rpow hN.le hNhi (by norm_num)
      _ = _ := by rw [← Real.rpow_mul hR0.le];norm_num
  have hVdiv : V/N ≤ 2 := (div_le_iff₀ hN).mpr hVN
  have hfirst : F*N^((3 : ℝ)/4)*(2*R^((1 : ℝ)/10)*(1+V/N)) ≤ 6*R^((347 : ℝ)/400) := by
    have hfac : 2*R^((1 : ℝ)/10)*(1+V/N) ≤ 6*R^((1 : ℝ)/10) := by
      have hh := mul_le_mul_of_nonneg_left (show 1+V/N ≤ 3 by linarith)
        (show 0 ≤ 2*R^((1 : ℝ)/10) by positivity)
      nlinarith
    calc
      _ ≤ (R^((1 : ℝ)/100)*R^((303 : ℝ)/400))*(6*R^((1 : ℝ)/10)) :=
        mul_le_mul (mul_le_mul hF hNp (Real.rpow_nonneg hN.le _) (by positivity)) hfac
          (by positivity) (by positivity)
      _ = 6*(R^((1 : ℝ)/100)*R^((303 : ℝ)/400)*R^((1 : ℝ)/10)) := by ring
      _ = _ := by rw [← Real.rpow_add hR0,← Real.rpow_add hR0];norm_num
  have hNroot : R^((1 : ℝ)/5) ≤ N^((1 : ℝ)/4) := by
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hR0.le _) hNlo (by norm_num : (0 : ℝ) ≤ 1/4)
    rw [← Real.rpow_mul hR0.le] at hh
    norm_num at hh
    exact hh
  have hratio : N^((3 : ℝ)/4)/N ≤ 1/R^((1 : ℝ)/5) := by
    have he : N^((3 : ℝ)/4)/N = 1/N^((1 : ℝ)/4) := by
      apply (div_eq_div_iff hN.ne' (Real.rpow_pos_of_pos hN _).ne').mpr
      rw [← Real.rpow_add hN]
      norm_num
    rw [he]
    exact div_le_div_of_nonneg_left zero_le_one (Real.rpow_pos_of_pos hR0 _) hNroot
  have hlog0 : 0 ≤ 1+Real.log (R^((1 : ℝ)/10)) := by
    have hh := Real.log_nonneg (Real.one_le_rpow hR.le (by norm_num : (0 : ℝ) ≤ 1/10))
    linarith
  have hsecond : F*N^((3 : ℝ)/4)*((U/N)*(1+Real.log (R^((1 : ℝ)/10)))) ≤ 2*R^((43 : ℝ)/50) := by
    calc
      _ = (F*U)*(N^((3 : ℝ)/4)/N)*(1+Real.log (R^((1 : ℝ)/10))) := by ring
      _ ≤ ((R^((1 : ℝ)/100)*R)*(1/R^((1 : ℝ)/5)))*(2*R^((1 : ℝ)/20)) :=
        mul_le_mul
          (mul_le_mul (mul_le_mul hF hUR hU (by positivity)) hratio (by positivity) (by positivity))
          hlog hlog0 (by positivity)
      _ = 2*((R^((1 : ℝ)/100)*R^(1 : ℝ)/R^((1 : ℝ)/5))*R^((1 : ℝ)/20)) := by
        rw [Real.rpow_one]
        ring
      _ = _ := by rw [← Real.rpow_add hR0,← Real.rpow_sub hR0,← Real.rpow_add hR0];norm_num
  have hp1 : R^((347 : ℝ)/400) ≤ R^((7 : ℝ)/8) := Real.rpow_le_rpow_of_exponent_le hR.le (by norm_num)
  have hp2 : R^((43 : ℝ)/50) ≤ R^((7 : ℝ)/8) := Real.rpow_le_rpow_of_exponent_le hR.le (by norm_num)
  have hsum : F*N^((3 : ℝ)/4)*(2*R^((1 : ℝ)/10)*(1+V/N)+(U/N)*(1+Real.log (R^((1 : ℝ)/10)))) ≤
      8*R^((7 : ℝ)/8) := by
    rw [mul_add]
    nlinarith
  apply hsum.trans
  calc
    _ ≤ R^((1 : ℝ)/40)*R^((7 : ℝ)/8) := mul_le_mul_of_nonneg_right hconstant (by positivity)
    _ = _ := by rw [← Real.rpow_add hR0];norm_num

end ErdosVarianceLargeScale


section

open _root_.Filter
namespace ErdosVarianceLargeScale

theorem eventual_large_error_budgets : ∀ᶠ R : ℝ in atTop,1 < R ∧
    1+Real.log (R^((1 : ℝ)/10)) ≤ 2*R^((1 : ℝ)/20) ∧ 8 ≤ R^((1 : ℝ)/40) := by
  have hlog := (isLittleO_log_rpow_rpow_atTop (1 : ℝ) (by norm_num : (0 : ℝ) < 1/20)).bound zero_lt_one
  filter_upwards [hlog,(tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/40)).eventually_ge_atTop 8,
    eventually_gt_atTop (1 : ℝ)] with R hlog hconstant hR
  have hR0 : 0 < R := by linarith
  have hlog0 : 0 ≤ Real.log R := (Real.log_pos hR).le
  have hl : Real.log R ≤ R^((1 : ℝ)/20) := by
    simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_nonneg hlog0,
      abs_of_nonneg (Real.rpow_nonneg hR0.le _),one_mul] using hlog
  have hone : 1 ≤ R^((1 : ℝ)/20) := Real.one_le_rpow hR.le (by norm_num)
  refine ⟨hR,?_,hconstant⟩
  rw [Real.log_rpow hR0]
  nlinarith

end ErdosVarianceLargeScale

end

section

open _root_.Filter
namespace ErdosVarianceLargeScale
open NumberTheoryLean ErdosHyperbolaError ErdosVarianceLargeCount
  ErdosInverseBoxHeight ErdosInverseEuler ErdosVarianceSmallModel

theorem source_large_error (alpha : ℝ) (halpha : 0 < alpha) :
    ∀ᶠ z : ℝ in atTop,1 < z ∧ ∀ (R : ℝ),z^alpha ≤ R →
      ∀ (H T0 : ℕ),1 ≤ H → 1 ≤ T0 →
        R^((4 : ℝ)/5) ≤ (H : ℝ) → (H : ℝ) ≤ R*(sourceZ z)^11 → T0 ≤ smallModulus (sourceW z) →
      ∀ (U V : ℝ),0 ≤ U → U ≤ R → 0 ≤ V → V ≤ 2*(H : ℝ) →
        hyperbolaEnvelope H T0*(2*R^((1 : ℝ)/10)*(1+V/((H*T0 : ℕ) : ℝ))+
          (U/((H*T0 : ℕ) : ℝ))*(1+Real.log (R^((1 : ℝ)/10)))) ≤ R^((9 : ℝ)/10) := by
  obtain ⟨R0,hR0⟩ := eventually_atTop.mp eventual_large_error_budgets
  filter_upwards [source_hyperbola_scales alpha halpha,(tendsto_rpow_atTop halpha).eventually_ge_atTop R0]
    with z hscale hzR
  refine ⟨hscale.1,?_⟩
  intro R hRlo H T0 hH hT0 hHlo hHhi hT0M U V hU hUR hV hVH
  have hs := hscale.2 R hRlo H T0 hH hT0 hHhi hT0M
  have hb := hR0 R (hzR.trans hRlo)
  have hHN : (H : ℝ) ≤ ((H*T0 : ℕ) : ℝ) := by
    have ht : (1 : ℝ) ≤ T0 := by exact_mod_cast hT0
    have hh := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg H)
    simpa only [mul_one,Nat.cast_mul] using hh
  have hN : (0 : ℝ) < ((H*T0 : ℕ) : ℝ) := by
    exact_mod_cast mul_pos (show 0 < H by omega) (show 0 < T0 by omega)
  have hF : 0 ≤ slowHyperbolaFactor (H*T0) T0 := by
    have hc := completionConstant_pos.le
    dsimp [slowHyperbolaFactor]
    positivity
  rw [hyperbolaEnvelope_factor]
  exact large_error_algebra R ((H*T0 : ℕ) : ℝ) (slowHyperbolaFactor (H*T0) T0) U V
    hs.1 hN hF hs.2.2 (hHlo.trans hHN) hs.2.1 hU hUR hV
    (hVH.trans (mul_le_mul_of_nonneg_left hHN (by norm_num))) hb.2.1 hb.2.2

end ErdosVarianceLargeScale

end


open _root_.Filter
namespace ErdosVarianceLargeScale
open NumberTheoryLean ErdosHyperbolaError ErdosVarianceLargeCount
  ErdosInverseBoxHeight ErdosInverseEuler ErdosPrimeInputs.PrimeProductOmissions

theorem source_large_pair_bound (alpha : ℝ) (halpha : 0 < alpha) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ z : ℝ in atTop,1 < z ∧
      ∀ (R : ℝ),z^alpha ≤ R → ∀ (H T0 T1 : ℕ),2 ≤ H → 0 < T0 → 0 < T1 →
        Squarefree T0 → (∀ t : ℕ,t.Prime → t ∣ T0 → t ∣ H) → T1.Coprime (H*T0) →
        R^((4 : ℝ)/5) ≤ (H : ℝ) → (H : ℝ) ≤ R*(sourceZ z)^11 → T0 ≤ smallModulus (sourceW z) →
      ∀ (C0 k0 p0 p1 m1 : ℤ),Int.gcd C0 (H : ℤ) = 1 → Int.gcd p0 (T0 : ℤ) = 1 →
        Int.gcd p1 (T1 : ℤ) = 1 →
      ∀ (x0 x1 y0 y1 : ℝ),x0 ≤ x1 → x1-x0 ≤ R → y0 ≤ y1 → y1-y0 ≤ 2*(H : ℝ) →
      ∀ (lcI rcI lcJ rcJ : Bool),
      ((siftedSourcePairs H T0 T1 C0 k0 p0 p1 m1 x0 x1 y0 y1 lcI rcI lcJ rcJ
        (reducedPrimes ⌊largeSieveCutoff R⌋₊ (H*T1))).card : ℝ) ≤
          C*(x1-x0)/((patternCard T0 T1 : ℝ)*Real.log R)+R^((9 : ℝ)/10) := by
  obtain ⟨C,hC,hfinite⟩ := finite_large_pair_bound
  obtain ⟨R0,hR0⟩ := eventually_atTop.mp hfinite
  refine ⟨C,hC,?_⟩
  filter_upwards [source_large_error alpha halpha,(tendsto_rpow_atTop halpha).eventually_ge_atTop R0]
    with z herr hzR
  refine ⟨herr.1,?_⟩
  intro R hRlo H T0 T1 hH hT0 hT1 hSF hsupport hT1N hHlo hHhi hT0M
    C0 k0 p0 p1 m1 hC0 hp0 hp1 x0 x1 y0 y1 hx hUR hy hVH lcI rcI lcJ rcJ
  have hb := (hR0 R (hzR.trans hRlo)).2 H T0 T1 hH hT0 hT1 hSF hsupport hT1N C0 k0 p0 p1 m1
    hC0 hp0 hp1 x0 x1 y0 y1 hx hy hVH lcI rcI lcJ rcJ
  have he := herr.2 R hRlo H T0 (by omega) hT0 hHlo hHhi hT0M (x1-x0) (y1-y0)
    (sub_nonneg.mpr hx) hUR (sub_nonneg.mpr hy) hVH
  exact hb.trans (add_le_add le_rfl he)

end ErdosVarianceLargeScale


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_SourceBlockFibreBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceLargeMap
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceLargeCount ErdosHyperbolaError
  ErdosLargeHeightBlocks ErdosInversePrimeBin ErdosPrimeInputs.PrimeProductOmissions
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem blockPatternPrimes_le_pairs (R theta w : ℝ) (H : ℕ) (C0 : ℤ)
    (hR : 1 < R) (htheta : 0 < theta) (hH : 0 < H) (hw : 0 ≤ w)
    (hP : ∀ p ∈ primeBin R theta,p.Prime) (hlarge : ∀ p ∈ primeBin R theta,w < (p : ℝ))
    (i : Fin (blockCount C0 R theta H)) (v : ErdosLargePatternLaw.FullPattern w H) :
    (blockPatternPrimes R theta w H C0 hw hP hlarge i v).card ≤
      (siftedSourcePairs H (divisorModulus w H) (coprimeModulus w H) C0 (v.2.1.val : ℤ)
        (v.1.val.val : ℤ) (v.2.2.1.val.val : ℤ) (v.2.2.2.val : ℤ)
        (blockLeft C0 R theta H i) (blockRight C0 R theta H i)
        (coordinateLower C0 R theta H i) (coordinateUpper C0 R theta H i) false true true false
          (reducedPrimes ⌊largeSieveCutoff R⌋₊ (H*coprimeModulus w H))).card := by
  apply original_prime_fibre_le_pairs (primeBin R theta) w H C0 hw hP hlarge _ v R hR
  intro p hp
  obtain ⟨hb,hv⟩ := (Finset.mem_filter.mp hp).2
  have hpP := (Finset.mem_filter.mp p.property).1
  have hprime := hP p hpP
  let : NeZero p.val := ⟨hprime.ne_zero⟩
  have hRp : 0 < R := by linarith
  have hbig := (mem_primeBin hRp.le htheta.le p).mp hpP
  have hbin := (mem_blockPrimes C0 R theta H i p hRp htheta).mp hb
  have hcoord := actual_m0_block_interval C0 R theta H i p hRp htheta hH
    (Finset.mem_filter.mp p.property).2 hb
  refine ⟨hv,hbig.2.1,hbin.2,?_⟩
  exact hcoord.1

theorem actual_block_rectangle_bounds (R theta : ℝ) (H : ℕ) (C0 : ℤ)
    (hR : 0 < R) (htheta : 0 < theta) (htheta1 : theta ≤ 1) (hH : 0 < H)
    (i : Fin (blockCount C0 R theta H)) :
    blockLeft C0 R theta H i ≤ blockRight C0 R theta H i ∧
    blockRight C0 R theta H i-blockLeft C0 R theta H i ≤ R ∧
    coordinateLower C0 R theta H i ≤ coordinateUpper C0 R theta H i ∧
    coordinateUpper C0 R theta H i-coordinateLower C0 R theta H i ≤ 2*(H : ℝ) := by
  have hn := blockCount_pos C0 R theta H
  have hright : blockLeft C0 R theta H i < blockRight C0 R theta H i :=
    ErdosTagSubbins.left_lt_right hR htheta hn
  refine ⟨hright.le,?_,?_,block_coordinate_width C0 R theta H i hR htheta hH⟩
  · change ErdosTagSubbins.right R theta (blockCount C0 R theta H) i-
      ErdosTagSubbins.left R theta (blockCount C0 R theta H) i ≤ R
    rw [ErdosTagSubbins.right_sub_left]
    unfold ErdosTagSubbins.step
    have hden : (1 : ℝ) ≤ blockCount C0 R theta H := by exact_mod_cast hn
    have hh := div_le_self (mul_nonneg htheta.le hR.le) hden
    have hnum : theta*R ≤ R := by nlinarith
    simpa only [mul_comm] using hh.trans hnum
  · unfold coordinateLower coordinateUpper
    exact (min_le_max).trans (le_add_of_nonneg_right (Nat.cast_nonneg H))

end ErdosVarianceLargeMap

end

section

open _root_.Filter
namespace ErdosVarianceLargeMap
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceLargeCount ErdosVarianceLargeScale
  ErdosLargeHeightBlocks ErdosInversePrimeBin ErdosInverseBoxHeight ErdosInverseEuler
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem source_block_fibre_bound (alpha : ℝ) (halpha : 0 < alpha) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ z : ℝ in atTop,1 < z ∧
      ∀ (R theta : ℝ),z^alpha ≤ R → 0 < theta → theta ≤ 1 →
      ∀ (H : ℕ) (C0 : ℤ),2 ≤ H → Int.gcd C0 (H : ℤ) = 1 →
        R^((4 : ℝ)/5) ≤ (H : ℝ) → (H : ℝ) ≤ R*(sourceZ z)^11 →
      ∀ (hw : 0 ≤ sourceW z) (hP : ∀ p ∈ primeBin R theta,p.Prime)
        (hlarge : ∀ p ∈ primeBin R theta,sourceW z < (p : ℝ))
        (i : Fin (blockCount C0 R theta H)) (v : ErdosLargePatternLaw.FullPattern (sourceW z) H),
        ((blockPatternPrimes R theta (sourceW z) H C0 hw hP hlarge i v).card : ℝ) ≤
          C*(blockRight C0 R theta H i-blockLeft C0 R theta H i)/
            ((patternCard (divisorModulus (sourceW z) H) (coprimeModulus (sourceW z) H) : ℝ)*Real.log R)+
              R^((9 : ℝ)/10) := by
  obtain ⟨C,hC,hbound⟩ := source_large_pair_bound alpha halpha
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with z hz
  refine ⟨hz.1,?_⟩
  intro R theta hRlo htheta htheta1 H C0 hH hC0 hHlo hHhi hw hP hlarge i v
  have hR1 : 1 < R := (Real.one_lt_rpow hz.1 halpha).trans_le hRlo
  have hR : 0 < R := by linarith
  have hH0 : 0 < H := by omega
  let T0 := divisorModulus (sourceW z) H
  let T1 := coprimeModulus (sourceW z) H
  have hT0 : 0 < T0 := divisorModulus_pos _ _
  have hT1 : 0 < T1 := coprimeModulus_pos _ _
  have hT0M : T0 ≤ smallModulus (sourceW z) := by
    have hh : T0 ≤ T0*T1 := by nlinarith
    exact hh.trans_eq (pattern_moduli_product _ _)
  have hSF : Squarefree T0 := IntervalBoundingSieve.squarefree_primeSet_product _
    (fun t ht => (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1)
  have hsupport : ∀ t : ℕ,t.Prime → t ∣ T0 → t ∣ H :=
    fun t _ ht => ht.trans (divisorModulus_dvd_H (sourceW z) H)
  have hcop : T1.Coprime (H*T0) := (effective_pattern_coprime _ _).symm
  have hunit := full_pattern_units (sourceW z) H v
  have hrectangle := actual_block_rectangle_bounds R theta H C0 hR htheta htheta1 hH0 i
  have hpairs := hz.2 R hRlo H T0 T1 hH hT0 hT1 hSF hsupport hcop hHlo hHhi hT0M
    C0 (v.2.1.val : ℤ) (v.1.val.val : ℤ) (v.2.2.1.val.val : ℤ) (v.2.2.2.val : ℤ)
    hC0 hunit.1 hunit.2
    (blockLeft C0 R theta H i) (blockRight C0 R theta H i)
    (coordinateLower C0 R theta H i) (coordinateUpper C0 R theta H i)
    hrectangle.1 hrectangle.2.1 hrectangle.2.2.1 hrectangle.2.2.2 false true true false
  have hactual := blockPatternPrimes_le_pairs R theta (sourceW z) H C0 hR1 htheta hH0 hw hP hlarge i v
  exact (show ((blockPatternPrimes R theta (sourceW z) H C0 hw hP hlarge i v).card : ℝ) ≤ _ by
    exact_mod_cast hactual).trans hpairs

end ErdosVarianceLargeMap

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_FullPrimeEventFibres
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceLargeMap
open NumberTheoryLean ErdosVarianceSmallModel ErdosLargeHeightBlocks ErdosInversePrimeBin
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem actualBlockIndex_mem (R theta : ℝ) (H : ℕ) (C0 : ℤ)
    (hR : 0 < R) (htheta : 0 < theta) (p : goodPrimes (primeBin R theta) H) :
    p.val ∈ blockPrimes C0 R theta H (actualBlockIndex R theta H C0 hR htheta p) :=
  Classical.choose_spec (unique_original_prime_block C0 R theta H p.val hR htheta
    (Finset.mem_filter.mp p.property).1).exists

theorem actualBlockIndex_eq_iff (R theta : ℝ) (H : ℕ) (C0 : ℤ)
    (hR : 0 < R) (htheta : 0 < theta) (p : goodPrimes (primeBin R theta) H)
    (i : Fin (blockCount C0 R theta H)) :
    actualBlockIndex R theta H C0 hR htheta p = i ↔ p.val ∈ blockPrimes C0 R theta H i := by
  constructor
  · intro he
    rw [← he]
    exact actualBlockIndex_mem R theta H C0 hR htheta p
  · intro hi
    exact (unique_original_prime_block C0 R theta H p.val hR htheta
      (Finset.mem_filter.mp p.property).1).unique (actualBlockIndex_mem R theta H C0 hR htheta p) hi

theorem fullPrimeEvent_card (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (E : ErdosLargePatternLaw.FullPattern w H → Prop) :
    (fullPrimeEvent P w H C0 hw hP hlarge E).card = (indexedFullPrimeEvent P w H C0 hw hP hlarge E).card :=
  Finset.card_image_of_injective _ Subtype.val_injective

theorem fullPrimeEvent_card_fibres (R theta w : ℝ) (H : ℕ) (C0 : ℤ)
    (hR : 0 < R) (htheta : 0 < theta) (hw : 0 ≤ w)
    (hP : ∀ p ∈ primeBin R theta,p.Prime) (hlarge : ∀ p ∈ primeBin R theta,w < (p : ℝ))
    (E : ErdosLargePatternLaw.FullPattern w H → Prop) :
    (fullPrimeEvent (primeBin R theta) w H C0 hw hP hlarge E).card =
      ∑ i : Fin (blockCount C0 R theta H),∑ v ∈ Finset.univ.filter E,
        (blockPatternPrimes R theta w H C0 hw hP hlarge i v).card := by
  let f (p : goodPrimes (primeBin R theta) H) :=
    (actualBlockIndex R theta H C0 hR htheta p,actualFullPattern (primeBin R theta) w H C0 hw hP hlarge p)
  let S : Finset (Fin (blockCount C0 R theta H) × ErdosLargePatternLaw.FullPattern w H) :=
    Finset.univ.product (Finset.univ.filter E)
  have hmaps : (indexedFullPrimeEvent (primeBin R theta) w H C0 hw hP hlarge E : Set _).MapsTo f (S : Set _) := by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,(Finset.mem_filter.mp hp).2⟩⟩
  rw [fullPrimeEvent_card,Finset.card_eq_sum_card_fiberwise hmaps]
  simp only [S,Finset.product_eq_sprod,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro v hv
  congr 1
  ext p
  simp only [indexedFullPrimeEvent,blockPatternPrimes,Finset.mem_filter,Finset.mem_univ,true_and,f,Prod.mk.injEq,
    actualBlockIndex_eq_iff]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨h.2.symm ▸ (Finset.mem_filter.mp hv).2,h⟩

end ErdosVarianceLargeMap

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_SourceFullEventCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosVarianceLargeMap
open ErdosVarianceSmallModel ErdosVarianceLargeCount
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem full_pattern_card_numeric (w : ℝ) (H : ℕ) :
    Fintype.card (ErdosLargePatternLaw.FullPattern w H) = patternCard (divisorModulus w H) (coprimeModulus w H) := by
  rw [ErdosLargePatternLaw.pattern_card,patternCard]
  ring

theorem full_pattern_weight_numeric (w : ℝ) (H : ℕ) :
    ErdosLargePatternLaw.weight w H = 1/(patternCard (divisorModulus w H) (coprimeModulus w H) : ℝ) := by
  unfold ErdosLargePatternLaw.weight patternCard
  push_cast
  congr 1
  ring

theorem patternEventWeight_card (w : ℝ) (H : ℕ) (E : ErdosLargePatternLaw.FullPattern w H → Prop) :
    patternEventWeight w H E = ((Finset.univ.filter E).card : ℝ)/
      (patternCard (divisorModulus w H) (coprimeModulus w H) : ℝ) := by
  rw [patternEventWeight,Finset.sum_const,nsmul_eq_mul,full_pattern_weight_numeric]
  ring

theorem patternEventWeight_nonneg (w : ℝ) (H : ℕ) (E : ErdosLargePatternLaw.FullPattern w H → Prop) :
    0 ≤ patternEventWeight w H E := Finset.sum_nonneg (fun _ _ => (ErdosLargePatternLaw.weight_positive w H).le)

end ErdosVarianceLargeMap



namespace ErdosVarianceLargeMap
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceLargeCount ErdosLargeHeightBlocks ErdosInversePrimeBin
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem full_event_count_bound (R theta w C err : ℝ) (H : ℕ) (C0 : ℤ)
    (hR : 0 < R) (htheta : 0 < theta) (herr : 0 ≤ err) (hw : 0 ≤ w)
    (hP : ∀ p ∈ primeBin R theta,p.Prime) (hlarge : ∀ p ∈ primeBin R theta,w < (p : ℝ))
    (hbound : ∀ (i : Fin (blockCount C0 R theta H)) (v : ErdosLargePatternLaw.FullPattern w H),
      ((blockPatternPrimes R theta w H C0 hw hP hlarge i v).card : ℝ) ≤
        C*(blockRight C0 R theta H i-blockLeft C0 R theta H i)/
          ((patternCard (divisorModulus w H) (coprimeModulus w H) : ℝ)*Real.log R)+err)
    (E : ErdosLargePatternLaw.FullPattern w H → Prop) :
    ((fullPrimeEvent (primeBin R theta) w H C0 hw hP hlarge E).card : ℝ) ≤
      C*theta*R/Real.log R*patternEventWeight w H E+
        (blockCount C0 R theta H : ℝ)*(patternCard (divisorModulus w H) (coprimeModulus w H) : ℝ)*err := by
  let B := Finset.univ.filter E
  let M : ℝ := patternCard (divisorModulus w H) (coprimeModulus w H)
  let n : ℝ := blockCount C0 R theta H
  have hinner : (∑ i : Fin (blockCount C0 R theta H),
      (C*(blockRight C0 R theta H i-blockLeft C0 R theta H i)/(M*Real.log R)+err)) =
        C*(theta*R)/(M*Real.log R)+n*err := by
    rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    congr 1
    calc
      _ = (C/(M*Real.log R))*∑ i : Fin (blockCount C0 R theta H),
          (blockRight C0 R theta H i-blockLeft C0 R theta H i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = _ := by rw [block_width_sum];ring
  have hsum : ((fullPrimeEvent (primeBin R theta) w H C0 hw hP hlarge E).card : ℝ) ≤
      (B.card : ℝ)*(C*(theta*R)/(M*Real.log R)+n*err) := by
    rw [fullPrimeEvent_card_fibres R theta w H C0 hR htheta hw hP hlarge E,Nat.cast_sum]
    simp_rw [Nat.cast_sum]
    calc
      _ ≤ ∑ i : Fin (blockCount C0 R theta H),∑ _v ∈ B,
          (C*(blockRight C0 R theta H i-blockLeft C0 R theta H i)/(M*Real.log R)+err) := by
        apply Finset.sum_le_sum
        intro i _hi
        exact Finset.sum_le_sum (fun v _hv => hbound i v)
      _ = _ := by
        rw [Finset.sum_comm]
        simp only [hinner,Finset.sum_const,nsmul_eq_mul]
  have hB : (B.card : ℝ) ≤ M := by
    have hh := Finset.card_le_univ B
    rw [full_pattern_card_numeric] at hh
    dsimp [M]
    exact_mod_cast hh
  have hevent : patternEventWeight w H E = (B.card : ℝ)/M := patternEventWeight_card w H E
  have herror : (B.card : ℝ)*(n*err) ≤ M*(n*err) := mul_le_mul_of_nonneg_right hB (by dsimp [n] <;> positivity)
  have he : (B.card : ℝ)*(C*(theta*R)/(M*Real.log R)+n*err) =
      C*theta*R/Real.log R*patternEventWeight w H E+(B.card : ℝ)*(n*err) := by
    rw [hevent]
    ring
  have hright : C*theta*R/Real.log R*patternEventWeight w H E+(B.card : ℝ)*(n*err) ≤
      C*theta*R/Real.log R*patternEventWeight w H E+n*M*err := by nlinarith
  exact hsum.trans (he.trans_le hright)

end ErdosVarianceLargeMap



open _root_.Filter
namespace ErdosVarianceLargeMap
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceLargeCount ErdosLargeHeightBlocks
  ErdosInversePrimeBin ErdosInverseBoxHeight
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem source_full_event_count (alpha : ℝ) (halpha : 0 < alpha) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ z : ℝ in atTop,1 < z ∧
      ∀ (R theta : ℝ),z^alpha ≤ R → 0 < theta → theta ≤ 1 →
      ∀ (H : ℕ) (C0 : ℤ),2 ≤ H → Int.gcd C0 (H : ℤ) = 1 →
        R^((4 : ℝ)/5) ≤ (H : ℝ) → (H : ℝ) ≤ R*(sourceZ z)^11 →
      ∀ (hw : 0 ≤ sourceW z) (hP : ∀ p ∈ primeBin R theta,p.Prime)
        (hlarge : ∀ p ∈ primeBin R theta,sourceW z < (p : ℝ))
        (E : ErdosLargePatternLaw.FullPattern (sourceW z) H → Prop),
        ((fullPrimeEvent (primeBin R theta) (sourceW z) H C0 hw hP hlarge E).card : ℝ) ≤
          C*theta*R/Real.log R*patternEventWeight (sourceW z) H E+
          (blockCount C0 R theta H : ℝ)*
            (patternCard (divisorModulus (sourceW z) H) (coprimeModulus (sourceW z) H) : ℝ)*R^((9 : ℝ)/10) := by
  obtain ⟨C,hC,hbound⟩ := source_block_fibre_bound alpha halpha
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with z hz
  refine ⟨hz.1,?_⟩
  intro R theta hRlo htheta htheta1 H C0 hH hC0 hHlo hHhi hw hP hlarge E
  have hR : 0 < R := (Real.rpow_pos_of_pos (by linarith [hz.1]) alpha).trans_le hRlo
  exact full_event_count_bound R theta (sourceW z) C (R^((9 : ℝ)/10)) H C0 hR htheta
    (Real.rpow_nonneg hR.le _) hw hP hlarge
    (hz.2 R theta hRlo htheta htheta1 H C0 hH hC0 hHlo hHhi hw hP hlarge) E

end ErdosVarianceLargeMap


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_PatternCardGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
namespace ErdosVarianceLargeMap
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceLargeCount ErdosInverseEuler ErdosInverseBoxHeight

theorem patternCard_le_smallModulus_sq (w : ℝ) (H : ℕ) :
    patternCard (divisorModulus w H) (coprimeModulus w H) ≤ (smallModulus w)^2 := by
  let T0 := divisorModulus w H
  let T1 := coprimeModulus w H
  calc
    _ = (T0*T1)*(T0.totient*T1.totient) := by unfold patternCard;ring
    _ ≤ (T0*T1)*(T0*T1) := Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.totient_le _) (Nat.totient_le _))
    _ = (smallModulus w)^2 := by rw [pattern_moduli_product,pow_two]

theorem source_patternCard_Z : ∀ᶠ z : ℝ in atTop,∀ H : ℕ,
    (patternCard (divisorModulus (sourceW z) H) (coprimeModulus (sourceW z) H) : ℝ) ≤ sourceZ z := by
  filter_upwards [smallModulus_source_power 2 1 zero_lt_one] with z hz
  intro H
  have hh : (patternCard (divisorModulus (sourceW z) H) (coprimeModulus (sourceW z) H) : ℝ) ≤
      (smallModulus (sourceW z) : ℝ)^2 := by exact_mod_cast patternCard_le_smallModulus_sq (sourceW z) H
  exact hh.trans (by simpa only [Real.rpow_one] using hz)

end ErdosVarianceLargeMap

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

end ErdosInverseSampleCost

end

section

open _root_.Filter
open scoped Topology
namespace ErdosVarianceSmallModel
open ErdosInversePrimeBin ErdosInverseBoxHeight ErdosInverseSampleCost

theorem source_model_population (alpha xi : ℝ) (ha : 0 < alpha) (hxi : 0 < xi) (hxi1 : xi ≤ 1) :
    ∀ᶠ z : ℝ in atTop,∀ R theta : ℝ,z^alpha ≤ R → xi/4 ≤ theta → theta ≤ xi →
      1 < R ∧ sourceW z ≤ R ∧ xi*R/(16*Real.log R) ≤ ((primeBin R theta).card : ℝ) := by
  obtain ⟨R0,hR0⟩ := eventually_atTop.mp (uniform_prime_bin_count (by positivity : 0 < xi/4))
  filter_upwards [(tendsto_rpow_atTop ha).eventually_ge_atTop R0,sourceW_le_power alpha ha]
    with z hz hW
  intro R theta hRlo htl htu
  have hc := hR0 R (hz.trans hRlo)
  have hRp : 0 < R := by linarith [hc.1]
  have hlog : 0 < Real.log R := Real.log_pos (by linarith [hc.1])
  refine ⟨by linarith [hc.1],hW.trans hRlo,?_⟩
  calc
    _ = (xi/4)*R/(4*Real.log R) := by ring
    _ ≤ theta*R/(4*Real.log R) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right htl hRp.le) (by positivity)
    _ ≤ _ := (hc.2 theta htl (htu.trans hxi1)).1

end ErdosVarianceSmallModel

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_PatternErrorNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


open _root_.Filter
namespace ErdosVarianceLargeMap
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceLargeCount ErdosLargeHeightBlocks
  ErdosInversePrimeBin ErdosInverseBoxHeight ErdosInverseEuler

theorem normalization_budgets (xi eps : ℝ) (hxi : 0 < xi) (heps : 0 < eps) :
    ∀ᶠ R : ℝ in atTop,1 < R ∧ Real.log R ≤ R^((1 : ℝ)/40) ∧
      16 ≤ eps*xi*R^((1 : ℝ)/20) := by
  have hlog := (isLittleO_log_rpow_rpow_atTop (1 : ℝ) (by norm_num : (0 : ℝ) < 1/40)).bound zero_lt_one
  filter_upwards [hlog,(tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/20)).eventually_ge_atTop (16/(eps*xi)),
    eventually_gt_atTop (1 : ℝ)] with R hlog hc hR
  have hR0 : 0 < R := by linarith
  refine ⟨hR,?_,?_⟩
  · simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_nonneg (Real.log_pos hR).le,
      abs_of_nonneg (Real.rpow_nonneg hR0.le _),one_mul] using hlog
  · have hh := (div_le_iff₀ (mul_pos heps hxi)).mp hc
    nlinarith

theorem source_pattern_error_normalized (alpha xi eps : ℝ)
    (halpha : 0 < alpha) (hxi : 0 < xi) (hxi1 : xi ≤ 1) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop,∀ (R theta : ℝ),z^alpha ≤ R → xi/4 ≤ theta → theta ≤ xi →
      ∀ (H : ℕ) (C0 : ℤ),0 < H →
        max (H : ℝ) (|(C0 : ℝ)|/R)/(H : ℝ) ≤ (sourceZ z)^12 →
        ((blockCount C0 R theta H : ℝ)*
          (patternCard (divisorModulus (sourceW z) H) (coprimeModulus (sourceW z) H) : ℝ)*R^((9 : ℝ)/10))/
            ((primeBin R theta).card : ℝ) ≤ eps := by
  obtain ⟨R0,hR0⟩ := eventually_atTop.mp (normalization_budgets xi eps hxi heps)
  filter_upwards [source_model_population alpha xi halpha hxi hxi1,source_patternCard_Z,
    source_Z_power_R alpha (1/40) 14 halpha (by norm_num) (by decide),
    sourceZ_tendsto_atTop.eventually_ge_atTop 2,(tendsto_rpow_atTop halpha).eventually_ge_atTop R0]
    with z hpop hM hZpow hZ hzR
  intro R theta hRlo hthetal hthetau H C0 hH hratio
  have hp := hpop R theta hRlo hthetal hthetau
  have hb := hR0 R (hzR.trans hRlo)
  have hR : 0 < R := by linarith [hp.1]
  have hlog : 0 < Real.log R := Real.log_pos hp.1
  have htheta : 0 ≤ theta := (by positivity : (0 : ℝ) ≤ xi/4).trans hthetal
  let n : ℝ := blockCount C0 R theta H
  let M : ℝ := patternCard (divisorModulus (sourceW z) H) (coprimeModulus (sourceW z) H)
  have hn : n ≤ (sourceZ z)^13 := blockCount_source_bound C0 R theta (sourceZ z) H
    hR htheta (hthetau.trans hxi1) hH hZ hratio
  have hMZ : M ≤ sourceZ z := hM H
  have hnM : n*M ≤ R^((1 : ℝ)/40) := by
    calc
      _ ≤ (sourceZ z)^13*sourceZ z := mul_le_mul hn hMZ (Nat.cast_nonneg _) (by positivity)
      _ = (sourceZ z)^14 := by ring
      _ ≤ _ := hZpow.2 R hRlo
  have hprod : (n*M*R^((9 : ℝ)/10))*(16*Real.log R) ≤ 16*R^((19 : ℝ)/20) := by
    have hpair := mul_le_mul hnM hb.2.1 hlog.le (Real.rpow_nonneg hR.le _)
    have hm := mul_le_mul_of_nonneg_left hpair (show 0 ≤ 16*R^((9 : ℝ)/10) by positivity)
    calc
      _ ≤ 16*R^((9 : ℝ)/10)*(R^((1 : ℝ)/40)*R^((1 : ℝ)/40)) := by nlinarith
      _ = 16*(R^((9 : ℝ)/10)*(R^((1 : ℝ)/40)*R^((1 : ℝ)/40))) := by ring
      _ = _ := by rw [← Real.rpow_add hR,← Real.rpow_add hR];norm_num
  have htarget : 16*R^((19 : ℝ)/20) ≤ eps*xi*R := by
    have hh := mul_le_mul_of_nonneg_right hb.2.2 (Real.rpow_nonneg hR.le ((19 : ℝ)/20))
    calc
      _ ≤ (eps*xi*R^((1 : ℝ)/20))*R^((19 : ℝ)/20) := hh
      _ = _ := by rw [mul_assoc (eps*xi),← Real.rpow_add hR];norm_num
  have herr : n*M*R^((9 : ℝ)/10) ≤ eps*(xi*R/(16*Real.log R)) := by
    have hh := (le_div_iff₀ (show 0 < 16*Real.log R by positivity)).mpr (hprod.trans htarget)
    have he : eps*(xi*R/(16*Real.log R)) = eps*xi*R/(16*Real.log R) := by ring
    exact hh.trans_eq he.symm
  have hlow : 0 < xi*R/(16*Real.log R) := by positivity
  have hPC : 0 < ((primeBin R theta).card : ℝ) := hlow.trans_le hp.2.2
  apply (div_le_iff₀ hPC).mpr
  exact herr.trans (mul_le_mul_of_nonneg_left hp.2.2 heps.le)

end ErdosVarianceLargeMap


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceFullPatternDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


open _root_.Filter
namespace ErdosVarianceLargeMap
open NumberTheoryLean ErdosVarianceSmallModel ErdosLargeHeightBlocks ErdosInversePrimeBin
  ErdosInverseBoxHeight ErdosInverseEuler
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem source_full_pattern_domination_jb247_oai (alpha : ℝ) (halpha : 0 < alpha) :
    ∃ C : ℝ,0 < C ∧ ∀ xi : ℝ,0 < xi → xi ≤ 1 → ∀ eps : ℝ,0 < eps →
      ∀ᶠ z : ℝ in atTop,1 < z ∧
      ∀ (R theta : ℝ),z^alpha ≤ R → xi/4 ≤ theta → theta ≤ xi →
      ∀ (H : ℕ) (C0 : ℤ),2 ≤ H → Int.gcd C0 (H : ℤ) = 1 →
        R^((4 : ℝ)/5) ≤ (H : ℝ) → (H : ℝ) ≤ R*(sourceZ z)^11 →
        max (H : ℝ) (|(C0 : ℝ)|/R)/(H : ℝ) ≤ (sourceZ z)^12 →
      ∃ (hw : 0 ≤ sourceW z) (hP : ∀ p ∈ primeBin R theta,p.Prime)
        (hlarge : ∀ p ∈ primeBin R theta,sourceW z < (p : ℝ)),
      ∀ E : ErdosLargePatternLaw.FullPattern (sourceW z) H → Prop,
        ((fullPrimeEvent (primeBin R theta) (sourceW z) H C0 hw hP hlarge E).card : ℝ)/
          ((primeBin R theta).card : ℝ) ≤ C*patternEventWeight (sourceW z) H E+eps := by
  obtain ⟨C,hC,hcount⟩ := source_full_event_count alpha halpha
  refine ⟨16*C,by positivity,?_⟩
  intro xi hxi hxi1 eps heps
  filter_upwards [hcount,source_pattern_error_normalized alpha xi eps halpha hxi hxi1 heps,
    source_model_population alpha xi halpha hxi hxi1,sourceW_tendsto_atTop.eventually_ge_atTop 0]
    with z hzcount hzerror hzpop hw
  refine ⟨hzcount.1,?_⟩
  intro R theta hRlo hthetal hthetau H C0 hH hC0 hHlo hHhi hratio
  have hpop := hzpop R theta hRlo hthetal hthetau
  have hR : 0 < R := by linarith [hpop.1]
  have hlog : 0 < Real.log R := Real.log_pos hpop.1
  have htheta : 0 < theta := (by positivity : (0 : ℝ) < xi/4).trans_le hthetal
  have htheta1 := hthetau.trans hxi1
  have hP : ∀ p ∈ primeBin R theta,p.Prime := fun p hp => ((mem_primeBin hR.le htheta.le p).mp hp).1
  have hlarge : ∀ p ∈ primeBin R theta,sourceW z < (p : ℝ) := fun p hp =>
    hpop.2.1.trans_lt ((mem_primeBin hR.le htheta.le p).mp hp).2.1
  refine ⟨hw,hP,hlarge,?_⟩
  intro E
  have hc := hzcount.2 R theta hRlo htheta htheta1 H C0 hH hC0 hHlo hHhi hw hP hlarge E
  have he := hzerror R theta hRlo hthetal hthetau H C0 (by omega) hratio
  have hlow : 0 < xi*R/(16*Real.log R) := by positivity
  have hPC : 0 < ((primeBin R theta).card : ℝ) := hlow.trans_le hpop.2.2
  have hcoef : C*theta*R/Real.log R ≤ (16*C)*((primeBin R theta).card : ℝ) := by
    apply (div_le_iff₀ hlog).mpr
    have hb := (div_le_iff₀ (show 0 < 16*Real.log R by positivity)).mp hpop.2.2
    have hm := mul_le_mul_of_nonneg_left hb hC.le
    have ht := mul_le_mul_of_nonneg_left hthetau (show 0 ≤ C*R by positivity)
    nlinarith only [hm,ht]
  have hmain : (C*theta*R/Real.log R*patternEventWeight (sourceW z) H E)/
      ((primeBin R theta).card : ℝ) ≤ (16*C)*patternEventWeight (sourceW z) H E := by
    apply (div_le_iff₀ hPC).mpr
    have hh := mul_le_mul_of_nonneg_right hcoef (patternEventWeight_nonneg (sourceW z) H E)
    nlinarith only [hh]
  have hd := div_le_div_of_nonneg_right hc hPC.le
  rw [add_div] at hd
  exact hd.trans (add_le_add hmain he)

end ErdosVarianceLargeMap


end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.ErdosVarianceLargeMap.source_full_pattern_domination_jb247_oai := @OAI.Erdos970.ErdosVarianceLargeMap.source_full_pattern_domination_jb247_oai
