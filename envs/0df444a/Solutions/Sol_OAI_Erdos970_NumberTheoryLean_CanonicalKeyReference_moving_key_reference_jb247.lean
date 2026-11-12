-- Prove2me | solution 1 for OAI.Erdos970.NumberTheoryLean.CanonicalKeyReference.moving_key_reference_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:08:58.770269+00:00
-- url     : https://prove2.me/submissions/c9c95fe7-6af2-41d1-8d7d-e0ec14f45404

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
import Mathlib.Analysis.Calculus.Deriv.Slope
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
import Mathlib.Analysis.SpecialFunctions.Exponential
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
import Mathlib.Data.Finset.Option
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
import Definitions.Def_OAIQ247J010
import Theorems.Thm_Erdos970_Mertens_LogZetaInteg_log_zeta_eq_integ_aux_jb247
import Theorems.Thm_Erdos970_Mertens_sum_M_eq_summand_le_jb247
import Theorems.Thm_OAI_Erdos970_NumberTheoryLean_ReferenceResidualSum_summed_source_residual_bound_jb247
import Theorems.Thm_OAI_Erdos970_NumberTheoryLean_UniformBoundaryCorrection_uniform_boundary_correction_div_jb247

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

lemma sum_sorted_products (s : Finset ℕ) (f : ℕ → ℝ) :
    (∑ l ∈ decreasingPrefixes s, (l.map f).prod) = ∏ p ∈ s, (1 + f p) := by
  rw [decreasingPrefixes, Finset.sum_image]
  · have hp (t : Finset ℕ) : ((t.sort (· ≥ ·)).map f).prod = ∏ p ∈ t, f p := by
      simpa only [Finset.sort_toFinset] using (List.prod_toFinset f (t.sort_nodup (· ≥ ·))).symm
    simp_rw [hp]
    exact (Finset.prod_one_add s).symm
  · intro t ht u hu h
    simpa only [Finset.sort_toFinset] using congrArg List.toFinset h

end ErdosPrimeInputs.PrimePrefixTail



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
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FiniteHistorySupport
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.FinitePathGeometry

open Set
open DerivativeWeights TransitionKernels

theorem nextGap_div_ratio {r t : ℝ} (ht : 0 < t) : nextGap r t / t = nextExponent r t := by
  unfold nextGap nextExponent
  field_simp

end NumberTheoryLean.FinitePathGeometry



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeRatioBins
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSingletonClassChainState _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeHistories

open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem terminal_append (w : ℝ) (z : Node) (ps qs : List ℕ) :
    terminal w z (ps++qs) = terminal w (terminal w z ps) qs := by
  exact List.foldl_append

end NumberTheoryLean.PrimeHistories

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

theorem omitted_lower_deviation {r x : ℝ} (hx : 0 < x) (homit : r-x < 2*x) :
    benchmark .even (r/x-1)-1 = -1 := by
  have hs : r/x-1 ≤ 2 := by
    have hd : r/x < 3 := (div_lt_iff₀ hx).mpr (by linarith)
    linarith
  rw [benchmark_even_below_two hs]
  ring

end NumberTheoryLean.ReferenceDifferentiation



namespace NumberTheoryLean.ReferenceAdmission

open _root_.Finset
open FinitePathGeometry PrimeTiltPrefixes
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass

theorem boundary_prime_exponent_upper {w : ℝ} (hw : 1 < w) {p : ℕ} (hp : p ∈ boundaryPrimes w) :
    primeExponent w p ≤ 2 := by
  obtain ⟨hpp,_⟩ := Finset.mem_filter.mp hp
  obtain ⟨hfloor,hprime⟩ := Nat.mem_primesLE.mp hpp
  have hp0 : (0:ℝ) < p := by exact_mod_cast hprime.pos
  apply (exponent_le_iff hw hp0).mpr
  exact (Nat.le_floor_iff (Real.rpow_pos_of_pos (by linarith : 0 < w) 2).le).mp hfloor

end NumberTheoryLean.ReferenceAdmission


namespace NumberTheoryLean.ReferenceCancellation

open _root_.MeasureTheory _root_.Set
open FinitePathGeometry LinearSieveFunctions BuchstabBridge ReferenceBenchmarkDecay
open ReferenceDifferentiation ReferenceAdmission

theorem upper_admission_above_two {r x : ℝ} (hx : 2 ≤ x) :
    childAdmitted .odd r x ↔ 2*x ≤ r-x := by
  change max (2*x) (x+2) ≤ r-x ↔ 2*x ≤ r-x
  rw [max_eq_left (by linarith)]

theorem actual_omitted_deviation_above_two {r x : ℝ} (hx : 2 ≤ x)
    (homit : ¬childAdmitted .odd r x) :
    benchmark .even (r/x-1)-1 = -1 := by
  rw [upper_admission_above_two hx] at homit
  exact omitted_lower_deviation (by linarith) (lt_of_not_ge homit)

end NumberTheoryLean.ReferenceCancellation



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_BoundaryPrimeMass
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.VariablePrimeTilt

open _root_.Finset
open ReferenceAdmission FinitePathGeometry
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

theorem variable_tilt_weight (t : ℝ) (ps : List ℕ) :
    (ps.map (fun p : ℕ => t*(p:ℝ)⁻¹)).prod=t^ps.length*prefixWeight ps := by
  induction ps with
  | nil => simp [prefixWeight]
  | cons p ps ih =>
    simp only [List.map_cons,List.prod_cons,List.length_cons,pow_succ,prefixWeight] at ih ⊢
    rw [ih]
    ring

end NumberTheoryLean.VariablePrimeTilt

end

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

open scoped BigOperators
namespace NumberTheoryLean.ReferencePruning
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

theorem sum_signedWeight (P : Finset ℕ) :
    (∑ ps ∈ decreasingPrefixes P,signedWeight ps) = survivorProduct P := by
  have h := sum_sorted_products P (fun p : ℕ => (-1 : ℝ)*(p : ℝ)⁻¹)
  simp_rw [VariablePrimeTilt.variable_tilt_weight] at h
  simpa only [signedWeight,survivorProduct,neg_one_mul,sub_eq_add_neg] using h

end NumberTheoryLean.ReferencePruning

end

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

theorem reference_polynomial_recurrence (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) :
    referencePolynomial w P i r=1-
      ∑ p ∈ P,if childAdmitted i r (primeExponent w p) then
        (p:ℝ)⁻¹*referencePolynomial w (P.filter (fun q => q<p)) i.flip (r-primeExponent w p) else 0 := by
  have h := sum_decreasing_by_first P (fun ps => if admitted w i r ps then signedWeight ps else 0)
  have he : referencePolynomial w P i r =
      ∑ ps ∈ decreasingPrefixes P,if admitted w i r ps then signedWeight ps else 0 := by
    rw [referencePolynomial,referencePrefixes,Finset.sum_filter]
    rfl
  have hnil : (if admitted w i r [] then signedWeight [] else 0)=1 := by
    simp [admitted,signedWeight,prefixWeight]
  rw [he,h,hnil]
  have hsum : (∑ p ∈ P,∑ ps ∈ decreasingPrefixes (P.filter (fun q => q<p)),
      if admitted w i r (p::ps) then signedWeight (p::ps) else 0) =
      -(∑ p ∈ P,if childAdmitted i r (primeExponent w p) then
        (p:ℝ)⁻¹*referencePolynomial w (P.filter (fun q => q<p)) i.flip (r-primeExponent w p) else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    by_cases hc : childAdmitted i r (primeExponent w p)
    · rw [ite_eq_left hc,referencePolynomial,referencePrefixes,Finset.sum_filter]
      rw [Finset.mul_sum,← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro ps _
      simp only [admitted,hc,true_and,signedWeight,List.length_cons,pow_succ,
        prefixWeight,List.map_cons,List.prod_cons]
      split_ifs <;> ring
    · simp [admitted,hc]
  rw [hsum]
  ring

end NumberTheoryLean.ReferencePrefixRecurrence

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReferenceCutoffRecurrence
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSingletonClassChainState _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_none _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_some
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferenceWeightedRecurrence

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry ReferenceAdmission ReferencePruning ReferencePrefixRecurrence
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.HarmonicPrimeMeasure

theorem weighted_reference_recurrence (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) (F : List ℕ → ℝ) :
    weightedValue w P i r F=F []-
      ∑ p ∈ P,if childAdmitted i r (primeExponent w p) then
        (p:ℝ)⁻¹*weightedValue w (P.filter (fun q => q<p)) i.flip (r-primeExponent w p) (fun ps => F (p::ps)) else 0 := by
  have h := sum_decreasing_by_first P (fun ps => if admitted w i r ps then signedWeight ps*F ps else 0)
  have he : weightedValue w P i r F =
      ∑ ps ∈ decreasingPrefixes P,if admitted w i r ps then signedWeight ps*F ps else 0 := by
    rw [weightedValue,referencePrefixes,Finset.sum_filter]
  have hnil : (if admitted w i r [] then signedWeight []*F [] else 0)=F [] := by
    simp [admitted,signedWeight,prefixWeight]
  rw [he,h,hnil]
  have hsum : (∑ p ∈ P,∑ ps ∈ decreasingPrefixes (P.filter (fun q => q<p)),
      if admitted w i r (p::ps) then signedWeight (p::ps)*F (p::ps) else 0) =
      -(∑ p ∈ P,if childAdmitted i r (primeExponent w p) then
        (p:ℝ)⁻¹*weightedValue w (P.filter (fun q => q<p)) i.flip (r-primeExponent w p) (fun ps => F (p::ps)) else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    by_cases hc : childAdmitted i r (primeExponent w p)
    · rw [ite_eq_left hc,weightedValue,referencePrefixes,Finset.sum_filter]
      rw [Finset.mul_sum,← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro ps _
      simp only [admitted,hc,true_and,signedWeight,List.length_cons,pow_succ,
        prefixWeight,List.map_cons,List.prod_cons]
      split_ifs <;> ring
    · simp [admitted,hc]
  rw [hsum]
  ring

end NumberTheoryLean.ReferenceWeightedRecurrence

end

section

namespace NumberTheoryLean.ReferenceForestTelescoping

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry PrimeHistories ReferenceAdmission ReferencePruning ReferenceWeightedRecurrence
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem suffixPrimes_nil (P : Finset ℕ) : suffixPrimes P []=P := by simp [suffixPrimes]

theorem suffixPrimes_cons (P : Finset ℕ) (p : ℕ) (ps : List ℕ) :
    suffixPrimes P (p::ps)=suffixPrimes (P.filter (fun q => q<p)) ps := by
  ext q
  simp [suffixPrimes,and_assoc,and_left_comm,and_comm]

theorem forestSum_recurrence (w : ℝ) (P : Finset ℕ) (z : Node) (G : Finset ℕ → Node → ℝ) :
    forestSum w P z G=G P z-
      ∑ p ∈ P,if childAdmitted z.side z.gap (primeExponent w p) then
        (p:ℝ)⁻¹*forestSum w (P.filter (fun q => q<p)) (step w z p) G else 0 := by
  have h := weighted_reference_recurrence w P z.side z.gap (fun ps => G (suffixPrimes P ps) (terminal w z ps))
  simpa only [forestSum,suffixPrimes_nil,terminal_nil,suffixPrimes_cons,terminal_cons,step] using h

theorem actual_forest_telescoping (w : ℝ) (G : Finset ℕ → Node → ℝ) (P : Finset ℕ) (z : Node) :
    forestSum w P z (recurrenceResidual w G)=G P z := by
  revert z
  refine Finset.strongInductionOn P ?_
  intro P ih z
  rw [forestSum_recurrence]
  have hs : (∑ p ∈ P,if childAdmitted z.side z.gap (primeExponent w p) then
      (p:ℝ)⁻¹*forestSum w (P.filter (fun q => q<p)) (step w z p) (recurrenceResidual w G) else 0)=
      ∑ p ∈ P,if childAdmitted z.side z.gap (primeExponent w p) then
        (p:ℝ)⁻¹*G (P.filter (fun q => q<p)) (step w z p) else 0 := by
    apply Finset.sum_congr rfl
    intro p hp
    have hsmall : P.filter (fun q => q<p) ⊂ P :=
      Finset.filter_ssubset.mpr ⟨p,hp,lt_irrefl p⟩
    rw [ih _ hsmall]
  rw [hs,recurrenceResidual]
  ring

end NumberTheoryLean.ReferenceForestTelescoping

end

section

namespace NumberTheoryLean.ReferenceCutoffRecurrence

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry PrimeHistories ReferenceAdmission ReferencePruning
open ReferencePrefixRecurrence ReferenceWeightedRecurrence ReferenceForestTelescoping
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem above_disjoint {P Q : Finset ℕ} (h : Above P Q) : Disjoint P Q := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact lt_irrefl p (h p hp p hq)

theorem union_filter_at_high {P Q : Finset ℕ} (h : Above P Q) {p : ℕ} (hp : p ∈ P) :
    (P∪Q).filter (fun q => q<p)=(P.filter (fun q => q<p))∪Q := by
  rw [Finset.filter_union,Finset.filter_eq_self.mpr (h p hp)]

theorem union_filter_at_low {P Q : Finset ℕ} (h : Above P Q) {p : ℕ} (hp : p ∈ Q) :
    (P∪Q).filter (fun q => q<p)=Q.filter (fun q => q<p) := by
  ext q
  simp only [Finset.mem_filter,Finset.mem_union]
  constructor
  · rintro ⟨hq,hqp⟩
    rcases hq with hq | hq
    · exact False.elim (lt_asymm hqp (h q hq p hp))
    · exact ⟨hq,hqp⟩
  · rintro ⟨hq,hqp⟩
    exact ⟨Or.inr hq,hqp⟩

theorem cutoff_polynomial_recurrence (w : ℝ) {P Q : Finset ℕ} (h : Above P Q) (i : Side) (r : ℝ) :
    referencePolynomial w (P∪Q) i r=referencePolynomial w Q i r-
      ∑ p ∈ P,if childAdmitted i r (primeExponent w p) then
        (p:ℝ)⁻¹*referencePolynomial w ((P.filter (fun q => q<p))∪Q) i.flip (r-primeExponent w p) else 0 := by
  have hfull := reference_polynomial_recurrence w (P∪Q) i r
  have hlow := reference_polynomial_recurrence w Q i r
  rw [Finset.sum_union (above_disjoint h)] at hfull
  have hh : (∑ p ∈ P,if childAdmitted i r (primeExponent w p) then
        (p:ℝ)⁻¹*referencePolynomial w ((P∪Q).filter (fun q => q<p)) i.flip (r-primeExponent w p) else 0)=
      ∑ p ∈ P,if childAdmitted i r (primeExponent w p) then
        (p:ℝ)⁻¹*referencePolynomial w ((P.filter (fun q => q<p))∪Q) i.flip (r-primeExponent w p) else 0 := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [union_filter_at_high h hp]
  have hl : (∑ p ∈ Q,if childAdmitted i r (primeExponent w p) then
        (p:ℝ)⁻¹*referencePolynomial w ((P∪Q).filter (fun q => q<p)) i.flip (r-primeExponent w p) else 0)=
      ∑ p ∈ Q,if childAdmitted i r (primeExponent w p) then
        (p:ℝ)⁻¹*referencePolynomial w (Q.filter (fun q => q<p)) i.flip (r-primeExponent w p) else 0 := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [union_filter_at_low h hp]
  rw [hh,hl] at hfull
  linarith

theorem difference_residual (w : ℝ) {P Q : Finset ℕ} (h : Above P Q)
    (B : Finset ℕ → Node → ℝ) (z : Node) :
    recurrenceResidual w (fun S y => referencePolynomial w (S∪Q) y.side y.gap-B S y) P z=
      cutoffInsertion w Q B P z := by
  have hrec := cutoff_polynomial_recurrence w h z.side z.gap
  have hsum : (∑ p ∈ P,if childAdmitted z.side z.gap (primeExponent w p) then
      (p:ℝ)⁻¹*(referencePolynomial w ((P.filter (fun q => q<p))∪Q) (step w z p).side (step w z p).gap-
        B (P.filter (fun q => q<p)) (step w z p)) else 0)=
    (∑ p ∈ P,if childAdmitted z.side z.gap (primeExponent w p) then
      (p:ℝ)⁻¹*referencePolynomial w ((P.filter (fun q => q<p))∪Q) z.side.flip (z.gap-primeExponent w p) else 0)-
    ∑ p ∈ P,if childAdmitted z.side z.gap (primeExponent w p) then
      (p:ℝ)⁻¹*B (P.filter (fun q => q<p)) (step w z p) else 0 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    split_ifs <;> simp [step,mul_sub]
  unfold recurrenceResidual cutoffInsertion
  dsimp only
  rw [hsum]
  linarith

theorem finite_cutoff_decomposition (w : ℝ) {P Q : Finset ℕ} (h : Above P Q)
    (B : Finset ℕ → Node → ℝ) (z : Node) :
    referencePolynomial w (P∪Q) z.side z.gap-B P z=
      forestSum w P z (cutoffInsertion w Q B) := by
  let G : Finset ℕ → Node → ℝ := fun S y => referencePolynomial w (S∪Q) y.side y.gap-B S y
  have ht := actual_forest_telescoping w G P z
  change G P z=_
  rw [← ht]
  unfold forestSum weightedValue
  apply Finset.sum_congr rfl
  intro ps _hp
  have hsub : Above (suffixPrimes P ps) Q := by
    intro p hp q hq
    exact h p (Finset.mem_filter.mp hp).1 q hq
  dsimp only
  rw [show recurrenceResidual w G (suffixPrimes P ps) (terminal w z ps)=
      cutoffInsertion w Q B (suffixPrimes P ps) (terminal w z ps) from difference_residual w hsub B _]

end NumberTheoryLean.ReferenceCutoffRecurrence

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

theorem boundary_subset_source {w b : ℝ} (hw : 1 < w) (hb : 2 < b) (closed : Bool) :
    boundaryPrimes w ⊆ sourcePrimes w b closed := by
  intro p hp
  have hpl := (sourcePrimes_membership hw 2 true p).mp (by rwa [sourcePrimes_boundary])
  apply (sourcePrimes_membership hw b closed p).mpr
  refine ⟨hpl.1,hpl.2.1,?_⟩
  have hle : primeExponent w p ≤ 2 := hpl.2.2
  cases closed with
  | false => exact hle.trans_lt hb
  | true => exact hle.trans hb.le

theorem sourcePrimes_partition {w b : ℝ} (hw : 1 < w) (hb : 2 < b) (closed : Bool) :
    sourcePrimes w b closed=highPrimes w b closed ∪ boundaryPrimes w := by
  ext p
  constructor
  · intro hp
    by_cases hhi : w^(2:ℝ)<(p:ℝ)
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hp,hhi⟩))
    · have hpm := (sourcePrimes_membership hw b closed p).mp hp
      apply Finset.mem_union.mpr
      right
      rw [← sourcePrimes_boundary]
      apply (sourcePrimes_membership hw 2 true p).mpr
      refine ⟨hpm.1,hpm.2.1,?_⟩
      exact (exponent_le_iff hw (by exact_mod_cast hpm.1.pos)).mpr (le_of_not_gt hhi)
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Finset.mem_filter.mp hp).1
    · exact boundary_subset_source hw hb closed hp

theorem highPrimes_above_boundary {w b : ℝ} (hw : 1 < w) (closed : Bool) :
    Above (highPrimes w b closed) (boundaryPrimes w) := by
  intro p hp q hq
  have hpHi := (Finset.mem_filter.mp hp).2
  have hqB := boundary_prime_exponent_upper hw hq
  have hqP : q.Prime := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hq).1).2
  have hqLe := (exponent_le_iff hw (by exact_mod_cast hqP.pos)).mp hqB
  exact_mod_cast hqLe.trans_lt hpHi

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

end NumberTheoryLean.ReferenceProductErrors

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ReferenceEulerRecurrence
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferenceEulerRecurrence

open _root_.Finset
open ReferencePruning ReferencePrefixRecurrence ReferenceCutoffRecurrence
open ReferenceSourcePrimeSets ReferenceProductsBasics ReferenceMertens ReferenceAdmission
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.HarmonicPrimeMeasure

lemma signedWeight_cons (p : ℕ) (ps : List ℕ) :
    signedWeight (p::ps)=(-(p:ℝ)⁻¹)*signedWeight ps := by
  simp only [signedWeight,List.length_cons,pow_succ,prefixWeight,List.map_cons,List.prod_cons]
  ring

theorem survivor_first_recurrence (P : Finset ℕ) :
    survivorProduct P=1-∑ p ∈ P,(p:ℝ)⁻¹*survivorProduct (P.filter (fun q => q<p)) := by
  have h := sum_decreasing_by_first P signedWeight
  rw [sum_signedWeight] at h
  have hnil : signedWeight []=1 := by simp [signedWeight,prefixWeight]
  rw [hnil] at h
  have hs : (∑ p ∈ P,∑ ps ∈ decreasingPrefixes (P.filter (fun q => q<p)),signedWeight (p::ps))=
      -(∑ p ∈ P,(p:ℝ)⁻¹*survivorProduct (P.filter (fun q => q<p))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    simp_rw [signedWeight_cons]
    rw [← Finset.mul_sum,sum_signedWeight]
    ring
  rw [hs] at h
  linarith

theorem survivor_cutoff_recurrence {P Q : Finset ℕ} (h : Above P Q) :
    survivorProduct (P∪Q)=survivorProduct Q-
      ∑ p ∈ P,(p:ℝ)⁻¹*survivorProduct ((P.filter (fun q => q<p))∪Q) := by
  have hf := survivor_first_recurrence (P∪Q)
  have hl := survivor_first_recurrence Q
  rw [Finset.sum_union (above_disjoint h)] at hf
  have hhi : (∑ p ∈ P,(p:ℝ)⁻¹*survivorProduct ((P∪Q).filter (fun q => q<p)))=
      ∑ p ∈ P,(p:ℝ)⁻¹*survivorProduct ((P.filter (fun q => q<p))∪Q) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [union_filter_at_high h hp]
  have hlo : (∑ p ∈ Q,(p:ℝ)⁻¹*survivorProduct ((P∪Q).filter (fun q => q<p)))=
      ∑ p ∈ Q,(p:ℝ)⁻¹*survivorProduct (Q.filter (fun q => q<p)) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [union_filter_at_low h hp]
  rw [hhi,hlo] at hf
  linarith

theorem referenceProduct_eq_survivor (w b : ℝ) (closed : Bool) :
    referenceProduct w b closed=survivorProduct (sourcePrimes w b closed) := rfl

theorem highPrimes_at_selected {w b : ℝ} (hw : 1 < w) (closed : Bool) {p : ℕ}
    (hp : p ∈ sourcePrimes w b closed) :
    highPrimes w (primeExponent w p) false=(highPrimes w b closed).filter (fun q => q<p) := by
  ext q
  simp only [highPrimes,Finset.mem_filter,sourcePrimes_at_selected hw closed hp]
  tauto

theorem actual_product_cutoff_identity {w b : ℝ} (hw : 1 < w) (hb : 2 < b) (closed : Bool) :
    referenceProduct w b closed=referenceProduct w 2 true-
      ∑ p ∈ highPrimes w b closed,(p:ℝ)⁻¹*referenceProduct w (primeExponent w p) false := by
  have hsep := highPrimes_above_boundary (b:=b) hw closed
  have hr := survivor_cutoff_recurrence hsep
  have hpart := sourcePrimes_partition hw hb closed
  rw [← hpart] at hr
  have hbase : survivorProduct (boundaryPrimes w)=referenceProduct w 2 true := by
    rw [referenceProduct_eq_survivor,sourcePrimes_boundary]
  rw [hbase] at hr
  change referenceProduct w b closed=referenceProduct w 2 true-
    (∑ p ∈ highPrimes w b closed,(p:ℝ)⁻¹*survivorProduct (((highPrimes w b closed).filter (fun q => q<p))∪boundaryPrimes w)) at hr
  rw [hr]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have hpS : p ∈ sourcePrimes w b closed := (Finset.mem_filter.mp hp).1
  have hchild := sourcePrimes_at_selected hw closed hpS
  rw [hpart,union_filter_at_high hsep hp] at hchild
  rw [referenceProduct_eq_survivor,hchild]

end NumberTheoryLean.ReferenceEulerRecurrence

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReferenceLocalResidual
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSingletonClassChainState _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferenceLocalResidual

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry PrimeHistories PrimeTiltGeometry ReferenceAdmission ReferencePruning
open ReferenceSourcePrimeSets ReferenceEulerRecurrence ReferenceMertens ReferenceDifferentiation
open ReferenceBenchmarkDecay ReferenceCancellation BoundaryAnomaly
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem admitted_child_benchmark {w : ℝ} (hw : 1 < w) (z : Node) {p : ℕ}
    (hp : p ∈ highPrimes w z.cutoff z.closed) (ha : childAdmitted z.side z.gap (primeExponent w p)) :
    nodeBenchmark w (step w z p)=referenceProduct w (primeExponent w p) false*
      benchmark z.side.flip (childRatio w z.gap p) := by
  have hxp := (highPrimes_membership hw z.cutoff z.closed p).mp hp |>.2.1
  unfold nodeBenchmark
  simp only [step]
  congr 1
  cases hi : z.side with
  | even => rfl
  | odd =>
    have hh : 2*primeExponent w p ≤ z.gap-primeExponent w p := by
      rw [hi] at ha
      exact (upper_admission_above_two hxp.le).mp ha
    have hc : 2 ≤ childRatio w z.gap p := by
      unfold childRatio
      have hd : 3 ≤ z.gap/primeExponent w p := (le_div_iff₀ (by linarith)).mpr (by linarith)
      linarith
    exact parent_even_eq_ordinary hc

theorem omitted_child_benchmark {w : ℝ} (hw : 1 < w) (z : Node) {p : ℕ}
    (hp : p ∈ highPrimes w z.cutoff z.closed) (ha : ¬childAdmitted z.side z.gap (primeExponent w p)) :
    benchmark z.side.flip (childRatio w z.gap p)=0 := by
  have hxp := (highPrimes_membership hw z.cutoff z.closed p).mp hp |>.2.1
  cases hi : z.side with
  | even => exact False.elim (ha (by rw [hi]; trivial))
  | odd =>
    have hh := actual_omitted_deviation_above_two hxp.le (by rwa [hi] at ha)
    change benchmark .even (z.gap/primeExponent w p-1)=0
    linarith

theorem admitted_benchmark_sum {w : ℝ} (hw : 1 < w) (z : Node) :
    (∑ p ∈ highPrimes w z.cutoff z.closed,if childAdmitted z.side z.gap (primeExponent w p) then
      (p:ℝ)⁻¹*nodeBenchmark w (step w z p) else 0)=
    ∑ p ∈ highPrimes w z.cutoff z.closed,(p:ℝ)⁻¹*referenceProduct w (primeExponent w p) false*
      benchmark z.side.flip (childRatio w z.gap p) := by
  apply Finset.sum_congr rfl
  intro p hp
  by_cases ha : childAdmitted z.side z.gap (primeExponent w p)
  · rw [ite_eq_left ha,admitted_child_benchmark hw z hp ha]
    ring
  · rw [ite_eq_right ha,omitted_child_benchmark hw z hp ha,mul_zero]

theorem source_insertion_identity {w : ℝ} (hw : 1 < w) (z : Node) (hb : 2 < z.cutoff) :
    sourceInsertion w z=anomaly w z.side z.gap+sourceResidual w z := by
  have hp := actual_product_cutoff_identity hw hb z.closed
  have hsum : (∑ p ∈ highPrimes w z.cutoff z.closed,(p:ℝ)⁻¹*referenceProduct w (primeExponent w p) false*
      (benchmark z.side.flip (childRatio w z.gap p)-1))=
    (∑ p ∈ highPrimes w z.cutoff z.closed,(p:ℝ)⁻¹*referenceProduct w (primeExponent w p) false*
      benchmark z.side.flip (childRatio w z.gap p))-
    ∑ p ∈ highPrimes w z.cutoff z.closed,(p:ℝ)⁻¹*referenceProduct w (primeExponent w p) false := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    ring
  have hbase : survivorProduct (boundaryPrimes w)=referenceProduct w 2 true := by
    rw [referenceProduct_eq_survivor,sourcePrimes_boundary]
  unfold sourceInsertion sourceResidual anomaly
  rw [admitted_benchmark_sum hw z,hsum,hbase]
  unfold nodeBenchmark
  linarith

end NumberTheoryLean.ReferenceLocalResidual

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeCompactWeights
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeBinMembership

open _root_.Set _root_.Finset
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes PrimeHistories
open PrimeRatioBins NormalizedPrimeBins PrimeKilledChain
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem step_consistent {w ell S : ℝ} {z : Node} {p : ℕ} (hell : 0 ≤ ell)
    (hr : 0 < z.gap) (hs : Valid z.side z.ratio) (hp : p ∈ nodeChildren w ell S z) :
    Consistent (step w z p) := by
  have hx := child_exponent_positive hell hp
  have ht := valid_pos (child_valid hs hp)
  change primeExponent w p = (z.gap-primeExponent w p)/childRatio w z.gap p
  rw [← nextGap_childRatio hr hx ht, nextGap_div_ratio ht, nextExponent_childRatio hr hx]

end NumberTheoryLean.PrimeBinMembership

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_ReferenceHistoryAdmission
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferenceHistoryAdmission

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry PrimeHistories PrimeTiltGeometry PrimeBinMembership ActualPrimeHigh
open ReferenceAdmission ReferencePruning ReferencePrefixRecurrence ReferenceSourcePrimeSets ReferenceEulerRecurrence
open ReferenceCancellation
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.HarmonicPrimeMeasure

theorem cap_lower_ratio {w : ℝ} {z : Node} {p : ℕ} (hs : Valid z.side z.ratio) (hz : Consistent z)
    (hx : 0 < primeExponent w p) (hcap : capGuard z.closed z.cutoff (primeExponent w p)) :
    z.ratio-1 ≤ childRatio w z.gap p := by
  have hxp : primeExponent w p ≤ z.cutoff := by
    cases hcl : z.closed with
    | false => have h : primeExponent w p < z.cutoff := by simpa [capGuard,hcl] using hcap
               exact h.le
    | true => simpa [capGuard,hcl] using hcap
  have he := (eq_div_iff (ne_of_gt (valid_pos hs))).mp hz
  have hm := mul_le_mul_of_nonneg_right hxp (valid_pos hs).le
  have hd : z.ratio ≤ z.gap/primeExponent w p := (le_div_iff₀ hx).mpr (by nlinarith)
  unfold childRatio
  linarith

theorem uncapped_child_iff {w : ℝ} (hw : 1 < w) {z : Node} (hs : Valid z.side z.ratio)
    (hz : Consistent z) (p : ℕ) :
    p ∈ uncappedChildren w 2 z ↔ p ∈ highPrimes w z.cutoff z.closed ∧
      childAdmitted z.side z.gap (primeExponent w p) := by
  constructor
  · intro hp
    obtain ⟨hprime,hx,hcap,hmin⟩ := Finset.mem_filter.mp hp
    have hpP := (Nat.mem_primesLE.mp hprime).2
    refine ⟨(highPrimes_membership hw z.cutoff z.closed p).mpr ⟨hpP,hx,hcap⟩,?_⟩
    cases hi : z.side with
    | even => trivial
    | odd =>
      rw [hi] at hmin
      apply (upper_admission_above_two hx.le).mpr
      have h2 : 2 ≤ childRatio w z.gap p := (le_max_left _ _).trans hmin
      have hdiv : 3 ≤ z.gap/primeExponent w p := by unfold childRatio at h2; linarith
      have hm := (le_div_iff₀ (by linarith : 0 < primeExponent w p)).mp hdiv
      linarith
  · rintro ⟨hp,ha⟩
    obtain ⟨hpP,hx,hcap⟩ := (highPrimes_membership hw z.cutoff z.closed p).mp hp
    have hx0 : 0 < primeExponent w p := by linarith
    have hxp : primeExponent w p ≤ z.cutoff := by
      cases hcl : z.closed with
      | false => have h : primeExponent w p < z.cutoff := by simpa [capGuard,hcl] using hcap
                 exact h.le
      | true => simpa [capGuard,hcl] using hcap
    have hpLe := (exponent_le_iff hw (by exact_mod_cast hpP.pos)).mp hxp
    have hprime := Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff (Real.rpow_pos_of_pos (by linarith : 0 < w) z.cutoff).le).mpr hpLe,hpP⟩
    apply Finset.mem_filter.mpr
    refine ⟨hprime,hx,hcap,?_⟩
    have hlo := cap_lower_ratio hs hz hx0 hcap
    cases hi : z.side with
    | even => exact hlo
    | odd =>
      rw [hi] at ha
      apply max_le
      · have hh := (upper_admission_above_two hx.le).mp ha
        unfold childRatio
        have hd : 3 ≤ z.gap/primeExponent w p := (le_div_iff₀ hx0).mpr (by linarith)
        linarith
      · exact hlo

theorem uncapped_child_invariants {w : ℝ} {z : Node} {p : ℕ}
    (hs : Valid z.side z.ratio) (hr : 0 < z.gap) (hp : p ∈ uncappedChildren w 2 z) :
    Valid (step w z p).side (step w z p).ratio ∧ 0 < (step w z p).gap ∧ Consistent (step w z p) := by
  have hone : uncappedAllowed w 2 z [p] := ⟨hp,trivial⟩
  obtain ⟨U,_hU,hU⟩ := (uncapped_iff_exists_ceiling w 2 z [p]).mp hone
  have hc := ((allowed_cons w 2 U z p []).mp hU).1
  exact ⟨child_valid hs hc,child_gap_positive (by norm_num) hr hs hc,step_consistent (by norm_num) hr hs hc⟩

theorem decreasing_cons_iff (P : Finset ℕ) (p : ℕ) (ps : List ℕ) :
    p::ps ∈ decreasingPrefixes P ↔ p ∈ P ∧ ps ∈ decreasingPrefixes (P.filter (fun q => q<p)) := by
  constructor
  · intro h
    have hp := (mem_decreasingPrefixes.mp h).2 p (by simp)
    refine ⟨hp,?_⟩
    have ht := (append_mem_decreasing_iff (singleton_prefix_mem hp)).mp h
    simpa [suffixPrimes] using ht
  · rintro ⟨hp,ht⟩
    apply (append_mem_decreasing_iff (singleton_prefix_mem hp)).mpr
    simpa [suffixPrimes] using ht

theorem referencePrefixes_cons_iff (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) (p : ℕ) (ps : List ℕ) :
    p::ps ∈ referencePrefixes w P i r ↔ p ∈ P ∧ childAdmitted i r (primeExponent w p) ∧
      ps ∈ referencePrefixes w (P.filter (fun q => q<p)) i.flip (r-primeExponent w p) := by
  simp only [referencePrefixes,Finset.mem_filter,decreasing_cons_iff,admitted]
  tauto

theorem reference_history_iff {w : ℝ} (hw : 1 < w) {z : Node} (hs : Valid z.side z.ratio)
    (hr : 0 < z.gap) (hz : Consistent z) (ps : List ℕ) :
    ps ∈ referencePrefixes w (highPrimes w z.cutoff z.closed) z.side z.gap ↔ uncappedAllowed w 2 z ps := by
  induction ps generalizing z with
  | nil => simp [referencePrefixes,mem_decreasingPrefixes,admitted,uncappedAllowed]
  | cons p ps ih =>
    rw [referencePrefixes_cons_iff]
    constructor
    · rintro ⟨hp,ha,ht⟩
      have hpU := (uncapped_child_iff hw hs hz p).mpr ⟨hp,ha⟩
      obtain ⟨hvs,hrs,hzs⟩ := uncapped_child_invariants hs hr hpU
      have hpS : p ∈ sourcePrimes w z.cutoff z.closed := (Finset.mem_filter.mp hp).1
      have he := highPrimes_at_selected hw z.closed hpS
      rw [← he] at ht
      exact ⟨hpU,(ih hvs hrs hzs).mp ht⟩
    · rintro ⟨hpU,htU⟩
      obtain ⟨hp,ha⟩ := (uncapped_child_iff hw hs hz p).mp hpU
      obtain ⟨hvs,hrs,hzs⟩ := uncapped_child_invariants hs hr hpU
      have ht := (ih hvs hrs hzs).mpr htU
      have hpS : p ∈ sourcePrimes w z.cutoff z.closed := (Finset.mem_filter.mp hp).1
      have he := highPrimes_at_selected hw z.closed hpS
      change ps ∈ referencePrefixes w (highPrimes w (primeExponent w p) false) z.side.flip (z.gap-primeExponent w p) at ht
      rw [he] at ht
      exact ⟨hp,ha,ht⟩

theorem reference_family_eq_uncapped {w : ℝ} (hw : 1 < w) {z : Node} (hs : Valid z.side z.ratio)
    (hr : 0 < z.gap) (hz : Consistent z) :
    referencePrefixes w (highPrimes w z.cutoff z.closed) z.side z.gap=uncappedPrefixes w 2 z := by
  ext ps
  rw [reference_history_iff hw hs hr hz,mem_uncappedPrefixes hw]

end NumberTheoryLean.ReferenceHistoryAdmission

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_RepresentativeStopGeometry
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.RepresentativeStopGeometry

open NumberTheoryLean.ReferenceAdmission

theorem sourceHeight_mono {x y : ℝ} (hxy : x ≤ y) : sourceHeight x ≤ sourceHeight y := by
  exact max_le_max (by linarith) (by linarith)

theorem representative_safety_admits {r rrep x xrep Delta : ℝ}
    (hDelta : 0 ≤ Delta) (hx : x ≤ xrep) (hr : rrep ≤ r)
    (hsafe : sourceHeight xrep+3*Delta ≤ rrep) : sourceHeight x ≤ r := by
  have hH := sourceHeight_mono hx
  linarith

theorem representative_to_actual_window {b₀ b₁ r rrep x xrep Delta h : ℝ}
    (hx : 0 < x) (hxr : x ≤ xrep) (hxh : xrep ≤ x+h)
    (hr : rrep ≤ r) (hrD : r ≤ rrep+Delta)
    (hb₀ : b₀ ≤ xrep) (hb₁ : xrep ≤ b₁)
    (hs₀ : 206/100 ≤ rrep/xrep) (hs₁ : rrep/xrep ≤ 216/100)
    (hsmall : Delta+(218/100)*h ≤ (2/100)*b₀) :
    b₀-h ≤ x ∧ x ≤ b₁ ∧ 204/100 ≤ r/x ∧ r/x ≤ 218/100 := by
  have hxp : 0 < xrep := hx.trans_le hxr
  have hlow := (le_div_iff₀ hxp).mp hs₀
  have hhigh := (div_le_iff₀ hxp).mp hs₁
  refine ⟨by linarith,hxr.trans hb₁,?_,?_⟩
  · apply (le_div_iff₀ hx).mpr
    nlinarith
  · apply (div_le_iff₀ hx).mpr
    nlinarith

end NumberTheoryLean.RepresentativeStopGeometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RepresentativeAdmission
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSingletonClassChainState _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_none _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_some
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.RepresentativeAdmission

open FinitePathGeometry PrimeHistories ReferenceAdmission RepresentativeStopGeometry
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem terminal_gap_sum (w : ℝ) (z : Node) (ps : List ℕ) :
    (terminal w z ps).gap = z.gap-(ps.map (primeExponent w)).sum := by
  induction ps generalizing z with
  | nil => simp
  | cons p ps ih =>
    rw [terminal_cons,ih,List.map_cons,List.sum_cons]
    change z.gap-primeExponent w p-(ps.map (primeExponent w)).sum = _
    ring

theorem representativeGap_le_actual (w : ℝ) (rep : ℕ → ℝ) (z : Node) (ps : List ℕ)
    (hrep : ∀ p ∈ ps,primeExponent w p ≤ rep p) :
    representativeGap rep z.gap ps ≤ (terminal w z ps).gap := by
  have hs : (ps.map (primeExponent w)).sum ≤ (ps.map rep).sum := by
    induction ps with
    | nil => simp
    | cons p ps ih =>
      simp only [List.map_cons,List.sum_cons]
      exact add_le_add (hrep p (by simp)) (ih (fun q hq => hrep q (by simp [hq])))
  rw [terminal_gap_sum]
  exact sub_le_sub_left hs z.gap

theorem admitted_of_even_prefix_safety (w : ℝ) (z : Node) (ps : List ℕ)
    (hsafe : ∀ pre : List ℕ,∀ p : ℕ,∀ tail : List ℕ,ps = pre++p::tail →
      (terminal w z (pre++[p])).side = .even →
      sourceHeight (primeExponent w p) ≤ (terminal w z (pre++[p])).gap) :
    admitted w z.side z.gap ps := by
  induction ps generalizing z with
  | nil => trivial
  | cons p ps ih =>
    constructor
    · cases hi : z.side with
      | even => trivial
      | odd =>
        have h := hsafe [] p ps rfl (by simp [terminal,step,hi,Side.flip])
        exact h
    · apply ih (step w z p)
      intro pre q tail htail hside
      have he : p::ps = (p::pre)++q::tail := by rw [List.cons_append,htail]
      have h := hsafe (p::pre) q tail he (by simpa only [List.cons_append,terminal_cons] using hside)
      simpa only [List.cons_append,terminal_cons] using h

theorem representative_safety_preserves_admission (w : ℝ) (rep : ℕ → ℝ)
    (z : Node) (ps : List ℕ) {Delta : ℝ} (hDelta : 0 ≤ Delta)
    (hrep : ∀ p ∈ ps,primeExponent w p ≤ rep p)
    (hsafe : ∀ pre : List ℕ,∀ p : ℕ,∀ tail : List ℕ,ps = pre++p::tail →
      (terminal w z (pre++[p])).side = .even →
      sourceHeight (rep p)+3*Delta ≤ representativeGap rep z.gap (pre++[p])) :
    admitted w z.side z.gap ps := by
  apply admitted_of_even_prefix_safety w z ps
  intro pre p tail heq hside
  have hsub : ∀ q ∈ pre++[p],q ∈ ps := by
    intro q hq
    rw [heq]
    simp only [List.mem_append,List.mem_cons] at hq ⊢
    tauto
  have hg := representativeGap_le_actual w rep z (pre++[p]) (fun q hq => hrep q (hsub q hq))
  have hx : primeExponent w p ≤ rep p := hrep p (hsub p (by simp))
  exact representative_safety_admits hDelta hx hg (hsafe pre p tail heq hside)

end NumberTheoryLean.RepresentativeAdmission

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeBinRepresentatives
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSingletonClassChainState _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_none _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_some
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeBinRepresentatives

open ErdosInversePrimeBin ErdosPrimeInputs.HarmonicPrimeMeasure
open PrimeHistories RepresentativeAdmission

theorem bin_exponent_bounds {w R xi : ℝ} (hw : 1 < w) (hR : 0 < R) (hxi : 0 ≤ xi)
    {p : ℕ} (hp : p ∈ primeBin R xi) :
    leftExponent w R < primeExponent w p ∧ primeExponent w p ≤ rightExponent w R xi := by
  obtain ⟨hprime,hlo,hhi⟩ := (mem_primeBin hR.le hxi p).mp hp
  have hp0 : (0:ℝ) < p := by exact_mod_cast hprime.pos
  exact ⟨div_lt_div_of_pos_right (Real.log_lt_log hR hlo) (Real.log_pos hw),
    div_le_div_of_nonneg_right (Real.log_le_log hp0 hhi) (Real.log_pos hw).le⟩

theorem bin_exponent_width {w R xi : ℝ} (hR : 0 < R) (hxi : 0 ≤ xi) :
    rightExponent w R xi-leftExponent w R = Real.log (1+xi)/Real.log w := by
  rw [rightExponent,leftExponent,Real.log_mul (by positivity : (1+xi:ℝ) ≠ 0) hR.ne']
  ring

theorem representative_error {w R xi : ℝ} (hw : 1 < w) (hR : 0 < R) (hxi : 0 ≤ xi)
    {p : ℕ} (hp : p ∈ primeBin R xi) :
    0 ≤ rightExponent w R xi-primeExponent w p ∧
      rightExponent w R xi-primeExponent w p ≤ xi/Real.log w := by
  have h := bin_exponent_bounds hw hR hxi hp
  have hlog : Real.log (1+xi) ≤ xi := by
    have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < 1+xi)
    linarith
  refine ⟨sub_nonneg.mpr h.2,?_⟩
  calc
    _ ≤ rightExponent w R xi-leftExponent w R := by linarith [h.1]
    _ = Real.log (1+xi)/Real.log w := bin_exponent_width hR hxi
    _ ≤ _ := div_le_div_of_nonneg_right hlog (Real.log_pos hw).le

theorem finite_gap_movement (w : ℝ) (rep : ℕ → ℝ) (z : Node) (ps : List ℕ) {h : ℝ}
    (hrep : ∀ p ∈ ps,0 ≤ rep p-primeExponent w p ∧ rep p-primeExponent w p ≤ h) :
    0 ≤ (terminal w z ps).gap-representativeGap rep z.gap ps ∧
      (terminal w z ps).gap-representativeGap rep z.gap ps ≤ (ps.length:ℝ)*h := by
  have hs : 0 ≤ (ps.map rep).sum-(ps.map (primeExponent w)).sum ∧
      (ps.map rep).sum-(ps.map (primeExponent w)).sum ≤ (ps.length:ℝ)*h := by
    induction ps with
    | nil => simp
    | cons p ps ih =>
      have hp := hrep p (by simp)
      have ht := ih (fun q hq => hrep q (by simp [hq]))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      constructor <;> linarith
  rw [terminal_gap_sum,representativeGap]
  constructor <;> linarith

theorem source_movement_bound {w B Clen xi : ℝ} (hw : 1 < w) (hC : 0 ≤ Clen) (hxi : 0 ≤ xi)
    (hcomp : Real.log B ≤ 2*Real.log w) (rep : ℕ → ℝ) (z : Node) (ps : List ℕ)
    (hlen : (ps.length:ℝ) ≤ Clen*Real.log B)
    (hrep : ∀ p ∈ ps,0 ≤ rep p-primeExponent w p ∧ rep p-primeExponent w p ≤ xi/Real.log w) :
    0 ≤ (terminal w z ps).gap-representativeGap rep z.gap ps ∧
      (terminal w z ps).gap-representativeGap rep z.gap ps ≤ 2*Clen*xi := by
  have hm := finite_gap_movement w rep z ps hrep
  have hlog := Real.log_pos hw
  refine ⟨hm.1,hm.2.trans ?_⟩
  calc
    _ ≤ (Clen*Real.log B)*(xi/Real.log w) :=
      mul_le_mul_of_nonneg_right hlen (div_nonneg hxi hlog.le)
    _ ≤ (Clen*(2*Real.log w))*(xi/Real.log w) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcomp hC) (div_nonneg hxi hlog.le)
    _ = _ := by field_simp [hlog.ne']

end NumberTheoryLean.PrimeBinRepresentatives

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_CorrectSearchTags
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.FiniteFirstTag


theorem firstTagFrom_append {n : ℕ} (F : ℕ → Option (Fin n × ℚ)) (k : ℕ) (ps qs : List ℕ)
    {t : Tag n} (ht : firstTagFrom F k ps = some t) : firstTagFrom F k (ps++qs) = some t := by
  induction ps generalizing k with
  | nil => simp [firstTagFrom] at ht
  | cons p ps ih =>
    cases hp : F p with
    | none =>
      simp only [List.cons_append,firstTagFrom,hp] at ht ⊢
      exact ih (k+1) ht
    | some bq =>
      simpa only [List.cons_append,firstTagFrom,hp] using ht

theorem firstTagFrom_map_invariant {n : ℕ} (F : ℕ → Option (Fin n × ℚ))
    (k : ℕ) (ps qs : List ℕ) (hmap : ps.map F = qs.map F) :
    firstTagFrom F k ps = firstTagFrom F k qs := by
  induction ps generalizing k qs with
  | nil =>
    have hq : qs = [] := List.map_eq_nil_iff.mp hmap.symm
    subst qs
    rfl
  | cons p ps ih =>
    cases qs with
    | nil => simp at hmap
    | cons q qs =>
      have hh := List.cons.inj hmap
      simp only [firstTagFrom,hh.1]
      cases hq : F q with
      | none => exact ih (k+1) qs hh.2
      | some bq => rfl

theorem tag_replacement_invariant {n : ℕ} (F : ℕ → Option (Fin n × ℚ))
    (pre tail : List ℕ) (p q : ℕ) (hpq : F p = F q) :
    firstTag F (pre++p::tail) = firstTag F (pre++q::tail) := by
  apply firstTagFrom_map_invariant
  simp only [List.map_append,List.map_cons,hpq]

theorem tag_prefix_invariant {n : ℕ} (F : ℕ → Option (Fin n × ℚ))
    (ps qs : List ℕ) (hmap : ps.map F = qs.map F) (k : ℕ) :
    firstTag F (ps.take k) = firstTag F (qs.take k) := by
  apply firstTagFrom_map_invariant
  rw [List.map_take,List.map_take,hmap]

end NumberTheoryLean.FiniteFirstTag

end

section

namespace NumberTheoryLean.ActualSourceTags

open _root_.Erdos970.Set
open ActualBinOwners FiniteFirstTag PrimeBinRepresentatives ErdosInversePrimeBin ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

theorem candidate_witness {n : ℕ} (Y w Cs eta : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (a : ℕ → ℤ) (p : ℕ) {b : Fin n} {q : ℚ}
    (ht : tagCandidate Y w Cs eta lower width label a p = some (b,q)) :
    b = label p ∧ p ∈ primeBin (lower (label p)) (width (label p)) ∧
      searchBin w (lower (label p)) ∧ owner Y w Cs eta (lower (label p)) (width (label p)) a = some q ∧
      aligns a q p := by
  by_cases hgood : p ∈ primeBin (lower (label p)) (width (label p)) ∧ searchBin w (lower (label p))
  · rw [tagCandidate,ite_eq_left hgood] at ht
    cases ho : owner Y w Cs eta (lower (label p)) (width (label p)) a with
    | none => simp [ho] at ht
    | some r =>
      rw [ho] at ht
      dsimp only at ht
      by_cases ha : aligns a r p
      · rw [ite_eq_left ha] at ht
        have hh := Prod.mk.inj (Option.some.inj ht)
        rcases hh with ⟨hb,hq⟩
        subst r
        exact ⟨hb.symm,hgood.1,hgood.2,rfl,ha⟩
      · simp [ha] at ht
  · simp [tagCandidate,hgood] at ht

theorem candidate_of_witness {n : ℕ} (Y w Cs eta : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (a : ℕ → ℤ) (p : ℕ) (q : ℚ)
    (hp : p ∈ primeBin (lower (label p)) (width (label p))) (hs : searchBin w (lower (label p)))
    (ho : owner Y w Cs eta (lower (label p)) (width (label p)) a = some q) (ha : aligns a q p) :
    tagCandidate Y w Cs eta lower width label a p = some (label p,q) := by
  simp only [tagCandidate,hp,hs,and_self,ite_true, if_true,ho,ha]

theorem candidate_replacement {n : ℕ} (Y w Cs eta : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (a : ℕ → ℤ) (p p' : ℕ) {b : Fin n} {q : ℚ}
    (ht : tagCandidate Y w Cs eta lower width label a p = some (b,q))
    (hlabel : label p' = label p)
    (hp' : p' ∈ primeBin (lower (label p')) (width (label p'))) (ha : aligns a q p') :
    tagCandidate Y w Cs eta lower width label a p' = tagCandidate Y w Cs eta lower width label a p := by
  have hc := candidate_witness Y w Cs eta lower width label a p ht
  have hs : searchBin w (lower (label p')) := by rw [hlabel]; exact hc.2.2.1
  have ho : owner Y w Cs eta (lower (label p')) (width (label p')) a = some q := by
    rw [hlabel]
    exact hc.2.2.2.1
  rw [candidate_of_witness Y w Cs eta lower width label a p' q hp' hs ho ha,ht,hlabel,← hc.1]

end NumberTheoryLean.ActualSourceTags

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_ActualTagFreezing
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSingletonClassChainState _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_none _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_some
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.StoppedVertexHistory

open _root_.Finset
open FinitePathGeometry PrimeHistories StoppedCountVertex ReferenceForestTelescoping ReferencePruning
open ErdosPrimeInputs.PrimePrefixMass

theorem after_node (w : ℝ) (v : Vertex) (ps : List ℕ) :
    (after w v ps).node = terminal w v.node ps := by
  induction ps generalizing v with
  | nil => rfl
  | cons p ps ih => exact ih (child w v p)

theorem after_past (w : ℝ) (v : Vertex) (ps : List ℕ) :
    (after w v ps).past = v.past++ps := by
  induction ps generalizing v with
  | nil => simp [after]
  | cons p ps ih =>
    change (after w (child w v p) ps).past = _
    rw [ih]
    simp [child,List.append_assoc]

theorem after_available (w : ℝ) (v : Vertex) (ps : List ℕ) :
    (after w v ps).available = suffixPrimes v.available ps := by
  induction ps generalizing v with
  | nil => simp [after,suffixPrimes_nil]
  | cons p ps ih =>
    change (after w (child w v p) ps).available = _
    rw [ih,suffixPrimes_cons]
    rfl

theorem after_scale (w : ℝ) (v : Vertex) (ps : List ℕ) :
    (after w v ps).scale = v.scale*prefixWeight ps := by
  induction ps generalizing v with
  | nil => simp [after,prefixWeight]
  | cons p ps ih =>
    change (after w (child w v p) ps).scale = _
    rw [ih]
    change (v.scale/(p:ℝ))*prefixWeight ps = v.scale*((p:ℝ)⁻¹*prefixWeight ps)
    ring

theorem prefixWeight_product (ps : List ℕ) : prefixWeight ps = ((ps.prod:ℕ):ℝ)⁻¹ := by
  induction ps with
  | nil => simp [prefixWeight]
  | cons p ps ih =>
    change (p:ℝ)⁻¹*prefixWeight ps = ((p*ps.prod:ℕ):ℝ)⁻¹
    rw [ih,Nat.cast_mul,mul_inv_rev]
    ring

theorem after_scale_product (w : ℝ) (v : Vertex) (ps : List ℕ) :
    (after w v ps).scale = v.scale/((ps.prod:ℕ):ℝ) := by
  rw [after_scale,prefixWeight_product,div_eq_mul_inv]

end NumberTheoryLean.StoppedVertexHistory



namespace NumberTheoryLean.FirstStopSemantics

open _root_.Finset
open StoppedCountVertex StoppedEvaluation StoppedVertexHistory StoppedTraceSets
attribute [local instance] Classical.propDecidable

theorem firstStop_nil (w : ℝ) (stop : List ℕ → Prop) (v : Vertex) (hs : lowerStop stop v) :
    FirstStop w stop v [] := by
  refine ⟨hs,?_⟩
  intro pre tail heq ht
  exact False.elim (ht (List.append_eq_nil_iff.mp heq.symm).2)

theorem stopped_first (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    {ps : List ℕ} (hp : ps ∈ stopped w stop n v) : FirstStop w stop v ps := by
  induction n generalizing v ps with
  | zero =>
    unfold stopped at hp
    rw [traces] at hp
    split_ifs at hp with hs
    · have heq : ps = [] := Finset.mem_singleton.mp hp
      subst ps
      exact firstStop_nil w stop v hs
    · exact False.elim (Finset.notMem_empty _ hp)
  | succ n ih =>
    unfold stopped at hp
    rw [traces] at hp
    split_ifs at hp with hs
    · have heq : ps = [] := Finset.mem_singleton.mp hp
      subst ps
      exact firstStop_nil w stop v hs
    · obtain ⟨p,_hp,hps⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨tail,ht,rfl⟩ := Finset.mem_image.mp hps
      have hfirst := ih (child w v p) ht
      refine ⟨hfirst.1,?_⟩
      intro pre suffix heq hsuffix
      cases pre with
      | nil => exact hs
      | cons q qs =>
        rw [List.cons_append] at heq
        have hhead := (List.cons.inj heq).1
        have htail := (List.cons.inj heq).2
        subst q
        exact hfirst.2 qs suffix htail hsuffix

end NumberTheoryLean.FirstStopSemantics



namespace NumberTheoryLean.StoppedTraceAdmission

open _root_.Finset
open FinitePathGeometry PrimeHistories StoppedCountVertex StoppedTraceSets
open ReferenceAdmission ReferencePruning ReferencePrefixRecurrence
open ErdosPrimeInputs.PrimePrefixMass
attribute [local instance] Classical.propDecidable

theorem reference_nil_mem (w : ℝ) (v : Vertex) :
    [] ∈ referencePrefixes w v.available v.node.side v.node.gap := by
  apply Finset.mem_filter.mpr
  exact ⟨mem_decreasingPrefixes.mpr ⟨by simp,by simp⟩,trivial⟩

theorem reference_child_cons (w : ℝ) (v : Vertex) {p : ℕ} (hp : p ∈ includedPrimes w v)
    {ps : List ℕ} (hps : ps ∈ referencePrefixes w (child w v p).available
      (child w v p).node.side (child w v p).node.gap) :
    p::ps ∈ referencePrefixes w v.available v.node.side v.node.gap := by
  have hchild := Finset.mem_filter.mp hp
  have htail := Finset.mem_filter.mp hps
  have hSuf : ps ∈ decreasingPrefixes (suffixPrimes v.available [p]) := by
    simpa only [suffixPrimes,List.mem_singleton,forall_eq,child] using htail.1
  have hdec := (append_mem_decreasing_iff (singleton_prefix_mem hchild.1)).mpr hSuf
  apply Finset.mem_filter.mpr
  refine ⟨by simpa only [List.singleton_append] using hdec,?_⟩
  exact ⟨hchild.2,htail.2⟩

theorem trace_reference_member (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    {ps : List ℕ} (hp : ps ∈ expanded w stop n v ∨ ps ∈ stopped w stop n v) :
    ps ∈ referencePrefixes w v.available v.node.side v.node.gap := by
  induction n generalizing v ps with
  | zero =>
    by_cases hs : StoppedEvaluation.lowerStop stop v
    · have heq : ps = [] := by simpa [expanded,stopped,traces,hs] using hp
      subst ps
      exact reference_nil_mem w v
    · have heq : ps = [] := by simpa [expanded,stopped,traces,hs] using hp
      subst ps
      exact reference_nil_mem w v
  | succ n ih =>
    by_cases hs : StoppedEvaluation.lowerStop stop v
    · have heq : ps = [] := by simpa [expanded,stopped,traces,hs] using hp
      subst ps
      exact reference_nil_mem w v
    · rcases hp with hExp | hStop
      · simp only [expanded,traces,hs,ite_false, if_false,Finset.mem_insert] at hExp
        rcases hExp with rfl | hExp
        · exact reference_nil_mem w v
        · obtain ⟨p,hp,hps⟩ := Finset.mem_biUnion.mp hExp
          obtain ⟨tail,ht,rfl⟩ := Finset.mem_image.mp hps
          exact reference_child_cons w v hp (ih (child w v p) (Or.inl ht))
      · simp only [stopped,traces,hs,ite_false, if_false] at hStop
        obtain ⟨p,hp,hps⟩ := Finset.mem_biUnion.mp hStop
        obtain ⟨tail,ht,rfl⟩ := Finset.mem_image.mp hps
        exact reference_child_cons w v hp (ih (child w v p) (Or.inr ht))

end NumberTheoryLean.StoppedTraceAdmission



namespace NumberTheoryLean.SourceStopPredicate

open _root_.Set _root_.Finset
open FinitePathGeometry PrimeHistories ReferenceAdmission RepresentativeAdmission RepresentativeStopGeometry
open PrimeBinRepresentatives ActualSourceTags ActualBinOwners FiniteFirstTag
open ErdosInversePrimeBin ErdosInverseAlignment ErdosPrimeInputs.HarmonicPrimeMeasure
attribute [local instance] Classical.propDecidable

theorem finite_safe_admits (w : ℝ) (rep : ℕ → ℝ) (z : Node) (Delta : ℝ) (ps : List ℕ)
    (hDelta : 0 ≤ Delta) (hrep : ∀ p ∈ ps,primeExponent w p ≤ rep p)
    (hs : representativeSafe w rep z Delta ps) : admitted w z.side z.gap ps := by
  apply representative_safety_preserves_admission w rep z ps hDelta hrep
  intro pre p tail heq hside
  have hmem : pre++[p] ∈ ps.inits := by
    apply (List.mem_inits _ _).mpr
    exact ⟨tail,by simpa only [List.append_assoc,List.singleton_append] using heq.symm⟩
  have h := hs (pre++[p]) hmem (by simp) hside
  rwa [List.getLastD_concat] at h

theorem candidate_admitted {n : ℕ} (Y : ℕ) (w Cs eta Clen B xi b₀ b₁ : ℝ)
    (lower width : Fin n → ℝ) (label : ℕ → Fin n) (a : ℕ → ℕ) (z : Node) (ps : List ℕ)
    (hw : 1 < w) (hC : 0 ≤ Clen) (hxi : 0 ≤ xi)
    (hlo : ∀ b,0 < lower b) (hwidth : ∀ b,0 ≤ width b)
    (hc : stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z ps) :
    admitted w z.side z.gap ps := by
  apply finite_safe_admits w (representative w lower width label) z (2*Clen*xi) ps (by positivity)
  · intro p hp
    exact (bin_exponent_bounds hw (hlo (label p)) (hwidth (label p)) (hc.2.2.1 p hp)).2
  · exact hc.2.2.2.1

end NumberTheoryLean.SourceStopPredicate



namespace NumberTheoryLean.ActualTagFreezing

open ActualSourceTags FiniteFirstTag SourceStopPredicate ErdosInversePrimeBin ErdosInverseAlignment

theorem sourceTag_replacement {n : ℕ} (Y w Cs eta : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (a : ℕ → ℤ) (pre tail : List ℕ) (p p' : ℕ) {b : Fin n} {q : ℚ}
    (ht : tagCandidate Y w Cs eta lower width label a p = some (b,q))
    (hlabel : label p' = label p)
    (hp' : p' ∈ primeBin (lower (label p')) (width (label p'))) (ha : aligns a q p') :
    sourceTag Y w Cs eta lower width label a (pre++p::tail) =
      sourceTag Y w Cs eta lower width label a (pre++p'::tail) := by
  have hc := candidate_replacement Y w Cs eta lower width label a p p' ht hlabel hp' ha
  exact tag_replacement_invariant _ pre tail p p' hc.symm

theorem all_prefix_tags_replacement {n : ℕ} (Y w Cs eta : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (a : ℕ → ℤ) (pre tail : List ℕ) (p p' : ℕ) {b : Fin n} {q : ℚ}
    (ht : tagCandidate Y w Cs eta lower width label a p = some (b,q))
    (hlabel : label p' = label p)
    (hp' : p' ∈ primeBin (lower (label p')) (width (label p'))) (ha : aligns a q p') (k : ℕ) :
    sourceTag Y w Cs eta lower width label a ((pre++p::tail).take k) =
      sourceTag Y w Cs eta lower width label a ((pre++p'::tail).take k) := by
  have hc := candidate_replacement Y w Cs eta lower width label a p p' ht hlabel hp' ha
  apply tag_prefix_invariant
  simp only [List.map_append,List.map_cons,hc]

theorem replacement_labels {n : ℕ} (label : ℕ → Fin n) (pre tail : List ℕ) (p p' : ℕ)
    (hlabel : label p' = label p) : (pre++p::tail).map label = (pre++p'::tail).map label := by
  simp only [List.map_append,List.map_cons,hlabel]

theorem replacement_representatives {n : ℕ} (w : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (pre tail : List ℕ) (p p' : ℕ) (hlabel : label p' = label p) :
    (pre++p::tail).map (representative w lower width label) =
      (pre++p'::tail).map (representative w lower width label) := by
  simp only [List.map_append,List.map_cons,representative,hlabel]

theorem forall_mem_replacement_iff (A : ℕ → Prop) (pre tail : List ℕ) (p q : ℕ)
    (hp : A p) (hq : A q) :
    (∀ r ∈ pre++p::tail,A r) ↔ (∀ r ∈ pre++q::tail,A r) := by
  have h (p q : ℕ) (hq : A q) (H : ∀ r ∈ pre++p::tail,A r) : ∀ r ∈ pre++q::tail,A r := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact H r (List.mem_append.mpr (Or.inl hr))
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact hq
      · exact H r (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hr)))
  exact ⟨h p q hq,h q p hp⟩

end NumberTheoryLean.ActualTagFreezing


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceCandidateFreezing
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSingletonClassChainState _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_none _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_some
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.RepresentativeTraceInvariance
open FinitePathGeometry PrimeHistories RepresentativeAdmission SourceStopPredicate

theorem terminal_side_length (w : ℝ) (z z' : Node) (ps qs : List ℕ)
    (hz : z.side = z'.side) (hlen : ps.length = qs.length) :
    (terminal w z ps).side = (terminal w z' qs).side := by
  induction ps generalizing qs z z' with
  | nil =>
    have hq : qs = [] := List.length_eq_zero_iff.mp hlen.symm
    subst qs
    exact hz
  | cons p ps ih =>
    cases qs with
    | nil => simp at hlen
    | cons q qs =>
      apply ih (step w z p) (step w z' q) qs
      · change z.side.flip = z'.side.flip
        rw [hz]
      · simpa using hlen

theorem representative_last_eq (rep : ℕ → ℝ) (ps qs : List ℕ)
    (hm : ps.map rep = qs.map rep) : rep (ps.getLastD 0) = rep (qs.getLastD 0) := by
  induction ps generalizing qs with
  | nil =>
    have hq : qs = [] := List.map_eq_nil_iff.mp hm.symm
    subst qs
    rfl
  | cons p ps ih =>
    cases qs with
    | nil => simp at hm
    | cons q qs =>
      have hh := List.cons.inj hm
      cases ps with
      | nil =>
        have hq : qs = [] := List.map_eq_nil_iff.mp hh.2.symm
        subst qs
        exact hh.1
      | cons r rs =>
        cases qs with
        | nil => simp at hh
        | cons s ss =>
          simpa using ih (s::ss) hh.2

theorem representativeWindow_map_iff (rep : ℕ → ℝ) (z : Node) (b₀ b₁ : ℝ)
    (ps qs : List ℕ) (hm : ps.map rep = qs.map rep) :
    representativeWindow rep z b₀ b₁ ps ↔ representativeWindow rep z b₀ b₁ qs := by
  have he := representative_last_eq rep ps qs hm
  simp only [representativeWindow,representativeGap,he,hm]

theorem representativeSafe_map_iff (w : ℝ) (rep : ℕ → ℝ) (z : Node) (Delta : ℝ)
    (ps qs : List ℕ) (hm : ps.map rep = qs.map rep) :
    representativeSafe w rep z Delta ps ↔ representativeSafe w rep z Delta qs := by
  have forward (ps qs : List ℕ) (hm : ps.map rep = qs.map rep)
      (hs : representativeSafe w rep z Delta ps) : representativeSafe w rep z Delta qs := by
    intro pre hpre hne hside
    obtain ⟨tail,htail⟩ := (List.mem_inits pre qs).mp hpre
    have hlen : ps.length = qs.length := by simpa using congrArg List.length hm
    have hk : pre.length ≤ ps.length := by rw [← htail,List.length_append] at hlen; omega
    have hm' : (ps.take pre.length).map rep = pre.map rep := by
      rw [List.map_take,hm,← htail,List.map_append,List.take_append]
      simp
    have hprefix : ps.take pre.length ∈ ps.inits :=
      (List.mem_inits _ _).mpr ⟨ps.drop pre.length,List.take_append_drop _ _⟩
    have hlen' : (ps.take pre.length).length = pre.length := by
      rw [List.length_take,Nat.min_eq_left hk]
    have hne' : ps.take pre.length ≠ [] := by
      intro he
      have : pre.length = 0 := by rw [he] at hlen'; simpa using hlen'.symm
      exact hne (List.length_eq_zero_iff.mp this)
    have hside' : (terminal w z (ps.take pre.length)).side = .even :=
      (terminal_side_length w z z _ _ rfl hlen').trans hside
    have hh := hs (ps.take pre.length) hprefix hne' hside'
    have he := representative_last_eq rep _ _ hm'
    simpa only [representativeGap,hm',he] using hh
  exact ⟨forward ps qs hm,forward qs ps hm.symm⟩

theorem all_prefix_representative_tests (w : ℝ) (rep : ℕ → ℝ) (z : Node)
    (Delta b₀ b₁ : ℝ) (ps qs : List ℕ) (hm : ps.map rep = qs.map rep) (k : ℕ) :
    (representativeSafe w rep z Delta (ps.take k) ↔ representativeSafe w rep z Delta (qs.take k)) ∧
    (representativeWindow rep z b₀ b₁ (ps.take k) ↔ representativeWindow rep z b₀ b₁ (qs.take k)) := by
  have ht : (ps.take k).map rep = (qs.take k).map rep := by rw [List.map_take,List.map_take,hm]
  exact ⟨representativeSafe_map_iff w rep z Delta _ _ ht,
    representativeWindow_map_iff rep z b₀ b₁ _ _ ht⟩
end NumberTheoryLean.RepresentativeTraceInvariance

end

section

namespace NumberTheoryLean.SourceCandidateFreezing
open FinitePathGeometry PrimeHistories RepresentativeAdmission SourceStopPredicate
open ActualSourceTags ActualTagFreezing FiniteFirstTag RepresentativeTraceInvariance
open ErdosInversePrimeBin ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

theorem forall_take_replacement_iff (A : ℕ → Prop) (pre tail : List ℕ) (p p' : ℕ)
    (hp : A p) (hp' : A p') (k : ℕ) :
    (∀ r ∈ (pre++p::tail).take k,A r) ↔ (∀ r ∈ (pre++p'::tail).take k,A r) := by
  have hm : ((pre++p::tail).take k).map A = ((pre++p'::tail).take k).map A := by
    rw [List.map_take,List.map_take]
    have he : A p = A p' := propext (iff_of_true hp hp')
    simp only [List.map_append,List.map_cons,he]
  have forward (ps qs : List ℕ) (hm : ps.map A = qs.map A)
      (hh : ∀ r ∈ ps,A r) : ∀ r ∈ qs,A r := by
    intro r hr
    have hm' : A r ∈ ps.map A := by rw [hm]; exact List.mem_map.mpr ⟨r,hr,rfl⟩
    obtain ⟨s,hs,he⟩ := List.mem_map.mp hm'
    rw [← he]
    exact hh s hs
  exact ⟨forward _ _ hm,forward _ _ hm.symm⟩

theorem prefix_tag_eq {n : ℕ} (F : ℕ → Option (Fin n × ℚ)) (ps : List ℕ) (k : ℕ)
    {t u : Tag n} (ht : firstTag F ps = some t) (hu : firstTag F (ps.take k) = some u) : u=t := by
  have hh := firstTagFrom_append F 0 (ps.take k) (ps.drop k) hu
  rw [List.take_append_drop] at hh
  exact Option.some.inj (hh.symm.trans ht)

theorem all_prefix_candidate_replacement {n : ℕ} (Y : ℕ) (w Cs eta Clen B xi b₀ b₁ : ℝ)
    (lower width : Fin n → ℝ) (label : ℕ → Fin n) (a : ℕ → ℕ) (z : Node)
    (pre tail : List ℕ) (p p' : ℕ) {t : Tag n}
    (ht : sourceTag (Y:ℝ) w Cs eta lower width label (sourceClass a) (pre++p::tail) = some t)
    (hc : tagCandidate (Y:ℝ) w Cs eta lower width label (sourceClass a) p = some (t.bin,t.rational))
    (hlabel : label p' = label p)
    (hp' : p' ∈ primeBin (lower (label p')) (width (label p')))
    (ha' : aligns (sourceClass a) t.rational p') (k : ℕ) :
    stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z ((pre++p::tail).take k) ↔
      stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z ((pre++p'::tail).take k) := by
  have hwit := candidate_witness (Y:ℝ) w Cs eta lower width label (sourceClass a) p hc
  have hp := hwit.2.1
  have ha := hwit.2.2.2.2
  have htags := all_prefix_tags_replacement (Y:ℝ) w Cs eta lower width label (sourceClass a)
    pre tail p p' hc hlabel hp' ha' k
  have hfull := sourceTag_replacement (Y:ℝ) w Cs eta lower width label (sourceClass a)
    pre tail p p' hc hlabel hp' ha'
  have ht' : sourceTag (Y:ℝ) w Cs eta lower width label (sourceClass a) (pre++p'::tail) = some t :=
    hfull.symm.trans ht
  have hlabels : ((pre++p::tail).take k).map label = ((pre++p'::tail).take k).map label := by
    rw [List.map_take,List.map_take,replacement_labels label pre tail p p' hlabel]
  have hrep := all_prefix_representative_tests w (representative w lower width label) z
    (2*Clen*xi) b₀ b₁ _ _ (replacement_representatives w lower width label pre tail p p' hlabel) k
  have hboxed := forall_take_replacement_iff
    (fun r => r ∈ primeBin (lower (label r)) (width (label r))) pre tail p p' hp hp' k
  have halign := forall_take_replacement_iff (aligns (sourceClass a) t.rational) pre tail p p' ha ha' k
  have hlen : ((pre++p::tail).take k).length = ((pre++p'::tail).take k).length := by
    simp only [List.length_take,List.length_append,List.length_cons]
  have hne : ((pre++p::tail).take k ≠ []) ↔ ((pre++p'::tail).take k ≠ []) := by
    rw [← List.length_pos_iff,← List.length_pos_iff,hlen]
  have forward (ps qs : List ℕ)
      (hps : firstTag (tagCandidate (Y:ℝ) w Cs eta lower width label (sourceClass a))
        ((pre++p::tail).take k) = sourceTag (Y:ℝ) w Cs eta lower width label (sourceClass a) ps)
      (htag : sourceTag (Y:ℝ) w Cs eta lower width label (sourceClass a) ps =
        sourceTag (Y:ℝ) w Cs eta lower width label (sourceClass a) qs)
      (hne : ps ≠ [] → qs ≠ []) (hlen : ps.length = qs.length)
      (hb : boxed lower width label ps → boxed lower width label qs)
      (hs : representativeSafe w (representative w lower width label) z (2*Clen*xi) ps →
        representativeSafe w (representative w lower width label) z (2*Clen*xi) qs)
      (hw : representativeWindow (representative w lower width label) z b₀ b₁ ps →
        representativeWindow (representative w lower width label) z b₀ b₁ qs)
      (hl : ps.map label = qs.map label)
      (ha : (∀ r ∈ ps,aligns (sourceClass a) t.rational r) → ∀ r ∈ qs,aligns (sourceClass a) t.rational r)
      (H : stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z ps) :
      stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z qs := by
    obtain ⟨hn,hlength,hbox,hsafe,hwindow,u,hu,hcount,hal⟩ := H
    have hu' := hps.trans hu
    have hut : u=t := prefix_tag_eq _ (pre++p::tail) k ht hu'
    subst u
    exact ⟨hne hn,by simpa only [← hlen] using hlength,hb hbox,hs hsafe,hw hwindow,
      t,htag.symm.trans hu,by simpa only [← hl] using hcount,ha hal⟩
  exact ⟨forward _ _ rfl htags hne.mp hlen hboxed.mp hrep.1.mp hrep.2.mp hlabels halign.mp,
    forward _ _ htags htags.symm hne.mpr hlen.symm hboxed.mpr hrep.1.mpr hrep.2.mpr hlabels.symm halign.mpr⟩
end NumberTheoryLean.SourceCandidateFreezing

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_CrossingBandGeometry
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSingletonClassChainState _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.LogarithmicBinScale


theorem logWidth_pos {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi) :
    0 < logWidth w z xi :=
  div_pos (span_log_pos hw hwz) (by exact_mod_cast binCount_pos hw hwz hxi)

theorem count_mul_logWidth {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi) :
    (binCount w z xi:ℝ)*logWidth w z xi = Real.log (z/w) := by
  have hn : (binCount w z xi:ℝ) ≠ 0 := by exact_mod_cast (binCount_pos hw hwz hxi).ne'
  unfold logWidth
  field_simp [hn]

theorem logWidth_le {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi) :
    logWidth w z xi ≤ Real.log (1+xi) := by
  have hlog : 0 < Real.log (1+xi) := Real.log_pos (by linarith)
  have hc := Nat.le_ceil (Real.log (z/w)/Real.log (1+xi))
  have hm := (div_le_iff₀ hlog).mp hc
  change Real.log (z/w) ≤ (binCount w z xi:ℝ)*Real.log (1+xi) at hm
  apply (div_le_iff₀ (by exact_mod_cast binCount_pos hw hwz hxi : (0:ℝ) < binCount w z xi)).mpr
  exact (by nlinarith : Real.log (z/w) ≤ Real.log (1+xi)*(binCount w z xi:ℝ))

theorem effectiveWidth_pos {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi) :
    0 < effectiveWidth w z xi := by
  exact sub_pos.mpr (Real.one_lt_exp_iff.mpr (logWidth_pos hw hwz hxi))

theorem effectiveWidth_le {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi) :
    effectiveWidth w z xi ≤ xi := by
  have he := Real.exp_le_exp.mpr (logWidth_le hw hwz hxi)
  rw [Real.exp_log (by linarith : 0 < 1+xi)] at he
  exact sub_le_iff_le_add.mpr (by linarith)

end NumberTheoryLean.LogarithmicBinScale



namespace NumberTheoryLean.LogarithmicBinEndpoints

open LogarithmicBinScale PrimeBinRepresentatives ErdosInversePrimeBin

theorem endpoint_zero (w z xi : ℝ) : endpoint w z xi 0 = w := by simp [endpoint]

theorem upper_endpoint (w z xi : ℝ) (i : Fin (binCount w z xi)) :
    upper w z xi i = endpoint w z xi (i.1+1) := by
  simp only [upper,width,lower,effectiveWidth,endpoint,Nat.cast_add,Nat.cast_one,add_mul,one_mul,Real.exp_add]
  ring

theorem endpoint_count {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi) :
    endpoint w z xi (binCount w z xi) = z := by
  rw [endpoint,count_mul_logWidth hw hwz hxi,Real.exp_log (div_pos (hw.trans hwz) hw)]
  field_simp [hw.ne']

theorem endpoint_pos {w z xi : ℝ} (hw : 0 < w) (k : ℕ) : 0 < endpoint w z xi k := by
  exact mul_pos hw (Real.exp_pos _)

theorem endpoint_mono {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    {k m : ℕ} (hkm : k ≤ m) : endpoint w z xi k ≤ endpoint w z xi m := by
  have hc : (k:ℝ) ≤ m := by exact_mod_cast hkm
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc (logWidth_pos hw hwz hxi).le)) hw.le

theorem bin_source_bounds {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    (i : Fin (binCount w z xi)) : w ≤ lower w z xi i ∧ lower w z xi i < upper w z xi i ∧
      upper w z xi i ≤ z := by
  have hlow : w ≤ lower w z xi i := by
    have h := endpoint_mono hw hwz hxi (Nat.zero_le i.1)
    simpa only [endpoint_zero,lower] using h
  have hstrict : lower w z xi i < upper w z xi i := by
    have hp : 0 < lower w z xi i := endpoint_pos hw _
    have he : 0 < width w z xi i := effectiveWidth_pos hw hwz hxi
    unfold upper
    nlinarith
  refine ⟨hlow,hstrict,?_⟩
  rw [upper_endpoint]
  exact (endpoint_mono hw hwz hxi (Nat.succ_le_of_lt i.isLt)).trans_eq (endpoint_count hw hwz hxi)

theorem bins_separated {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    (i j : Fin (binCount w z xi)) (hij : i ≠ j) :
    upper w z xi i ≤ lower w z xi j ∨ upper w z xi j ≤ lower w z xi i := by
  have hne : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · apply Or.inl
    rw [upper_endpoint]
    exact endpoint_mono hw hwz hxi (by omega)
  · apply Or.inr
    rw [upper_endpoint]
    exact endpoint_mono hw hwz hxi (by omega)

theorem bin_prime_in_source {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    (i : Fin (binCount w z xi)) {p : ℕ} (hp : p ∈ primeBin (lower w z xi i) (width w z xi i)) :
    p.Prime ∧ w < (p:ℝ) ∧ (p:ℝ) ≤ z := by
  have hb := (mem_primeBin (endpoint_pos hw i.1).le (effectiveWidth_pos hw hwz hxi).le p).mp hp
  have hs := bin_source_bounds hw hwz hxi i
  exact ⟨hb.1,hs.1.trans_lt hb.2.1,hb.2.2.trans hs.2.2⟩

end NumberTheoryLean.LogarithmicBinEndpoints



namespace NumberTheoryLean.LogarithmicBinLabels

open LogarithmicBinScale LogarithmicBinEndpoints ErdosInversePrimeBin

theorem coordinate_bounds {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    {p : ℕ} (hp : w < (p:ℝ) ∧ (p:ℝ) ≤ z) :
    0 < coordinate w z xi p ∧ coordinate w z xi p ≤ (binCount w z xi:ℝ) := by
  have hlog : 0 < Real.log ((p:ℝ)/w) := by
    apply Real.log_pos
    exact (lt_div_iff₀ hw).mpr (by simpa only [one_mul] using hp.1)
  have hd := logWidth_pos hw hwz hxi
  refine ⟨div_pos hlog hd,?_⟩
  apply (div_le_iff₀ hd).mpr
  rw [count_mul_logWidth hw hwz hxi]
  exact Real.log_le_log (div_pos (hw.trans hp.1) hw) (div_le_div_of_nonneg_right hp.2 hw.le)

theorem index_eq_ceiling {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    {p : ℕ} (hp : w < (p:ℝ) ∧ (p:ℝ) ≤ z) : index w z xi p = ⌈coordinate w z xi p⌉₊-1 := by
  have hc : ⌈coordinate w z xi p⌉₊ ≤ binCount w z xi := Nat.ceil_le.mpr (coordinate_bounds hw hwz hxi hp).2
  exact min_eq_right (by omega)

theorem label_coordinate_bounds {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    {p : ℕ} (hp : w < (p:ℝ) ∧ (p:ℝ) ≤ z) :
    ((label hw hwz hxi p).1:ℝ) < coordinate w z xi p ∧
      coordinate w z xi p ≤ ((label hw hwz hxi p).1:ℝ)+1 := by
  have hc := coordinate_bounds hw hwz hxi hp
  have hpos : 0 < ⌈coordinate w z xi p⌉₊ := Nat.ceil_pos.mpr hc.1
  have hlow := Nat.ceil_lt_add_one hc.1.le
  have hhigh := Nat.le_ceil (coordinate w z xi p)
  have he : ((label hw hwz hxi p).1:ℝ) = (⌈coordinate w z xi p⌉₊:ℝ)-1 := by
    change (index w z xi p:ℝ) = _
    rw [index_eq_ceiling hw hwz hxi hp,Nat.cast_sub (by omega : 1 ≤ ⌈coordinate w z xi p⌉₊)]
    norm_num
  rw [he]
  constructor <;> linarith

theorem label_value_bounds {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    {p : ℕ} (hp : w < (p:ℝ) ∧ (p:ℝ) ≤ z) :
    lower w z xi (label hw hwz hxi p) < (p:ℝ) ∧
      (p:ℝ) ≤ upper w z xi (label hw hwz hxi p) := by
  have hb := label_coordinate_bounds hw hwz hxi hp
  have hd := logWidth_pos hw hwz hxi
  have hpw : 0 < (p:ℝ)/w := div_pos (hw.trans hp.1) hw
  have he : coordinate w z xi p*logWidth w z xi = Real.log ((p:ℝ)/w) := by
    unfold coordinate
    field_simp [hd.ne']
  have hlo := mul_lt_mul_of_pos_right hb.1 hd
  have hhi := mul_le_mul_of_nonneg_right hb.2 hd.le
  rw [he] at hlo hhi
  have hExpLo := Real.exp_lt_exp.mpr hlo
  have hExpHi := Real.exp_le_exp.mpr hhi
  rw [Real.exp_log hpw] at hExpLo hExpHi
  constructor
  · have h := (lt_div_iff₀ hw).mp hExpLo
    simpa only [lower,endpoint,mul_comm] using h
  · rw [upper_endpoint]
    have h := (div_le_iff₀ hw).mp hExpHi
    simpa only [endpoint,Nat.cast_add,Nat.cast_one,mul_comm] using h

theorem label_prime_membership {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    {p : ℕ} (hprime : p.Prime) (hp : w < (p:ℝ) ∧ (p:ℝ) ≤ z) :
    p ∈ primeBin (lower w z xi (label hw hwz hxi p)) (width w z xi (label hw hwz hxi p)) := by
  apply (mem_primeBin (endpoint_pos hw _).le (effectiveWidth_pos hw hwz hxi).le p).mpr
  exact ⟨hprime,(label_value_bounds hw hwz hxi hp).1,(label_value_bounds hw hwz hxi hp).2⟩

end NumberTheoryLean.LogarithmicBinLabels



namespace NumberTheoryLean.LogarithmicBinPartition

open _root_.Set _root_.Finset
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels ErdosInversePrimeBin

theorem mem_sourcePrimeSet {w z : ℝ} (hw : 0 < w) (hwz : w < z) (p : ℕ) :
    p ∈ sourcePrimeSet w z ↔ p.Prime ∧ w < (p:ℝ) ∧ (p:ℝ) ≤ z := by
  constructor
  · intro hp
    obtain ⟨hup,hnot⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hbound,hprime⟩ := Nat.mem_primesLE.mp hup
    refine ⟨hprime,?_,(Nat.le_floor_iff (hw.trans hwz).le).mp hbound⟩
    by_contra! hlo
    exact hnot (Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff hw.le).mpr hlo,hprime⟩)
  · rintro ⟨hprime,hlo,hhi⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff (hw.trans hwz).le).mpr hhi,hprime⟩,?_⟩
    intro hp
    exact (not_le_of_gt hlo) ((Nat.le_floor_iff hw.le).mp (Nat.mem_primesLE.mp hp).1)

theorem bin_mem_iff_label {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    (i : Fin (binCount w z xi)) (p : ℕ) :
    p ∈ primeBin (lower w z xi i) (width w z xi i) ↔
      p.Prime ∧ w < (p:ℝ) ∧ (p:ℝ) ≤ z ∧ label hw hwz hxi p = i := by
  constructor
  · intro hp
    have hs := bin_prime_in_source hw hwz hxi i hp
    have hI := (mem_primeBin (endpoint_pos hw _).le (effectiveWidth_pos hw hwz hxi).le p).mp hp
    have hL := label_value_bounds hw hwz hxi hs.2
    refine ⟨hs.1,hs.2.1,hs.2.2,?_⟩
    by_contra hne
    have hsep := bins_separated hw hwz hxi i (label hw hwz hxi p) (Ne.symm hne)
    have huI : (p:ℝ) ≤ upper w z xi i := hI.2.2
    have hlI : lower w z xi i < (p:ℝ) := hI.2.1
    rcases hsep with hsep | hsep <;> linarith [hlI,hL.1,hL.2]
  · rintro ⟨hprime,hlo,hhi,heq⟩
    rw [← heq]
    exact label_prime_membership hw hwz hxi hprime ⟨hlo,hhi⟩

end NumberTheoryLean.LogarithmicBinPartition



namespace NumberTheoryLean.LogarithmicBinMaps

open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open SourceStopPredicate PrimeBinRepresentatives RepresentativeAdmission PrimeHistories
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem source_representative_error {w z xi : ℝ} (hw : 1 < w) (hwz : w < z) (hxi : 0 < xi)
    {p : ℕ} (hp : p ∈ sourcePrimeSet w z) :
    0 ≤ representative w (lower w z xi) (width w z xi) (label (by linarith : 0 < w) hwz hxi) p-primeExponent w p ∧
      representative w (lower w z xi) (width w z xi) (label (by linarith : 0 < w) hwz hxi) p-primeExponent w p ≤ xi/Real.log w := by
  have hw0 : 0 < w := by linarith
  have hs := (mem_sourcePrimeSet hw0 hwz p).mp hp
  have hbin := label_prime_membership hw0 hwz hxi hs.1 hs.2
  have he := representative_error hw (endpoint_pos hw0 _) (effectiveWidth_pos hw0 hwz hxi).le hbin
  refine ⟨he.1,he.2.trans ?_⟩
  exact div_le_div_of_nonneg_right (effectiveWidth_le hw0 hwz hxi) (Real.log_pos hw).le

theorem source_prefix_movement {w z xi B Clen : ℝ} (hw : 1 < w) (hwz : w < z) (hxi : 0 < xi)
    (hC : 0 ≤ Clen) (hcomp : Real.log B ≤ 2*Real.log w) (v : Node) (ps : List ℕ)
    (hp : ∀ p ∈ ps,p ∈ sourcePrimeSet w z) (hlen : (ps.length:ℝ) ≤ Clen*Real.log B) :
    0 ≤ (terminal w v ps).gap-representativeGap
      (representative w (lower w z xi) (width w z xi) (label (by linarith : 0 < w) hwz hxi)) v.gap ps ∧
    (terminal w v ps).gap-representativeGap
      (representative w (lower w z xi) (width w z xi) (label (by linarith : 0 < w) hwz hxi)) v.gap ps ≤ 2*Clen*xi := by
  exact source_movement_bound hw hC hxi.le hcomp _ v ps hlen
    (fun p hps => source_representative_error hw hwz hxi (hp p hps))

end NumberTheoryLean.LogarithmicBinMaps



namespace NumberTheoryLean.BinReplacementOrder
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosInversePrimeBin

theorem prime_order_replacement {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    (p p' q : ℕ) (hp : p ∈ sourcePrimeSet w z) (hp' : p' ∈ sourcePrimeSet w z)
    (hq : q ∈ sourcePrimeSet w z) (he : label hw hwz hxi p' = label hw hwz hxi p)
    (hne : label hw hwz hxi q ≠ label hw hwz hxi p) :
    (p < q ↔ p' < q) ∧ (q < p ↔ q < p') := by
  have bp := label_value_bounds hw hwz hxi ((mem_sourcePrimeSet hw hwz p).mp hp).2
  have bp' := label_value_bounds hw hwz hxi ((mem_sourcePrimeSet hw hwz p').mp hp').2
  have bq := label_value_bounds hw hwz hxi ((mem_sourcePrimeSet hw hwz q).mp hq).2
  rw [he] at bp'
  have hs := bins_separated hw hwz hxi (label hw hwz hxi p) (label hw hwz hxi q) hne.symm
  rcases hs with hs | hs
  · have h1 : p < q := by exact_mod_cast (show (p:ℝ)<q by linarith)
    have h2 : p' < q := by exact_mod_cast (show (p':ℝ)<q by linarith)
    exact ⟨iff_of_true h1 h2,iff_of_false (Nat.not_lt_of_ge h1.le) (Nat.not_lt_of_ge h2.le)⟩
  · have h1 : q < p := by exact_mod_cast (show (q:ℝ)<p by linarith)
    have h2 : q < p' := by exact_mod_cast (show (q:ℝ)<p' by linarith)
    exact ⟨iff_of_false (Nat.not_lt_of_ge h1.le) (Nat.not_lt_of_ge h2.le),iff_of_true h1 h2⟩

theorem unique_label_other {n : ℕ} (label : ℕ → Fin n) (pre tail : List ℕ) (p : ℕ)
    (hc : ((pre++p::tail).map label).count (label p) = 1) :
    ∀ q ∈ pre++tail,label q ≠ label p := by
  have h0 : ((pre++tail).map label).count (label p) = 0 := by
    simp only [List.map_append,List.map_cons,List.count_append,List.count_cons_self] at hc ⊢
    omega
  intro q hq he
  have hm : label p ∈ (pre++tail).map label := List.mem_map.mpr ⟨q,hq,he⟩
  have hh := List.count_pos_iff.mpr hm
  omega

theorem decreasing_replacement {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    (pre tail : List ℕ) (p p' : ℕ)
    (hall : ∀ q ∈ pre++p::tail,q ∈ sourcePrimeSet w z)
    (hp' : p' ∈ sourcePrimeSet w z)
    (he : label hw hwz hxi p' = label hw hwz hxi p)
    (hc : ((pre++p::tail).map (label hw hwz hxi)).count (label hw hwz hxi p) = 1) :
    (pre++p::tail).Pairwise (· > ·) ↔ (pre++p'::tail).Pairwise (· > ·) := by
  have hp := hall p (by simp)
  have hother := unique_label_other (label hw hwz hxi) pre tail p hc
  have hqall (q : ℕ) (hq : q ∈ pre++tail) : q ∈ sourcePrimeSet w z := by
    apply hall q
    simp only [List.mem_append,List.mem_cons] at hq ⊢
    tauto
  have horder (q : ℕ) (hq : q ∈ pre++tail) :=
    prime_order_replacement hw hwz hxi p p' q hp hp' (hqall q hq) he (hother q hq)
  simp only [List.pairwise_append,List.pairwise_cons]
  constructor
  · rintro ⟨hpre,htail,hcross⟩
    refine ⟨hpre,⟨?_,htail.2⟩,?_⟩
    · intro q hq
      exact (horder q (by simp [hq])).2.mp (htail.1 q hq)
    · intro q hq r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact (horder q (by simp [hq])).1.mp (hcross q hq p (by simp))
      · exact hcross q hq r (by simp [hr])
  · rintro ⟨hpre,htail,hcross⟩
    refine ⟨hpre,⟨?_,htail.2⟩,?_⟩
    · intro q hq
      exact (horder q (by simp [hq])).2.mpr (htail.1 q hq)
    · intro q hq r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact (horder q (by simp [hq])).1.mpr (hcross q hq p' (by simp))
      · exact hcross q hq r (by simp [hr])

end NumberTheoryLean.BinReplacementOrder



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ExponentialMesh
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ExponentialMesh

open _root_.Set _root_.Filter
open scoped Topology

theorem log_pow_sqrt (n : ℕ) {w : ℝ} (hw : 0 ≤ Real.log w) :
    (Real.sqrt (Real.log w))^(2*n) = (Real.log w)^n := by
  rw [pow_mul,Real.sq_sqrt hw]

theorem log_power_exp_tendsto (C : ℝ) (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun w : ℝ => C*(Real.log w)^n*Real.exp (-c*Real.sqrt (Real.log w))) atTop (𝓝 0) := by
  have hbase : Tendsto (fun x : ℝ => C*x^(2*n)*Real.exp (-c*x)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((2*n:ℕ):ℝ) c hc).const_mul C
    simpa only [Real.rpow_natCast,mul_zero,mul_assoc] using h
  apply Tendsto.congr' _ (hbase.comp (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop))
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (0:ℝ))] with w hw
  simp only [Function.comp_apply,log_pow_sqrt n hw]

end NumberTheoryLean.ExponentialMesh

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_SourceCompactCoupling
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.MarkedSourceSmallness

open _root_.Filter
open scoped Topology
open ExponentialMesh

theorem moving_compact_gap_small (R : ℝ) {K : ℝ} (hK : 0 < K) :
    ∀ᶠ w : ℝ in atTop, R < 6*(K*(Real.log w)^2) := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max (1:ℝ) (1+R/(6*K))))] with w hw
  have hL : 1 ≤ Real.log w := (le_max_left _ _).trans hw
  have hR : 1+R/(6*K) ≤ Real.log w := (le_max_right _ _).trans hw
  have hm := mul_le_mul_of_nonneg_left hR (show 0 ≤ 6*K by positivity)
  have he : 6*K*(1+R/(6*K)) = 6*K+R := by field_simp [hK.ne']
  rw [he] at hm
  have hSq : Real.log w ≤ (Real.log w)^2 := by nlinarith
  have hs := mul_le_mul_of_nonneg_left hSq (show 0 ≤ 6*K by positivity)
  nlinarith

end NumberTheoryLean.MarkedSourceSmallness

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_SourceNodeCoordinates
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceNodeCoordinates

open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeBinMembership
open RegeneratingInverseBands ArrivalKernelGeometry SourceLowRemoval
open InvariantInverseWeights DerivativeWeights

theorem node_gap_eq {B : ℝ} {start : Node} (hs : Valid start.side start.ratio)
    (hcons : Consistent start) (hcut : start.cutoff=B) : start.gap=B*start.ratio := by
  have he : start.cutoff=start.gap/start.ratio := hcons
  rw [hcut] at he
  exact ((eq_div_iff (valid_pos hs).ne').mp he).symm

theorem source_node_bounds {B : ℝ} (hB : 0 < B) (start : Node)
    (hi : start.side=.even) (h199 : 199/100 ≤ start.ratio) (h23 : start.ratio ≤ 23/10)
    (hcons : Consistent start) (hcut : start.cutoff=B) :
    Valid start.side start.ratio ∧ 0 < start.gap ∧ B ≤ start.gap ∧ start.gap ≤ (23/10:ℝ)*B := by
  have hs : Valid start.side start.ratio := by rw [hi]; change 198/100 ≤ start.ratio; linarith
  have he := node_gap_eq hs hcons hcut
  refine ⟨hs,?_,?_,?_⟩
  · rw [he]; exact mul_pos hB (valid_pos hs)
  · nlinarith
  · nlinarith

end NumberTheoryLean.SourceNodeCoordinates

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

namespace NumberTheoryLean.ReferenceSourceDecomposition

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh
open ReferenceAdmission ReferencePruning ReferenceWeightedRecurrence ReferenceForestTelescoping ReferenceCutoffRecurrence
open ReferenceSourcePrimeSets ReferenceEulerRecurrence ReferenceHistoryAdmission ReferenceLocalResidual
open BoundaryAnomaly UniformBoundaryCorrection
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.HarmonicPrimeMeasure

theorem suffix_highPrimes {w : ℝ} (hw : 1 < w) {z : Node} (hs : Valid z.side z.ratio)
    (hr : 0 < z.gap) (hz : Consistent z) {ps : List ℕ} (hp : uncappedAllowed w 2 z ps) :
    suffixPrimes (highPrimes w z.cutoff z.closed) ps=
      highPrimes w (terminal w z ps).cutoff (terminal w z ps).closed := by
  induction ps generalizing z with
  | nil => simp only [suffixPrimes_nil,terminal_nil]
  | cons p ps ih =>
    obtain ⟨hchild,htail⟩ := hp
    have hpH := ((uncapped_child_iff hw hs hz p).mp hchild).1
    have hpS : p ∈ sourcePrimes w z.cutoff z.closed := (Finset.mem_filter.mp hpH).1
    obtain ⟨hvs,hrs,hzs⟩ := uncapped_child_invariants hs hr hchild
    rw [suffixPrimes_cons,terminal_cons,← highPrimes_at_selected hw z.closed hpS]
    exact ih (z := step w z p) hvs hrs hzs htail

theorem uncapped_cutoff_gt_two {w : ℝ} {z : Node} (hb : 2 < z.cutoff) {ps : List ℕ}
    (hp : uncappedAllowed w 2 z ps) : 2 < (terminal w z ps).cutoff := by
  induction ps generalizing z with
  | nil => exact hb
  | cons p ps ih =>
    obtain ⟨hc,ht⟩ := hp
    have hx : 2 < primeExponent w p := (Finset.mem_filter.mp hc).2.1
    exact ih hx ht

theorem forest_insertion_eq_corrections {w : ℝ} (hw : 1 < w) {z : Node} (hs : Valid z.side z.ratio)
    (hr : 0 < z.gap) (hz : Consistent z) (hb : 2 < z.cutoff) :
    forestSum w (highPrimes w z.cutoff z.closed) z
      (cutoffInsertion w (boundaryPrimes w) (fun _ y => nodeBenchmark w y))=
      boundaryCorrection w 2 z+residualCorrection w z := by
  unfold forestSum weightedValue boundaryCorrection residualCorrection
  rw [reference_family_eq_uncapped hw hs hr hz,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ps hp
  have hpA : uncappedAllowed w 2 z ps := (Finset.mem_filter.mp hp).2
  have hsuf := suffix_highPrimes hw hs hr hz hpA
  have hcap := uncapped_cutoff_gt_two hb hpA
  dsimp only
  rw [hsuf]
  change signedWeight ps*sourceInsertion w (terminal w z ps)=_
  rw [source_insertion_identity hw _ hcap]
  unfold signedWeight
  ring

theorem actual_reference_decomposition {w : ℝ} (hw : 1 < w) {z : Node} (hs : Valid z.side z.ratio)
    (hr : 0 < z.gap) (hz : Consistent z) (hb : 2 < z.cutoff) :
    sourceReference w z-nodeBenchmark w z=boundaryCorrection w 2 z+residualCorrection w z := by
  have h := finite_cutoff_decomposition w (highPrimes_above_boundary (b:=z.cutoff) hw z.closed)
    (fun _ y => nodeBenchmark w y) z
  rw [← sourcePrimes_partition hw hb z.closed] at h
  exact h.trans (forest_insertion_eq_corrections hw hs hr hz hb)

end NumberTheoryLean.ReferenceSourceDecomposition

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



namespace NumberTheoryLean.ReferenceProductErrorBounds

open _root_.Finset
open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeTiltGeometry
open ReferenceMertens ReferenceSourcePrimeSets ReferenceBenchmarkDecay ReferenceDifferentiation
open ReferenceResidualErrors
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem primeError_pos (c w t : ℝ) : 0 < primeError c w t := Real.exp_pos _

theorem primeError_antitone {c w t s : ℝ} (hc : 0 ≤ c) (hw : 1 < w) (hts : t ≤ s) :
    primeError c w s ≤ primeError c w t := by
  apply Real.exp_le_exp.mpr
  have h := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hts (Real.log_pos hw).le)
  nlinarith

end NumberTheoryLean.ReferenceProductErrorBounds



namespace NumberTheoryLean.ReferenceLogScale

open _root_.Filter
open scoped Topology
open ReferenceProductErrorBounds ExponentialMesh

theorem primeError_two_eq (c w : ℝ) :
    primeError c w 2=Real.exp (-(c*Real.sqrt 2)*Real.sqrt (Real.log w)) := by
  unfold primeError
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

theorem log_power_primeError_tendsto (C : ℝ) (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun w : ℝ => C*(Real.log w)^n*primeError c w 2) atTop (𝓝 0) := by
  have h := log_power_exp_tendsto C n (mul_pos hc (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)))
  simpa only [primeError_two_eq] using h

theorem primeError_two_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun w : ℝ => primeError c w 2) atTop (𝓝 0) := by
  simpa only [pow_zero,one_mul] using log_power_primeError_tendsto 1 0 hc

end NumberTheoryLean.ReferenceLogScale



namespace NumberTheoryLean.ReferenceProductLower

open _root_.Filter
open scoped Topology
open ReferenceProductsBasics ReferenceMertens ReferenceProductErrors ReferenceProductErrorBounds ReferenceLogScale

theorem reference_product_lower : ∃ w₀ : ℝ,1 < w₀ ∧ ∀ w : ℝ,w₀ ≤ w →
    ∀ b : ℝ,2 ≤ b → ∀ closed : Bool,1/(4*b) ≤ referenceProduct w b closed := by
  obtain ⟨c,C,wP,hc,hC,hwP,hP⟩ := reference_product_strong
  have hdec : Tendsto (fun w => C*primeError c w 2) atTop (𝓝 0) := by
    simpa only [mul_zero] using (primeError_two_tendsto hc).const_mul C
  obtain ⟨wE,hwE⟩ := eventually_atTop.mp (hdec.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/2)))
  obtain ⟨wN,hwN⟩ := eventually_atTop.mp normalization_eventually_bounded
  refine ⟨max wP (max wE wN),hwP.trans_le (le_max_left _ _),?_⟩
  intro w hw b hb closed
  have hwp : wP ≤ w := (le_max_left _ _).trans hw
  have hwe : wE ≤ w := ((le_max_left _ _).trans (le_max_right _ _)).trans hw
  have hwn : wN ≤ w := ((le_max_right _ _).trans (le_max_right _ _)).trans hw
  have hw1 : 1 < w := hwP.trans_le hwp
  have hb0 : 0 < b := by linarith
  have hD : 0 < normalization w/b := div_pos (normalization_pos hw1) hb0
  have herr : |referenceProduct w b closed/(normalization w/b)-1| ≤ 1/2 := by
    apply (hP w hwp b hb closed).trans
    apply le_trans (mul_le_mul_of_nonneg_left (primeError_antitone hc.le hw1 hb) hC.le)
    exact hwE w hwe
  have hratio : (1/2:ℝ) ≤ referenceProduct w b closed/(normalization w/b) := by
    have hlow := (abs_le.mp herr).1
    linarith
  have hm := (le_div_iff₀ hD).mp hratio
  have hn := (hwN w hwn).1
  calc
    1/(4*b) = ((1/2:ℝ)/b)/2 := by ring
    _ ≤ (normalization w/b)/2 :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hn hb0.le) (by norm_num)
    _ ≤ referenceProduct w b closed := by linarith

end NumberTheoryLean.ReferenceProductLower



namespace NumberTheoryLean.ReferenceResidualSum

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeTiltGeometry ActualPrimeHigh ActualBoundaryDomain
open SourceNodeCoordinates ReferenceSourceDecomposition ReferenceProductErrorBounds
open ReferenceLocalResidual TwoStepDensityBounds
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

theorem signed_residual_le_absolute (w : ℝ) (start : Node) :
    |residualCorrection w start| ≤ residualAbsoluteSum w start := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro ps _hp
  simp only [abs_mul,abs_of_nonneg (prefixWeight_nonneg ps),abs_pow,abs_neg,abs_one,one_pow,one_mul]
  exact le_rfl

end NumberTheoryLean.ReferenceResidualSum



namespace NumberTheoryLean.ReferenceRelativeError

open FinitePathGeometry PrimeHistories PrimeBinMembership SourceNodeCoordinates
open ReferenceMertens ReferenceProductsBasics ReferenceProductLower ReferenceDifferentiation
open ReferenceLocalResidual ReferenceSourceDecomposition ReferenceResidualSum ReferenceProductErrorBounds
open UniformBoundaryCorrection

theorem source_relative_reference_error (d : ℝ) (hd : 0 < d) :
    ∃ c A C B₀ w₀ : ℝ,0 < c ∧ 0 < A ∧ 0 < C ∧ 0 < B₀ ∧ 1 < w₀ ∧
      ∀ w B : ℝ,w₀ ≤ w → B₀ ≤ B → Real.log B ≤ d*Real.log w → ∀ start : Node,
        start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B →
        |sourceReference w start/referenceProduct w B start.closed-parentBenchmark .even start.ratio| ≤
          A/B+C*B^2*(1+Real.log B)*primeError c w 2 := by
  obtain ⟨AB,BB,wB,hAB,hBB,hwB,hBoundary⟩ := uniform_boundary_correction_div_jb247 2 d le_rfl hd
  obtain ⟨c,CR,wR,hc,hCR,_hwR,hResidual⟩ := summed_source_residual_bound_jb247
  obtain ⟨wV,_hwV,hV⟩ := reference_product_lower
  refine ⟨c,4*AB,4*CR,max BB 4,max wB (max wR wV),hc,by positivity,by positivity,
    hBB.trans_le (le_max_left _ _),hwB.trans_le (le_max_left _ _),?_⟩
  intro w B hw hB hcomp start hi h199 h23 hcons hcut
  have hwB' : wB ≤ w := (le_max_left _ _).trans hw
  have hwR' : wR ≤ w := ((le_max_left _ _).trans (le_max_right _ _)).trans hw
  have hwV' : wV ≤ w := ((le_max_right _ _).trans (le_max_right _ _)).trans hw
  have hBB' : BB ≤ B := (le_max_left _ _).trans hB
  have hB4 : 4 ≤ B := (le_max_right _ _).trans hB
  have hBpos : 0 < B := by linarith
  have hw1 : 1 < w := hwB.trans_le hwB'
  obtain ⟨hs,hr,_hsize1,_hsize2⟩ := source_node_bounds hBpos start hi h199 h23 hcons hcut
  have hbnd := hBoundary B w hBB' hwB' hcomp start hi h199 h23 hcons hcut
  have hres := (signed_residual_le_absolute w start).trans (hResidual w hwR' B hB4 start hi h199 h23 hcons hcut)
  have hdecomp := actual_reference_decomposition hw1 hs hr hcons (by rw [hcut]; linarith)
  have hab : |sourceReference w start-nodeBenchmark w start| ≤
      AB/B^2+CR*B*(1+Real.log B)*primeError c w 2 := by
    rw [hdecomp]
    exact (abs_add_le _ _).trans (add_le_add hbnd hres)
  have hlow := hV w hwV' B (by linarith) start.closed
  have hVpos : 0 < referenceProduct w B start.closed := availableProduct_pos _ _ _
  have heq : sourceReference w start/referenceProduct w B start.closed-parentBenchmark .even start.ratio=
      (sourceReference w start-nodeBenchmark w start)/referenceProduct w B start.closed := by
    unfold nodeBenchmark
    rw [hi,hcut]
    field_simp
  have hL : 0 ≤ 1+Real.log B := by have h := Real.log_nonneg (show 1 ≤ B by linarith); linarith
  have hE := primeError_pos c w 2
  rw [heq,abs_div,abs_of_pos hVpos]
  calc
    _ ≤ (AB/B^2+CR*B*(1+Real.log B)*primeError c w 2)/referenceProduct w B start.closed :=
      div_le_div_of_nonneg_right hab hVpos.le
    _ ≤ (AB/B^2+CR*B*(1+Real.log B)*primeError c w 2)/(1/(4*B)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hlow
    _ = _ := by field_simp

end NumberTheoryLean.ReferenceRelativeError



namespace NumberTheoryLean.MovingLocalReference

open _root_.Filter _root_.Asymptotics
open scoped Topology
open FinitePathGeometry PrimeHistories PrimeBinMembership ReferenceMertens ReferenceDifferentiation
open ReferenceSourceDecomposition ReferenceProductErrorBounds ReferenceLogScale ReferenceRelativeError

theorem log_square_le_base {K : ℝ} (hK : 0 ≤ K) :
    ∀ᶠ w : ℝ in atTop,K*(Real.log w)^2 ≤ w := by
  have h : (fun w : ℝ => K*(Real.log w)^2)=o[atTop](fun w => w) := by
    simpa only [Real.rpow_ofNat,Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (2:ℝ) (s:=1) (by norm_num)).const_mul_left K
  filter_upwards [h.bound (by norm_num : (0:ℝ)<1),eventually_ge_atTop (0:ℝ)] with w hw hw0
  simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hK (sq_nonneg _)),abs_of_nonneg hw0,one_mul] using hw

theorem moving_local_reference (K ε : ℝ) (hK : 0 < K) (hε : 0 < ε) :
    ∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧ ∀ w B : ℝ,w₀ ≤ w → B₀ ≤ B →
      B ≤ K*(Real.log w)^2 → ∀ start : Node,
        start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B →
        |sourceReference w start/referenceProduct w B start.closed-parentBenchmark .even start.ratio| ≤ ε := by
  obtain ⟨c,A,C,BR,wR,hc,hA,hC,hBR,hwR,hR⟩ := source_relative_reference_error 1 (by norm_num)
  obtain ⟨wS,hwS⟩ := eventually_atTop.mp (log_square_le_base hK.le)
  have hdec := log_power_primeError_tendsto (2*C*K^2) 5 hc
  obtain ⟨wE,hwE⟩ := eventually_atTop.mp
    (hdec.eventually (eventually_le_nhds (show (0:ℝ)<ε/2 by linarith)))
  let B₀ := max BR (2*A/ε)
  let w₀ := max wR (max wS (max wE (Real.exp 1)))
  refine ⟨B₀,w₀,hBR.trans_le (le_max_left _ _),hwR.trans_le (le_max_left _ _),?_⟩
  intro w B hw hB hscale start hi h199 h23 hcons hcut
  have hwR' : wR ≤ w := (le_max_left _ _).trans hw
  have hwS' : wS ≤ w := ((le_max_left _ _).trans (le_max_right _ _)).trans hw
  have hwE' : wE ≤ w := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hw
  have hwExp : Real.exp 1 ≤ w := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hw
  have hBR' : BR ≤ B := (le_max_left _ _).trans hB
  have hBl : 2*A/ε ≤ B := (le_max_right _ _).trans hB
  have hBpos : 0 < B := hBR.trans_le hBR'
  have hlogw : 1 ≤ Real.log w := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hwExp
  have hBw : B ≤ w := hscale.trans (hwS w hwS')
  have hlogs : Real.log B ≤ Real.log w := Real.log_le_log hBpos hBw
  have hcomp : Real.log B ≤ (1:ℝ)*Real.log w := by simpa only [one_mul] using hlogs
  have herr := hR w B hwR' hBR' hcomp start hi h199 h23 hcons hcut
  have hsmall : A/B ≤ ε/2 := by
    apply (div_le_iff₀ hBpos).mpr
    have hh := (div_le_iff₀ hε).mp hBl
    nlinarith
  have hBsq : B^2 ≤ K^2*(Real.log w)^4 := by nlinarith [mul_self_le_mul_self hBpos.le hscale]
  have hL : 1+Real.log B ≤ 2*Real.log w := by linarith
  have hLogPos : 0 ≤ Real.log w := by linarith
  have hE := primeError_pos c w 2
  have hpoly : C*B^2*(1+Real.log B)*primeError c w 2 ≤ 2*C*K^2*(Real.log w)^5*primeError c w 2 := by
    have hh : B^2*(1+Real.log B) ≤ (K^2*(Real.log w)^4)*(2*Real.log w) := by
      calc
        _ ≤ B^2*(2*Real.log w) := mul_le_mul_of_nonneg_left hL (sq_nonneg B)
        _ ≤ _ := mul_le_mul_of_nonneg_right hBsq (by positivity)
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hC.le) hE.le
    convert! hm using 1 <;> first | (with_reducible_and_instances rfl) | ring
  have htail := hwE w hwE'
  linarith

end NumberTheoryLean.MovingLocalReference


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

end ErdosInverseEuler

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_MovingStopMargins
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ActualSourceStopBinding

open _root_.Finset
open FinitePathGeometry PrimeHistories SourceStopPredicate StoppedCountVertex StoppedEvaluation
open StoppedVertexHistory StoppedTraceSets StoppedCountAdapters FlatStoppedIdentity
open ReferenceAdmission ReferencePruning ErdosInverseCounts
attribute [local instance] Classical.propDecidable

theorem actual_source_stops_first {n : ℕ} (Y : ℕ) (w Cs eta Clen B xi b₀ b₁ mu : ℝ)
    (lower width : Fin n → ℝ) (label : ℕ → Fin n) (a : ℕ → ℕ) (z : Node) (P : Finset ℕ)
    {ps : List ℕ}
    (hp : ps ∈ stopped w (stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z)
      P.card (rootVertex z ∅ P mu)) :
    (terminal w z ps).side = .even ∧
      stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z ps ∧
      ∀ pre tail : List ℕ,ps = pre++tail → tail ≠ [] →
        ¬((terminal w z pre).side = .even ∧
          stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z pre) := by
  have h := FirstStopSemantics.stopped_first w
    (stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z) P.card (rootVertex z ∅ P mu) hp
  simpa only [FirstStopSemantics.FirstStop,lowerStop,after_node,after_past,rootVertex,List.nil_append,and_assoc] using h

end NumberTheoryLean.ActualSourceStopBinding

end

section

namespace NumberTheoryLean.FirstStopFreezing
open FinitePathGeometry PrimeHistories SourceStopPredicate ActualSourceTags FiniteFirstTag
open SourceCandidateFreezing RepresentativeTraceInvariance
open StoppedCountVertex StoppedVertexHistory StoppedEvaluation StoppedCountAdapters FirstStopSemantics
open ErdosInversePrimeBin ErdosInverseAlignment

theorem firstStop_iff_takes (w : ℝ) (stop : List ℕ → Prop) (v : Vertex) (ps : List ℕ) :
    FirstStop w stop v ps ↔ lowerStop stop (after w v ps) ∧
      ∀ k < ps.length,¬lowerStop stop (after w v (ps.take k)) := by
  constructor
  · intro h
    refine ⟨h.1,?_⟩
    intro k hk
    apply h.2 (ps.take k) (ps.drop k) (List.take_append_drop k ps).symm
    intro hz
    have hh := congrArg List.length hz
    simp only [List.length_drop,List.length_nil] at hh
    omega
  · rintro ⟨h,hs⟩
    refine ⟨h,?_⟩
    intro pre tail heq htail
    have htpos : 0 < tail.length := List.length_pos_iff.mpr htail
    have hlen : pre.length < ps.length := by rw [heq,List.length_append]; omega
    have hh := hs pre.length hlen
    simpa only [heq,List.take_append,List.take_length,Nat.sub_self,List.take_zero,List.append_nil] using hh

theorem first_source_stop_replacement {n : ℕ} (Y : ℕ) (w Cs eta Clen B xi b₀ b₁ mu : ℝ)
    (lower width : Fin n → ℝ) (label : ℕ → Fin n) (a : ℕ → ℕ) (z : Node) (P : Finset ℕ)
    (pre tail : List ℕ) (p p' : ℕ) {t : Tag n}
    (ht : sourceTag (Y:ℝ) w Cs eta lower width label (sourceClass a) (pre++p::tail) = some t)
    (hc : tagCandidate (Y:ℝ) w Cs eta lower width label (sourceClass a) p = some (t.bin,t.rational))
    (hlabel : label p' = label p)
    (hp' : p' ∈ primeBin (lower (label p')) (width (label p')))
    (ha' : aligns (sourceClass a) t.rational p') :
    FirstStop w (stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z)
      (rootVertex z ∅ P mu) (pre++p::tail) ↔
    FirstStop w (stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z)
      (rootVertex z ∅ P mu) (pre++p'::tail) := by
  let stop := stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z
  let v := rootVertex z ∅ P mu
  have hlen : (pre++p::tail).length = (pre++p'::tail).length := by simp
  have he (k : ℕ) : lowerStop stop (after w v ((pre++p::tail).take k)) ↔
      lowerStop stop (after w v ((pre++p'::tail).take k)) := by
    have hside := terminal_side_length w z z ((pre++p::tail).take k) ((pre++p'::tail).take k) rfl
      (by simp only [List.length_take,hlen])
    have hh := all_prefix_candidate_replacement Y w Cs eta Clen B xi b₀ b₁ lower width label a z
      pre tail p p' ht hc hlabel hp' ha' k
    simp only [lowerStop,after_node,after_past,v,rootVertex,List.nil_append,hside]
    exact and_congr_right (fun _ => hh)
  have hlast := he (pre++p::tail).length
  simp only [List.take_length] at hlast
  rw [hlen,List.take_length] at hlast
  rw [firstStop_iff_takes,firstStop_iff_takes]
  change (lowerStop stop (after w v (pre++p::tail)) ∧ _) ↔
    (lowerStop stop (after w v (pre++p'::tail)) ∧ _)
  rw [hlast]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro k
  rw [hlen,he k]
end NumberTheoryLean.FirstStopFreezing

end

section

namespace NumberTheoryLean.StoppedTraceMembership
open FinitePathGeometry PrimeHistories StoppedCountVertex StoppedVertexHistory StoppedEvaluation
open StoppedTraceSets StoppedTraceAdmission FirstStopSemantics ReferenceAdmission ReferencePruning
open ReferencePrefixRecurrence ErdosPrimeInputs.PrimePrefixMass
attribute [local instance] Classical.propDecidable

theorem reference_cons_iff (w : ℝ) (v : Vertex) (p : ℕ) (ps : List ℕ) :
    p::ps ∈ referencePrefixes w v.available v.node.side v.node.gap ↔
    p ∈ includedPrimes w v ∧ ps ∈ referencePrefixes w (child w v p).available
      (child w v p).node.side (child w v p).node.gap := by
  constructor
  · intro h
    obtain ⟨hD,hA⟩ := Finset.mem_filter.mp h
    have hp := (mem_decreasingPrefixes.mp hD).2 p (by simp)
    have htail := (append_mem_decreasing_iff (singleton_prefix_mem hp)).mp hD
    refine ⟨Finset.mem_filter.mpr ⟨hp,hA.1⟩,Finset.mem_filter.mpr ⟨?_,hA.2⟩⟩
    simpa only [suffixPrimes,List.mem_singleton,forall_eq,child] using htail
  · rintro ⟨hp,hps⟩
    exact reference_child_cons w v hp hps

theorem stopped_length (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    {ps : List ℕ} (hp : ps ∈ stopped w stop n v) : ps.length ≤ n := by
  induction n generalizing v ps with
  | zero =>
    by_cases hs : lowerStop stop v
    · have he : ps=[] := by simpa only [stopped,traces,hs,ite_true, if_true,Finset.mem_singleton] using hp
      simp [he]
    · simp [stopped,traces,hs] at hp
  | succ n ih =>
    by_cases hs : lowerStop stop v
    · have he : ps=[] := by simpa only [stopped,traces,hs,ite_true, if_true,Finset.mem_singleton] using hp
      simp [he]
    · simp only [stopped,traces,hs,ite_false, if_false] at hp
      obtain ⟨p,_hp,hps⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨tail,ht,rfl⟩ := Finset.mem_image.mp hps
      exact Nat.succ_le_succ (ih (child w v p) ht)

theorem stopped_of_reference_first (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    (ps : List ℕ) (hlen : ps.length ≤ n)
    (href : ps ∈ referencePrefixes w v.available v.node.side v.node.gap)
    (hf : FirstStop w stop v ps) : ps ∈ stopped w stop n v := by
  induction ps generalizing n v with
  | nil =>
    have hs : lowerStop stop v := hf.1
    cases n <;> simp [stopped,traces,hs]
  | cons p ps ih =>
    obtain ⟨hp,ht⟩ := (reference_cons_iff w v p ps).mp href
    have hroot : ¬lowerStop stop v := hf.2 [] (p::ps) rfl (by simp)
    have hfirst : FirstStop w stop (child w v p) ps := by
      refine ⟨hf.1,?_⟩
      intro pre tail heq htail
      exact hf.2 (p::pre) tail (by simp only [List.cons_append,heq]) htail
    cases n with
    | zero => simp at hlen
    | succ n =>
      have hh := ih n (child w v p) (by simpa using hlen) ht hfirst
      simp only [stopped,traces,hroot,ite_false, if_false]
      exact Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_image.mpr ⟨ps,hh,rfl⟩⟩

end NumberTheoryLean.StoppedTraceMembership

end

section

namespace NumberTheoryLean.TagBelowStopWindow
open _root_.Filter FinitePathGeometry PrimeHistories SourceStopPredicate ActualSourceTags FiniteFirstTag
open PrimeBinRepresentatives ErdosInversePrimeBin ErdosInverseAlignment

theorem replacement_product (pre tail : List ℕ) (p : ℕ) :
    (pre++p::tail).prod=p*(pre.prod*tail.prod) := by
  rw [List.prod_append,List.prod_cons]
  ac_rfl

end NumberTheoryLean.TagBelowStopWindow

end

section

namespace NumberTheoryLean.ActualFrozenStopFamily
open FinitePathGeometry PrimeHistories SourceStopPredicate ActualSourceTags FiniteFirstTag
open StoppedCountVertex StoppedVertexHistory StoppedEvaluation StoppedCountAdapters StoppedTraceSets
open FirstStopSemantics StoppedTraceAdmission StoppedTraceMembership FirstStopFreezing
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open BinReplacementOrder ReferenceAdmission ActualSourceStopBinding ErdosInversePrimeBin ErdosInverseAlignment
open ErdosPrimeInputs.PrimePrefixMass
attribute [local instance] Classical.propDecidable

theorem actual_stopped_replacement (Y : ℕ) (w top Cs eta Clen B xi b₀ b₁ mu : ℝ)
    (hw : 1 < w) (hwtop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen)
    (a : ℕ → ℕ) (z : Node) (pre tail : List ℕ) (p p' : ℕ)
    {t : Tag (binCount w top xi)}
    (hs : pre++p::tail ∈ stopped w
      (stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) hwtop hxi) a z)
      (sourcePrimeSet w top).card (rootVertex z ∅ (sourcePrimeSet w top) mu))
    (ht : sourceTag (Y:ℝ) w Cs eta (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) hwtop hxi) (sourceClass a) (pre++p::tail) = some t)
    (hc : tagCandidate (Y:ℝ) w Cs eta (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) hwtop hxi) (sourceClass a) p = some (t.bin,t.rational))
    (hp' : p' ∈ primeBin (lower w top xi t.bin) (width w top xi t.bin))
    (ha' : aligns (sourceClass a) t.rational p') :
    pre++p'::tail ∈ stopped w
      (stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) hwtop hxi) a z)
      (sourcePrimeSet w top).card (rootVertex z ∅ (sourcePrimeSet w top) mu) := by
  let lo := lower w top xi
  let wi := width w top xi
  let lab := label (zero_lt_one.trans hw) hwtop hxi
  let P := sourcePrimeSet w top
  let stop := stopCandidate Y w Cs eta Clen B xi b₀ b₁ lo wi lab a z
  let v := rootVertex z ∅ P mu
  have hw0 : 0 < w := zero_lt_one.trans hw
  have htag := candidate_witness (Y:ℝ) w Cs eta lo wi lab (sourceClass a) p hc
  have hnew := (bin_mem_iff_label hw0 hwtop hxi t.bin p').mp hp'
  have hlabel : lab p' = lab p := hnew.2.2.2.trans htag.1
  have hp'own : p' ∈ primeBin (lo (lab p')) (wi (lab p')) := by
    change p' ∈ primeBin (lower w top xi (lab p')) (width w top xi (lab p'))
    have hnewlabel : lab p' = t.bin := hnew.2.2.2
    rw [hnewlabel]
    exact hp'
  have hp'S : p' ∈ P := (mem_sourcePrimeSet hw0 hwtop p').mpr ⟨hnew.1,hnew.2.1,hnew.2.2.1⟩
  have href := trace_reference_member w stop P.card v (Or.inr hs)
  have hD := mem_decreasingPrefixes.mp (Finset.mem_filter.mp href).1
  have hall : ∀ q ∈ pre++p::tail,q ∈ P := hD.2
  have hf := stopped_first w stop P.card v hs
  have hcand : stop (pre++p::tail) := by
    have hh := hf.1.2
    simpa only [after_past,v,rootVertex,List.nil_append] using hh
  have hcount : ((pre++p::tail).map lab).count (lab p)=1 := by
    obtain ⟨u,hu,huCount,_huAlign⟩ := hcand.2.2.2.2.2
    have hut : u=t := Option.some.inj (hu.symm.trans ht)
    subst u
    rw [← htag.1]
    exact huCount
  have hdec := (decreasing_replacement hw0 hwtop hxi pre tail p p' hall hp'S hlabel hcount).mp hD.1
  have hfirst : FirstStop w stop v (pre++p'::tail) :=
    (first_source_stop_replacement Y w Cs eta Clen B xi b₀ b₁ mu lo wi lab a z P pre tail p p'
      ht hc hlabel hp'own ha').mp hf
  have hnewCand : stop (pre++p'::tail) := by
    have hh := hfirst.1.2
    simpa only [after_past,v,rootVertex,List.nil_append] using hh
  have hadmit := candidate_admitted Y w Cs eta Clen B xi b₀ b₁ lo wi lab a z (pre++p'::tail)
    hw hC hxi.le (fun i => endpoint_pos hw0 _) (fun i => (effectiveWidth_pos hw0 hwtop hxi).le) hnewCand
  have hmem : ∀ q ∈ pre++p'::tail,q ∈ P :=
    (ActualTagFreezing.forall_mem_replacement_iff (fun q => q ∈ P) pre tail p p'
      (hall p (by simp)) hp'S).mp hall
  apply stopped_of_reference_first w stop P.card v (pre++p'::tail)
  · have hl := stopped_length w stop P.card v hs
    simpa only [List.length_append,List.length_cons] using hl
  · exact Finset.mem_filter.mpr ⟨mem_decreasingPrefixes.mpr ⟨hdec,hmem⟩,hadmit⟩
  · exact hfirst

end NumberTheoryLean.ActualFrozenStopFamily

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_FrozenSuffixData
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.FrozenSuffixData
open PrimeHistories StoppedVertexHistory StoppedCountVertex ReferencePruning

theorem terminal_suffix_cutoff (w : ℝ) (z z' : Node) (tail : List ℕ) (htail : tail ≠ []) :
    (terminal w z tail).cutoff=(terminal w z' tail).cutoff ∧
      (terminal w z tail).closed=false ∧ (terminal w z' tail).closed=false := by
  induction tail generalizing z z' with
  | nil => exact False.elim (htail rfl)
  | cons p ps ih =>
    cases ps with
    | nil => simp [terminal,step]
    | cons q qs => exact ih (step w z p) (step w z' p) (by simp)

end NumberTheoryLean.FrozenSuffixData

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_SourceMarkedStopping
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.MarkedPrefixTools
open FinitePathGeometry PrimeHistories FiniteFirstTag ActualSourceTags PrimeBinRepresentatives
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem terminal_cutoff_last (w : ℝ) (z : Node) (ps : List ℕ) (hne : ps ≠ []) :
    (terminal w z ps).cutoff=primeExponent w (ps.getLast hne) := by
  conv_lhs => rw [← List.dropLast_append_getLast hne]
  rw [terminal_append]
  rfl

theorem terminal_lastD (w : ℝ) (z : Node) (ps : List ℕ) (hne : ps ≠ []) :
    (terminal w z ps).cutoff=primeExponent w (ps.getLastD 0) := by
  have hh := terminal_cutoff_last w z ps hne
  have he : ps.getLastD 0=ps.getLast hne := by
    conv_lhs => rw [← List.dropLast_append_getLast hne]
    exact List.getLastD_concat
  rwa [he]

end NumberTheoryLean.MarkedPrefixTools

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_SourceStopWindow
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceStopWindow
open FinitePathGeometry PrimeHistories SourceStopPredicate RepresentativeAdmission RepresentativeStopGeometry
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinMaps
open MarkedPrefixTools ErdosInversePrimeBin ErdosPrimeInputs.HarmonicPrimeMeasure

theorem candidate_source_primes (Y : ℕ) {w top Cs eta Clen B xi b₀ b₁ : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (a : ℕ → ℕ) (z : Node) (ps : List ℕ)
    (hc : stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) a z ps) :
    ∀ p ∈ ps,p ∈ sourcePrimeSet w top := by
  intro p hp
  exact (mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mpr
    (bin_prime_in_source (zero_lt_one.trans hw) htop hxi _ (hc.2.2.1 p hp))

theorem candidate_actual_window (Y : ℕ) {w top Cs eta Clen B xi b₀ b₁ : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen)
    (hcomp : Real.log B ≤ 2*Real.log w)
    (hsmall : 2*Clen*xi+(218/100)*(xi/Real.log w) ≤ (2/100)*b₀)
    (a : ℕ → ℕ) (z : Node) (ps : List ℕ)
    (hc : stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) a z ps) :
    b₀-xi/Real.log w ≤ (terminal w z ps).cutoff ∧ (terminal w z ps).cutoff ≤ b₁ ∧
      204/100 ≤ (terminal w z ps).gap/(terminal w z ps).cutoff ∧
      (terminal w z ps).gap/(terminal w z ps).cutoff ≤ 218/100 := by
  let rep := representative w (lower w top xi) (width w top xi) (label (zero_lt_one.trans hw) htop hxi)
  have hsource := candidate_source_primes Y hw htop hxi a z ps hc
  have hlast : ps.getLastD 0 ∈ ps := by
    have he : ps.getLastD 0=ps.getLast hc.1 := by
      conv_lhs => rw [← List.dropLast_append_getLast hc.1]
      exact List.getLastD_concat
    rw [he]
    exact List.getLast_mem hc.1
  have hp := (mem_sourcePrimeSet (zero_lt_one.trans hw) htop _).mp (hsource _ hlast)
  have hx1 : 1 < primeExponent w (ps.getLastD 0) :=
    (one_lt_div (Real.log_pos hw)).mpr (Real.log_lt_log (zero_lt_one.trans hw) hp.2.1)
  have hx := source_representative_error hw htop hxi (hsource _ hlast)
  change 0 ≤ rep (ps.getLastD 0)-primeExponent w (ps.getLastD 0) ∧
    rep (ps.getLastD 0)-primeExponent w (ps.getLastD 0) ≤ xi/Real.log w at hx
  rw [← terminal_lastD w z ps hc.1] at hx hx1
  have hr := source_prefix_movement hw htop hxi hC hcomp z ps hsource hc.2.1
  change 0 ≤ (terminal w z ps).gap-representativeGap rep z.gap ps ∧
    (terminal w z ps).gap-representativeGap rep z.gap ps ≤ 2*Clen*xi at hr
  have hwin := hc.2.2.2.2.1
  exact representative_to_actual_window (r := (terminal w z ps).gap)
    (rrep := representativeGap rep z.gap ps) (x := (terminal w z ps).cutoff) (xrep := rep (ps.getLastD 0))
    (Delta := 2*Clen*xi) (h := xi/Real.log w) (by linarith) (by linarith [hx.1]) (by linarith [hx.2])
    (by linarith [hr.1]) (by linarith [hr.2]) hwin.1 hwin.2.1 hwin.2.2.1 hwin.2.2.2 hsmall
end NumberTheoryLean.SourceStopWindow

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_MovingStopBandParameters
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.MovingStopBandParameters
open _root_.Filter FinitePathGeometry PrimeHistories SourceStopPredicate SourceStopWindow
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open MarkedPrefixTools MarkedSourceSmallness ErdosPrimeInputs.HarmonicPrimeMeasure

theorem moving_stop_band_conditions (Clen xi : ℝ) (hxi : 0 ≤ xi) {K : ℝ} (hK : 0 < K) :
    ∀ᶠ w : ℝ in atTop,1 < w ∧ 1 ≤ Real.log w ∧ 401 ≤ K*(Real.log w)^2 ∧
      2*Clen*xi+(218/100)*(xi/Real.log w) ≤ (2/100)*(K*(Real.log w)^2) ∧
      xi/Real.log w ≤ (K*(Real.log w)^2)/2 := by
  let M := max 401 (max (2*xi) (50*(2*Clen*xi+(218/100)*xi)+1))
  filter_upwards [moving_compact_gap_small (6*M) hK,
    Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_gt_atTop (1:ℝ)] with w hm hlog hw
  have hb : M < K*(Real.log w)^2 := by linarith
  have h₁ : (401:ℝ) ≤ M := le_max_left _ _
  have h₂ : 2*xi ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have h₃ : 50*(2*Clen*xi+(218/100)*xi)+1 ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have hd := div_le_self hxi hlog
  exact ⟨hw,hlog,by linarith,by linarith,by linarith⟩

theorem last_prime_cutoff_power {w : ℝ} (hw : 1 < w) (z : Node) (ps : List ℕ)
    (hne : ps ≠ []) (hP : 0 < (ps.getLastD 0:ℝ)) :
    w^(terminal w z ps).cutoff=(ps.getLastD 0:ℝ) := by
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hw),terminal_lastD w z ps hne,primeExponent]
  have he : Real.log w*(Real.log (ps.getLastD 0:ℝ)/Real.log w)=Real.log (ps.getLastD 0:ℝ) := by
    field_simp [(Real.log_pos hw).ne']
  rw [he,Real.exp_log hP]

theorem candidate_moving_last_prime_lower (Y : ℕ) {w top Cs eta Clen B xi K b₁ : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen)
    (hcomp : Real.log B ≤ 2*Real.log w)
    (hsmall : 2*Clen*xi+(218/100)*(xi/Real.log w) ≤ (2/100)*(K*(Real.log w)^2))
    (hhalf : xi/Real.log w ≤ (K*(Real.log w)^2)/2)
    (residue : ℕ → ℕ) (z : Node) (ps : List ℕ)
    (hc : stopCandidate Y w Cs eta Clen B xi (K*(Real.log w)^2) b₁ (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) residue z ps) :
    Real.exp ((K/2)*(Real.log w)^3) ≤ (ps.getLastD 0:ℝ) ∧
      w^(terminal w z ps).cutoff=(ps.getLastD 0:ℝ) := by
  have hwindow := candidate_actual_window Y hw htop hxi hC hcomp hsmall residue z ps hc
  have hsource := candidate_source_primes Y hw htop hxi residue z ps hc
  have hlast : ps.getLastD 0 ∈ ps := by
    have he : ps.getLastD 0=ps.getLast hc.1 := by
      conv_lhs => rw [← List.dropLast_append_getLast hc.1]
      exact List.getLastD_concat
    rw [he]
    exact List.getLast_mem hc.1
  have hprime := (mem_sourcePrimeSet (zero_lt_one.trans hw) htop _).mp (hsource _ hlast)
  have hP : 0 < (ps.getLastD 0:ℝ) := by exact_mod_cast hprime.1.pos
  refine ⟨?_,last_prime_cutoff_power hw z ps hc.1 hP⟩
  have hcut : (K*(Real.log w)^2)/2 ≤ (terminal w z ps).cutoff := by linarith [hwindow.1]
  have hlogP : Real.log (ps.getLastD 0:ℝ)=(terminal w z ps).cutoff*Real.log w := by
    rw [terminal_lastD w z ps hc.1,primeExponent,div_mul_cancel₀ _ (Real.log_pos hw).ne']
  rw [← Real.exp_log hP]
  apply Real.exp_le_exp.mpr
  calc
    _ = ((K*(Real.log w)^2)/2)*Real.log w := by ring
    _ ≤ (terminal w z ps).cutoff*Real.log w := mul_le_mul_of_nonneg_right hcut (Real.log_pos hw).le
    _ = _ := hlogP.symm
end NumberTheoryLean.MovingStopBandParameters


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_ActualRepeatedBinStep
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.CandidateTerminalGeometry
open FinitePathGeometry PrimeHistories PrimeBinMembership SourceStopPredicate SourceStopWindow
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open MovingStopBandParameters FrozenSuffixData
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem terminal_ratio_div_cutoff (w : ℝ) (z : Node) (ps : List ℕ) (hne : ps ≠ [])
    (hx : (terminal w z ps).cutoff ≠ 0) :
    (terminal w z ps).ratio=(terminal w z ps).gap/(terminal w z ps).cutoff := by
  induction ps generalizing z with
  | nil => exact False.elim (hne rfl)
  | cons p ps ih =>
    cases ps with
    | nil =>
      change primeExponent w p ≠ 0 at hx
      change PrimeTiltGeometry.childRatio w z.gap p=(z.gap-primeExponent w p)/primeExponent w p
      unfold PrimeTiltGeometry.childRatio
      field_simp [hx]
    | cons q qs => exact ih (step w z p) (by simp) hx

theorem candidate_terminal_geometry (Y : ℕ) {w top Cs eta Clen B xi b₀ b₁ : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen)
    (hcomp : Real.log B ≤ 2*Real.log w) (hpos : 0 < b₀-xi/Real.log w)
    (hsmall : 2*Clen*xi+(218/100)*(xi/Real.log w) ≤ (2/100)*b₀)
    (residue : ℕ → ℕ) (z : Node) (ps : List ℕ)
    (hc : stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) residue z ps) :
    b₀-xi/Real.log w ≤ (terminal w z ps).cutoff ∧ (terminal w z ps).cutoff ≤ b₁ ∧
      204/100 ≤ (terminal w z ps).ratio ∧ (terminal w z ps).ratio ≤ 218/100 ∧
      Consistent (terminal w z ps) ∧ (terminal w z ps).closed=false := by
  have hwin := candidate_actual_window Y hw htop hxi hC hcomp hsmall residue z ps hc
  have hx : 0 < (terminal w z ps).cutoff := hpos.trans_le hwin.1
  have hfrac := terminal_ratio_div_cutoff w z ps hc.1 hx.ne'
  have hlo : 204/100 ≤ (terminal w z ps).ratio := by rw [hfrac]; exact hwin.2.2.1
  have hhi : (terminal w z ps).ratio ≤ 218/100 := by rw [hfrac]; exact hwin.2.2.2
  have hcons : Consistent (terminal w z ps) := by
    apply (eq_div_iff (show (terminal w z ps).ratio ≠ 0 by linarith)).mpr
    have hh := (eq_div_iff hx.ne').mp hfrac
    nlinarith
  exact ⟨hwin.1,hwin.2.1,hlo,hhi,hcons,(terminal_suffix_cutoff w z z ps hc.1).2.1⟩
end NumberTheoryLean.CandidateTerminalGeometry



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_CanonicalCorrectionSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.CanonicalKeyReplacement
open PrimeHistories CanonicalStopKey CanonicalKeyWitness ActualStopGroupFiber
open SourceStopPredicate ActualTagFreezing ActualFrozenStopFamily BinReplacementOrder
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosInversePrimeBin ErdosInverseAlignment


variable {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
  {Y : ℕ} {Cs eta Clen B b₀ b₁ mu : ℝ} {a : ℕ → ℕ} {z : Node}
  {k : Key (binCount w top xi)} (d : Witness hw htop hxi Y Cs eta Clen B b₀ b₁ mu a z k)

include d

theorem aligning_word_mem (hC : 0 ≤ Clen) (p : ℕ)
    (hp : p∈primeBin (lower w top xi k.tag.bin) (width w top xi k.tag.bin))
    (ha : aligns (sourceClass a) k.tag.rational p) :
    k.pre++p::k.tail∈family Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z :=
  actual_stopped_replacement Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi hC a z k.pre k.tail d.p₀ p
    d.mem_family d.tag d.prime_tag hp ha

end NumberTheoryLean.CanonicalKeyReplacement



namespace NumberTheoryLean.MovingCandidateBands
open _root_.Filter _root_.Erdos970.Filter FinitePathGeometry PrimeHistories PrimeBinMembership SourceStopPredicate
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open MovingStopBandParameters CandidateTerminalGeometry


theorem moving_candidate_node_window {Clen xi K : ℝ} (hC : 0 ≤ Clen)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hK : 0 < K) :
    ∀ᶠ w : ℝ in atTop,∃ hw : 1 < w,∀ top : ℝ,∀ htop : w < top,
      ∀ B : ℝ,Real.log B ≤ 2*Real.log w → ∀ Y : ℕ,∀ Cs eta b₁ : ℝ,
      ∀ (residue : ℕ → ℕ) (z : Node) (ps : List ℕ),
      stopCandidate Y w Cs eta Clen B xi (K*(Real.log w)^2) b₁ (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) residue z ps →
      K*(Real.log w)^2-xi/Real.log w ≤ (terminal w z ps).cutoff ∧ (terminal w z ps).cutoff ≤ b₁ ∧
        204/100 ≤ (terminal w z ps).ratio ∧ (terminal w z ps).ratio ≤ 218/100 ∧
        Consistent (terminal w z ps) ∧ (terminal w z ps).closed=false ∧
        Real.exp ((K/2)*(Real.log w)^3) ≤ (ps.getLastD 0:ℝ) ∧
        w^(terminal w z ps).cutoff=(ps.getLastD 0:ℝ) := by
  filter_upwards [moving_stop_band_conditions Clen xi hxi.le hK] with w hcond
  obtain ⟨hw,hlog,hb₀,hsmall,hhalf⟩ := hcond
  refine ⟨hw,?_⟩
  intro top htop B hcomp Y Cs eta b₁ residue z ps hc
  have hstep : xi/Real.log w ≤ 1 := (div_le_self hxi.le hlog).trans hxi1
  have hpos : 0 < K*(Real.log w)^2-xi/Real.log w := by linarith
  have hn := candidate_terminal_geometry Y hw htop hxi hC hcomp hpos hsmall residue z ps hc
  have hP := candidate_moving_last_prime_lower Y hw htop hxi hC hcomp hsmall hhalf residue z ps hc
  exact ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2.1,hn.2.2.2.2.2,hP.1,hP.2⟩

end NumberTheoryLean.MovingCandidateBands



namespace NumberTheoryLean.CanonicalKeyBands
open _root_.Filter _root_.Erdos970.Filter FinitePathGeometry PrimeHistories CanonicalStopKey CanonicalKeyWitness CanonicalKeyReplacement
open SourceStopPredicate TagBelowStopWindow MovingCandidateBands
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosInversePrimeBin
open scoped Topology


theorem last_fixed_tail (pre tail : List ℕ) (p : ℕ) (htail : tail≠[]) :
    (pre++p::tail).getLastD 0=tail.getLastD 0 := by
  rw [← List.dropLast_append_getLast htail,← List.cons_append,← List.append_assoc]
  simp only [List.getLastD_concat]

end NumberTheoryLean.CanonicalKeyBands



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_LossBounds
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosBoundaryLoss

theorem log_two_bounds : (69:ℝ)/100 < Real.log 2 ∧ Real.log 2 < (7:ℝ)/10 := by
  constructor
  · linarith [Real.log_two_gt_d9]
  · linarith [Real.log_two_lt_d9]

end ErdosBoundaryLoss

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceRootReference
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Filter
open scoped Topology
namespace ErdosPositiveReference
open ErdosOmissionBindings ErdosOmissionTail ErdosContinuousOmission
open ErdosBoundaryIntegral ErdosBoundaryLoss
open Erdos970Dependency.InvariantCostBound
open NumberTheoryLean.BuchstabBridge

theorem exp_gamma_lt_two : Real.exp Real.eulerMascheroniConstant < 2 := by
  have hg : Real.eulerMascheroniConstant < Real.log 2 := by
    linarith [Real.eulerMascheroniConstant_lt_two_thirds,log_two_bounds.1]
  have h := Real.exp_lt_exp.mpr hg
  simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using h

end ErdosPositiveReference

end


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_StoppedReferenceFinite
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosStoppedReferenceUpper
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.BuchstabBridge
open NumberTheoryLean.LinearSieveFunctions NumberTheoryLean.ReferenceDifferentiation

theorem log_near_two_upper {s : ℝ} (hs : 2 ≤ s) :
    Real.log (s-1) ≤ 1/10+(10/11)*(s-21/10) := by
  have hpos : 0 < s-1 := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hpos (by norm_num : (0:ℝ)<11/10))
  rw [Real.log_div (ne_of_gt hpos) (by norm_num : (11/10:ℝ)≠0)] at hlog
  have ht := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<11/10)
  linarith

theorem parent_benchmark_le_32 {s : ℝ} (hs : 2 ≤ s) (hu : s ≤ 218/100) :
    parentBenchmark .even s ≤ 32/100 := by
  rw [parent_even_eq_starting (by linarith : s ≤ 4)]
  unfold startingExtension
  have hlog := log_near_two_upper hs
  have hnonneg : 0 ≤ Real.log (s-1) := Real.log_nonneg (by linarith)
  have hA : sieveA ≤ 4 := by
    unfold sieveA
    linarith [ErdosPositiveReference.exp_gamma_lt_two]
  have hm := mul_le_mul_of_nonneg_right hA hnonneg
  apply (div_le_iff₀ (by linarith : 0 < s)).mpr
  nlinarith

end ErdosStoppedReferenceUpper

end

section

namespace ErdosStoppedReferenceUpper
open _root_.Filter
open NumberTheoryLean FinitePathGeometry PrimeHistories PrimeBinMembership
open ReferenceAdmission ReferencePruning ReferenceProductsBasics ReferenceMertens
open ReferenceSourcePrimeSets ReferenceSourceDecomposition ReferenceDifferentiation
open ErdosPrimeInputs.MertensStrong

theorem strict_euler_split {w P : ℝ} (hw : 0 ≤ w) (hP : w < P) :
    primeProduct w*availableProduct w P false=strictEuler P := by
  classical
  have hP0 : 0 ≤ P := hw.trans hP.le
  have he : availablePrimes 0 P false = Nat.primesLE ⌊w⌋₊ ∪ availablePrimes w P false := by
    ext p
    simp only [Finset.mem_union,availablePrimes_membership hP0,Bool.false_eq_true,ite_false, if_false,Nat.mem_primesLE,
      Nat.le_floor_iff hw]
    constructor
    · rintro ⟨hp,_hp0,hpP⟩
      by_cases hpw : (p:ℝ) ≤ w
      · exact Or.inl ⟨hpw,hp⟩
      · exact Or.inr ⟨hp,lt_of_not_ge hpw,hpP⟩
    · rintro (⟨hpw,hp⟩|⟨hp,hwp,hpP⟩)
      · exact ⟨hp,by exact_mod_cast hp.pos,hpw.trans_lt hP⟩
      · exact ⟨hp,by exact_mod_cast hp.pos,hpP⟩
  have hd : Disjoint (Nat.primesLE ⌊w⌋₊) (availablePrimes w P false) := by
    apply Finset.disjoint_left.mpr
    intro p hp hpa
    have hlo := ((availablePrimes_membership hP0 false p).mp hpa).2.1
    have hhi := (Nat.le_floor_iff hw).mp (Nat.mem_primesLE.mp hp).1
    linarith
  simp only [primeProduct_eq_survivor,strictEuler,availableProduct]
  rw [he]
  exact (Finset.prod_union hd).symm

theorem moving_finite_reference_upper (K : ℝ) (hK : 0 < K) :
    ∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧ ∀ w B : ℝ,w₀ ≤ w → B₀ ≤ B →
      B ≤ K*(Real.log w)^2 → ∀ z : Node,
      z.side=.even → 2 ≤ z.ratio → z.ratio ≤ 218/100 → Consistent z → z.cutoff=B →
      sourceReference w z ≤ (321/1000)*referenceProduct w B z.closed := by
  obtain ⟨B₀,w₀,hB₀,hw₀,h⟩ := MovingLocalReference.moving_local_reference K (1/1000) hK (by norm_num)
  refine ⟨B₀,w₀,hB₀,hw₀,?_⟩
  intro w B hw hB hscale z hi hlo hhi hcons hcut
  have herr := h w B hw hB hscale z hi (by linarith) (by linarith) hcons hcut
  have hf := parent_benchmark_le_32 hlo hhi
  have hquot : sourceReference w z/referenceProduct w B z.closed ≤ 321/1000 := by
    linarith [(abs_le.mp herr).2]
  exact (div_le_iff₀ (availableProduct_pos w (w^B) z.closed)).mp hquot

theorem moving_vertex_reference_upper (K : ℝ) (hK : 0 < K) :
    ∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧ ∀ w B J : ℝ,w₀ ≤ w → B₀ ≤ B →
      B ≤ K*(Real.log w)^2 → 0 ≤ J → ∀ v : StoppedCountVertex.Vertex,
      v.node.side=.even → 2 ≤ v.node.ratio → v.node.ratio ≤ 218/100 →
      Consistent v.node → v.node.cutoff=B → v.node.closed=false →
      v.available=sourcePrimes w B false → v.scale=J*primeProduct w →
      StoppedCountVertex.referenceValue w v ≤ (321/1000)*J*strictEuler (w^B) := by
  obtain ⟨B₀,w₀,hB₀,hw₀,h⟩ := moving_finite_reference_upper K hK
  refine ⟨max B₀ 2,w₀,hB₀.trans_le (le_max_left _ _),hw₀,?_⟩
  intro w B J hw hB hscale hJ v hi hlo hhi hcons hcut hclosed hav hmu
  have hB' : B₀ ≤ B := (le_max_left _ _).trans hB
  have hB2 : 2 ≤ B := (le_max_right _ _).trans hB
  have hw1 : 1 < w := hw₀.trans_le hw
  have hw0 : 0 < w := by linarith
  have hwp : w < w^B := by
    simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hw1 (show (1:ℝ)<B by linarith)
  have href := h w B hw hB' hscale v.node hi hlo hhi hcons hcut
  rw [hclosed] at href
  have hmu0 : 0 ≤ J*primeProduct w := mul_nonneg hJ (actual_primeProduct_pos w).le
  have hs := mul_le_mul_of_nonneg_left href hmu0
  have he : StoppedCountVertex.referenceValue w v=(J*primeProduct w)*sourceReference w v.node := by
    simp only [StoppedCountVertex.referenceValue,sourceReference,hav,hmu,hcut,hclosed]
  rw [he]
  calc
    _ ≤ (J*primeProduct w)*((321/1000)*referenceProduct w B false) := hs
    _ = (321/1000)*J*(primeProduct w*availableProduct w (w^B) false) := by
      unfold referenceProduct
      ring
    _ = _ := by rw [strict_euler_split hw0.le hwp]

theorem strict_euler_le_closed {P : ℝ} (hP : 100 ≤ P) :
    strictEuler P ≤ (51/50)*primeProduct P := by
  have hclosed : availableProduct 0 P true=primeProduct P := by
    rw [closed_product_ratio (by norm_num : (0:ℝ)≤0) (by linarith : (0:ℝ)≤P)]
    have hz : primeProduct 0=1 := by
      norm_num [primeProduct_eq_survivor,survivorProduct]
    rw [hz,div_one]
  have he := endpoint_relative_bound (a:=0) (by linarith : 2≤P)
  rw [hclosed] at he
  have hrec : 2/P ≤ 1/50 := (div_le_iff₀ (by linarith : 0<P)).mpr (by linarith)
  have hquot : strictEuler P/primeProduct P ≤ 51/50 := by
    unfold strictEuler
    linarith [(abs_le.mp he).2]
  exact (div_le_iff₀ (actual_primeProduct_pos P)).mp hquot

theorem reference_strict_to_closed {R J P : ℝ} (hJ : 0 ≤ J) (hP : 100 ≤ P)
    (hR : R ≤ (321/1000)*J*strictEuler P) :
    R ≤ (33/100)*J*primeProduct P := by
  have hE := strict_euler_le_closed hP
  have hm := mul_le_mul_of_nonneg_left hE (show 0 ≤ (321/1000:ℝ)*J by positivity)
  have hnonneg : 0 ≤ J*primeProduct P := mul_nonneg hJ (actual_primeProduct_pos P).le
  nlinarith

end ErdosStoppedReferenceUpper

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_StoppedReferencePrimes
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosStoppedReferenceUpper
open NumberTheoryLean FinitePathGeometry PrimeHistories ReferencePruning ReferenceAdmission
open ReferenceProductsBasics ReferenceSourcePrimeSets LogarithmicBinPartition
open StoppedCountVertex StoppedVertexHistory StoppedCountAdapters StoppedTraceSets
open ErdosPrimeInputs.PrimePrefixMass

theorem below_all_iff_last (ps : List ℕ) (hne : ps ≠ []) (hdec : ps.Pairwise (· > ·)) (q : ℕ) :
    (∀ p ∈ ps,q<p) ↔ q<ps.getLastD 0 := by
  have he : ps.getLastD 0=ps.getLast hne := by
    conv_lhs => rw [← List.dropLast_append_getLast hne]
    exact List.getLastD_concat
  rw [he]
  constructor
  · intro h
    exact h _ (List.getLast_mem hne)
  · intro h p hp
    have hdec' : (ps.dropLast++[ps.getLast hne]).Pairwise (· > ·) := by
      rwa [List.dropLast_append_getLast]
    rw [← List.dropLast_append_getLast hne] at hp
    rcases List.mem_append.mp hp with hp | hp
    · exact h.trans ((List.pairwise_append.mp hdec').2.2 p hp _ (by simp))
    · have heq := List.mem_singleton.mp hp
      simpa only [heq] using h

theorem suffix_source_primes {w top : ℝ} (hw : 0 < w) (htop : w < top)
    (ps : List ℕ) (hne : ps ≠ []) (hdec : ps.Pairwise (· > ·))
    (hsource : ∀ p ∈ ps,p ∈ sourcePrimeSet w top) :
    suffixPrimes (sourcePrimeSet w top) ps=availablePrimes w (ps.getLastD 0:ℝ) false := by
  classical
  have hlast : ps.getLastD 0 ∈ ps := by
    have he : ps.getLastD 0=ps.getLast hne := by
      conv_lhs => rw [← List.dropLast_append_getLast hne]
      exact List.getLastD_concat
    rw [he]
    exact List.getLast_mem hne
  have hlastP := (mem_sourcePrimeSet hw htop _).mp (hsource _ hlast)
  have hp0 : 0 ≤ (ps.getLastD 0:ℝ) := Nat.cast_nonneg _
  ext q
  rw [suffixPrimes,Finset.mem_filter,mem_sourcePrimeSet hw htop,
    availablePrimes_membership hp0]
  simp only [Bool.false_eq_true,ite_false, if_false]
  rw [below_all_iff_last ps hne hdec q]
  constructor
  · rintro ⟨⟨hq,hwq,_⟩,hql⟩
    exact ⟨hq,hwq,by exact_mod_cast hql⟩
  · rintro ⟨hq,hwq,hql⟩
    exact ⟨⟨hq,hwq,hql.le.trans hlastP.2.2⟩,by exact_mod_cast hql⟩

theorem after_source_primes {w top : ℝ} (hw : 0 < w) (htop : w < top)
    (v : Vertex) (hv : v.available=sourcePrimeSet w top)
    (ps : List ℕ) (hne : ps ≠ []) (hdec : ps.Pairwise (· > ·))
    (hsource : ∀ p ∈ ps,p ∈ sourcePrimeSet w top) :
    (after w v ps).available=availablePrimes w (ps.getLastD 0:ℝ) false := by
  rw [after_available,hv]
  exact suffix_source_primes hw htop ps hne hdec hsource

theorem after_original_scale (w : ℝ) (Y : ℕ) (z : Node) (P : Finset ℕ) (ps : List ℕ) :
    (after w (rootVertex z ∅ P ((Y:ℝ)*ErdosPrimeInputs.MertensStrong.primeProduct w)) ps).scale=
      ((Y:ℝ)/(ps.prod:ℝ))*ErdosPrimeInputs.MertensStrong.primeProduct w := by
  rw [after_scale_product]
  change ((Y:ℝ)*ErdosPrimeInputs.MertensStrong.primeProduct w)/(ps.prod:ℝ)=_
  ring

theorem actual_stopped_vertex_data {n : ℕ} (Y : ℕ)
    (w top Cs eta Clen B xi b₀ b₁ : ℝ) (hw : 0 < w) (htop : w < top)
    (lower width : Fin n → ℝ) (label : ℕ → Fin n) (a : ℕ → ℕ) (z : Node)
    (ps : List ℕ)
    (hp : ps ∈ stopped w (SourceStopPredicate.stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z)
      (sourcePrimeSet w top).card
      (rootVertex z ∅ (sourcePrimeSet w top) ((Y:ℝ)*ErdosPrimeInputs.MertensStrong.primeProduct w))) :
    (terminal w z ps).side=.even ∧ ps ≠ [] ∧ ps.Pairwise (· > ·) ∧
      (after w (rootVertex z ∅ (sourcePrimeSet w top)
        ((Y:ℝ)*ErdosPrimeInputs.MertensStrong.primeProduct w)) ps).available=
        availablePrimes w (ps.getLastD 0:ℝ) false := by
  classical
  have hf := ActualSourceStopBinding.actual_source_stops_first Y w Cs eta Clen B xi b₀ b₁
    ((Y:ℝ)*ErdosPrimeInputs.MertensStrong.primeProduct w) lower width label a z (sourcePrimeSet w top) hp
  have ht := StoppedTraceAdmission.trace_reference_member w
    (SourceStopPredicate.stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z)
    (sourcePrimeSet w top).card
    (rootVertex z ∅ (sourcePrimeSet w top) ((Y:ℝ)*ErdosPrimeInputs.MertensStrong.primeProduct w)) (Or.inr hp)
  have hd := mem_decreasingPrefixes.mp (Finset.mem_filter.mp ht).1
  refine ⟨hf.1,hf.2.1.1,hd.1,?_⟩
  exact after_source_primes hw htop _ rfl ps hf.2.1.1 hd.1 hd.2

end ErdosStoppedReferenceUpper

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FiniteBoxWordMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace ErdosStoppedReferenceUpper
open _root_.Filter _root_.Erdos970.Filter
open NumberTheoryLean FinitePathGeometry PrimeHistories PrimeBinMembership
open ReferenceAdmission ReferencePruning ReferenceProductsBasics ReferenceSourcePrimeSets
open SourceStopPredicate StoppedCountVertex StoppedVertexHistory StoppedCountAdapters StoppedTraceSets
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open MovingCandidateBands MovingStopBandParameters MarkedSourceSmallness
open ErdosPrimeInputs.MertensStrong

theorem actual_stopped_reference_upper {Clen xi K rho : ℝ} (hC : 0 ≤ Clen)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hK : 0 < K) (hrho : 0 < rho) :
    ∀ᶠ w : ℝ in atTop,∃ hw : 1 < w,∀ top : ℝ,∀ htop : w < top,
      ∀ B : ℝ,Real.log B ≤ 2*Real.log w → ∀ Y : ℕ,∀ Cs eta : ℝ,
      ∀ (residue : ℕ → ℕ) (z : Node) (ps : List ℕ),
      ps ∈ stopped w
        (stopCandidate Y w Cs eta Clen B xi (K*(Real.log w)^2) (rho*K*(Real.log w)^2)
          (lower w top xi) (width w top xi) (label (zero_lt_one.trans hw) htop hxi) residue z)
        (sourcePrimeSet w top).card
        (rootVertex z ∅ (sourcePrimeSet w top) ((Y:ℝ)*primeProduct w)) →
      referenceValue w (after w (rootVertex z ∅ (sourcePrimeSet w top) ((Y:ℝ)*primeProduct w)) ps)
        ≤ (33/100)*((Y:ℝ)/(ps.prod:ℝ))*strictEuler (ps.getLastD 0:ℝ) ∧
      referenceValue w (after w (rootVertex z ∅ (sourcePrimeSet w top) ((Y:ℝ)*primeProduct w)) ps)
        ≤ (33/100)*((Y:ℝ)/(ps.prod:ℝ))*primeProduct (ps.getLastD 0:ℝ) := by
  obtain ⟨B₀,w₀,hB₀,_hw₀,hR⟩ := moving_vertex_reference_upper (rho*K) (mul_pos hrho hK)
  filter_upwards [moving_candidate_node_window hC hxi hxi1 hK,
    moving_stop_band_conditions Clen xi hxi.le hK,moving_compact_gap_small (12*B₀) hK,
    eventually_ge_atTop w₀,eventually_ge_atTop (100:ℝ)] with w hwin hcond hlarge hw₀ hw100
  obtain ⟨hw,hwin⟩ := hwin
  refine ⟨hw,?_⟩
  intro top htop B hcomp Y Cs eta residue z ps hp
  let bins := label (zero_lt_one.trans hw) htop hxi
  let v := rootVertex z ∅ (sourcePrimeSet w top) ((Y:ℝ)*primeProduct w)
  have hf := ActualSourceStopBinding.actual_source_stops_first Y w Cs eta Clen B xi
    (K*(Real.log w)^2) (rho*K*(Real.log w)^2) ((Y:ℝ)*primeProduct w)
    (lower w top xi) (width w top xi) bins residue z (sourcePrimeSet w top) hp
  have hn := hwin top htop B hcomp Y Cs eta (rho*K*(Real.log w)^2) residue z ps hf.2.1
  obtain ⟨hlo,hhi,hrlo,hrhi,hcons,hclosed,_hPlower,hpower⟩ := hn
  have hhalf := hcond.2.2.2.2
  have hcut : B₀ ≤ (terminal w z ps).cutoff := by nlinarith
  have hcutscale : (terminal w z ps).cutoff ≤ (rho*K)*(Real.log w)^2 := hhi
  have hJ : 0 ≤ (Y:ℝ)/(ps.prod:ℝ) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hd := actual_stopped_vertex_data Y w top Cs eta Clen B xi
    (K*(Real.log w)^2) (rho*K*(Real.log w)^2) (zero_lt_one.trans hw) htop
    (lower w top xi) (width w top xi) bins residue z ps hp
  have hav : (after w v ps).available=sourcePrimes w (terminal w z ps).cutoff false := by
    rw [sourcePrimes,hpower]
    exact hd.2.2.2
  have hvnode : (after w v ps).node=terminal w z ps := after_node w v ps
  have href := hR w (terminal w z ps).cutoff ((Y:ℝ)/(ps.prod:ℝ)) hw₀ hcut hcutscale hJ
    (after w v ps) (by rw [hvnode]; exact hf.1) (by rw [hvnode]; linarith)
    (by rw [hvnode]; exact hrhi) (by rw [hvnode]; exact hcons) (by rw [hvnode])
    (by rw [hvnode]; exact hclosed) hav (after_original_scale w Y z (sourcePrimeSet w top) ps)
  rw [hpower] at href
  have hP100 : 100 ≤ (ps.getLastD 0:ℝ) := by
    have hsource := (mem_sourcePrimeSet (zero_lt_one.trans hw) htop _).mp
      ((SourceStopWindow.candidate_source_primes Y hw htop hxi residue z ps hf.2.1) (ps.getLastD 0)
        (by
          have he : ps.getLastD 0=ps.getLast hf.2.1.1 := by
            conv_lhs => rw [← List.dropLast_append_getLast hf.2.1.1]
            exact List.getLastD_concat
          rw [he]
          exact List.getLast_mem hf.2.1.1))
    exact hw100.trans hsource.2.1.le
  have hstrict : 0 ≤ ((Y:ℝ)/(ps.prod:ℝ))*strictEuler (ps.getLastD 0:ℝ) :=
    mul_nonneg hJ (availableProduct_pos 0 _ false).le
  exact ⟨by dsimp [v] at href <;> nlinarith,reference_strict_to_closed hJ hP100 href⟩

end ErdosStoppedReferenceUpper



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_CanonicalKeyReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.CanonicalKeyReference
open _root_.Filter PrimeHistories CanonicalStopKey CanonicalKeyWitness CanonicalKeyReplacement CanonicalKeyBands
open ActualStopGroupFiber StoppedCountVertex StoppedVertexHistory StoppedCountAdapters StoppedTraceSets
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosInversePrimeBin ErdosInverseAlignment ErdosPrimeInputs.MertensStrong
open scoped Topology


theorem moving_key_reference_jb247_oai {Clen xi Kstop rho : ℝ} (hC : 0 ≤ Clen)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hK : 0 < Kstop) (hrho : 0 < rho) :
    ∀ᶠ w : ℝ in atTop,∃ hw : 1 < w,∀ top : ℝ,∀ htop : w < top,
      ∀ B : ℝ,Real.log B ≤ 2*Real.log w → ∀ Y : ℕ,∀ Cs eta : ℝ,
      ∀ (a : ℕ → ℕ) (z : Node) (k : Key (binCount w top xi)),
      ∀ _d : Witness hw htop hxi Y Cs eta Clen B (Kstop*(Real.log w)^2)
        (rho*Kstop*(Real.log w)^2) ((Y:ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊) a z k,
      ∀ p∈primeBin (lower w top xi k.tag.bin) (width w top xi k.tag.bin),
      aligns (SourceStopPredicate.sourceClass a) k.tag.rational p →
      referenceValue w (after w (rootVertex z ∅ (sourcePrimeSet w top)
        ((Y:ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊)) (k.pre++p::k.tail))
        ≤ (33/100)*primeProduct (k.tail.getLastD 0:ℝ)*
          ((Y:ℝ)/((p:ℝ)*(k.pre.prod*k.tail.prod:ℕ))) := by
  filter_upwards [ErdosStoppedReferenceUpper.actual_stopped_reference_upper hC hxi hxi1 hK hrho]
    with w hRef
  obtain ⟨hw,hRef⟩ := hRef
  refine ⟨hw,?_⟩
  intro top htop B hcomp Y Cs eta a z k d p hp ha
  have hm := aligning_word_mem hw htop hxi d hC p hp ha
  rw [family,ErdosInverseEuler.smallEuler_eq_primeProduct] at hm
  have hh := (hRef top htop B hcomp Y Cs eta a z (k.pre++p::k.tail) hm).2
  rw [last_fixed_tail k.pre k.tail p d.tail_nonempty,
    TagBelowStopWindow.replacement_product,Nat.cast_mul] at hh
  rw [ErdosInverseEuler.smallEuler_eq_primeProduct]
  convert hh using 1 <;> first | rfl | ring
end NumberTheoryLean.CanonicalKeyReference


end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.NumberTheoryLean.CanonicalKeyReference.moving_key_reference_jb247_oai := @OAI.Erdos970.NumberTheoryLean.CanonicalKeyReference.moving_key_reference_jb247_oai
