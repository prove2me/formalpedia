-- Prove2me | solution 1 for OAI.Erdos970.ErdosVarianceUniformMoments.uniform_model_chebyshev_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:49:01.335204+00:00
-- url     : https://prove2.me/submissions/3aeda3a0-c9b2-4b37-b9d7-565696d4d990

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
import Definitions.Def_OAIQ247J007
import Theorems.Thm_Erdos970_Mertens_LogZetaInteg_log_zeta_eq_integ_aux_jb247
import Theorems.Thm_Erdos970_Mertens_sum_M_eq_summand_le_jb247
import Theorems.Thm_OAI_Erdos970_ErdosVarianceMoments_finite_joint_moment_estimate_jb247

section
-- module Solutions.OAIQ247_JB.Compat
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

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

namespace ErdosUniformMobiusRemainder

theorem totient_ratio_le_divisors (H : ℕ) (hH : 1 ≤ H) :
    (H : ℝ)/(H.totient : ℝ) ≤ (H.divisors.card : ℝ) := by
  have hphi : 0 < H.totient := Nat.totient_pos.mpr hH
  have hs : H ≤ H.divisors.card*H.totient := by
    calc
      _ = ∑ d ∈ H.divisors,d.totient := (Nat.sum_totient H).symm
      _ ≤ ∑ _d ∈ H.divisors,H.totient := Finset.sum_le_sum (fun d hd =>
        Nat.le_of_dvd hphi (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd)))
      _ = _ := by simp
  apply (div_le_iff₀ (show (0 : ℝ) < H.totient by exact_mod_cast hphi)).mpr
  exact_mod_cast hs

theorem divisor_totient_quarter : ∃ C : ℝ,0 < C ∧ ∀ H : ℕ,1 ≤ H →
    (H.divisors.card : ℝ)*(H : ℝ)/(H.totient : ℝ) ≤ C*(H : ℝ)^((1 : ℝ)/4) := by
  obtain ⟨C,hC,hb⟩ := ErdosDivisorBounds.divisor_power_subpower 2 (by norm_num : (0 : ℝ) < 1/4)
  refine ⟨C,hC,?_⟩
  intro H hH
  calc
    _ = (H.divisors.card : ℝ)*((H : ℝ)/(H.totient : ℝ)) := by ring
    _ ≤ (H.divisors.card : ℝ)*(H.divisors.card : ℝ) :=
      mul_le_mul_of_nonneg_left (totient_ratio_le_divisors H hH) (Nat.cast_nonneg _)
    _ = (H.divisors.card : ℝ)^2 := by ring
    _ ≤ _ := hb H hH

theorem divisor_totient_length_bound : ∃ C : ℝ,0 < C ∧ ∀ (H : ℕ) (Y : ℝ),
    1 ≤ H → (H : ℝ) ≤ Y →
      (H.divisors.card : ℝ)*(H : ℝ)/(Y*(H.totient : ℝ)) ≤ C/Y^((1 : ℝ)/2) := by
  obtain ⟨C,hC,hb⟩ := divisor_totient_quarter
  refine ⟨C,hC,?_⟩
  intro H Y hH hHY
  have hY1 : 1 ≤ Y := (show (1 : ℝ) ≤ H by exact_mod_cast hH).trans hHY
  have hY : 0 < Y := by linarith
  have hpow : (H : ℝ)^((1 : ℝ)/4) ≤ Y^((1 : ℝ)/2) :=
    (Real.rpow_le_rpow (Nat.cast_nonneg _) hHY (by norm_num)).trans
      (Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num))
  have hroot : 0 < Y^((1 : ℝ)/2) := Real.rpow_pos_of_pos hY _
  have hrootSq : Y^((1 : ℝ)/2)*Y^((1 : ℝ)/2)=Y := by
    rw [← Real.rpow_add hY]
    norm_num
  calc
    _ = ((H.divisors.card : ℝ)*(H : ℝ)/(H.totient : ℝ))/Y := by ring
    _ ≤ (C*(H : ℝ)^((1 : ℝ)/4))/Y := div_le_div_of_nonneg_right (hb H hH) hY.le
    _ ≤ (C*Y^((1 : ℝ)/2))/Y := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC.le) hY.le
    _ = _ := by
      apply (div_eq_div_iff hY.ne' hroot.ne').mpr
      rw [mul_assoc,hrootSq]

end ErdosUniformMobiusRemainder

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_IntervalPairCount
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosRandomVariance
attribute [local instance] Classical.propDecidable

theorem congruenceIndicator_symm (d i j : ℕ) :
    congruenceIndicator d i j = congruenceIndicator d j i := by
  have he : Nat.ModEq d i j ↔ Nat.ModEq d j i := ⟨fun h => h.symm, fun h => h.symm⟩
  simp only [congruenceIndicator, he]

theorem residue_indicator_sum (J d a : ℕ) :
    (∑ i ∈ Finset.range J, congruenceIndicator d i a) =
      (((Finset.range J).filter (fun i => Nat.ModEq d i a)).card : ℝ) := by
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    congruenceIndicator]

theorem residue_indicator_bound (J d a : ℕ) (hd : 0 < d) :
    (∑ i ∈ Finset.range J, congruenceIndicator d i a) ≤ (J : ℝ)/d+1 := by
  rw [residue_indicator_sum]
  have hc : ((Finset.range J).filter (fun i => Nat.ModEq d i a)).card ≤ J/d+1 := by
    rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card J hd a]
    split_ifs <;> omega
  have hcr : (((Finset.range J).filter (fun i => Nat.ModEq d i a)).card : ℝ) ≤
      (J/d : ℕ)+1 := by exact_mod_cast hc
  have hdiv : ((J/d : ℕ) : ℝ) ≤ (J : ℝ)/d := by
    apply (le_div_iff₀ (show (0 : ℝ) < d by exact_mod_cast hd)).mpr
    exact_mod_cast Nat.div_mul_le_self J d
  linarith

theorem interval_pair_congruence_bound (J d : ℕ) (hd : 0 < d) :
    (∑ i ∈ Finset.range J, ∑ j ∈ Finset.range J, congruenceIndicator d i j) ≤
      (J : ℝ)^2/d+J := by
  calc
    _ = ∑ i ∈ Finset.range J, ∑ j ∈ Finset.range J, congruenceIndicator d j i := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact congruenceIndicator_symm d i j
    _ ≤ ∑ _i ∈ Finset.range J, ((J : ℝ)/d+1) :=
      Finset.sum_le_sum (fun i _ => residue_indicator_bound J d i hd)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] <;> ring

end ErdosRandomVariance

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_PairDensityExpansion
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosRandomVariance
attribute [local instance] Classical.propDecidable

theorem prime_indicator_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (i j : ℕ) :
    (∏ p ∈ P, congruenceIndicator p i j) = congruenceIndicator (∏ p ∈ P,p) i j := by
  by_cases h : Nat.ModEq (∏ p ∈ P,p) i j
  · have hh := (ErdosInverseHits.modEq_prime_product_iff P hP i j).mp h
    rw [show congruenceIndicator (∏ p ∈ P,p) i j = 1 by simp [congruenceIndicator,h]]
    apply Finset.prod_eq_one
    intro p hp
    simp [congruenceIndicator,hh p hp]
  · have hn : ¬∀ p ∈ P, Nat.ModEq p i j :=
      fun hh => h ((ErdosInverseHits.modEq_prime_product_iff P hP i j).mpr hh)
    push Not at hn
    obtain ⟨p,hp,hn⟩ := hn
    rw [show congruenceIndicator (∏ p ∈ P,p) i j = 0 by simp [congruenceIndicator,h]]
    apply Finset.prod_eq_zero hp
    simp [congruenceIndicator,hn]

theorem pairCoefficient_nonneg (P S : Finset ℕ) (hP : ∀ p ∈ P,p.Prime) :
    0 ≤ pairCoefficient P S := by
  unfold pairCoefficient
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun p _ => by positivity)
  · apply Finset.prod_nonneg
    intro p hp
    have hh := hP p (Finset.mem_sdiff.mp hp).1
    apply sub_nonneg.mpr
    exact (div_le_one (show (0 : ℝ) < p by exact_mod_cast hh.pos)).mpr (by exact_mod_cast hh.two_le)

theorem pairKernel_expansion (P : Finset ℕ) (hP : ∀ p ∈ P,p.Prime) (i j : ℕ) :
    pairKernel P i j = ∑ S ∈ P.powerset,
      pairCoefficient P S*congruenceIndicator (∏ p ∈ S,p) i j := by
  rw [pairKernel, Finset.prod_add]
  apply Finset.sum_congr rfl
  intro S hS
  have hpS : ∀ p ∈ S,p.Prime := fun p hp => hP p ((Finset.mem_powerset.mp hS) hp)
  rw [Finset.prod_mul_distrib, prime_indicator_product S hpS]
  unfold pairCoefficient
  ring

theorem pairCoefficient_sum (P : Finset ℕ) :
    (∑ S ∈ P.powerset, pairCoefficient P S) = sieveProduct P := by
  unfold pairCoefficient sieveProduct
  rw [← Finset.prod_add]
  apply Finset.prod_congr rfl
  intro p _
  ring

theorem pairCoefficient_div_product (P S : Finset ℕ) :
    pairCoefficient P S/((∏ p ∈ S,p : ℕ) : ℝ) =
      (∏ p ∈ S, ((1 : ℝ)/p)^2)*(∏ p ∈ P \ S, (1-2/(p : ℝ))) := by
  unfold pairCoefficient
  rw [Nat.cast_prod]
  calc
    _ = ((∏ p ∈ S,(1 : ℝ)/p)/(∏ p ∈ S,(p : ℝ)))*(∏ p ∈ P \ S,(1-2/(p : ℝ))) := by ring
    _ = _ := by
      rw [← Finset.prod_div_distrib]
      congr 1
      apply Finset.prod_congr rfl
      intro p _
      ring

theorem pairCoefficient_normalized_sum (P : Finset ℕ) :
    (∑ S ∈ P.powerset, pairCoefficient P S/((∏ p ∈ S,p : ℕ) : ℝ)) = (sieveProduct P)^2 := by
  simp only [pairCoefficient_div_product]
  rw [← Finset.prod_add]
  unfold sieveProduct
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p _
  ring

theorem pairKernel_diagonal (P : Finset ℕ) (i : ℕ) : pairKernel P i i = sieveProduct P := by
  unfold pairKernel sieveProduct
  apply Finset.prod_congr rfl
  intro p _
  simp only [congruenceIndicator, Nat.ModEq.refl, ite_true, if_true, mul_one]
  ring

theorem pairKernel_interval_sum (P : Finset ℕ) (hP : ∀ p ∈ P,p.Prime) (J : ℕ) :
    (∑ i ∈ Finset.range J, ∑ j ∈ Finset.range J, pairKernel P i j) ≤
      ((J : ℝ)*sieveProduct P)^2+(J : ℝ)*sieveProduct P := by
  have hexpand :
      (∑ i ∈ Finset.range J, ∑ j ∈ Finset.range J, pairKernel P i j) =
      ∑ S ∈ P.powerset, pairCoefficient P S*
        (∑ i ∈ Finset.range J, ∑ j ∈ Finset.range J, congruenceIndicator (∏ p ∈ S,p) i j) := by
    simp only [pairKernel_expansion P hP]
    have hs (i : ℕ) :
        (∑ j ∈ Finset.range J, ∑ S ∈ P.powerset,
          pairCoefficient P S*congruenceIndicator (∏ p ∈ S,p) i j) =
        ∑ S ∈ P.powerset, ∑ j ∈ Finset.range J,
          pairCoefficient P S*congruenceIndicator (∏ p ∈ S,p) i j := Finset.sum_comm
    simp only [hs]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  rw [hexpand]
  calc
    _ ≤ ∑ S ∈ P.powerset, pairCoefficient P S*((J : ℝ)^2/((∏ p ∈ S,p : ℕ) : ℝ)+J) := by
      apply Finset.sum_le_sum
      intro S hS
      have hprod : 0 < ∏ p ∈ S,p := Finset.prod_pos
        (fun p hp => (hP p ((Finset.mem_powerset.mp hS) hp)).pos)
      exact mul_le_mul_of_nonneg_left (interval_pair_congruence_bound J _ hprod) (pairCoefficient_nonneg P S hP)
    _ = (J : ℝ)^2*(∑ S ∈ P.powerset,pairCoefficient P S/((∏ p ∈ S,p : ℕ) : ℝ))+
        (J : ℝ)*(∑ S ∈ P.powerset,pairCoefficient P S) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro S _
      ring
    _ = _ := by rw [pairCoefficient_normalized_sum,pairCoefficient_sum]; ring

end ErdosRandomVariance

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_PositionDensities
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceMoments
attribute [local instance] Classical.decEq

theorem affine_forbidden_injective (p : ℕ) (u : (ZMod p)ˣ) (c : ZMod p) :
    Function.Injective (fun x : ZMod p => c-(u : ZMod p)*x) := by
  intro x y h
  have hm : (u : ZMod p)*x = (u : ZMod p)*y := by linear_combination -h
  have hh := congrArg (fun z : ZMod p => (↑(u⁻¹) : ZMod p)*z) hm
  simpa only [← mul_assoc,u.inv_mul,one_mul] using hh

theorem forbiddenClasses_card (S : Finset ℕ) (p : ℕ) (u : (ZMod p)ˣ) (c : ZMod p) :
    (forbiddenClasses S p u c).card = (positionResidues S p).card := by
  have he : forbiddenClasses S p u c = (positionResidues S p).image (fun x => c-(u : ZMod p)*x) := by
    simp only [forbiddenClasses,positionResidues,Finset.image_image,Function.comp_def]
  rw [he,Finset.card_image_of_injective _ (affine_forbidden_injective p u c)]

theorem mem_forbiddenClasses (S : Finset ℕ) (p : ℕ) (u : (ZMod p)ˣ) (c x : ZMod p) :
    x ∈ forbiddenClasses S p u c ↔ ∃ j ∈ S,x+(u : ZMod p)*(j : ZMod p) = c := by
  simp only [forbiddenClasses,Finset.mem_image]
  constructor
  · rintro ⟨j,hj,he⟩
    exact ⟨j,hj,by linear_combination -he⟩
  · rintro ⟨j,hj,he⟩
    exact ⟨j,hj,by linear_combination -he⟩

theorem positionResidues_le_positions (S : Finset ℕ) (p : ℕ) : (positionResidues S p).card ≤ S.card :=
  Finset.card_image_le

theorem positionResidues_le_modulus (S : Finset ℕ) (p : ℕ) [NeZero p] : (positionResidues S p).card ≤ p := by
  have hh := Finset.card_le_univ (positionResidues S p)
  simpa only [ZMod.card] using hh

theorem forbiddenClasses_full_of_card (S : Finset ℕ) (p : ℕ) [NeZero p]
    (u : (ZMod p)ˣ) (c : ZMod p) (hfull : (positionResidues S p).card = p) :
    forbiddenClasses S p u c = Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  simp only [Finset.card_univ,ZMod.card,forbiddenClasses_card,hfull]
  exact le_rfl

end ErdosVarianceMoments

end

section

namespace ErdosVarianceMoments
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem positionDensity_bounds (S : Finset ℕ) (p : ℕ) [NeZero p] :
    0 ≤ positionDensity S p ∧ positionDensity S p ≤ 1 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  refine ⟨by dsimp [positionDensity] <;> positivity,?_⟩
  apply (div_le_one hp).mpr
  exact_mod_cast positionResidues_le_modulus S p

theorem positionDensity_le_two (S : Finset ℕ) (hS : S.card ≤ 2) (p : ℕ) [NeZero p] :
    positionDensity S p ≤ 2/(p : ℝ) := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (positionResidues_le_positions S p).trans hS

theorem positionResidues_singleton (j p : ℕ) : (positionResidues {j} p).card = 1 := by
  simp only [positionResidues,Finset.image_singleton,Finset.card_singleton]

theorem positionResidues_pair (i j p : ℕ) :
    (positionResidues {i,j} p).card = if Nat.ModEq p i j then 1 else 2 := by
  by_cases h : Nat.ModEq p i j
  · have he := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
    simp only [positionResidues,Finset.image_insert,Finset.image_singleton,he,Finset.insert_eq_of_mem
      (Finset.mem_singleton_self _),Finset.card_singleton,ite_eq_left h]
  · have he : (i : ZMod p) ≠ (j : ZMod p) := by
      intro he
      exact h ((ZMod.natCast_eq_natCast_iff _ _ _).mp he)
    have hnot : (i : ZMod p) ∉ ({(j : ZMod p)} : Finset (ZMod p)) := by
      simpa only [Finset.mem_singleton] using he
    simp only [positionResidues,Finset.image_insert,Finset.image_singleton,
      Finset.card_insert_of_notMem hnot,Finset.card_singleton,ite_eq_right h]

theorem jointDensity_singleton (P : Finset ℕ) (j : ℕ) :
    jointDensity P {j} = ErdosRandomVariance.sieveProduct P := by
  simp only [jointDensity,positionDensity,positionResidues_singleton,Nat.cast_one,ErdosRandomVariance.sieveProduct]

theorem jointDensity_pair (P : Finset ℕ) (i j : ℕ) :
    jointDensity P {i,j} = ErdosRandomVariance.pairKernel P i j := by
  apply Finset.prod_congr rfl
  intro p _hp
  by_cases h : Nat.ModEq p i j
  · simp only [positionDensity,positionResidues_pair,ite_eq_left h,Nat.cast_one,
      ErdosRandomVariance.congruenceIndicator]
    ring
  · simp only [positionDensity,positionResidues_pair,ite_eq_right h,Nat.cast_ofNat,
      ErdosRandomVariance.congruenceIndicator]
    ring

end ErdosVarianceMoments

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_RealCoprimeResidueCount
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosInverseCRT
attribute [local instance] Classical.decEq

theorem mem_crtResidues {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (E : ∀ i,Finset (ZMod (m i))) (r : ZMod (∏ i,m i)) :
    r ∈ crtResidues m hcop E ↔ ∀ i,(ZMod.prodEquivPi m hcop r) i ∈ E i := by
  constructor
  · intro hr
    obtain ⟨f,hf,hfr⟩ := Finset.mem_map.mp hr
    have he : ZMod.prodEquivPi m hcop r = f := by
      rw [← hfr]
      exact (ZMod.prodEquivPi m hcop).apply_symm_apply f
    rw [he]
    exact Fintype.mem_piFinset.mp hf
  · intro hr
    exact Finset.mem_map.mpr ⟨ZMod.prodEquivPi m hcop r,Fintype.mem_piFinset.mpr hr,
      (ZMod.prodEquivPi m hcop).symm_apply_apply r⟩

theorem crtResidues_card {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j))) (E : ∀ i,Finset (ZMod (m i))) :
    (crtResidues m hcop E).card = ∏ i,(E i).card := by
  rw [crtResidues,Finset.card_map,Fintype.card_piFinset]

end ErdosInverseCRT



namespace ErdosVarianceMoments
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem crt_coordinate_val {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    [NeZero (∏ i,m i)] (r : ZMod (∏ i,m i)) (i : ι) :
    (ZMod.prodEquivPi m hcop r) i = (r.val : ZMod (m i)) := by
  calc
    (ZMod.prodEquivPi m hcop r) i =
        (ZMod.prodEquivPi m hcop (r.val : ZMod (∏ j,m j))) i := by
      rw [ZMod.natCast_zmod_val]
    _ = (r.val : ZMod (m i)) := by
      rw [ZMod.prodEquivPi_apply]
      exact map_natCast (ZMod.castHom (Finset.dvd_prod_of_mem m (Finset.mem_univ i)) (ZMod (m i))) r.val

theorem literal_residue_choices_card {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    [NeZero (∏ i,m i)] (E : ∀ i,Finset (ZMod (m i))) :
    (Finset.univ.filter (fun r : ZMod (∏ i,m i) => ∀ i,(r.val : ZMod (m i)) ∈ E i)).card =
      ∏ i,(E i).card := by
  have he : Finset.univ.filter (fun r : ZMod (∏ i,m i) => ∀ i,(r.val : ZMod (m i)) ∈ E i) =
      ErdosInverseCRT.crtResidues m hcop E := by
    ext r
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,ErdosInverseCRT.mem_crtResidues,
      crt_coordinate_val]
  rw [he,ErdosInverseCRT.crtResidues_card]

theorem canonical_filter_card (N : ℕ) [NeZero N] (f : ℕ → Prop) [DecidablePred f] :
    (Finset.univ.filter (fun r : ZMod N => f r.val)).card =
      ((Finset.range N).filter f).card := by
  apply Finset.card_bij (fun r _ => r.val)
  · intro r hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr r.val_lt,(Finset.mem_filter.mp hr).2⟩
  · intro r _hr s _hs he
    exact ZMod.val_injective N he
  · intro n hn
    have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
    refine ⟨(n : ZMod N),?_,?_⟩
    · simp only [Finset.mem_filter,Finset.mem_univ,true_and,ZMod.val_natCast,Nat.mod_eq_of_lt hlt]
      exact (Finset.mem_filter.mp hn).2
    · simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hlt]

theorem mem_allowedClasses (S : Finset ℕ) (p : ℕ) [NeZero p]
    (u : (ZMod p)ˣ) (c x : ZMod p) :
    x ∈ allowedClasses S p u c ↔ ∀ j ∈ S,x+(u : ZMod p)*(j : ZMod p) ≠ c := by
  simp only [allowedClasses,Finset.mem_sdiff,Finset.mem_univ,true_and,mem_forbiddenClasses,
    not_exists,not_and]

theorem allowedClasses_card (S : Finset ℕ) (p : ℕ) [NeZero p]
    (u : (ZMod p)ˣ) (c : ZMod p) :
    (allowedClasses S p u c).card = p-(positionResidues S p).card := by
  rw [allowedClasses,Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,ZMod.card,
    forbiddenClasses_card]

end ErdosVarianceMoments



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

namespace ErdosVarianceMoments
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem prime_residue_choices_card (P : Finset ℕ) (hP : ∀ p ∈ P,p.Prime)
    [NeZero (∏ p ∈ P,p)] (E : ∀ p : ℕ,Finset (ZMod p)) :
    (Finset.univ.filter (fun r : ZMod (∏ p ∈ P,p) => ∀ p ∈ P,(r.val : ZMod p) ∈ E p)).card =
      ∏ p ∈ P,(E p).card := by
  have hcop : Pairwise (fun i j : P => Nat.Coprime i.val j.val) := by
    intro i j hij
    exact (Nat.coprime_primes (hP i i.property) (hP j j.property)).mpr
      (fun he => hij (Subtype.ext he))
  have he : (∏ i : P,(i : ℕ)) = ∏ p ∈ P,p := Finset.prod_coe_sort P (fun p => p)
  let : NeZero (∏ i : P,(i : ℕ)) := ⟨by rw [he];exact NeZero.ne _⟩
  have hc := literal_residue_choices_card (fun i : P => (i : ℕ)) hcop (fun i => E i)
  have hn := (canonical_filter_card (∏ i : P,(i : ℕ))
    (fun n => ∀ i : P,(n : ZMod i.val) ∈ E i.val)).symm.trans hc
  calc
    _ = ((Finset.range (∏ p ∈ P,p)).filter (fun n => ∀ p ∈ P,(n : ZMod p) ∈ E p)).card :=
      canonical_filter_card _ _
    _ = _ := by
      simpa only [he,Finset.prod_coe_sort P (fun p => (E p).card),Subtype.forall] using hn

theorem prime_unit_avoidance_card (P S : Finset ℕ) (hP : ∀ p ∈ P,p.Prime)
    [NeZero (∏ p ∈ P,p)] (u : ∀ p : ℕ,(ZMod p)ˣ) (c : ∀ p : ℕ,ZMod p) :
    (Finset.univ.filter (fun r : ZMod (∏ p ∈ P,p) =>
      ∀ p ∈ P,∀ j ∈ S,(r.val : ZMod p)+(u p : ZMod p)*(j : ZMod p) ≠ c p)).card =
      ∏ p ∈ P,(p-(positionResidues S p).card) := by
  let E (p : ℕ) : Finset (ZMod p) :=
    if hp : p = 0 then ∅ else @allowedClasses S p ⟨hp⟩ (u p) (c p)
  have hmem (p : ℕ) (hp : p ∈ P) (x : ZMod p) :
      x ∈ E p ↔ ∀ j ∈ S,x+(u p : ZMod p)*(j : ZMod p) ≠ c p := by
    have hn := (hP p hp).ne_zero
    let : NeZero p := ⟨hn⟩
    simp only [E,dite_eq_right hn,mem_allowedClasses]
  have hcard (p : ℕ) (hp : p ∈ P) : (E p).card = p-(positionResidues S p).card := by
    have hn := (hP p hp).ne_zero
    let : NeZero p := ⟨hn⟩
    simp only [E,dite_eq_right hn,allowedClasses_card]
  have hf : Finset.univ.filter (fun r : ZMod (∏ p ∈ P,p) =>
      ∀ p ∈ P,∀ j ∈ S,(r.val : ZMod p)+(u p : ZMod p)*(j : ZMod p) ≠ c p) =
      Finset.univ.filter (fun r : ZMod (∏ p ∈ P,p) => ∀ p ∈ P,(r.val : ZMod p) ∈ E p) := by
    apply Finset.filter_congr
    intro r _hr
    exact forall_congr' (fun p => forall_congr' (fun hp => (hmem p hp _).symm))
  rw [hf,prime_residue_choices_card P hP E]
  exact Finset.prod_congr rfl hcard

theorem product_allowed_eq_density (P S : Finset ℕ) (hP : ∀ p ∈ P,p.Prime) :
    ((∏ p ∈ P,(p-(positionResidues S p).card) : ℕ) : ℝ) =
      ((∏ p ∈ P,p : ℕ) : ℝ)*jointDensity P S := by
  rw [Nat.cast_prod,Nat.cast_prod,jointDensity,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  let : NeZero p := ⟨(hP p hp).ne_zero⟩
  have hle := positionResidues_le_modulus S p
  rw [Nat.cast_sub hle,positionDensity]
  have hn : (p : ℝ) ≠ 0 := by exact_mod_cast (hP p hp).ne_zero
  field_simp

end ErdosVarianceMoments

end

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_SmallModelMeasure
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem atomWeight_pos (R xi w : ℝ) (H : ℕ) (C0 : ℤ) (hR : 0 < R) (hxi : 0 ≤ xi) (hH : 0 < H) :
    0 < atomWeight R xi w H C0 := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hphi : (0 : ℝ) < H.totient := by exact_mod_cast Nat.totient_pos.mpr hH
  have hT0 : (0 : ℝ) < divisorModulus w H := by exact_mod_cast divisorModulus_pos w H
  have hT1 : (0 : ℝ) < (coprimeModulus w H).totient := by
    exact_mod_cast Nat.totient_pos.mpr (coprimeModulus_pos w H)
  have hY : 0 < modelLength R xi (H : ℝ) (C0 : ℝ) := by
    dsimp [modelLength,interceptScale]
    positivity
  unfold atomWeight
  positivity

theorem modelMass_card (R xi w : ℝ) (H : ℕ) (C0 : ℤ) (E : ModelPoint w H → Prop) :
    modelMass R xi w H C0 E =
      (((modelUniverse R xi w H C0).filter E).card : ℝ)*atomWeight R xi w H C0 := by
  simp only [modelMass,Finset.sum_const,nsmul_eq_mul]

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

theorem divisorPhaseUnit_coe (H : ℕ) (C0 m : ℤ) (hC0 : Int.gcd C0 (H : ℤ) = 1)
    (hm : m.natAbs.Coprime H) (t : ℕ) (htH : t ∣ H) :
    (divisorPhaseUnit H C0 m hC0 hm t htH : ZMod t) = divisorPhase C0 m t := rfl

end ErdosVarianceMoments

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ActualModelTargets
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
attribute [local instance] Classical.propDecidable

theorem modelIndicator_binary (w : ℝ) (H : ℕ) (C0 : ℤ) (qA : ℕ)
    (beta delta : ∀ t : ℕ,ZMod t) (j : ℕ) (v : ModelPoint w H) :
    modelIndicator w H C0 qA beta delta j v = 0 ∨ modelIndicator w H C0 qA beta delta j v = 1 := by
  unfold modelIndicator
  split <;> simp

theorem jointCondition_split (w : ℝ) (H : ℕ) (C0 : ℤ) (qA : ℕ)
    (beta delta : ∀ t : ℕ,ZMod t) (S : Finset ℕ) (v : ModelPoint w H) :
    jointCondition w H C0 qA beta delta S v ↔
      (∀ t ∈ divisorPrimes w H,∀ j ∈ S,patternKValue w H v.2 t+divisorPhase C0 v.1 t*(j : ZMod t) ≠ beta t) ∧
      (∀ t ∈ coprimePrimes w H,∀ j ∈ S,patternPValue w H v.2 t*(qA : ZMod t)*
        ((v.1 : ZMod t)+(H : ZMod t)*(j : ZMod t)) ≠ delta t) := by
  constructor
  · intro h
    exact ⟨fun t ht j hj => (h j hj).1 t ht,fun t ht j hj => (h j hj).2 t ht⟩
  · rintro ⟨h0,h1⟩ j hj
    exact ⟨fun t ht => h0 t ht j hj,fun t ht => h1 t ht j hj⟩

theorem jointIndicator_singleton (w : ℝ) (H : ℕ) (C0 : ℤ) (qA : ℕ)
    (beta delta : ∀ t : ℕ,ZMod t) (j : ℕ) (v : ModelPoint w H) :
    jointIndicator w H C0 qA beta delta {j} v = modelIndicator w H C0 qA beta delta j v := by
  simp [jointIndicator,jointCondition,modelIndicator]

theorem jointIndicator_pair (w : ℝ) (H : ℕ) (C0 : ℤ) (qA : ℕ)
    (beta delta : ∀ t : ℕ,ZMod t) (i j : ℕ) (v : ModelPoint w H) :
    jointIndicator w H C0 qA beta delta {i,j} v =
      modelIndicator w H C0 qA beta delta i v*modelIndicator w H C0 qA beta delta j v := by
  by_cases hi : modelSurvives w H C0 qA beta delta i v <;>
    by_cases hj : modelSurvives w H C0 qA beta delta j v <;>
    simp [jointIndicator,jointCondition,modelIndicator,hi,hj]

end ErdosVarianceMoments

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_CoprimePositionSieve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosVarianceMoments
open NumberTheoryLean ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem jointCondition_coordinates (w : ℝ) (H : ℕ) (C0 : ℤ) (qA : ℕ)
    (beta delta : ∀ t : ℕ,ZMod t) (S : Finset ℕ) (m : ℤ) (s : Pattern w H) :
    jointCondition w H C0 qA beta delta S (m,s) ↔
      divisorJoint w H C0 beta S m s.2 ∧ coprimeJoint w H qA delta S m s.1 :=
  jointCondition_split w H C0 qA beta delta S (m,s)

theorem divisorJoint_card (w : ℝ) (H : ℕ) (C0 : ℤ) (beta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (m : ℤ) (hC0 : Int.gcd C0 (H : ℤ) = 1) (hm : m.natAbs.Coprime H) :
    (Finset.univ.filter (divisorJoint w H C0 beta S m)).card =
      ∏ t ∈ divisorPrimes w H,(t-(positionResidues S t).card) := by
  let u (t : ℕ) : (ZMod t)ˣ :=
    if ht : t ∣ H then divisorPhaseUnit H C0 m hC0 hm t ht else 1
  have hunit (t : ℕ) (ht : t ∈ divisorPrimes w H) : (u t : ZMod t) = divisorPhase C0 m t := by
    simp only [u,dite_eq_left (Finset.mem_filter.mp ht).2,divisorPhaseUnit_coe]
  have hP (t : ℕ) (ht : t ∈ divisorPrimes w H) : t.Prime :=
    (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1
  let : NeZero (∏ t ∈ divisorPrimes w H,t) := ⟨(divisorModulus_pos w H).ne'⟩
  have hh := prime_unit_avoidance_card (divisorPrimes w H) S hP u beta
  have he : Finset.univ.filter (divisorJoint w H C0 beta S m) =
      Finset.univ.filter (fun k : ZMod (divisorModulus w H) =>
        ∀ t ∈ divisorPrimes w H,∀ j ∈ S,(k.val : ZMod t)+(u t : ZMod t)*(j : ZMod t) ≠ beta t) := by
    apply Finset.filter_congr
    intro k _hk
    unfold divisorJoint
    exact forall_congr' (fun t => forall_congr' (fun ht => by rw [hunit t ht]))
  rw [he]
  exact hh

theorem conditional_pattern_card (w : ℝ) (H : ℕ) (C0 : ℤ) (qA : ℕ)
    (beta delta : ∀ t : ℕ,ZMod t) (S : Finset ℕ) (m : ℤ)
    (hC0 : Int.gcd C0 (H : ℤ) = 1) (hm : m.natAbs.Coprime H) :
    (Finset.univ.filter (fun s : Pattern w H => jointCondition w H C0 qA beta delta S (m,s))).card =
      (Finset.univ.filter (coprimeJoint w H qA delta S m)).card*
        ∏ t ∈ divisorPrimes w H,(t-(positionResidues S t).card) := by
  have he : Finset.univ.filter (fun s : Pattern w H => jointCondition w H C0 qA beta delta S (m,s)) =
      (Finset.univ.filter (coprimeJoint w H qA delta S m)).product
        (Finset.univ.filter (divisorJoint w H C0 beta S m)) := by
    ext s
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.product_eq_sprod,Finset.mem_product,
      jointCondition_coordinates,and_comm]
  rw [he,Finset.product_eq_sprod,Finset.card_product,divisorJoint_card w H C0 beta S m hC0 hm]

end ErdosVarianceMoments



namespace ErdosVarianceMoments
open NumberTheoryLean ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem patternPrimeUnit_coe (w : ℝ) (H : ℕ) (p : (ZMod (coprimeModulus w H))ˣ)
    (t : ℕ) (ht : t ∣ coprimeModulus w H) :
    (patternPrimeUnit w H p t ht : ZMod t) = (p.val.val : ZMod t) := by
  change ZMod.castHom ht (ZMod t) p.val = _
  calc
    ZMod.castHom ht (ZMod t) p.val =
      ZMod.castHom ht (ZMod t) (p.val.val : ZMod (coprimeModulus w H)) := by rw [ZMod.natCast_zmod_val]
    _ = _ := map_natCast (ZMod.castHom ht (ZMod t)) p.val.val

theorem unit_mul_eq_iff {M : Type*} [Monoid M] (u : Mˣ) (x c : M) :
    (u : M)*x = c ↔ x = (u⁻¹ : Mˣ)*c := by
  constructor
  · intro h
    have hh := congrArg (fun y : M => (u⁻¹ : Mˣ)*y) h
    simpa only [← mul_assoc,Units.inv_mul,one_mul] using hh
  · intro h
    rw [h,← mul_assoc,Units.mul_inv,one_mul]

theorem mem_coprimeForbidden (w : ℝ) (H qA : ℕ) (delta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (p : (ZMod (coprimeModulus w H))ˣ) (t : ℕ)
    (ht : t ∈ coprimePrimes w H) (hqA : qA.Coprime t) (x : ZMod t) :
    x ∈ coprimeForbidden w H qA delta S p t ht hqA ↔
      ∃ j ∈ S,(p.val.val : ZMod t)*(qA : ZMod t)*(x+(H : ZMod t)*(j : ZMod t)) = delta t := by
  rw [coprimeForbidden,mem_forbiddenClasses]
  apply exists_congr
  intro j
  apply and_congr_right
  intro _hj
  have hh := unit_mul_eq_iff (coprimeCoefficientUnit w H qA p t ht hqA)
    (x+(H : ZMod t)*(j : ZMod t)) (delta t)
  have hc : (coprimeCoefficientUnit w H qA p t ht hqA : ZMod t) =
      (p.val.val : ZMod t)*(qA : ZMod t) := by
    simpa only [coprimeCoefficientUnit,Units.val_mul,ZMod.coe_unitOfCoprime] using
      congrArg (fun v : ZMod t => v*(qA : ZMod t))
        (patternPrimeUnit_coe w H p t (Finset.dvd_prod_of_mem _ ht))
  rw [hc] at hh
  simpa only [coprimeShiftUnit,ZMod.coe_unitOfCoprime] using hh.symm

end ErdosVarianceMoments



namespace ErdosVarianceMoments
open NumberTheoryLean ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem coprimeJoint_avoidance (w : ℝ) (H qA : ℕ) (delta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (p : (ZMod (coprimeModulus w H))ˣ)
    (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t) (m : ℤ) :
    coprimeJoint w H qA delta S m p ↔
      ∀ t ∈ coprimePrimes w H,(m : ZMod t) ∉ coprimeForbiddenFamily w H qA delta S p hqA t := by
  unfold coprimeJoint
  apply forall_congr'
  intro t
  apply forall_congr'
  intro ht
  simp only [coprimeForbiddenFamily,dite_eq_left ht,mem_coprimeForbidden,not_exists,not_and]

theorem nonzero_positionDensity_two (P S : Finset ℕ) (hS : S.card ≤ 2)
    (hne : jointDensity P S ≠ 0) (h2 : 2 ∈ P) : positionDensity S 2 ≤ 1/2 := by
  have hn : 1-positionDensity S 2 ≠ 0 := (Finset.prod_ne_zero_iff.mp hne) 2 h2
  have hcard := positionResidues_le_positions S 2
  have hnot : (positionResidues S 2).card ≠ 2 := by
    intro he
    apply hn
    norm_num [positionDensity,he]
  have hle : (positionResidues S 2).card ≤ 1 := by omega
  unfold positionDensity
  exact div_le_div_of_nonneg_right (by exact_mod_cast hle) (by norm_num)

end ErdosVarianceMoments


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_JointModelCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceMoments
open NumberTheoryLean ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem zero_jointDensity_full_class (P S : Finset ℕ) (hP : ∀ t ∈ P,t.Prime)
    (hz : jointDensity P S = 0) : ∃ t ∈ P,(positionResidues S t).card = t := by
  obtain ⟨t,ht,hzero⟩ := Finset.prod_eq_zero_iff.mp hz
  have htpos : (0 : ℝ) < t := by exact_mod_cast (hP t ht).pos
  have he : ((positionResidues S t).card : ℝ)/(t : ℝ) = 1 := by
    change 1-((positionResidues S t).card : ℝ)/(t : ℝ) = 0 at hzero
    linarith
  refine ⟨t,ht,?_⟩
  exact_mod_cast (div_eq_one_iff_eq htpos.ne').mp he

theorem zero_coprimeJoint (w : ℝ) (H qA : ℕ) (delta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (p : (ZMod (coprimeModulus w H))ˣ)
    (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t)
    (hz : jointDensity (coprimePrimes w H) S = 0) (m : ℤ) :
    ¬coprimeJoint w H qA delta S m p := by
  obtain ⟨t,ht,hfull⟩ := zero_jointDensity_full_class (coprimePrimes w H) S
    (fun t ht => (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1) hz
  let : NeZero t := ⟨(LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1.ne_zero⟩
  have he : coprimeForbidden w H qA delta S p t ht (hqA t ht) = Finset.univ :=
    forbiddenClasses_full_of_card _ _ _ _ hfull
  intro h
  have hav := (coprimeJoint_avoidance w H qA delta S p hqA m).mp h t ht
  apply hav
  simp only [coprimeForbiddenFamily,dite_eq_left ht,he,Finset.mem_univ]

theorem zero_coprimePositionSurvivors (w : ℝ) (H qA : ℕ) (delta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (p : (ZMod (coprimeModulus w H))ˣ)
    (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t)
    (hz : jointDensity (coprimePrimes w H) S = 0) (b c : ℝ) :
    coprimePositionSurvivors w H qA delta S p b c = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro m hm
  exact zero_coprimeJoint w H qA delta S p hqA hz m (Finset.mem_filter.mp hm).2

end ErdosVarianceMoments

end

section

namespace ErdosVarianceMoments
open ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem unitInterval_eq_modelUnitIntegers (R xi : ℝ) (H : ℕ) (C0 : ℤ) :
    unitIntervalIntegers H (modelLeft R xi (C0 : ℝ)) (modelRight R xi (H : ℝ) (C0 : ℝ)) =
      modelUnitIntegers R xi H C0 := by
  ext m
  simp only [unitIntervalIntegers,modelUnitIntegers,modelIntegers,Finset.mem_filter,Nat.coprime_comm]

theorem joint_model_card (R xi w : ℝ) (H qA : ℕ) (C0 : ℤ)
    (beta delta : ∀ t : ℕ,ZMod t) (S : Finset ℕ) (hC0 : Int.gcd C0 (H : ℤ) = 1) :
    ((modelUniverse R xi w H C0).filter (jointCondition w H C0 qA beta delta S)).card =
      (∑ p : (ZMod (coprimeModulus w H))ˣ,
        (coprimePositionSurvivors w H qA delta S p (modelLeft R xi (C0 : ℝ))
          (modelRight R xi (H : ℝ) (C0 : ℝ))).card)*
        ∏ t ∈ divisorPrimes w H,(t-(positionResidues S t).card) := by
  have hsplit : ((modelUniverse R xi w H C0).filter (jointCondition w H C0 qA beta delta S)).card =
      ∑ m ∈ modelUnitIntegers R xi H C0,
        (Finset.univ.filter (fun s : Pattern w H => jointCondition w H C0 qA beta delta S (m,s))).card := by
    simp only [modelUniverse,Finset.product_eq_sprod,Finset.card_filter,Finset.sum_product]
  rw [hsplit]
  have hc : (∑ m ∈ modelUnitIntegers R xi H C0,
        (Finset.univ.filter (fun s : Pattern w H => jointCondition w H C0 qA beta delta S (m,s))).card) =
      (∑ m ∈ modelUnitIntegers R xi H C0,
        (Finset.univ.filter (coprimeJoint w H qA delta S m)).card)*
        ∏ t ∈ divisorPrimes w H,(t-(positionResidues S t).card) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    exact conditional_pattern_card w H C0 qA beta delta S m hC0 (Finset.mem_filter.mp hm).2
  rw [hc]
  congr 1
  simp only [coprimePositionSurvivors,unitInterval_eq_modelUnitIntegers,Finset.card_filter]
  exact Finset.sum_comm

theorem joint_model_mass (R xi w : ℝ) (H qA : ℕ) (C0 : ℤ)
    (beta delta : ∀ t : ℕ,ZMod t) (S : Finset ℕ) (hC0 : Int.gcd C0 (H : ℤ) = 1) :
    modelMass R xi w H C0 (jointCondition w H C0 qA beta delta S) =
      atomWeight R xi w H C0*((divisorModulus w H : ℝ)*jointDensity (divisorPrimes w H) S)*
        ∑ p : (ZMod (coprimeModulus w H))ˣ,
          ((coprimePositionSurvivors w H qA delta S p (modelLeft R xi (C0 : ℝ))
            (modelRight R xi (H : ℝ) (C0 : ℝ))).card : ℝ) := by
  rw [modelMass_card,joint_model_card R xi w H qA C0 beta delta S hC0,Nat.cast_mul,Nat.cast_sum,
    product_allowed_eq_density (divisorPrimes w H) S (fun t ht =>
      (NumberTheoryLean.LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1)]
  change (_*((divisorModulus w H : ℝ)*jointDensity (divisorPrimes w H) S))*_ = _
  ring

end ErdosVarianceMoments

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_OddEulerCorrection
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosOddEulerCorrection

theorem correction_nonneg (k : ℕ) : 0 ≤ correction k := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hp : (0 : ℝ) < ((k : ℝ)+2)^2 := by positivity
  apply sub_nonneg.mpr
  apply (div_le_one hp).mpr
  nlinarith

theorem correction_le_one (k : ℕ) : correction k ≤ 1 := by
  dsimp [correction]
  have : (0 : ℝ) ≤ 1/((k : ℝ)+2)^2 := by positivity
  linarith

theorem correction_range (N : ℕ) :
    (∏ k ∈ Finset.range N, correction k) = ((N : ℝ)+2)/(2*((N : ℝ)+1)) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.prod_range_succ,ih]
    dsimp [correction]
    push_cast
    have h1 : (N : ℝ)+1 ≠ 0 := by positivity
    have h2 : (N : ℝ)+2 ≠ 0 := by positivity
    field_simp
    ring

theorem correction_finite_lower (S : Finset ℕ) :
    (1 : ℝ)/2 ≤ ∏ k ∈ S, correction k := by
  let N := S.sup id+1
  have hS : S ⊆ Finset.range N := by
    intro k hk
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hk)
  have hprod := Finset.prod_le_prod_of_subset_of_le_one hS
    (fun k _ => correction_nonneg k) (fun k _ _ => correction_le_one k)
  have hhalf : (1 : ℝ)/2 ≤ ∏ k ∈ Finset.range N, correction k := by
    rw [correction_range]
    apply (le_div_iff₀ (show (0 : ℝ) < 2*((N : ℝ)+1) by positivity)).mpr
    linarith
  exact hhalf.trans hprod

theorem odd_correction_product_lower (P : Finset ℕ) (hP : ∀ p ∈ P,3 ≤ p) :
    (1 : ℝ)/2 ≤ ∏ p ∈ P, (1-1/((p : ℝ)-1)^2) := by
  classical
  have h := correction_finite_lower (P.image (fun p => p-3))
  rw [Finset.prod_image (fun p hp q hq he => by have := hP p hp; have := hP q hq; omega)] at h
  have he : (∏ p ∈ P, correction (p-3)) = ∏ p ∈ P, (1-1/((p : ℝ)-1)^2) := by
    apply Finset.prod_congr rfl
    intro p hp
    dsimp [correction]
    rw [Nat.cast_sub (hP p hp)]
    norm_num only [Nat.cast_ofNat]
    rw [show (p : ℝ)-3+2=(p : ℝ)-1 by ring]
  rwa [he] at h

theorem odd_two_class_factorization (P : Finset ℕ) (hP : ∀ p ∈ P,3 ≤ p) :
    (∏ p ∈ P, (1-2/(p : ℝ))) =
      (∏ p ∈ P, (1-1/((p : ℝ)-1)^2))*(∏ p ∈ P, (1-1/(p : ℝ)))^2 := by
  rw [← Finset.prod_pow,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hP p hp
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ)-1 ≠ 0 := by linarith
  field_simp
  ring

theorem odd_two_class_product_lower (P : Finset ℕ) (hP : ∀ p ∈ P,3 ≤ p) :
    (1 : ℝ)/2*(∏ p ∈ P, (1-1/(p : ℝ)))^2 ≤ ∏ p ∈ P, (1-2/(p : ℝ)) := by
  rw [odd_two_class_factorization P hP]
  exact mul_le_mul_of_nonneg_right (odd_correction_product_lower P hP) (sq_nonneg _)

end ErdosOddEulerCorrection


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_JointModelDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceMoments
open ErdosRandomVariance
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem jointDensity_nonneg (P S : Finset ℕ) (hP : ∀ t ∈ P,t.Prime) :
    0 ≤ jointDensity P S := by
  apply Finset.prod_nonneg
  intro t ht
  let : NeZero t := ⟨(hP t ht).ne_zero⟩
  exact sub_nonneg.mpr (positionDensity_bounds S t).2

theorem odd_position_density_lower (P S : Finset ℕ) (hP : ∀ t ∈ P,3 ≤ t) (hS : S.card ≤ 2) :
    (1 : ℝ)/2*(sieveProduct P)^2 ≤ jointDensity P S := by
  have hh := ErdosOddEulerCorrection.odd_two_class_product_lower P hP
  apply hh.trans
  apply Finset.prod_le_prod
  · intro t ht
    have ht3 : (3 : ℝ) ≤ t := by exact_mod_cast hP t ht
    exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr (by linarith))
  · intro t ht
    let : NeZero t := ⟨by have := hP t ht;omega⟩
    exact sub_le_sub_left (positionDensity_le_two S hS t) 1

theorem nonzero_jointDensity_lower (P S : Finset ℕ) (hP : ∀ t ∈ P,t.Prime)
    (hS : S.card ≤ 2) (hne : jointDensity P S ≠ 0) :
    (1 : ℝ)/2*(sieveProduct P)^2 ≤ jointDensity P S := by
  by_cases h2 : 2 ∈ P
  · have hodd (t : ℕ) (ht : t ∈ P.erase 2) : 3 ≤ t := by
      have hh := Finset.mem_erase.mp ht
      have hp := (hP t hh.2).two_le
      omega
    have hO := odd_position_density_lower (P.erase 2) S hodd hS
    have hO0 := jointDensity_nonneg (P.erase 2) S (fun t ht => hP t (Finset.mem_erase.mp ht).2)
    have hT := nonzero_positionDensity_two P S hS hne h2
    have hK : jointDensity P S = (1-positionDensity S 2)*jointDensity (P.erase 2) S :=
      (Finset.mul_prod_erase P (fun t => 1-positionDensity S t) h2).symm
    have hV : sieveProduct P = (1/2 : ℝ)*sieveProduct (P.erase 2) := by
      rw [sieveProduct,← Finset.mul_prod_erase P (fun t => 1-1/(t : ℝ)) h2]
      norm_num [sieveProduct]
    have hmul := mul_le_mul_of_nonneg_right (show (1 : ℝ)/2 ≤ 1-positionDensity S 2 by linarith) hO0
    rw [hV,hK]
    nlinarith [sq_nonneg (sieveProduct (P.erase 2))]
  · exact odd_position_density_lower P S (fun t ht => by
      have hp := (hP t ht).two_le
      have hn : t ≠ 2 := fun he => h2 (he ▸ ht)
      omega) hS

end ErdosVarianceMoments

end

section

open _root_.Filter
namespace ErdosVarianceUniformMoments
open NumberTheoryLean ErdosVarianceMoments ErdosRandomVariance ErdosInverseEuler
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem densityInverseConstant_pos : 0 < densityInverseConstant := by
  dsimp [densityInverseConstant]
  positivity

theorem actual_sieveProduct (w : ℝ) :
    sieveProduct (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) = SmallSieveFinite.smallEuler ⌊w⌋₊ := by
  simp only [sieveProduct,SmallSieveFinite.smallEuler,one_div]

theorem uniform_density_inverse : ∀ᶠ w : ℝ in atTop,2 ≤ w ∧
    ∀ S : Finset ℕ,S.card ≤ 2 → jointDensity (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) S ≠ 0 →
      (jointDensity (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) S)⁻¹ ≤
        densityInverseConstant*(Real.log w)^2 := by
  filter_upwards [smallEuler_log_bounds] with w hw
  refine ⟨hw.1,?_⟩
  intro S hS hne
  let P := LargePrimeDeletion.cutoffPrimes ⌊w⌋₊
  let V := SmallSieveFinite.smallEuler ⌊w⌋₊
  let K := jointDensity P S
  let B := 2*Real.exp Real.eulerMascheroniConstant*Real.log w
  have hP (t : ℕ) (ht : t ∈ P) : t.Prime := (LargePrimeDeletion.mem_cutoffPrimes.mp ht).1
  have hlow := nonzero_jointDensity_lower P S hP hS hne
  rw [actual_sieveProduct] at hlow
  have hV : 0 < V := hw.2.1
  have hVB : 1 ≤ V*B := by
    have hh := mul_le_mul_of_nonneg_left hw.2.2.2 hV.le
    change V*V⁻¹ ≤ V*B at hh
    simpa only [mul_inv_cancel₀ hV.ne'] using hh
  have hsq : (1 : ℝ) ≤ V^2*B^2 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hVB 2
    simpa only [one_pow,mul_pow] using hh
  have hm := mul_le_mul_of_nonneg_right hlow (sq_nonneg B)
  have hKpos : 0 < K := (by dsimp [K,V] at *;positivity : 0 < (1 : ℝ)/2*V^2).trans_le hlow
  have hb : 2*B^2 = densityInverseConstant*(Real.log w)^2 := by
    dsimp [B,densityInverseConstant]
    ring
  have hmain : 1 ≤ (densityInverseConstant*(Real.log w)^2)*K := by
    rw [← hb]
    dsimp [K,V] at *
    nlinarith
  rw [← one_div]
  exact (div_le_iff₀ hKpos).mpr hmain

end ErdosVarianceUniformMoments

end

section

namespace ErdosVarianceMoments
open NumberTheoryLean ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem jointDensity_split (w : ℝ) (H : ℕ) (S : Finset ℕ) :
    jointDensity (divisorPrimes w H) S*jointDensity (coprimePrimes w H) S =
      jointDensity (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) S := by
  unfold jointDensity divisorPrimes coprimePrimes
  exact Finset.prod_filter_mul_prod_filter_not _ _ _

end ErdosVarianceMoments

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_StableFiniteVariance
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosRandomVariance
open scoped BigOperators

theorem moment_sum {ι α : Type*} (C : Finset α) (w : α → ℝ)
    (J : Finset ι) (f : ι → α → ℝ) :
    weightedMoment C w (fun x => ∑ j ∈ J, f j x) = ∑ j ∈ J, weightedMoment C w (f j) := by
  unfold weightedMoment
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

theorem moment_indicator_square {ι α : Type*} (C : Finset α) (w : α → ℝ)
    (J : Finset ι) (I : ι → α → ℝ) :
    weightedMoment C w (fun x => (indicatorSum J I x)^2) =
      ∑ i ∈ J, ∑ j ∈ J, weightedMoment C w (fun x => I i x * I j x) := by
  have he (x : α) : (indicatorSum J I x)^2 = ∑ i ∈ J, ∑ j ∈ J, I i x * I j x := by
    rw [indicatorSum, pow_two, Finset.sum_mul_sum]
  simp only [he, moment_sum]

theorem centered_moment_identity {α : Type*} (C : Finset α) (w f : α → ℝ) (M : ℝ) :
    weightedMoment C w (fun x => (f x-M)^2) =
      weightedMoment C w (fun x => (f x)^2) - 2*M*weightedMoment C w f +
        M^2*(∑ x ∈ C, w x) := by
  unfold weightedMoment
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem stable_finite_variance {ι α : Type*} (C : Finset α) (w : α → ℝ)
    (J : Finset ι) (I : ι → α → ℝ) (K : ι → ι → ℝ) (V zeta : ℝ)
    (hV : 0 ≤ V) (hzeta : 0 ≤ zeta)
    (hI : ∀ j ∈ J, ∀ x ∈ C, I j x = 0 ∨ I j x = 1)
    (hMass : (∑ x ∈ C, w x) ≤ 1+zeta)
    (hLower : ∀ j ∈ J, (1-zeta)*V ≤ weightedMoment C w (I j))
    (hUpper : ∀ j ∈ J, weightedMoment C w (I j) ≤ (1+zeta)*V)
    (hPair : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      weightedMoment C w (fun x => I i x*I j x) ≤ (1+zeta)*K i j)
    (hDiag : ∀ j ∈ J, K j j = V)
    (hModel : (∑ i ∈ J, ∑ j ∈ J, K i j) ≤ ((J.card : ℝ)*V)^2+(J.card : ℝ)*V) :
    weightedMoment C w (fun x => (indicatorSum J I x-(J.card : ℝ)*V)^2) ≤
      (1+zeta)*((J.card : ℝ)*V)+4*zeta*((J.card : ℝ)*V)^2 := by
  classical
  let M := (J.card : ℝ)*V
  have hM : 0 ≤ M := mul_nonneg (Nat.cast_nonneg _) hV
  have hMean : (1-zeta)*M ≤ weightedMoment C w (indicatorSum J I) := by
    change (1-zeta)*M ≤ weightedMoment C w (fun x => ∑ j ∈ J, I j x)
    rw [moment_sum]
    have h := Finset.sum_le_sum (fun j hj => hLower j hj)
    simp only [Finset.sum_const, nsmul_eq_mul] at h
    dsimp only [M]
    nlinarith [h]
  have hAll : ∀ i ∈ J, ∀ j ∈ J,
      weightedMoment C w (fun x => I i x*I j x) ≤ (1+zeta)*K i j := by
    intro i hi j hj
    by_cases hij : i = j
    · subst j
      have he : weightedMoment C w (fun x => I i x*I i x) = weightedMoment C w (I i) := by
        unfold weightedMoment
        apply Finset.sum_congr rfl
        intro x hx
        rcases hI i hi x hx with h | h <;> simp [h]
      rw [he, hDiag i hi]
      exact hUpper i hi
    · exact hPair i hi j hj hij
  have hSecond : weightedMoment C w (fun x => (indicatorSum J I x)^2) ≤ (1+zeta)*(M^2+M) := by
    rw [moment_indicator_square]
    calc
      _ ≤ ∑ i ∈ J, ∑ j ∈ J, (1+zeta)*K i j :=
        Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hAll i hi j hj))
      _ = (1+zeta)*(∑ i ∈ J, ∑ j ∈ J, K i j) := by simp only [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hModel (by linarith)
  have hMeanScaled := mul_le_mul_of_nonneg_left hMean (show 0 ≤ 2*M by positivity)
  have hMassScaled := mul_le_mul_of_nonneg_left hMass (sq_nonneg M)
  change weightedMoment C w (fun x => (indicatorSum J I x-M)^2) ≤ (1+zeta)*M+4*zeta*M^2
  rw [centered_moment_identity]
  nlinarith [hSecond, hMeanScaled, hMassScaled]

end ErdosRandomVariance

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_WeightedChebyshev
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosRandomVariance

theorem weighted_chebyshev {α : Type*} (C : Finset α) (w f : α → ℝ)
    (M a B : ℝ) (hw : ∀ x ∈ C, 0 ≤ w x) (ha : 0 < a)
    (hBound : weightedMoment C w (fun x => (f x-M)^2) ≤ B) :
    (∑ x ∈ C with a ≤ |f x-M|, w x) ≤ B/a^2 := by
  classical
  have hlocal (x : α) (hx : x ∈ C.filter (fun x => a ≤ |f x-M|)) :
      a^2*w x ≤ w x*(f x-M)^2 := by
    obtain ⟨hxC,hxE⟩ := Finset.mem_filter.mp hx
    have hsq : a^2 ≤ (f x-M)^2 := by
      nlinarith [sq_abs (f x-M),abs_nonneg (f x-M)]
    nlinarith [mul_le_mul_of_nonneg_right hsq (hw x hxC)]
  have hs : a^2*(∑ x ∈ C with a ≤ |f x-M|, w x) ≤ B := by
    calc
      _ = ∑ x ∈ C with a ≤ |f x-M|, a^2*w x := Finset.mul_sum ..
      _ ≤ ∑ x ∈ C with a ≤ |f x-M|, w x*(f x-M)^2 := Finset.sum_le_sum hlocal
      _ ≤ ∑ x ∈ C, w x*(f x-M)^2 := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun x hx _ => mul_nonneg (hw x hx) (sq_nonneg _))
      _ ≤ B := hBound
  apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
  nlinarith [hs]

theorem weighted_relative_chebyshev {α : Type*} (C : Finset α) (w f : α → ℝ)
    (M eta beta : ℝ) (hw : ∀ x ∈ C, 0 ≤ w x) (hM : 0 < M) (heta : 0 < eta)
    (hBound : weightedMoment C w (fun x => (f x-M)^2) ≤ beta*M^2) :
    (∑ x ∈ C with eta*M ≤ |f x-M|, w x) ≤ beta/eta^2 := by
  classical
  have h := weighted_chebyshev C w f M (eta*M) (beta*M^2) hw (mul_pos heta hM) hBound
  have he : beta*M^2/(eta*M)^2 = beta/eta^2 := by
    field_simp [hM.ne',heta.ne']
  rwa [he] at h

end ErdosRandomVariance


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_StableSourceVariance
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
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
namespace ErdosRandomVariance

theorem variancePrimes_prime (w : ℝ) (p : ℕ) (hp : p ∈ variancePrimes w) : p.Prime :=
  (Finset.mem_filter.mp hp).2

theorem sieveProduct_pos (P : Finset ℕ) (hP : ∀ p ∈ P,p.Prime) : 0 < sieveProduct P := by
  apply Finset.prod_pos
  intro p hp
  have h := hP p hp
  apply sub_pos.mpr
  exact (div_lt_one (show (0 : ℝ) < p by exact_mod_cast h.pos)).mpr
    (by exact_mod_cast h.one_lt)

theorem variance_product_limit :
    Tendsto (fun w : ℝ => Real.log w*sieveProduct (variancePrimes w)) atTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
  have he3 : Tendsto _root_.Erdos970.Mertens.E₃ atTop (𝓝 (0 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).mp _root_.Erdos970.Mertens.E₃.bound'
  have h := he3.rexp.const_mul (Real.exp (-Real.eulerMascheroniConstant))
  simp only [Real.exp_zero,mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with w hw
  rw [sieveProduct,variancePrimes,_root_.Erdos970.Mertens.prod_one_minus_div_prime_eq hw]
  field_simp [ne_of_gt (Real.log_pos hw)]

theorem source_mean_large (delta K : ℝ) (hdelta : 0 < delta) (hK : 0 < K) :
    ∀ᶠ w : ℝ in atTop, 1 < w ∧ ∀ J : ℕ, w^delta ≤ (J : ℝ) →
      K ≤ (J : ℝ)*sieveProduct (variancePrimes w) := by
  let c := Real.exp (-Real.eulerMascheroniConstant)/2
  have hc : 0 < c := by dsimp [c] <;> positivity
  have hlt : c < Real.exp (-Real.eulerMascheroniConstant) := by
    dsimp [c] <;> nlinarith [Real.exp_pos (-Real.eulerMascheroniConstant)]
  have hlow := variance_product_limit.eventually (lt_mem_nhds hlt)
  have hsmall := (isLittleO_log_rpow_rpow_atTop (1 : ℝ) hdelta).bound (div_pos hc hK)
  filter_upwards [hlow,hsmall,eventually_gt_atTop (1 : ℝ)] with w hwc hlog hw
  refine ⟨hw,?_⟩
  intro J hJ
  have hw0 : 0 < w := by linarith
  have hL : 0 < Real.log w := Real.log_pos hw
  have hlog' : Real.log w ≤ (c/K)*w^delta := by
    simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_pos hL,
      abs_of_nonneg (Real.rpow_nonneg hw0.le delta)] using hlog
  have hV : 0 < sieveProduct (variancePrimes w) := sieveProduct_pos _ (variancePrimes_prime w)
  have hm := mul_le_mul_of_nonneg_right hlog' hV.le
  have hbase : c/(c/K) ≤ w^delta*sieveProduct (variancePrimes w) := by
    apply (div_le_iff₀ (div_pos hc hK)).mpr
    nlinarith [hwc,hm]
  have he : c/(c/K)=K := by field_simp [hc.ne',hK.ne']
  rw [he] at hbase
  exact hbase.trans (mul_le_mul_of_nonneg_right hJ hV.le)

end ErdosRandomVariance

end


open _root_.Filter
namespace ErdosRandomVariance

universe u

theorem stable_prime_variance {α : Type*} (C : Finset α) (w : α → ℝ)
    (J : ℕ) (I : ℕ → α → ℝ) (P : Finset ℕ) (hP : ∀ p ∈ P,p.Prime)
    (zeta : ℝ) (hzeta : 0 ≤ zeta)
    (hI : ∀ j ∈ Finset.range J, ∀ x ∈ C, I j x = 0 ∨ I j x = 1)
    (hMass : (∑ x ∈ C, w x) ≤ 1+zeta)
    (hLower : ∀ j ∈ Finset.range J, (1-zeta)*sieveProduct P ≤ weightedMoment C w (I j))
    (hUpper : ∀ j ∈ Finset.range J, weightedMoment C w (I j) ≤ (1+zeta)*sieveProduct P)
    (hPair : ∀ i ∈ Finset.range J, ∀ j ∈ Finset.range J, i ≠ j →
      weightedMoment C w (fun x => I i x*I j x) ≤ (1+zeta)*pairKernel P i j) :
    weightedMoment C w (fun x => (indicatorSum (Finset.range J) I x-(J : ℝ)*sieveProduct P)^2) ≤
      (1+zeta)*((J : ℝ)*sieveProduct P)+4*zeta*((J : ℝ)*sieveProduct P)^2 := by
  simpa only [Finset.card_range] using stable_finite_variance C w (Finset.range J) I
    (pairKernel P) (sieveProduct P) zeta (sieveProduct_pos P hP).le hzeta hI hMass hLower hUpper
    hPair (fun j _ => pairKernel_diagonal P j)
    (by simpa only [Finset.card_range] using pairKernel_interval_sum P hP J)

theorem stable_source_variance (delta eps : ℝ) (hdelta : 0 < delta) (heps : 0 < eps) :
    ∀ᶠ W : ℝ in atTop, 1 < W ∧ ∀ (J : ℕ), W^delta ≤ (J : ℝ) →
      ∀ (α : Type u) (C : Finset α) (w : α → ℝ) (I : ℕ → α → ℝ) (zeta : ℝ),
      0 ≤ zeta → zeta ≤ 1 →
      (∀ j ∈ Finset.range J, ∀ x ∈ C, I j x = 0 ∨ I j x = 1) →
      (∑ x ∈ C, w x) ≤ 1+zeta →
      (∀ j ∈ Finset.range J, (1-zeta)*sieveProduct (variancePrimes W) ≤ weightedMoment C w (I j)) →
      (∀ j ∈ Finset.range J, weightedMoment C w (I j) ≤ (1+zeta)*sieveProduct (variancePrimes W)) →
      (∀ i ∈ Finset.range J, ∀ j ∈ Finset.range J, i ≠ j →
        weightedMoment C w (fun x => I i x*I j x) ≤ (1+zeta)*pairKernel (variancePrimes W) i j) →
      weightedMoment C w
        (fun x => (indicatorSum (Finset.range J) I x-(J : ℝ)*sieveProduct (variancePrimes W))^2) ≤
        (eps+4*zeta)*((J : ℝ)*sieveProduct (variancePrimes W))^2 := by
  filter_upwards [source_mean_large delta (2/eps) hdelta (div_pos (by norm_num) heps)] with W hW
  refine ⟨hW.1,?_⟩
  intro J hJ α C w I zeta hzeta hzeta1 hI hMass hLower hUpper hPair
  let M := (J : ℝ)*sieveProduct (variancePrimes W)
  have hM : 2/eps ≤ M := hW.2 J hJ
  have hM0 : 0 ≤ M := mul_nonneg (Nat.cast_nonneg _) (sieveProduct_pos _ (variancePrimes_prime W)).le
  have h2 : 2 ≤ eps*M := by nlinarith [(div_le_iff₀ heps).mp hM]
  have hmain := stable_prime_variance C w J I (variancePrimes W) (variancePrimes_prime W)
    zeta hzeta hI hMass hLower hUpper hPair
  change weightedMoment C w (fun x => (indicatorSum (Finset.range J) I x-M)^2) ≤ (eps+4*zeta)*M^2
  change weightedMoment C w (fun x => (indicatorSum (Finset.range J) I x-M)^2) ≤ (1+zeta)*M+4*zeta*M^2 at hmain
  nlinarith [mul_le_mul_of_nonneg_right h2 hM0,mul_le_mul_of_nonneg_right hzeta1 hM0]

end ErdosRandomVariance


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_StableSourceChebyshev
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


open _root_.Filter
namespace ErdosRandomVariance

universe u

theorem stable_source_chebyshev (delta eps : ℝ) (hdelta : 0 < delta) (heps : 0 < eps) :
    ∀ᶠ W : ℝ in atTop, 1 < W ∧ ∀ (J : ℕ), W^delta ≤ (J : ℝ) →
      ∀ (α : Type u) (C : Finset α) (w : α → ℝ) (I : ℕ → α → ℝ) (zeta eta : ℝ),
      (∀ x ∈ C, 0 ≤ w x) → 0 ≤ zeta → zeta ≤ 1 → 0 < eta →
      (∀ j ∈ Finset.range J, ∀ x ∈ C, I j x = 0 ∨ I j x = 1) →
      (∑ x ∈ C, w x) ≤ 1+zeta →
      (∀ j ∈ Finset.range J, (1-zeta)*sieveProduct (variancePrimes W) ≤ weightedMoment C w (I j)) →
      (∀ j ∈ Finset.range J, weightedMoment C w (I j) ≤ (1+zeta)*sieveProduct (variancePrimes W)) →
      (∀ i ∈ Finset.range J, ∀ j ∈ Finset.range J, i ≠ j →
        weightedMoment C w (fun x => I i x*I j x) ≤ (1+zeta)*pairKernel (variancePrimes W) i j) →
      (∑ x ∈ C with eta*((J : ℝ)*sieveProduct (variancePrimes W)) ≤
        |indicatorSum (Finset.range J) I x-(J : ℝ)*sieveProduct (variancePrimes W)|, w x) ≤
        (eps+4*zeta)/eta^2 := by
  classical
  filter_upwards [stable_source_variance delta eps hdelta heps] with W hW
  refine ⟨hW.1,?_⟩
  intro J hJ α C w I zeta eta hw hzeta hzeta1 heta hI hMass hLower hUpper hPair
  have hJpos : (0 : ℝ) < J := lt_of_lt_of_le
    (Real.rpow_pos_of_pos (show 0 < W by linarith [hW.1]) delta) hJ
  have hM := mul_pos hJpos (sieveProduct_pos _ (variancePrimes_prime W))
  exact weighted_relative_chebyshev C w (indicatorSum (Finset.range J) I)
    ((J : ℝ)*sieveProduct (variancePrimes W)) eta (eps+4*zeta) hw hM heta
    (hW.2 J hJ α C w I zeta hzeta hzeta1 hI hMass hLower hUpper hPair)

end ErdosRandomVariance


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_MomentIndicators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace ErdosVarianceUniformMoments
open NumberTheoryLean ErdosVarianceMoments ErdosVarianceSmallModel ErdosRandomVariance
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem weighted_joint_eq_mass (R xi w : ℝ) (H qA : ℕ) (C0 : ℤ)
    (beta delta : ∀ t : ℕ,ZMod t) (S : Finset ℕ) :
    weightedMoment (modelUniverse R xi w H C0) (fun _ => atomWeight R xi w H C0)
      (jointIndicator w H C0 qA beta delta S) =
      modelMass R xi w H C0 (jointCondition w H C0 qA beta delta S) := by
  unfold weightedMoment modelMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _hv
  unfold jointIndicator
  split_ifs <;> simp

theorem weighted_single_eq_mass (R xi w : ℝ) (H qA : ℕ) (C0 : ℤ)
    (beta delta : ∀ t : ℕ,ZMod t) (j : ℕ) :
    weightedMoment (modelUniverse R xi w H C0) (fun _ => atomWeight R xi w H C0)
      (modelIndicator w H C0 qA beta delta j) =
      modelMass R xi w H C0 (jointCondition w H C0 qA beta delta {j}) := by
  rw [← weighted_joint_eq_mass]
  congr 1
  funext v
  exact (jointIndicator_singleton w H C0 qA beta delta j v).symm

theorem weighted_pair_eq_mass (R xi w : ℝ) (H qA : ℕ) (C0 : ℤ)
    (beta delta : ∀ t : ℕ,ZMod t) (i j : ℕ) :
    weightedMoment (modelUniverse R xi w H C0) (fun _ => atomWeight R xi w H C0)
      (fun v => modelIndicator w H C0 qA beta delta i v*modelIndicator w H C0 qA beta delta j v) =
      modelMass R xi w H C0 (jointCondition w H C0 qA beta delta {i,j}) := by
  rw [← weighted_joint_eq_mass]
  congr 1
  funext v
  exact (jointIndicator_pair w H C0 qA beta delta i j v).symm

end ErdosVarianceUniformMoments


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_UniformJointModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
namespace ErdosUniformMobiusRemainder

theorem cutoffExponent_margin (M : ℝ) : 2*M+10 < cutoffExponent M := by
  dsimp [cutoffExponent]
  linarith

theorem source_sqrt_lower (M xi W Y : ℝ) (hxi : 0 < xi) (hW : 0 < W)
    (hY : xi*W^(cutoffExponent M) ≤ Y) :
    xi^((1 : ℝ)/2)*W^(M+6) ≤ Y^((1 : ℝ)/2) := by
  have hp := Real.rpow_le_rpow (show 0 ≤ xi*W^(cutoffExponent M) by positivity) hY
    (by norm_num : (0 : ℝ) ≤ 1/2)
  rw [Real.mul_rpow hxi.le (Real.rpow_nonneg hW.le _) ,← Real.rpow_mul hW.le] at hp
  have he : cutoffExponent M*((1 : ℝ)/2)=M+6 := by dsimp [cutoffExponent] <;> ring
  rwa [he] at hp

theorem remainder_scalar_bound (C A M xi W : ℝ) (H : ℕ) (Y : ℝ)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hxi : 0 < xi) (hW : 0 < W)
    (hH : 1 ≤ H) (hHY : (H : ℝ) ≤ Y) (hYscale : xi*W^(cutoffExponent M) ≤ Y)
    (hdiv : (H.divisors.card : ℝ)*(H : ℝ)/(Y*(H.totient : ℝ)) ≤ C/Y^((1 : ℝ)/2)) :
    A*(H.divisors.card : ℝ)*(H : ℝ)/(Y*(H.totient : ℝ))*W^M*(Real.log W)^2 ≤
      (A*C/xi^((1 : ℝ)/2))*((Real.log W)^2/W^(6 : ℝ)) := by
  have hY : 0 < Y := (show (0 : ℝ) < H by exact_mod_cast hH).trans_le hHY
  have hroot := source_sqrt_lower M xi W Y hxi hW hYscale
  have hbase : A*(H.divisors.card : ℝ)*(H : ℝ)/(Y*(H.totient : ℝ)) ≤
      A*C/(xi^((1 : ℝ)/2)*W^(M+6)) := by
    calc
      _ = A*((H.divisors.card : ℝ)*(H : ℝ)/(Y*(H.totient : ℝ))) := by ring
      _ ≤ A*(C/Y^((1 : ℝ)/2)) := mul_le_mul_of_nonneg_left hdiv hA
      _ = A*C/Y^((1 : ℝ)/2) := by ring
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hA hC) (by positivity) hroot
  have hf : W^(M+6)=W^M*W^(6 : ℝ) := by rw [Real.rpow_add hW]
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg hW.le M)) (sq_nonneg (Real.log W))
  have he : (A*C/(xi^((1 : ℝ)/2)*W^(M+6)))*W^M*(Real.log W)^2 =
      (A*C/xi^((1 : ℝ)/2))*((Real.log W)^2/W^(6 : ℝ)) := by
    rw [hf]
    field_simp
  exact hmul.trans_eq he

theorem uniform_mobius_remainder (M : ℝ) (_hM : 0 ≤ M) :
    ∃ Cs : ℝ,2*M+10 < Cs ∧ ∀ xi : ℝ,0 < xi → ∀ A : ℝ,0 ≤ A →
      ∀ eps : ℝ,0 < eps → ∀ᶠ W : ℝ in atTop,1 < W ∧
        ∀ (H : ℕ) (Y : ℝ),1 ≤ H → (H : ℝ) ≤ Y → xi*W^Cs ≤ Y →
          A*(H.divisors.card : ℝ)*(H : ℝ)/(Y*(H.totient : ℝ))*W^M*(Real.log W)^2 ≤ eps := by
  obtain ⟨C,hC,hbound⟩ := divisor_totient_length_bound
  refine ⟨cutoffExponent M,cutoffExponent_margin M,?_⟩
  intro xi hxi A hA eps heps
  by_cases hA0 : A=0
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with W hW
    refine ⟨hW,?_⟩
    intro H Y _ _ _
    simpa only [hA0,zero_mul,zero_div] using heps.le
  have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
  let K := A*C/xi^((1 : ℝ)/2)
  have hK : 0 < K := by dsimp [K] <;> positivity
  have hlittle := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 6)).bound (div_pos heps hK)
  filter_upwards [hlittle,eventually_gt_atTop (1 : ℝ)] with W hlog hW
  refine ⟨hW,?_⟩
  intro H Y hH hHY hYscale
  have hW0 : 0 < W := by linarith
  have hlog' : (Real.log W)^2 ≤ (eps/K)*W^(6 : ℝ) := by
    simpa only [Real.rpow_two,Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (Real.log W)),abs_of_nonneg (Real.rpow_nonneg hW0.le (6 : ℝ))] using hlog
  have hsmall : K*((Real.log W)^2/W^(6 : ℝ)) ≤ eps := by
    have hh := (div_le_iff₀ (Real.rpow_pos_of_pos hW0 (6 : ℝ))).mpr hlog'
    have hm := mul_le_mul_of_nonneg_left hh hK.le
    have he : K*(eps/K)=eps := by field_simp
    exact hm.trans_eq he
  exact (remainder_scalar_bound C A M xi W H Y hC.le hA hxi hW0 hH hHY hYscale
    (hbound H Y hH hHY)).trans hsmall

end ErdosUniformMobiusRemainder

end


namespace ErdosVarianceUniformMoments
open NumberTheoryLean ErdosVarianceMoments ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem zero_joint_model_mass (R xi w : ℝ) (H qA : ℕ) (C0 : ℤ)
    (hC0 : Int.gcd C0 (H : ℤ) = 1) (beta delta : ∀ t : ℕ,ZMod t)
    (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t) (S : Finset ℕ)
    (hz : jointDensity (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) S = 0) :
    modelMass R xi w H C0 (jointCondition w H C0 qA beta delta S) = 0 := by
  have hmul : jointDensity (divisorPrimes w H) S*jointDensity (coprimePrimes w H) S = 0 :=
    (jointDensity_split w H S).trans hz
  rw [joint_model_mass R xi w H qA C0 beta delta S hC0]
  rcases mul_eq_zero.mp hmul with h0|h1
  · rw [h0,mul_zero,mul_zero,zero_mul]
  · have hf (p : (ZMod (coprimeModulus w H))ˣ) :
        coprimePositionSurvivors w H qA delta S p (modelLeft R xi (C0 : ℝ))
          (modelRight R xi (H : ℝ) (C0 : ℝ)) = ∅ :=
      zero_coprimePositionSurvivors w H qA delta S p hqA h1 _ _
    simp only [hf,Finset.card_empty,Nat.cast_zero,Finset.sum_const_zero,mul_zero]

end ErdosVarianceUniformMoments



open _root_.Filter
namespace ErdosVarianceUniformMoments
open NumberTheoryLean ErdosVarianceMoments ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem uniform_joint_model_relative (zeta : ℝ) (hzeta : 0 < zeta) :
    ∃ Cs : ℝ,0 < Cs ∧ ∀ xi : ℝ,0 < xi → ∀ᶠ w : ℝ in atTop,2 ≤ w ∧
      ∀ (R : ℝ),0 < R → ∀ (H qA : ℕ),0 < H → ∀ (C0 : ℤ),Int.gcd C0 (H : ℤ) = 1 →
        ∀ (beta delta : ∀ t : ℕ,ZMod t),
        (∀ t ∈ coprimePrimes w H,qA.Coprime t) →
        xi*w^Cs ≤ modelLength R xi (H : ℝ) (C0 : ℝ) →
        ∀ S : Finset ℕ,S.card ≤ 2 →
          |modelMass R xi w H C0 (jointCondition w H C0 qA beta delta S)-
            jointDensity (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) S| ≤
              zeta*jointDensity (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) S := by
  let s := max 480024 (-96*Real.log (zeta/2))
  have hs : 480024 ≤ s := le_max_left _ _
  have hs0 : 0 ≤ s := by linarith
  have hexp : Real.exp (-s/96) ≤ zeta/2 := by
    have hsecond : -96*Real.log (zeta/2) ≤ s := le_max_right _ _
    calc
      _ ≤ Real.exp (Real.log (zeta/2)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := Real.exp_log (by positivity)
  obtain ⟨Cs,hCs,hrem⟩ := ErdosUniformMobiusRemainder.uniform_mobius_remainder (2*s) (by positivity)
  refine ⟨Cs,by linarith,?_⟩
  intro xi hxi
  have hA : 0 ≤ 4*densityInverseConstant := mul_nonneg (by norm_num) densityInverseConstant_pos.le
  filter_upwards [uniform_density_inverse,hrem xi hxi (4*densityInverseConstant) hA (zeta/2) (by positivity)]
    with w hden hremw
  refine ⟨hden.1,?_⟩
  intro R hR H qA hH C0 hC0 beta delta hqA hscale S hS
  let K := jointDensity (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) S
  change |modelMass R xi w H C0 (jointCondition w H C0 qA beta delta S)-K| ≤ zeta*K
  by_cases hzero : K = 0
  · have hm := zero_joint_model_mass R xi w H qA C0 hC0 beta delta hqA S hzero
    simp only [hm,hzero,sub_zero,abs_zero,mul_zero,le_refl]
  have hP (t : ℕ) (ht : t ∈ LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) : t.Prime :=
    (LargePrimeDeletion.mem_cutoffPrimes.mp ht).1
  have hK : 0 < K := lt_of_le_of_ne (jointDensity_nonneg _ S hP) (Ne.symm hzero)
  let Y := modelLength R xi (H : ℝ) (C0 : ℝ)
  let E := 4*(H.divisors.card : ℝ)*(H : ℝ)/(Y*(H.totient : ℝ))*(w^s)^2
  have hW : 0 < w := by linarith [hden.1]
  have hYH : (H : ℝ) ≤ Y := by
    dsimp [Y,modelLength,interceptScale]
    exact le_add_of_nonneg_right (by positivity)
  have hY : 0 < Y := (show (0 : ℝ) < H by exact_mod_cast hH).trans_le hYH
  have hE : 0 ≤ E := by dsimp [E] <;> positivity
  have hbudget := hremw.2 H Y hH hYH hscale
  have hp : (w^s)^2 = w^(2*s) := by
    rw [← Real.rpow_two,← Real.rpow_mul hW.le]
    congr 1
    ring
  have hbudget' : E*(densityInverseConstant*(Real.log w)^2) ≤ zeta/2 := by
    have he : E*(densityInverseConstant*(Real.log w)^2) =
      (4*densityInverseConstant)*(H.divisors.card : ℝ)*(H : ℝ)/(Y*(H.totient : ℝ))*
        w^(2*s)*(Real.log w)^2 := by dsimp [E];rw [hp];ring
    exact he.trans_le hbudget
  have hinv : E/K ≤ zeta/2 := by
    calc
      E/K = E*K⁻¹ := div_eq_mul_inv _ _
      _ ≤ E*(densityInverseConstant*(Real.log w)^2) :=
        mul_le_mul_of_nonneg_left (hden.2 S hS hzero) hE
      _ ≤ _ := hbudget'
  have hEbound : E ≤ (zeta/2)*K := (div_le_iff₀ hK).mp hinv
  have hf := finite_joint_moment_estimate_jb247 R xi w hR hxi.le hden.1 s hs H qA hH C0 hC0 beta delta hqA S hS
  have heterm := mul_le_mul_of_nonneg_left hexp hK.le
  change K*Real.exp (-s/96) ≤ K*(zeta/2) at heterm
  change |modelMass R xi w H C0 (jointCondition w H C0 qA beta delta S)-K| ≤ K*Real.exp (-s/96)+E at hf
  change |modelMass R xi w H C0 (jointCondition w H C0 qA beta delta S)-K| ≤ zeta*K
  linarith

end ErdosVarianceUniformMoments


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_StableModelMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceUniformMoments
open NumberTheoryLean ErdosVarianceMoments ErdosVarianceSmallModel ErdosRandomVariance ErdosInverseEuler
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem variancePrimes_eq_cutoff (w : ℝ) :
    variancePrimes w = LargePrimeDeletion.cutoffPrimes ⌊w⌋₊ :=
  (cutoffPrimes_eq_filtered_Ioc _).symm

theorem model_moment_bounds (R xi w : ℝ) (H qA : ℕ) (C0 : ℤ)
    (beta delta : ∀ t : ℕ,ZMod t) (zeta : ℝ)
    (hrel : ∀ S : Finset ℕ,S.card ≤ 2 →
      |modelMass R xi w H C0 (jointCondition w H C0 qA beta delta S)-
        jointDensity (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) S| ≤
          zeta*jointDensity (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) S) :
    (∑ _v ∈ modelUniverse R xi w H C0,atomWeight R xi w H C0) ≤ 1+zeta ∧
    (∀ j : ℕ,(1-zeta)*sieveProduct (variancePrimes w) ≤
      weightedMoment (modelUniverse R xi w H C0) (fun _ => atomWeight R xi w H C0)
        (modelIndicator w H C0 qA beta delta j)) ∧
    (∀ j : ℕ,weightedMoment (modelUniverse R xi w H C0) (fun _ => atomWeight R xi w H C0)
        (modelIndicator w H C0 qA beta delta j) ≤ (1+zeta)*sieveProduct (variancePrimes w)) ∧
    (∀ i j : ℕ,weightedMoment (modelUniverse R xi w H C0) (fun _ => atomWeight R xi w H C0)
        (fun v => modelIndicator w H C0 qA beta delta i v*modelIndicator w H C0 qA beta delta j v) ≤
          (1+zeta)*pairKernel (variancePrimes w) i j) := by
  have hmass := hrel ∅ (by simp)
  have he : jointCondition w H C0 qA beta delta ∅ = (fun _ => True) := by
    funext v
    exact propext (by simp [jointCondition])
  rw [he] at hmass
  have hkempty : jointDensity (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) ∅ = 1 := by
    simp [jointDensity,positionDensity,positionResidues]
  simp only [hkempty,mul_one,modelMass,Finset.filter_true] at hmass
  have hsingle (j : ℕ) := hrel {j} (by simp)
  have hsingle' (j : ℕ) :
      |weightedMoment (modelUniverse R xi w H C0) (fun _ => atomWeight R xi w H C0)
          (modelIndicator w H C0 qA beta delta j)-sieveProduct (variancePrimes w)| ≤
        zeta*sieveProduct (variancePrimes w) := by
    simpa only [weighted_single_eq_mass,variancePrimes_eq_cutoff,jointDensity_singleton] using hsingle j
  refine ⟨by linarith [(abs_le.mp hmass).2],?_,?_,?_⟩
  · intro j
    nlinarith [(abs_le.mp (hsingle' j)).1]
  · intro j
    nlinarith [(abs_le.mp (hsingle' j)).2]
  · intro i j
    have hcard : ({i,j} : Finset ℕ).card ≤ 2 := by
      calc
        _ ≤ ({j} : Finset ℕ).card+1 := Finset.card_insert_le i _
        _ = 2 := by simp
    have hh := hrel {i,j} hcard
    rw [jointDensity_pair,← weighted_pair_eq_mass] at hh
    rw [variancePrimes_eq_cutoff]
    nlinarith [(abs_le.mp hh).2]

end ErdosVarianceUniformMoments

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_GuardedHardPrimeSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


section

open _root_.Filter
namespace ErdosVarianceUniformMoments
open NumberTheoryLean ErdosVarianceMoments ErdosVarianceSmallModel ErdosRandomVariance
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem uniform_model_chebyshev_jb247_oai (a eta tau : ℝ) (ha : 0 < a) (heta : 0 < eta) (htau : 0 < tau) :
    ∃ Cs : ℝ,0 < Cs ∧ ∀ xi : ℝ,0 < xi → ∀ᶠ w : ℝ in atTop,2 ≤ w ∧
      ∀ (R : ℝ),0 < R → ∀ (H qA : ℕ),0 < H → ∀ (C0 : ℤ),Int.gcd C0 (H : ℤ) = 1 →
        ∀ (beta delta : ∀ t : ℕ,ZMod t),
        (∀ t ∈ coprimePrimes w H,qA.Coprime t) →
        xi*w^Cs ≤ modelLength R xi (H : ℝ) (C0 : ℝ) →
        ∀ J : ℕ,w^a ≤ (J : ℝ) →
          modelMass R xi w H C0 (modelBadEvent J w H qA C0 beta delta eta) ≤ tau := by
  let zeta := min 1 (tau*eta^2/8)
  have hzeta : 0 < zeta := lt_min zero_lt_one (by positivity)
  have hzeta1 : zeta ≤ 1 := min_le_left _ _
  let eps := tau*eta^2/2
  have heps : 0 < eps := by dsimp [eps] <;> positivity
  obtain ⟨Cs,hCs,huniform⟩ := uniform_joint_model_relative zeta hzeta
  refine ⟨Cs,hCs,?_⟩
  intro xi hxi
  filter_upwards [huniform xi hxi,stable_source_chebyshev a eps ha heps] with w hw hstable
  refine ⟨hw.1,?_⟩
  intro R hR H qA hH C0 hC0 beta delta hqA hscale J hJ
  have hmom := model_moment_bounds R xi w H qA C0 beta delta zeta
    (hw.2 R hR H qA hH C0 hC0 beta delta hqA hscale)
  have hh := hstable.2 J hJ (ModelPoint w H) (modelUniverse R xi w H C0)
    (fun _ => atomWeight R xi w H C0) (modelIndicator w H C0 qA beta delta) zeta eta
    (fun _ _ => (atomWeight_pos R xi w H C0 hR hxi.le hH).le) hzeta.le hzeta1 heta
    (fun j _ v _ => modelIndicator_binary w H C0 qA beta delta j v)
    hmom.1 (fun j _ => hmom.2.1 j) (fun j _ => hmom.2.2.1 j)
    (fun i _ j _ _ => hmom.2.2.2 i j)
  have hV : sieveProduct (variancePrimes w) = SmallSieveFinite.smallEuler ⌊w⌋₊ := by
    rw [variancePrimes_eq_cutoff,actual_sieveProduct]
  rw [hV] at hh
  have hbudget : (eps+4*zeta)/eta^2 ≤ tau := by
    apply (div_le_iff₀ (sq_pos_of_pos heta)).mpr
    have hz : zeta ≤ tau*eta^2/8 := min_le_right _ _
    dsimp [eps]
    linarith
  exact hh.trans hbudget

end ErdosVarianceUniformMoments

end


end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.ErdosVarianceUniformMoments.uniform_model_chebyshev_jb247_oai := @OAI.Erdos970.ErdosVarianceUniformMoments.uniform_model_chebyshev_jb247_oai
