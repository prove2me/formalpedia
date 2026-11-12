-- Prove2me | solution 1 for OAI.Erdos970.ErdosVarianceWeighted.source_selection_hard_mass_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:58:01.6797+00:00
-- url     : https://prove2.me/submissions/bdca56d1-6d32-4c9f-aa1f-08520d0074c8

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
import Definitions.Def_OAIQ247J008
import Theorems.Thm_Erdos970_Mertens_LogZetaInteg_log_zeta_eq_integ_aux_jb247
import Theorems.Thm_Erdos970_Mertens_sum_M_eq_summand_le_jb247
import Theorems.Thm_OAI_Erdos970_ErdosVarianceCommon_source_actual_bad_to_common_jb247
import Theorems.Thm_OAI_Erdos970_ErdosVarianceLargeMap_source_full_pattern_domination_jb247
import Theorems.Thm_OAI_Erdos970_ErdosVarianceSmallModel_source_residue_fibre_bound_jb247
import Theorems.Thm_OAI_Erdos970_ErdosVarianceUniformMoments_uniform_model_chebyshev_jb247

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeHitRepresentative
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseHits

theorem primeHitRepresentative_spec (q : ℕ) (hq : Squarefree q) (a : ℕ → ℕ) :
    1 ≤ primeHitRepresentative q hq a ∧ primeHitRepresentative q hq a ≤ q ∧
      ∀ n : ℕ,(∀ p ∈ q.primeFactors,n%p = a p%p) ↔ Nat.ModEq q n (primeHitRepresentative q hq a) :=
  (exists_prime_hit_representative q hq a).choose_spec

end ErdosInverseHits

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_FactorDividesAbscissa
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

theorem aligned_prime_not_dvd_den (a : ℕ → ℤ) (q : ℚ) {p : ℕ}
    (hp : p.Prime) (hq : aligns a q p) : ¬p ∣ q.den := by
  intro hd
  have hd0 : (q.den : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  have hn0 : (q.num : ZMod p) = 0 := by
    change (q.den : ZMod p)*(a p : ZMod p) = (q.num : ZMod p) at hq
    simpa only [hd0,zero_mul] using hq.symm
  have hn : p ∣ q.num.natAbs := Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hn0)
  have hg := Nat.dvd_gcd hn hd
  rw [q.reduced.gcd_eq_one] at hg
  exact hp.not_dvd_one hg

end ErdosInverseAlignment

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

end ErdosInversePrimeBin

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_AlignedPrimeCongruence
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosAlignedProgression
open ErdosInverseAlignment ErdosInverseHits ErdosInverseCounts

theorem aligned_den_coprime_prime (a : ℕ → ℕ) (r : ℚ) (p : ℕ) (hp : p.Prime)
    (ha : aligns (fun s => (a s : ℤ)) r p) : r.den.Coprime p :=
  (hp.coprime_iff_not_dvd.mpr (aligned_prime_not_dvd_den _ r hp ha)).symm

end ErdosAlignedProgression

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReciprocalEnvelope
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceSmallModel

theorem totalScale_pos (R H C0 : ℝ) (hH : 0 < H) : 0 < totalScale R H C0 :=
  hH.trans_le (le_max_left _ _)

theorem primeWidth_pos (R xi H C0 : ℝ) (hR : 0 < R) (hxi : 0 < xi) (hH : 0 < H) :
    0 < primeWidth R xi H C0 :=
  lt_min (mul_pos hxi hR) (div_pos (mul_pos hR hH) (totalScale_pos R H C0 hH))

theorem primeWidth_caps (R xi H C0 : ℝ) :
    primeWidth R xi H C0 ≤ xi*R ∧ primeWidth R xi H C0 ≤ R*H/totalScale R H C0 :=
  ⟨min_le_left _ _,min_le_right _ _⟩

theorem modelLength_bounds (R xi H C0 : ℝ) (hR : 0 < R) (hxi : 0 ≤ xi)
    (hxi1 : xi ≤ 1) (hH : 0 < H) :
    H ≤ modelLength R xi H C0 ∧ xi*totalScale R H C0 ≤ modelLength R xi H C0 := by
  have hc : 0 ≤ interceptScale R C0 := div_nonneg (abs_nonneg _) hR.le
  have hxiH := mul_le_mul_of_nonneg_right hxi1 hH.le
  constructor
  · dsimp [modelLength]
    nlinarith [mul_nonneg hxi hc]
  · rcases le_total H (interceptScale R C0) with h | h
    · rw [totalScale,max_eq_right h]
      dsimp [modelLength]
      linarith
    · rw [totalScale,max_eq_left h]
      dsimp [modelLength]
      nlinarith

theorem small_model_area (R xi H C0 : ℝ) (hR : 0 < R) (hxi : 0 < xi) (hH : 0 < H) :
    primeWidth R xi H C0*modelLength R xi H C0 ≤ 2*xi*R*H := by
  have hT := totalScale_pos R H C0 hH
  have hc : 0 ≤ interceptScale R C0 := div_nonneg (abs_nonneg _) hR.le
  have hcT : interceptScale R C0 ≤ totalScale R H C0 := le_max_right _ _
  have hw0 := primeWidth_pos R xi H C0 hR hxi hH
  have hcap := primeWidth_caps R xi H C0
  have hfirst := mul_le_mul_of_nonneg_right hcap.1 hH.le
  have hsecond : primeWidth R xi H C0*interceptScale R C0 ≤ R*H := by
    have hmul := (le_div_iff₀ hT).mp hcap.2
    have hmono := mul_le_mul_of_nonneg_left hcT hw0.le
    linarith
  have hsecond' := mul_le_mul_of_nonneg_left hsecond hxi.le
  dsimp [modelLength]
  nlinarith

end ErdosVarianceSmallModel

end

section

namespace ErdosVarianceSmallModel

theorem reciprocal_bin_range (R xi C0 p : ℝ) (hR : 0 < R) (_hxi : 0 ≤ xi)
    (hp : R < p) (hpU : p ≤ (1+xi)*R) :
    min (C0/R) (C0/((1+xi)*R)) ≤ C0/p ∧ C0/p ≤ max (C0/R) (C0/((1+xi)*R)) := by
  have hpp : 0 < p := hR.trans hp
  have hu : 1/((1+xi)*R) ≤ 1/p := one_div_le_one_div_of_le hpp hpU
  have hl : 1/p ≤ 1/R := one_div_le_one_div_of_le hR hp.le
  rcases le_total 0 C0 with hC | hC
  · have h1 : C0/((1+xi)*R) ≤ C0/p := by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hu hC
    have h2 : C0/p ≤ C0/R := by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hl hC
    exact ⟨(min_le_right _ _).trans h1,h2.trans (le_max_left _ _)⟩
  · have h1 : C0/p ≤ C0/((1+xi)*R) := by simpa only [mul_one_div] using mul_le_mul_of_nonpos_left hu hC
    have h2 : C0/R ≤ C0/p := by simpa only [mul_one_div] using mul_le_mul_of_nonpos_left hl hC
    exact ⟨(min_le_left _ _).trans h2,h1.trans (le_max_right _ _)⟩

theorem reciprocal_bin_spread (R xi C0 : ℝ) (hR : 0 < R) (hxi : 0 ≤ xi) :
    |C0/R-C0/((1+xi)*R)| ≤ xi*interceptScale R C0 := by
  have hden : 0 < (1+xi)*R := by positivity
  have he : C0/R-C0/((1+xi)*R) = C0*xi/((1+xi)*R) := by field_simp <;> ring
  rw [he,abs_div,abs_mul,abs_of_nonneg hxi,abs_of_pos hden]
  calc
    _ ≤ |C0| * xi/R := div_le_div_of_nonneg_left (mul_nonneg (abs_nonneg _) hxi) hR (by nlinarith)
    _ = _ := by dsimp [interceptScale] <;> ring

theorem moving_interval_enclosure (R xi H C0 p m : ℝ) (hR : 0 < R) (hxi : 0 ≤ xi)
    (hp : R < p) (hpU : p ≤ (1+xi)*R) (hm : C0/p ≤ m ∧ m < C0/p+H) :
    modelLeft R xi C0 ≤ m ∧ m < modelRight R xi H C0 := by
  have hr := reciprocal_bin_range R xi C0 p hR hxi hp hpU
  have hs := reciprocal_bin_spread R xi C0 hR hxi
  have hspread : max (C0/R) (C0/((1+xi)*R))-min (C0/R) (C0/((1+xi)*R)) ≤ xi*interceptScale R C0 := by
    rw [max_sub_min_eq_abs]
    simpa only [abs_sub_comm (C0/R) (C0/((1+xi)*R))] using hs
  refine ⟨hr.1.trans hm.1,?_⟩
  dsimp only [modelRight,modelLeft,modelLength]
  linarith [hm.2,hr.2]

theorem mem_modelIntegers (R xi H C0 : ℝ) (m : ℤ) :
    m ∈ modelIntegers R xi H C0 ↔ modelLeft R xi C0 ≤ (m : ℝ) ∧ (m : ℝ) < modelRight R xi H C0 := by
  simp only [modelIntegers,Finset.mem_Ico,Int.ceil_le,Int.lt_ceil]

end ErdosVarianceSmallModel

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_PositionDensities
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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

theorem positionResidues_le_modulus (S : Finset ℕ) (p : ℕ) [NeZero p] : (positionResidues S p).card ≤ p := by
  have hh := Finset.card_le_univ (positionResidues S p)
  simpa only [ZMod.card] using hh

end ErdosVarianceMoments

end

section

namespace ErdosVarianceMoments
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

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

namespace ErdosVarianceSmallModel
open NumberTheoryLean ErdosInverseEuler ErdosHyperbolaError
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem pattern_moduli_product (w : ℝ) (H : ℕ) :
    divisorModulus w H*coprimeModulus w H = smallModulus w := by
  unfold divisorModulus coprimeModulus divisorPrimes coprimePrimes
  rw [Finset.prod_filter_mul_prod_filter_not]
  rfl

theorem pattern_totient (w : ℝ) (H : ℕ) :
    (H*divisorModulus w H*coprimeModulus w H).totient =
      H.totient*divisorModulus w H*(coprimeModulus w H).totient := by
  rw [Nat.totient_mul (effective_pattern_coprime w H),
    source_totient_product H (divisorModulus w H) (divisorModulus_dvd_H w H) (divisorModulus_pos w H)]
  ring

theorem pattern_modulus_size (w : ℝ) (H : ℕ) :
    H*divisorModulus w H*coprimeModulus w H = H*smallModulus w := by
  rw [Nat.mul_assoc,pattern_moduli_product]

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

theorem mem_modelUniverse (R xi w : ℝ) (H : ℕ) (C0 : ℤ) (v : ModelPoint w H) :
    v ∈ modelUniverse R xi w H C0 ↔
      modelLeft R xi (C0 : ℝ) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < modelRight R xi (H : ℝ) (C0 : ℝ) ∧
        v.1.natAbs.Coprime H := by
  simp only [modelUniverse,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_univ,and_true,
    modelUnitIntegers,Finset.mem_filter,mem_modelIntegers,and_assoc]

end ErdosVarianceSmallModel

end

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



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ActualCofactorCellData
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosCofactorChoices
attribute [local instance] Classical.decEq

theorem mem_selections {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ) (f : ι → Finset ℕ) :
    f ∈ selections P m ↔ ∀ i, f i ⊆ P i ∧ (f i).card = m i := by
  simp only [selections, Fintype.mem_piFinset, Finset.mem_powersetCard]

end ErdosCofactorChoices

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_SourceLabelCount
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseCells
open ErdosInverseHits ErdosGeometricValueCells
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

theorem cofactorHit_eq (q : ℕ) (hq : Squarefree q) (a : ℕ → ℕ) :
    cofactorHit q a = primeHitRepresentative q hq a := by simp only [cofactorHit,dite_eq_left hq]

theorem cofactorHit_spec (q : ℕ) (hq : Squarefree q) (a : ℕ → ℕ) :
    1 ≤ cofactorHit q a ∧ cofactorHit q a ≤ q ∧
      ∀ p ∈ q.primeFactors,cofactorHit q a%p = a p%p := by
  rw [cofactorHit_eq q hq a]
  have hh := primeHitRepresentative_spec q hq a
  exact ⟨hh.1,hh.2.1,(hh.2.2 _).mpr (Nat.ModEq.refl _)⟩

end ErdosInverseCells

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_AlignedCofactorSplit
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceEffective
open ErdosInverseAlignment ErdosPrimitiveIntercept ErdosInverseCells
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem badPrimeProduct_pos (a : ℕ → ℤ) (r : ℚ) (qf : ℕ) : 0 < badPrimeProduct a r qf :=
  Finset.prod_pos (fun _p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos)

theorem aligned_bad_product (a : ℕ → ℤ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    alignedPrimeProduct a r qf*badPrimeProduct a r qf = qf := by
  rw [alignedPrimeProduct,alignedPrimeFactors,badPrimeProduct,badPrimeFactors,
    Finset.prod_filter_mul_prod_filter_not,Nat.prod_primeFactors_of_squarefree hq]

theorem alignedCofactor_eq_product (a : ℕ → ℤ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    alignedCofactor a r qf = alignedPrimeProduct a r qf := by
  unfold alignedCofactor
  nth_rw 1 [← aligned_bad_product a r qf hq]
  exact Nat.mul_div_cancel _ (badPrimeProduct_pos a r qf)

theorem alignedCofactor_mul_bad (a : ℕ → ℤ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    alignedCofactor a r qf*badPrimeProduct a r qf = qf := by
  rw [alignedCofactor_eq_product a r qf hq]
  exact aligned_bad_product a r qf hq

end ErdosVarianceEffective

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_EffectiveNumerator
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceEffective
open ErdosInverseAlignment ErdosPrimitiveIntercept ErdosInverseCells
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem prime_dvd_hitNumerator_iff (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (p : ℕ) (hp : p ∈ qf.primeFactors) :
    (p : ℤ) ∣ hitNumerator a r qf ↔ aligns (fun t => (a t : ℤ)) r p := by
  have hclass : (cofactorHit qf a : ZMod p) = (a p : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr ((cofactorHit_spec qf hq a).2.2 p hp)
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [hitNumerator,Int.cast_sub,Int.cast_mul,Int.cast_natCast,hclass,sub_eq_zero,aligns]

theorem alignedCofactor_dvd_hitNumerator (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    (alignedCofactor (fun t => (a t : ℤ)) r qf : ℤ) ∣ hitNumerator a r qf := by
  apply Int.natCast_dvd.mpr
  rw [alignedCofactor_eq_product _ r qf hq]
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).prime
  · intro p hp
    obtain ⟨hpf,halign⟩ := Finset.mem_filter.mp hp
    exact Int.natCast_dvd.mp ((prime_dvd_hitNumerator_iff a r qf hq p hpf).mpr halign)

theorem hitNumerator_coprime_den (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) :
    (hitNumerator a r qf).natAbs.Coprime r.den := by
  apply Nat.coprime_of_dvd
  intro p hp hpN hpD
  have hD0 : (r.den : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpD
  have hN0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (Int.natCast_dvd.mpr hpN)
  have hA0 : (r.num : ZMod p) = 0 := by
    simpa only [hitNumerator,Int.cast_sub,Int.cast_mul,Int.cast_natCast,hD0,zero_mul,zero_sub,neg_eq_zero]
      using hN0
  have hpA : p ∣ r.num.natAbs := Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hA0)
  have hdiv := Nat.dvd_gcd hpA hpD
  rw [r.reduced.gcd_eq_one] at hdiv
  exact hp.not_dvd_one hdiv

theorem hitNumerator_coprime_bad (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    (hitNumerator a r qf).natAbs.Coprime (badPrimeProduct (fun t => (a t : ℤ)) r qf) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  obtain ⟨hpf,hnon⟩ := Finset.mem_filter.mp hp
  apply Nat.Coprime.symm
  apply (Nat.prime_of_mem_primeFactors hpf).coprime_iff_not_dvd.mpr
  intro hdiv
  exact hnon ((prime_dvd_hitNumerator_iff a r qf hq p hpf).mp (Int.natCast_dvd.mpr hdiv))

end ErdosVarianceEffective

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_EffectiveCoordinates
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceEffective
open ErdosInverseAlignment ErdosPrimitiveIntercept ErdosInverseCells

theorem effectiveModulus_pos (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) : 0 < effectiveModulus a r qf :=
  Nat.mul_pos r.pos (badPrimeProduct_pos _ r qf)

theorem effectiveIntercept_identity (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    (alignedCofactor (fun t => (a t : ℤ)) r qf : ℤ)*effectiveIntercept a r qf = hitNumerator a r qf := by
  rw [effectiveIntercept,mul_comm]
  exact Int.ediv_mul_cancel (alignedCofactor_dvd_hitNumerator a r qf hq)

theorem hitNumerator_coprime_effectiveModulus (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    (hitNumerator a r qf).natAbs.Coprime (effectiveModulus a r qf) :=
  (hitNumerator_coprime_den a r qf).mul_right (hitNumerator_coprime_bad a r qf hq)

theorem effectiveIntercept_coprime (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    (effectiveIntercept a r qf).natAbs.Coprime (effectiveModulus a r qf) := by
  have hdiv : effectiveIntercept a r qf ∣ hitNumerator a r qf := by
    refine ⟨(alignedCofactor (fun t => (a t : ℤ)) r qf : ℤ),?_⟩
    rw [mul_comm]
    exact (effectiveIntercept_identity a r qf hq).symm
  exact (hitNumerator_coprime_effectiveModulus a r qf hq).of_dvd_left
    (Int.natAbs_dvd_natAbs.mpr hdiv)

theorem effective_coordinates_gcd (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    Int.gcd (effectiveIntercept a r qf) (effectiveModulus a r qf : ℤ) = 1 := by
  simpa only [Int.gcd_def,Int.natAbs_natCast] using (effectiveIntercept_coprime a r qf hq).gcd_eq_one

theorem denominator_full_cofactor (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    r.den*qf = alignedCofactor (fun t => (a t : ℤ)) r qf*effectiveModulus a r qf := by
  calc
    _ = r.den*(alignedCofactor (fun t => (a t : ℤ)) r qf*badPrimeProduct (fun t => (a t : ℤ)) r qf) :=
      congrArg (fun x : ℕ => r.den*x) (alignedCofactor_mul_bad (fun t => (a t : ℤ)) r qf hq).symm
    _ = _ := by unfold effectiveModulus;ring

end ErdosVarianceEffective

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_EffectiveProgression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceEffective
open ErdosInverseCells ErdosInverseHits ErdosHypotheticalTag ErdosAlignedProgression

theorem effective_den_coprime_prime (a : ℕ → ℕ) (r : ℚ) (qf p : ℕ)
    (hHp : (effectiveModulus a r qf).Coprime p) : r.den.Coprime p :=
  hHp.of_dvd_left (dvd_mul_right _ _)

theorem effective_initial_identity (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (p : ℕ) [NeZero p] (hHp : (effectiveModulus a r qf).Coprime p) :
    (r.den : ℤ)*((cofactorHit qf a : ℤ)+(qf : ℤ)*
      (intervalK p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf) : ℤ)) =
      r.num+(alignedCofactor (fun t => (a t : ℤ)) r qf : ℤ)*(p : ℤ)*
        intervalM0 p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf) := by
  have hN := effectiveIntercept_identity a r qf hq
  unfold hitNumerator at hN
  have hD : (r.den : ℤ)*(qf : ℤ) =
      (alignedCofactor (fun t => (a t : ℤ)) r qf : ℤ)*(effectiveModulus a r qf : ℤ) := by
    exact_mod_cast denominator_full_cofactor a r qf hq
  have hm := intervalM0_identity p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf)
  linear_combination -hN+
    (intervalK p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf) : ℤ)*hD-
    (alignedCofactor (fun t => (a t : ℤ)) r qf : ℤ)*hm

theorem effective_progression_identity (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (p : ℕ) [NeZero p] (hHp : (effectiveModulus a r qf).Coprime p) (j : ℤ) :
    (r.den : ℤ)*((cofactorHit qf a : ℤ)+(qf : ℤ)*
      ((intervalK p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf) : ℤ)+(p : ℤ)*j)) =
      r.num+(alignedCofactor (fun t => (a t : ℤ)) r qf : ℤ)*(p : ℤ)*
        (intervalM0 p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf)+
          (effectiveModulus a r qf : ℤ)*j) := by
  have hb := effective_initial_identity a r qf hq p hHp
  have hD : (r.den : ℤ)*(qf : ℤ) =
      (alignedCofactor (fun t => (a t : ℤ)) r qf : ℤ)*(effectiveModulus a r qf : ℤ) := by
    exact_mod_cast denominator_full_cofactor a r qf hq
  linear_combination hb+(p : ℤ)*j*hD

end ErdosVarianceEffective

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_EffectiveAvoidance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceEffective
open ErdosInverseCells

theorem effectiveInteger_nat_coordinate (a : ℕ → ℕ) (r : ℚ) (qf p : ℕ) [NeZero p]
    (hHp : (effectiveModulus a r qf).Coprime p) (j : ℕ) :
    ((effectiveBase a r qf p hHp+p*qf*j : ℕ) : ℤ) = effectiveInteger a r qf p hHp (j : ℤ) := by
  simp only [effectiveBase,effectiveInteger,Nat.cast_add,Nat.cast_mul]
  ring

theorem effective_avoidance_not_dvd (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (p : ℕ) [NeZero p] (hHp : (effectiveModulus a r qf).Coprime p)
    (t : ℕ) (ht : t.Prime) (htH : ¬t ∣ effectiveModulus a r qf) (j : ℤ) :
    (effectiveInteger a r qf p hHp j : ZMod t) ≠ (a t : ZMod t) ↔
      (p : ZMod t)*(alignedCofactor (fun u => (a u : ℤ)) r qf : ZMod t)*
        ((intervalM0 p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf) : ZMod t)+
          (effectiveModulus a r qf : ZMod t)*(j : ZMod t)) ≠
        (r.den : ZMod t)*(a t : ZMod t)-(r.num : ZMod t) := by
  let : Fact t.Prime := ⟨ht⟩
  have hDH := effective_den_coprime_prime a r qf t (ht.coprime_iff_not_dvd.mpr htH).symm
  have hD0 : (r.den : ZMod t) ≠ 0 := by
    intro he
    exact (ht.coprime_iff_not_dvd.mp hDH.symm) ((ZMod.natCast_eq_zero_iff _ _).mp he)
  have hid : (r.den : ZMod t)*(effectiveInteger a r qf p hHp j : ZMod t) =
      (r.num : ZMod t)+(p : ZMod t)*(alignedCofactor (fun u => (a u : ℤ)) r qf : ZMod t)*
        ((intervalM0 p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf) : ZMod t)+
          (effectiveModulus a r qf : ZMod t)*(j : ZMod t)) := by
    have he := congrArg (fun z : ℤ => (z : ZMod t)) (effective_progression_identity a r qf hq p hHp j)
    simpa only [effectiveInteger,Int.cast_add,Int.cast_mul,Int.cast_natCast,mul_comm (p : ZMod t)] using he
  apply not_congr
  constructor
  · intro he
    rw [he] at hid
    linear_combination -hid
  · intro he
    apply mul_left_cancel₀ hD0
    linear_combination hid+he

theorem effective_avoidance_unit (a : ℕ → ℕ) (r : ℚ) (qf p : ℕ) [NeZero p]
    (hHp : (effectiveModulus a r qf).Coprime p) (t : ℕ) (hqt : qf.Coprime t) (j : ℤ) :
    (effectiveInteger a r qf p hHp j : ZMod t) ≠ (a t : ZMod t) ↔
      ((intervalK p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf) : ℕ) : ZMod t)+
        (p : ZMod t)*(j : ZMod t) ≠
        ((a t : ZMod t)-(cofactorHit qf a : ZMod t))*(↑((ZMod.unitOfCoprime qf hqt)⁻¹) : ZMod t) := by
  let v := ZMod.unitOfCoprime qf hqt
  have hu : (qf : ZMod t)*(↑(v⁻¹) : ZMod t) = 1 := by
    simpa only [v,ZMod.coe_unitOfCoprime] using v.mul_inv
  simp only [effectiveInteger,Int.cast_add,Int.cast_mul,Int.cast_natCast]
  apply not_congr
  constructor
  · intro he
    have hh := congrArg (fun x : ZMod t => x*(↑(v⁻¹) : ZMod t)) he
    linear_combination hh-
      ((intervalK p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf) : ZMod t)+(p : ZMod t)*(j : ZMod t))*hu
  · intro he
    have hh := congrArg (fun x : ZMod t => (qf : ZMod t)*x) he
    linear_combination hh+((a t : ZMod t)-(cofactorHit qf a : ZMod t))*hu

end ErdosVarianceEffective

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_SmallEffectivePrimeSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceEffective
open ErdosPrimitiveIntercept

theorem full_cofactor_coprime_small (qf : ℕ) (hq : Squarefree qf) (w : ℝ)
    (hlarge : ∀ u ∈ qf.primeFactors,w < (u : ℝ)) (t : ℕ) (ht : t.Prime) (htw : (t : ℝ) ≤ w) :
    qf.Coprime t := by
  apply Nat.Coprime.symm
  apply ht.coprime_iff_not_dvd.mpr
  intro hdiv
  have hh := hlarge t (Nat.mem_primeFactors.mpr ⟨ht,hdiv,hq.ne_zero⟩)
  linarith

end ErdosVarianceEffective

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ActualPatternClass
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

theorem actual_pattern_class (w : ℝ) (H : ℕ) [NeZero H] (C0 : ℤ)
    (hC0 : Int.gcd C0 (H : ℤ) = 1) (m : ℤ) (hm : m.natAbs.Coprime H)
    (s : Pattern w H) (p k : ℕ)
    (hEquation : (p : ℤ)*m = C0+(H : ℤ)*(k : ℤ))
    (hp1 : (p : ZMod (coprimeModulus w H)) = (s.1 : ZMod (coprimeModulus w H)))
    (hk0 : (k : ZMod (divisorModulus w H)) = s.2) :
    Int.ModEq ((H*divisorModulus w H*coprimeModulus w H : ℕ) : ℤ)
      (p : ℤ) (patternClass w H C0 hC0 m hm s : ℤ) := by
  have hkNat : Nat.ModEq (divisorModulus w H) k s.2.val := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    rw [ZMod.natCast_zmod_val]
    exact hk0
  have hkInt := Int.natCast_modEq_iff.mpr hkNat
  have hlift : Int.ModEq ((H : ℤ)*(divisorModulus w H : ℤ))
      ((H : ℤ)*(k : ℤ)) ((H : ℤ)*(s.2.val : ℤ)) := hkInt.mul_left'
  have hpm : Int.ModEq ((H*divisorModulus w H : ℕ) : ℤ) ((p : ℤ)*m)
      (C0+(H : ℤ)*(s.2.val : ℤ)) := by
    simpa only [Nat.cast_mul,← hEquation] using hlift.add_left C0
  have hpmZ : (p : ZMod (H*divisorModulus w H))*(m : ZMod (H*divisorModulus w H)) =
      (liftedNumeratorUnit w H C0 hC0 s.2 : ZMod (H*divisorModulus w H)) := by
    simpa only [liftedNumeratorUnit,ZMod.coe_unitOfIsCoprime,Int.cast_mul,Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff _ _ _).mpr hpm
  have hminv : (m : ZMod (H*divisorModulus w H))*
      (↑((coordinateUnit w H m hm)⁻¹) : ZMod (H*divisorModulus w H)) = 1 := by
    simpa only [coordinateUnit,ZMod.coe_unitOfIsCoprime] using (coordinateUnit w H m hm).mul_inv
  have hmul := congrArg (fun x : ZMod (H*divisorModulus w H) =>
    x*(↑((coordinateUnit w H m hm)⁻¹) : ZMod (H*divisorModulus w H))) hpmZ
  have hpUnit : (p : ZMod (H*divisorModulus w H)) =
      (restrictionUnit w H C0 hC0 m hm s.2 : ZMod (H*divisorModulus w H)) := by
    simpa only [mul_assoc,hminv,mul_one,restrictionUnit,Units.val_mul] using hmul
  have hp0 : Nat.ModEq (H*divisorModulus w H) p (restrictionUnit w H C0 hC0 m hm s.2).val.val := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    rw [ZMod.natCast_zmod_val]
    exact hpUnit
  have hp1' : Nat.ModEq (coprimeModulus w H) p s.1.val.val := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    rw [ZMod.natCast_zmod_val]
    exact hp1
  exact Int.natCast_modEq_iff.mpr (Nat.chineseRemainder_modEq_unique (effective_pattern_coprime w H) hp0 hp1')

end ErdosVarianceSmallModel

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

theorem primeM_bounds (P : Finset ℕ) (H : ℕ) (C0 : ℤ) (hP : ∀ p ∈ P,p.Prime) (hH : 0 < H)
    (p : goodPrimes P H) :
    (C0 : ℝ)/(p.val : ℝ) ≤ (primeM P H C0 hP p : ℝ) ∧
      (primeM P H C0 hP p : ℝ) < (C0 : ℝ)/(p.val : ℝ)+(H : ℝ) := by
  let : NeZero p.val := ⟨(hP _ (Finset.mem_filter.mp p.property).1).ne_zero⟩
  exact intervalM0_bounds p.val H (Finset.mem_filter.mp p.property).2 C0 hH

theorem primeM_coprime (P : Finset ℕ) (H : ℕ) (C0 : ℤ) (hP : ∀ p ∈ P,p.Prime)
    (hC0 : Int.gcd C0 (H : ℤ) = 1) (p : goodPrimes P H) :
    (primeM P H C0 hP p).natAbs.Coprime H := by
  apply Nat.coprime_of_dvd
  intro t ht htm htH
  have htm' : (t : ℤ) ∣ primeM P H C0 hP p := Int.natCast_dvd.mpr htm
  have htH' : (t : ℤ) ∣ (H : ℤ) := by exact_mod_cast htH
  have hsub := dvd_sub (dvd_mul_of_dvd_right htm' (p.val : ℤ))
    (dvd_mul_of_dvd_left htH' (primeK P H C0 hP p : ℤ))
  rw [primeMK_identity,add_sub_cancel_right] at hsub
  have hdiv := Nat.dvd_gcd (Int.natCast_dvd.mp hsub) htH
  have hg : Nat.gcd C0.natAbs H = 1 := by simpa only [Int.gcd_def,Int.natAbs_natCast] using hC0
  rw [hg] at hdiv
  exact ht.not_dvd_one hdiv

theorem primePoint_mem_model (P : Finset ℕ) (R xi w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (hR : 0 < R) (hxi : 0 ≤ xi) (hH : 0 < H) (hC0 : Int.gcd C0 (H : ℤ) = 1)
    (hbin : ∀ p ∈ P,R < (p : ℝ) ∧ (p : ℝ) ≤ (1+xi)*R) (p : goodPrimes P H) :
    primePoint P w H C0 hw hP hlarge p ∈ modelUniverse R xi w H C0 := by
  have hpP := (Finset.mem_filter.mp p.property).1
  have hm := moving_interval_enclosure R xi (H : ℝ) (C0 : ℝ) (p.val : ℝ)
    (primeM P H C0 hP p) hR hxi (hbin _ hpP).1 (hbin _ hpP).2 (primeM_bounds P H C0 hP hH p)
  apply (mem_modelUniverse R xi w H C0 _).mpr
  exact ⟨hm.1,hm.2,primeM_coprime P H C0 hP hC0 p⟩

end ErdosVarianceSmallModel

end

section

namespace ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem primeFibre_image_subset (P : Finset ℕ) (w : ℝ) (H : ℕ) [NeZero H] (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (hC0 : Int.gcd C0 (H : ℤ) = 1) (v : ModelPoint w H) (hm : v.1.natAbs.Coprime H) :
    (primeFibre P w H C0 hw hP hlarge v).image Subtype.val ⊆
      residueFibre P (H : ℝ) (C0 : ℝ) v.1 (H*divisorModulus w H*coprimeModulus w H)
        (patternClass w H C0 hC0 v.1 hm v.2 : ℤ) := by
  intro q hq
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
  have he := (Finset.mem_filter.mp hp).2
  have hpm : primeM P H C0 hP p = v.1 := congrArg Prod.fst he
  have hp1 : (p.val : ZMod (coprimeModulus w H)) = (v.2.1 : ZMod (coprimeModulus w H)) := by
    simpa only [primePoint,ZMod.coe_unitOfCoprime] using
      congrArg (fun z : ModelPoint w H => (z.2.1 : ZMod (coprimeModulus w H))) he
  have hk0 : (primeK P H C0 hP p : ZMod (divisorModulus w H)) = v.2.2 :=
    congrArg (fun z : ModelPoint w H => z.2.2) he
  have hEquation : (p.val : ℤ)*v.1 = C0+(H : ℤ)*(primeK P H C0 hP p : ℤ) := by
    rw [← hpm]
    exact primeMK_identity P H C0 hP p
  have hbounds := primeM_bounds P H C0 hP (Nat.pos_of_ne_zero (NeZero.ne H)) p
  rw [hpm] at hbounds
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp p.property).1,hbounds⟩,?_⟩
  exact actual_pattern_class w H C0 hC0 v.1 hm v.2 p.val (primeK P H C0 hP p) hEquation hp1 hk0

theorem primeFibre_card_le_residue (P : Finset ℕ) (w : ℝ) (H : ℕ) [NeZero H] (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (hC0 : Int.gcd C0 (H : ℤ) = 1) (v : ModelPoint w H) (hm : v.1.natAbs.Coprime H) :
    (primeFibre P w H C0 hw hP hlarge v).card ≤
      (residueFibre P (H : ℝ) (C0 : ℝ) v.1 (H*divisorModulus w H*coprimeModulus w H)
        (patternClass w H C0 hC0 v.1 hm v.2 : ℤ)).card := by
  calc
    _ = ((primeFibre P w H C0 hw hP hlarge v).image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ _ := Finset.card_le_card (primeFibre_image_subset P w H C0 hw hP hlarge hC0 v hm)

end ErdosVarianceSmallModel

end

section

namespace ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem actualPrimeEvent_card (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (E : ModelPoint w H → Prop) :
    (actualPrimeEvent P w H C0 hw hP hlarge E).card = (indexedPrimeEvent P w H C0 hw hP hlarge E).card :=
  Finset.card_image_of_injective _ Subtype.val_injective

theorem actualPrimeEvent_card_fibres (P : Finset ℕ) (R xi w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (hR : 0 < R) (hxi : 0 ≤ xi) (hH : 0 < H) (hC0 : Int.gcd C0 (H : ℤ) = 1)
    (hbin : ∀ p ∈ P,R < (p : ℝ) ∧ (p : ℝ) ≤ (1+xi)*R) (E : ModelPoint w H → Prop) :
    (actualPrimeEvent P w H C0 hw hP hlarge E).card =
      ∑ v ∈ (modelUniverse R xi w H C0).filter E,(primeFibre P w H C0 hw hP hlarge v).card := by
  rw [actualPrimeEvent_card]
  have hmaps : (indexedPrimeEvent P w H C0 hw hP hlarge E : Set (goodPrimes P H)).MapsTo
      (primePoint P w H C0 hw hP hlarge) ((modelUniverse R xi w H C0).filter E) := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨primePoint_mem_model P R xi w H C0 hw hP hlarge hR hxi hH hC0 hbin p,
      (Finset.mem_filter.mp hp).2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro v hv
  congr 1
  ext p
  simp only [indexedPrimeEvent,primeFibre,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · exact fun hh => hh.2
  · intro he
    exact ⟨he.symm ▸ (Finset.mem_filter.mp hv).2,he⟩

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

theorem prime_divisorPhase_eq (P : Finset ℕ) (H : ℕ) (C0 : ℤ) (hP : ∀ p ∈ P,p.Prime)
    (hC0 : Int.gcd C0 (H : ℤ) = 1) (p : goodPrimes P H) (t : ℕ) (htH : t ∣ H) :
    (p.val : ZMod t) = divisorPhase C0 (primeM P H C0 hP p) t := by
  have hm := (primeM_coprime P H C0 hP hC0 p).of_dvd_right htH
  have hminv := ZMod.coe_int_mul_inv_eq_one (int_isCoprime_of_natAbs _ t hm)
  have hH0 : (H : ZMod t) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr htH
  have he := congrArg (fun n : ℤ => (n : ZMod t)) (primeMK_identity P H C0 hP p)
  have hEq : (p.val : ZMod t)*(primeM P H C0 hP p : ZMod t) = (C0 : ZMod t) := by
    simpa only [Int.cast_mul,Int.cast_natCast,Int.cast_add,hH0,zero_mul,add_zero] using he
  have hh := congrArg (fun x : ZMod t => x*(primeM P H C0 hP p : ZMod t)⁻¹) hEq
  simpa only [mul_assoc,hminv,mul_one,divisorPhase] using hh

theorem primePoint_pValue (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (p : goodPrimes P H) (t : ℕ) (ht : t ∣ coprimeModulus w H) :
    patternPValue w H (primePoint P w H C0 hw hP hlarge p).2 t = (p.val : ZMod t) := by
  exact cast_nat_residue (coprimeModulus w H) t p.val ht

theorem primePoint_kValue (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (p : goodPrimes P H) (t : ℕ) (ht : t ∣ divisorModulus w H) :
    patternKValue w H (primePoint P w H C0 hw hP hlarge p).2 t = (primeK P H C0 hP p : ZMod t) := by
  exact cast_nat_residue (divisorModulus w H) t (primeK P H C0 hP p) ht

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

namespace ErdosVarianceCommon
open NumberTheoryLean ErdosVarianceEffective ErdosInverseCounts ErdosHypotheticalTag
  ErdosInverseHits ErdosInverseTail
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem mem_commonSurvivors (J : ℕ) (w : ℝ) (a : ℕ → ℕ) (r : ℚ)
    (qf p : ℕ) [NeZero p] (hHp : (effectiveModulus a r qf).Coprime p) (j : ℕ) :
    j ∈ commonSurvivors J w a r qf p hHp ↔ j < J ∧
      ∀ t ∈ LargePrimeDeletion.cutoffPrimes ⌊w⌋₊,
        (effectiveInteger a r qf p hHp (j : ℤ) : ZMod t) ≠ (a t : ZMod t) := by
  simp only [commonSurvivors,ProgressionSmallSieve.progressionSurvivors,SievePartition.mem_survivors,
    Finset.mem_range,ProgressionSmallSieve.progressionHit]
  apply and_congr_right
  intro _hj
  apply forall_congr'
  intro t
  apply forall_congr'
  intro _ht
  rw [← Nat.cast_mul,← Nat.cast_add,effectiveInteger_nat_coordinate,← ZMod.intCast_eq_intCast_iff]
  simp only [Int.cast_natCast]

end ErdosVarianceCommon

end

section

namespace ErdosVarianceMoments
open ErdosVarianceSmallModel ErdosVarianceEffective ErdosInverseCells ErdosPrimitiveIntercept ErdosInverseAlignment

theorem aligned_isolated_coprime_effective (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (p : ℕ) (hp : p.Prime) (hqp : qf.Coprime p) (halign : aligns (fun t => (a t : ℤ)) r p) :
    (effectiveModulus a r qf).Coprime p := by
  have hD := ErdosAlignedProgression.aligned_den_coprime_prime a r p hp halign
  have hd : badPrimeProduct (fun t => (a t : ℤ)) r qf ∣ qf := by
    refine ⟨alignedCofactor (fun t => (a t : ℤ)) r qf,?_⟩
    simpa only [mul_comm] using (alignedCofactor_mul_bad (fun t => (a t : ℤ)) r qf hq).symm
  exact hD.mul_left (hqp.of_dvd_left hd)

theorem aligned_coefficient_coprime_small (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (w : ℝ) (hlarge : ∀ u ∈ qf.primeFactors,w < (u : ℝ)) (t : ℕ) (ht : t.Prime) (htw : (t : ℝ) ≤ w) :
    (alignedCofactor (fun u => (a u : ℤ)) r qf).Coprime t := by
  have hd : alignedCofactor (fun u => (a u : ℤ)) r qf ∣ qf :=
    ⟨badPrimeProduct (fun u => (a u : ℤ)) r qf,(alignedCofactor_mul_bad (fun u => (a u : ℤ)) r qf hq).symm⟩
  exact (full_cofactor_coprime_small qf hq w hlarge t ht htw).of_dvd_left hd

end ErdosVarianceMoments

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

theorem weight_sum (w : ℝ) (H : ℕ) : (∑ _v : FullPattern w H,weight w H)=1 := by
  have hT0 : (divisorModulus w H : ℝ) ≠ 0 := by exact_mod_cast (divisorModulus_pos w H).ne'
  have hT1 : (coprimeModulus w H : ℝ) ≠ 0 := by exact_mod_cast (coprimeModulus_pos w H).ne'
  have hP0 : ((divisorModulus w H).totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (divisorModulus_pos w H)).ne'
  have hP1 : ((coprimeModulus w H).totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (coprimeModulus_pos w H)).ne'
  simp only [Finset.sum_const,Finset.card_univ,pattern_card,nsmul_eq_mul,Nat.cast_mul,weight]
  field_simp

theorem indicator_binary (w : ℝ) (H qA : ℕ) (beta delta : ∀ t : ℕ,ZMod t)
    (j : ℕ) (v : FullPattern w H) : indicator w H qA beta delta j v=0 ∨ indicator w H qA beta delta j v=1 := by
  unfold indicator
  split_ifs <;> simp

theorem count_eq_indicator_sum (w : ℝ) (H qA J : ℕ) (beta delta : ∀ t : ℕ,ZMod t)
    (v : FullPattern w H) : (survivorCount w H qA J beta delta v : ℝ)=
      ∑ j ∈ Finset.range J,indicator w H qA beta delta j v := by
  simp only [survivorCount,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,indicator]

end ErdosLargePatternLaw



namespace ErdosLargePatternLaw
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceMoments

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem projectedUnit_coe (M t : ℕ) [NeZero M] (ht : t ∣ M) (p : (ZMod M)ˣ) :
    (projectedUnit M t ht p : ZMod t) = (p.val.val : ZMod t) := by
  change ZMod.castHom ht (ZMod t) p.val = _
  calc
    ZMod.castHom ht (ZMod t) p.val =
        ZMod.castHom ht (ZMod t) (p.val.val : ZMod M) :=
      congrArg (ZMod.castHom ht (ZMod t)) (ZMod.natCast_zmod_val p.val).symm
    _ = _ := map_natCast (ZMod.castHom ht (ZMod t)) p.val.val

theorem joint_condition_split (w : ℝ) (H qA : ℕ) (beta delta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (p0 : (ZMod (divisorModulus w H))ˣ) (k0 : ZMod (divisorModulus w H))
    (p1 : (ZMod (coprimeModulus w H))ˣ) (m1 : ZMod (coprimeModulus w H)) :
    jointCondition w H qA beta delta S (p0,k0,p1,m1) ↔
      divisorCondition w H beta S p0 k0 ∧ coprimeCondition w H qA delta S p1 m1 := by
  constructor
  · intro h
    exact ⟨fun t ht j hj => (h j hj).1 t ht,fun t ht j hj => (h j hj).2 t ht⟩
  · rintro ⟨h0,h1⟩ j hj
    exact ⟨fun t ht => h0 t ht j hj,fun t ht => h1 t ht j hj⟩

theorem divisor_condition_card (w : ℝ) (H : ℕ) (beta : ∀ t : ℕ,ZMod t) (S : Finset ℕ)
    (p0 : (ZMod (divisorModulus w H))ˣ) :
    (Finset.univ.filter (divisorCondition w H beta S p0)).card =
      ∏ t ∈ divisorPrimes w H,(t-(positionResidues S t).card) := by
  let u (t : ℕ) : (ZMod t)ˣ :=
    if ht : t ∈ divisorPrimes w H then projectedUnit (divisorModulus w H) t (Finset.dvd_prod_of_mem _ ht) p0 else 1
  have hu (t : ℕ) (ht : t ∈ divisorPrimes w H) : (u t : ZMod t)=(p0.val.val : ZMod t) := by
    dsimp only [u]
    rw [dite_eq_left ht]
    exact projectedUnit_coe (divisorModulus w H) t (Finset.dvd_prod_of_mem _ ht) p0
  have hP (t : ℕ) (ht : t ∈ divisorPrimes w H) : t.Prime :=
    (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1
  let : NeZero (∏ t ∈ divisorPrimes w H,t) := ⟨(divisorModulus_pos w H).ne'⟩
  have hh := prime_unit_avoidance_card (divisorPrimes w H) S hP u beta
  have he : Finset.univ.filter (divisorCondition w H beta S p0) =
      Finset.univ.filter (fun k0 : ZMod (divisorModulus w H) =>
        ∀ t ∈ divisorPrimes w H,∀ j ∈ S,(k0.val : ZMod t)+(u t : ZMod t)*(j : ZMod t) ≠ beta t) := by
    apply Finset.filter_congr
    intro k0 _
    unfold divisorCondition
    exact forall_congr' (fun t => forall_congr' (fun ht => by rw [hu t ht]))
  rw [he]
  exact hh

theorem multiply_unit_iff (t : ℕ) (u : (ZMod t)ˣ) (x c : ZMod t) :
    (u : ZMod t)*x=c ↔ x=(↑(u⁻¹) : ZMod t)*c := by
  constructor
  · intro h
    have hh := congrArg (fun y : ZMod t => (↑(u⁻¹) : ZMod t)*y) h
    simpa only [← mul_assoc,Units.inv_mul,one_mul] using hh
  · intro h
    rw [h,← mul_assoc,Units.mul_inv,one_mul]

theorem coprime_condition_card (w : ℝ) (H qA : ℕ) (delta : ∀ t : ℕ,ZMod t) (S : Finset ℕ)
    (p1 : (ZMod (coprimeModulus w H))ˣ) (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t) :
    (Finset.univ.filter (coprimeCondition w H qA delta S p1)).card =
      ∏ t ∈ coprimePrimes w H,(t-(positionResidues S t).card) := by
  let u (t : ℕ) : (ZMod t)ˣ := if ht : t ∈ coprimePrimes w H then
      ZMod.unitOfCoprime H
        (((LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1.coprime_iff_not_dvd.mpr
          (Finset.mem_filter.mp ht).2).symm) else 1
  let coeff (t : ℕ) (ht : t ∈ coprimePrimes w H) : (ZMod t)ˣ :=
    projectedUnit (coprimeModulus w H) t (Finset.dvd_prod_of_mem _ ht) p1*ZMod.unitOfCoprime qA (hqA t ht)
  let c (t : ℕ) : ZMod t := if ht : t ∈ coprimePrimes w H then (↑((coeff t ht)⁻¹) : ZMod t)*delta t else 0
  have hu (t : ℕ) (ht : t ∈ coprimePrimes w H) : (u t : ZMod t)=(H : ZMod t) := by
    simp only [u,dite_eq_left ht,ZMod.coe_unitOfCoprime]
  have hc (t : ℕ) (ht : t ∈ coprimePrimes w H) :
      (coeff t ht : ZMod t)=(p1.val.val : ZMod t)*(qA : ZMod t) := by
    simp only [coeff,Units.val_mul,ZMod.coe_unitOfCoprime]
    exact congrArg (fun v : ZMod t => v*(qA : ZMod t))
      (projectedUnit_coe (coprimeModulus w H) t (Finset.dvd_prod_of_mem _ ht) p1)
  have hP (t : ℕ) (ht : t ∈ coprimePrimes w H) : t.Prime :=
    (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1
  let : NeZero (∏ t ∈ coprimePrimes w H,t) := ⟨(coprimeModulus_pos w H).ne'⟩
  have hh := prime_unit_avoidance_card (coprimePrimes w H) S hP u c
  have he : Finset.univ.filter (coprimeCondition w H qA delta S p1) =
      Finset.univ.filter (fun m1 : ZMod (coprimeModulus w H) =>
        ∀ t ∈ coprimePrimes w H,∀ j ∈ S,(m1.val : ZMod t)+(u t : ZMod t)*(j : ZMod t) ≠ c t) := by
    apply Finset.filter_congr
    intro m1 _
    unfold coprimeCondition
    apply forall_congr'
    intro t
    apply forall_congr'
    intro ht
    rw [hu t ht]
    apply forall_congr'
    intro j
    apply forall_congr'
    intro _hj
    simp only [c,dite_eq_left ht]
    rw [← hc t ht]
    exact not_congr (multiply_unit_iff t (coeff t ht) _ _)
  rw [he]
  exact hh

end ErdosLargePatternLaw


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_HarmonicConditioning
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseCells
open ErdosInverseSampling
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

theorem harmonicMass_nonneg (Q : Finset ℕ) : 0 ≤ harmonicMass Q := by unfold harmonicMass;positivity

end ErdosInverseCells

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

section

namespace ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem atomWeight_totient (R xi w : ℝ) (H : ℕ) (C0 : ℤ) :
    atomWeight R xi w H C0 = (H : ℝ)/
      (((H*divisorModulus w H*coprimeModulus w H).totient : ℝ)*modelLength R xi (H : ℝ) (C0 : ℝ)) := by
  rw [pattern_totient]
  simp only [atomWeight,Nat.cast_mul]
  congr 1
  ring

theorem prime_bound_le_atom (R xi w : ℝ) (H : ℕ) (C0 : ℤ) (n : ℕ) (C : ℝ)
    (hR : 1 < R) (hxi : 0 < xi) (hH : 0 < H) (hC : 0 ≤ C)
    (hPopulation : xi*R/(16*Real.log R) ≤ (n : ℝ)) :
    C*primeWidth R xi (H : ℝ) (C0 : ℝ)/
      (((H*divisorModulus w H*coprimeModulus w H).totient : ℝ)*Real.log R) ≤
      (32*C*(n : ℝ))*atomWeight R xi w H C0 := by
  have hRp : 0 < R := by linarith
  have hlog : 0 < Real.log R := Real.log_pos hR
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hM : 0 < H*divisorModulus w H*coprimeModulus w H :=
    Nat.mul_pos (Nat.mul_pos hH (divisorModulus_pos w H)) (coprimeModulus_pos w H)
  have hphi : (0 : ℝ) < (H*divisorModulus w H*coprimeModulus w H).totient := by
    exact_mod_cast Nat.totient_pos.mpr hM
  have hY : 0 < modelLength R xi (H : ℝ) (C0 : ℝ) := by
    dsimp [modelLength,interceptScale]
    positivity
  have hpop := (div_le_iff₀ (by positivity : 0 < 16*Real.log R)).mp hPopulation
  have harea := small_model_area R xi (H : ℝ) (C0 : ℝ) hRp hxi hHR
  have hpopH := mul_le_mul_of_nonneg_right hpop (show 0 ≤ 2*(H : ℝ) by positivity)
  have hwidth : primeWidth R xi (H : ℝ) (C0 : ℝ)*modelLength R xi (H : ℝ) (C0 : ℝ) ≤
      32*(n : ℝ)*Real.log R*(H : ℝ) := by nlinarith
  calc
    _ ≤ ((32*C*(n : ℝ))*(H : ℝ))/
        (((H*divisorModulus w H*coprimeModulus w H).totient : ℝ)*modelLength R xi (H : ℝ) (C0 : ℝ)) := by
      apply (div_le_div_iff₀ (mul_pos hphi hlog) (mul_pos hphi hY)).mpr
      have hh := mul_le_mul_of_nonneg_left hwidth
        (mul_nonneg hC (hphi.le))
      nlinarith
    _ = _ := by rw [atomWeight_totient];ring

theorem finite_model_domination (P : Finset ℕ) (R xi w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (hR : 1 < R) (hxi : 0 < xi) (hH : 0 < H) (hC0 : Int.gcd C0 (H : ℤ) = 1)
    (hbin : ∀ p ∈ P,R < (p : ℝ) ∧ (p : ℝ) ≤ (1+xi)*R)
    (C : ℝ) (hC : 0 ≤ C) (hPopulation : xi*R/(16*Real.log R) ≤ (P.card : ℝ))
    (hFibre : ∀ v ∈ modelUniverse R xi w H C0,
      ((primeFibre P w H C0 hw hP hlarge v).card : ℝ) ≤
        C*primeWidth R xi (H : ℝ) (C0 : ℝ)/
          (((H*divisorModulus w H*coprimeModulus w H).totient : ℝ)*Real.log R))
    (E : ModelPoint w H → Prop) :
    ((actualPrimeEvent P w H C0 hw hP hlarge E).card : ℝ)/(P.card : ℝ) ≤
      (32*C)*modelMass R xi w H C0 E := by
  have hRp : 0 < R := by linarith
  have hlog : 0 < Real.log R := Real.log_pos hR
  have hPpos : (0 : ℝ) < P.card := (by positivity : 0 < xi*R/(16*Real.log R)).trans_le hPopulation
  have hatom := prime_bound_le_atom R xi w H C0 P.card C hR hxi hH hC hPopulation
  apply (div_le_iff₀ hPpos).mpr
  calc
    _ = ∑ v ∈ (modelUniverse R xi w H C0).filter E,((primeFibre P w H C0 hw hP hlarge v).card : ℝ) := by
      rw [actualPrimeEvent_card_fibres P R xi w H C0 hw hP hlarge hRp hxi.le hH hC0 hbin E,Nat.cast_sum]
    _ ≤ ∑ _v ∈ (modelUniverse R xi w H C0).filter E,(32*C*(P.card : ℝ))*atomWeight R xi w H C0 := by
      apply Finset.sum_le_sum
      intro v hv
      exact (hFibre v (Finset.mem_filter.mp hv).1).trans hatom
    _ = ((32*C)*modelMass R xi w H C0 E)*(P.card : ℝ) := by
      rw [← Finset.mul_sum]
      change (32*C*(P.card : ℝ))*modelMass R xi w H C0 E = _
      ring

end ErdosVarianceSmallModel

end

section

open _root_.Filter
open scoped Topology
namespace ErdosVarianceSmallModel
open ErdosInversePrimeBin ErdosInverseBoxHeight ErdosInverseEuler

theorem source_prime_model_domination (alpha : ℝ) (ha : 0 < alpha) :
    ∃ C : ℝ,0 < C ∧ ∀ xi : ℝ,0 < xi → xi ≤ 1 →
      ∀ᶠ z : ℝ in atTop,
      ∀ (R theta : ℝ) (H : ℕ) (C0 : ℤ),
        z^alpha ≤ R → xi/4 ≤ theta → theta ≤ xi → 0 < H → Int.gcd C0 (H : ℤ) = 1 →
        (H : ℝ) ≤ R^((4 : ℝ)/5) → totalScale R (H : ℝ) (C0 : ℝ)/(H : ℝ) ≤ (sourceZ z)^12 →
        ∃ (hw : 0 ≤ sourceW z) (hP : ∀ p ∈ primeBin R theta,p.Prime)
          (hlarge : ∀ p ∈ primeBin R theta,sourceW z < (p : ℝ)),
        ∀ E : ModelPoint (sourceW z) H → Prop,
          ((actualPrimeEvent (primeBin R theta) (sourceW z) H C0 hw hP hlarge E).card : ℝ)/
            ((primeBin R theta).card : ℝ) ≤ C*modelMass R xi (sourceW z) H C0 E := by
  obtain ⟨C,hC,hFibres⟩ := source_residue_fibre_bound_jb247 alpha ha
  refine ⟨32*C,by positivity,?_⟩
  intro xi hxi hxi1
  filter_upwards [hFibres xi hxi hxi1,source_model_population alpha xi ha hxi hxi1,
    sourceW_tendsto_atTop.eventually_ge_atTop 2] with z hFibre hPopulation hW
  intro R theta H C0 hRlo htl htu hH hC0 hHsmall hRatio
  have hpops := hPopulation R theta hRlo htl htu
  have hR : 0 < R := by linarith [hpops.1]
  have ht : 0 ≤ theta := (by positivity : (0 : ℝ) ≤ xi/4).trans htl
  let P := primeBin R theta
  have hP : ∀ p ∈ P,p.Prime := fun p hp => ((mem_primeBin hR.le ht p).mp hp).1
  have hlarge : ∀ p ∈ P,sourceW z < (p : ℝ) :=
    fun p hp => hpops.2.1.trans_lt ((mem_primeBin hR.le ht p).mp hp).2.1
  have hbin : ∀ p ∈ P,R < (p : ℝ) ∧ (p : ℝ) ≤ (1+xi)*R := by
    intro p hp
    have hh := (mem_primeBin hR.le ht p).mp hp
    refine ⟨hh.2.1,?_⟩
    have htR := mul_le_mul_of_nonneg_right htu hR.le
    nlinarith [hh.2.2]
  have hw : 0 ≤ sourceW z := by linarith
  let : NeZero H := ⟨hH.ne'⟩
  refine ⟨hw,hP,hlarge,?_⟩
  intro E
  apply finite_model_domination P R xi (sourceW z) H C0 hw hP hlarge hpops.1 hxi hH hC0 hbin C hC.le hpops.2.2
  · intro v hv
    have hm := (mem_modelUniverse R xi (sourceW z) H C0 v).mp hv |>.2.2
    let M := H*divisorModulus (sourceW z) H*coprimeModulus (sourceW z) H
    have hM : 0 < M := Nat.mul_pos (Nat.mul_pos hH (divisorModulus_pos _ H)) (coprimeModulus_pos _ H)
    have hMbound : (M : ℝ) ≤ (H : ℝ)*(smallModulus (sourceW z) : ℝ) := by
      have hh := pattern_modulus_size (sourceW z) H
      have he : (M : ℝ) = (H : ℝ)*(smallModulus (sourceW z) : ℝ) := by exact_mod_cast hh
      exact he.le
    calc
      _ ≤ ((residueFibre P (H : ℝ) (C0 : ℝ) v.1 M
          (patternClass (sourceW z) H C0 hC0 v.1 hm v.2 : ℤ)).card : ℝ) := by
        exact_mod_cast primeFibre_card_le_residue P (sourceW z) H C0 hw hP hlarge hC0 v hm
      _ ≤ _ := hFibre.2 P R (H : ℝ) (C0 : ℝ) v.1 M
        (patternClass (sourceW z) H C0 hC0 v.1 hm v.2 : ℤ) hRlo (by exact_mod_cast hH) hM
        hHsmall hMbound hRatio (fun p hp => ⟨hP p hp,(hbin p hp).1,(hbin p hp).2⟩)

end ErdosVarianceSmallModel

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_TwoSingletonBins
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.SingletonBinSelection
open ErdosCofactorChoices

attribute [local instance] Classical.propDecidable

theorem erase_selection_mem {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (f : Fin n → Finset ℕ)
    (hf : f ∈ selections P m) (i : Fin n) : eraseSelection f i ∈ selections P (eraseMultiplicity m i) := by
  apply (mem_selections _ _ _).mpr
  intro k
  by_cases hki : k=i
  · subst k; simp [eraseSelection,eraseMultiplicity]
  · simpa only [eraseSelection,eraseMultiplicity,ite_eq_right hki] using (mem_selections P m f).mp hf k

theorem erased_coordinate_empty {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (i : Fin n)
    (f : Fin n → Finset ℕ) (hf : f ∈ selections P (eraseMultiplicity m i)) : f i=∅ := by
  have hh := ((mem_selections P _ f).mp hf i).2
  simpa [eraseMultiplicity] using hh

theorem fill_selection_mem {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (i : Fin n)
    (hmi : m i=1) (f : Fin n → Finset ℕ) (hf : f ∈ selections P (eraseMultiplicity m i))
    (p : ℕ) (hp : p ∈ P i) : fillSelection f i p ∈ selections P m := by
  apply (mem_selections _ _ _).mpr
  intro k
  by_cases hki : k=i
  · subst k; simp [fillSelection,hmi,hp]
  · have hh := (mem_selections P _ f).mp hf k
    simpa [fillSelection,eraseMultiplicity,hki] using hh

theorem erase_fill {n : ℕ} (f : Fin n → Finset ℕ) (i : Fin n) (p : ℕ) (he : f i=∅) :
    eraseSelection (fillSelection f i p) i=f := by
  funext k
  by_cases hki : k=i
  · subst k; simp [eraseSelection,he]
  · simp [eraseSelection,fillSelection,hki]

theorem fill_erase {n : ℕ} (f : Fin n → Finset ℕ) (i : Fin n) (p : ℕ) (he : f i={p}) :
    fillSelection (eraseSelection f i) i p=f := by
  funext k
  by_cases hki : k=i
  · subst k; simp [fillSelection,he]
  · simp [eraseSelection,fillSelection,hki]

theorem singleton_selection_recovery {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (i : Fin n) (hmi : m i=1) (f : Fin n → Finset ℕ) (hf : f ∈ selections P m) :
    ∃ p ∈ P i,f i={p} ∧ fillSelection (eraseSelection f i) i p=f := by
  have hi := (mem_selections P m f).mp hf i
  obtain ⟨p,hp⟩ := Finset.card_eq_one.mp (hi.2.trans hmi)
  exact ⟨p,hi.1 (by rw [hp]; simp),hp,fill_erase f i p hp⟩
end NumberTheoryLean.SingletonBinSelection



namespace NumberTheoryLean.SingletonBinProduct
open ErdosCofactorChoices SingletonBinSelection

attribute [local instance] Classical.propDecidable

theorem filled_product {n : ℕ} (f : Fin n → Finset ℕ) (i : Fin n) (p : ℕ) (he : f i=∅) :
    selectionProduct (fillSelection f i p)=p*selectionProduct f := by
  have hp : ∀ k,(∏ q ∈ fillSelection f i p k,q)=(if k=i then p else 1)*(∏ q ∈ f k,q) := by
    intro k
    by_cases hki : k=i
    · subst k; simp [fillSelection,he]
    · simp [fillSelection,hki]
  unfold selectionProduct
  simp_rw [hp]
  rw [Finset.prod_mul_distrib]
  simp

theorem filled_reciprocal {n : ℕ} (f : Fin n → Finset ℕ) (i : Fin n) (p : ℕ) (he : f i=∅) :
    (selectionProduct (fillSelection f i p):ℝ)⁻¹=(p:ℝ)⁻¹*(selectionProduct f:ℝ)⁻¹ := by
  rw [filled_product f i p he,Nat.cast_mul,mul_inv_rev]
  ring

end NumberTheoryLean.SingletonBinProduct



namespace NumberTheoryLean.SingletonBinSum
open ErdosCofactorChoices SingletonBinSelection SingletonBinProduct

attribute [local instance] Classical.propDecidable

theorem singleton_sum {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (i : Fin n) (hmi : m i=1)
    (G : (Fin n → Finset ℕ) → ℝ) :
    (∑ f ∈ selections P m,G f)=
      ∑ p ∈ P i,∑ f ∈ selections P (eraseMultiplicity m i),G (fillSelection f i p) := by
  symm
  rw [← Finset.sum_product' (P i) (selections P (eraseMultiplicity m i)) (fun p f => G (fillSelection f i p))]
  apply Finset.sum_bij (fun x _ => fillSelection x.2 i x.1)
  · intro x hx
    exact fill_selection_mem P m i hmi x.2 (Finset.mem_product.mp hx).2 x.1 (Finset.mem_product.mp hx).1
  · intro x hx y hy he
    have hpx : fillSelection x.2 i x.1 i={x.1} := by simp [fillSelection]
    have hpy : fillSelection y.2 i y.1 i={y.1} := by simp [fillSelection]
    have hp : x.1=y.1 := by
      have hh := congrFun he i
      rw [hpx,hpy] at hh
      exact Finset.singleton_injective hh
    have hf : x.2=y.2 := by
      have hh := congrArg (fun f => eraseSelection f i) he
      rwa [erase_fill x.2 i x.1 (erased_coordinate_empty P m i x.2 (Finset.mem_product.mp hx).2),
        erase_fill y.2 i y.1 (erased_coordinate_empty P m i y.2 (Finset.mem_product.mp hy).2)] at hh
    exact Prod.ext hp hf
  · intro f hf
    obtain ⟨p,hp,_hfp,he⟩ := singleton_selection_recovery P m i hmi f hf
    exact ⟨(p,eraseSelection f i),Finset.mem_product.mpr ⟨hp,erase_selection_mem P m f hf i⟩,he⟩
  · intro x _
    rfl

theorem singleton_weighted_sum {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (i : Fin n) (hmi : m i=1)
    (G : (Fin n → Finset ℕ) → ℝ) :
    (∑ f ∈ selections P m,(selectionProduct f:ℝ)⁻¹*G f)=
      ∑ p ∈ P i,∑ f ∈ selections P (eraseMultiplicity m i),
        ((p:ℝ)⁻¹*(selectionProduct f:ℝ)⁻¹)*G (fillSelection f i p) := by
  rw [singleton_sum P m i hmi]
  apply Finset.sum_congr rfl
  intro p _hp
  apply Finset.sum_congr rfl
  intro f hf
  rw [filled_reciprocal f i p (erased_coordinate_empty P m i f hf)]
end NumberTheoryLean.SingletonBinSum



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_FullEndpointData
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
namespace ErdosVarianceSmallModel
open ErdosInversePrimeBin ErdosInverseBoxHeight ErdosVarianceEffective

theorem source_effective_point_domination (alpha : ℝ) (ha : 0 < alpha) :
    ∃ C : ℝ,0 < C ∧ ∀ xi : ℝ,0 < xi → xi ≤ 1 →
      ∀ᶠ z : ℝ in atTop,
      ∀ (R theta : ℝ) (a : ℕ → ℕ) (r : ℚ) (qf : ℕ),Squarefree qf →
        z^alpha ≤ R → xi/4 ≤ theta → theta ≤ xi →
        (effectiveModulus a r qf : ℝ) ≤ R^((4 : ℝ)/5) →
        effectiveSize a r qf R/(effectiveModulus a r qf : ℝ) ≤ (sourceZ z)^12 →
        ∃ (hw : 0 ≤ sourceW z) (hP : ∀ p ∈ primeBin R theta,p.Prime)
          (hlarge : ∀ p ∈ primeBin R theta,sourceW z < (p : ℝ)),
        ∀ E : ModelPoint (sourceW z) (effectiveModulus a r qf) → Prop,
          ((actualPrimeEvent (primeBin R theta) (sourceW z) (effectiveModulus a r qf)
            (effectiveIntercept a r qf) hw hP hlarge E).card : ℝ)/((primeBin R theta).card : ℝ) ≤
            C*modelMass R xi (sourceW z) (effectiveModulus a r qf) (effectiveIntercept a r qf) E := by
  obtain ⟨C,hC,hdom⟩ := source_prime_model_domination alpha ha
  refine ⟨C,hC,?_⟩
  intro xi hxi hxi1
  filter_upwards [hdom xi hxi hxi1] with z hz
  intro R theta a r qf hq hRlo htl htu hHsmall hRatio
  exact hz R theta (effectiveModulus a r qf) (effectiveIntercept a r qf)
    hRlo htl htu (effectiveModulus_pos a r qf) (effective_coordinates_gcd a r qf hq) hHsmall hRatio

end ErdosVarianceSmallModel

end


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_ActualPrimeSelectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceMoments
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceEffective ErdosVarianceCommon
  ErdosInverseCells
attribute [local instance] Classical.propDecidable

theorem actual_primePoint_survives (P : Finset ℕ) (w : ℝ) (a : ℕ → ℕ) (r : ℚ) (qf : ℕ)
    (hq : Squarefree qf) (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hPLarge : ∀ p ∈ P,w < (p : ℝ))
    (hQLarge : ∀ t ∈ qf.primeFactors,w < (t : ℝ)) (p : ℕ) [NeZero p]
    (hpGood : p ∈ goodPrimes P (effectiveModulus a r qf)) (j : ℕ) :
    actualModelSurvives w a r qf j
      (primePoint P w (effectiveModulus a r qf) (effectiveIntercept a r qf) hw hP hPLarge ⟨p,hpGood⟩) ↔
      ∀ t ∈ LargePrimeDeletion.cutoffPrimes ⌊w⌋₊,
        (effectiveInteger a r qf p (Finset.mem_filter.mp hpGood).2 (j : ℤ) : ZMod t) ≠ (a t : ZMod t) := by
  let H := effectiveModulus a r qf
  let C0 := effectiveIntercept a r qf
  let qA := alignedCofactor (fun t => (a t : ℤ)) r qf
  let v := primePoint P w H C0 hw hP hPLarge ⟨p,hpGood⟩
  have hC0 : Int.gcd C0 (H : ℤ) = 1 := effective_coordinates_gcd a r qf hq
  have hHp : H.Coprime p := (Finset.mem_filter.mp hpGood).2
  have h0 (t : ℕ) (ht : t ∈ divisorPrimes w H) :
      (patternKValue w H v.2 t+divisorPhase C0 v.1 t*(j : ZMod t) ≠ actualDivisorTarget a qf t) ↔
        (effectiveInteger a r qf p hHp (j : ℤ) : ZMod t) ≠ (a t : ZMod t) := by
    have htt := (Finset.mem_filter.mp ht).1
    have hprime := (LargePrimeDeletion.mem_cutoffPrimes.mp htt).1
    have htw := (Nat.le_floor_iff hw).mp (LargePrimeDeletion.mem_cutoffPrimes.mp htt).2
    have hqt := full_cofactor_coprime_small qf hq w hQLarge t hprime htw
    have ht0 : t ∣ divisorModulus w H := Finset.dvd_prod_of_mem _ ht
    dsimp only [v]
    rw [primePoint_kValue P w H C0 hw hP hPLarge ⟨p,hpGood⟩ t ht0]
    change ((primeK P H C0 hP ⟨p,hpGood⟩ : ZMod t) +
      divisorPhase C0 (primeM P H C0 hP ⟨p,hpGood⟩) t * (j : ZMod t) ≠ _) ↔ _
    rw [← prime_divisorPhase_eq P H C0 hP hC0 ⟨p,hpGood⟩ t (Finset.mem_filter.mp ht).2]
    have hh := effective_avoidance_unit a r qf p hHp t hqt (j : ℤ)
    simpa [H,C0,primeK,actualDivisorTarget,ZMod.unitOfCoprime] using hh.symm
  have h1 (t : ℕ) (ht : t ∈ coprimePrimes w H) :
      (patternPValue w H v.2 t*(qA : ZMod t)*((v.1 : ZMod t)+(H : ZMod t)*(j : ZMod t)) ≠ actualCoprimeTarget a r t) ↔
        (effectiveInteger a r qf p hHp (j : ℤ) : ZMod t) ≠ (a t : ZMod t) := by
    have htt := (Finset.mem_filter.mp ht).1
    have hprime := (LargePrimeDeletion.mem_cutoffPrimes.mp htt).1
    have ht1 : t ∣ coprimeModulus w H := Finset.dvd_prod_of_mem _ ht
    dsimp only [v]
    rw [primePoint_pValue P w H C0 hw hP hPLarge ⟨p,hpGood⟩ t ht1]
    have hh := effective_avoidance_not_dvd a r qf hq p hHp t hprime (Finset.mem_filter.mp ht).2 (j : ℤ)
    simpa only [H,C0,qA,primePoint,primeM,actualCoprimeTarget,Int.cast_natCast] using hh.symm
  change modelSurvives w H C0 qA (actualDivisorTarget a qf) (actualCoprimeTarget a r) j v ↔ _
  constructor
  · intro hv t ht
    by_cases hdiv : t ∣ H
    · have ht0 : t ∈ divisorPrimes w H := Finset.mem_filter.mpr ⟨ht,hdiv⟩
      exact (h0 t ht0).mp (hv.1 t ht0)
    · have ht1 : t ∈ coprimePrimes w H := Finset.mem_filter.mpr ⟨ht,hdiv⟩
      exact (h1 t ht1).mp (hv.2 t ht1)
  · intro hv
    refine ⟨?_,?_⟩
    · intro t ht
      exact (h0 t ht).mpr (hv t (Finset.mem_filter.mp ht).1)
    · intro t ht
      exact (h1 t ht).mpr (hv t (Finset.mem_filter.mp ht).1)

theorem common_card_eq_model_sum (P : Finset ℕ) (J : ℕ) (w : ℝ) (a : ℕ → ℕ) (r : ℚ) (qf : ℕ)
    (hq : Squarefree qf) (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hPLarge : ∀ p ∈ P,w < (p : ℝ))
    (hQLarge : ∀ t ∈ qf.primeFactors,w < (t : ℝ)) (p : ℕ) [NeZero p]
    (hpGood : p ∈ goodPrimes P (effectiveModulus a r qf)) :
    ((commonSurvivors J w a r qf p (Finset.mem_filter.mp hpGood).2).card : ℝ) =
      ∑ j ∈ Finset.range J,actualModelIndicator w a r qf j
        (primePoint P w (effectiveModulus a r qf) (effectiveIntercept a r qf) hw hP hPLarge ⟨p,hpGood⟩) := by
  classical
  let v := primePoint P w (effectiveModulus a r qf) (effectiveIntercept a r qf) hw hP hPLarge ⟨p,hpGood⟩
  have he : commonSurvivors J w a r qf p (Finset.mem_filter.mp hpGood).2 =
      (Finset.range J).filter (fun j => actualModelSurvives w a r qf j v) := by
    ext j
    simp only [mem_commonSurvivors,Finset.mem_filter,Finset.mem_range]
    exact and_congr Iff.rfl (actual_primePoint_survives P w a r qf hq hw hP hPLarge hQLarge p hpGood j).symm
  rw [he,Finset.natCast_card_filter]
  rfl

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_FullPatternSurvivors
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

theorem actualFullPattern_survives (P : Finset ℕ) (w : ℝ) (H qA : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (hC0 : Int.gcd C0 (H : ℤ) = 1) (beta delta : ∀ t : ℕ,ZMod t)
    (p : goodPrimes P H) (j : ℕ) :
    ErdosLargePatternLaw.survives w H qA beta delta j (actualFullPattern P w H C0 hw hP hlarge p) ↔
      modelSurvives w H C0 qA beta delta j (primePoint P w H C0 hw hP hlarge p) := by
  unfold ErdosLargePatternLaw.survives modelSurvives
  apply and_congr
  · apply forall_congr'
    intro t
    apply forall_congr'
    intro ht
    have ht0 : t ∣ divisorModulus w H := Finset.dvd_prod_of_mem _ ht
    rw [full_k0_projection P w H C0 hw hP hlarge p t ht0,
      full_p0_projection P w H C0 hw hP hlarge p t ht0,
      primePoint_kValue P w H C0 hw hP hlarge p t ht0]
    change ((primeK P H C0 hP p : ZMod t)+(p.val : ZMod t)*(j : ZMod t) ≠ beta t) ↔
      ((primeK P H C0 hP p : ZMod t)+divisorPhase C0 (primeM P H C0 hP p) t*(j : ZMod t) ≠ beta t)
    rw [← prime_divisorPhase_eq P H C0 hP hC0 p t (Finset.mem_filter.mp ht).2]
  · apply forall_congr'
    intro t
    apply forall_congr'
    intro ht
    have ht1 : t ∣ coprimeModulus w H := Finset.dvd_prod_of_mem _ ht
    rw [full_p1_projection P w H C0 hw hP hlarge p t ht1,
      full_m1_projection P w H C0 hw hP hlarge p t ht1,
      primePoint_pValue P w H C0 hw hP hlarge p t ht1]
    rfl

theorem full_count_eq_common (P : Finset ℕ) (J : ℕ) (w : ℝ) (a : ℕ → ℕ) (r : ℚ) (qf : ℕ)
    (hq : Squarefree qf) (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (hQLarge : ∀ t ∈ qf.primeFactors,w < (t : ℝ)) (p : ℕ) [NeZero p]
    (hpGood : p ∈ goodPrimes P (ErdosVarianceEffective.effectiveModulus a r qf)) :
    ErdosLargePatternLaw.survivorCount w (ErdosVarianceEffective.effectiveModulus a r qf)
      (ErdosVarianceEffective.alignedCofactor (fun t => (a t : ℤ)) r qf) J
      (actualDivisorTarget a qf) (actualCoprimeTarget a r)
      (actualFullPattern P w (ErdosVarianceEffective.effectiveModulus a r qf)
        (ErdosVarianceEffective.effectiveIntercept a r qf) hw hP hlarge ⟨p,hpGood⟩) =
      (ErdosVarianceCommon.commonSurvivors J w a r qf p (Finset.mem_filter.mp hpGood).2).card := by
  unfold ErdosLargePatternLaw.survivorCount
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter,Finset.mem_range,ErdosVarianceCommon.mem_commonSurvivors]
  apply and_congr Iff.rfl
  exact (actualFullPattern_survives P w _ _ _ hw hP hlarge
    (ErdosVarianceEffective.effective_coordinates_gcd a r qf hq)
    (actualDivisorTarget a qf) (actualCoprimeTarget a r) ⟨p,hpGood⟩ j).trans
      (actual_primePoint_survives P w a r qf hq hw hP hlarge hQLarge p hpGood j)

end ErdosVarianceLargeMap

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_FullPatternVariance
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosLargePatternLaw
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceMoments

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem four_coordinate_count {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (P : A → B → Prop) (Q : C → D → Prop) (n m : ℕ)
    (hP : ∀ a,(Finset.univ.filter (P a)).card=n)
    (hQ : ∀ c,(Finset.univ.filter (Q c)).card=m) :
    (Finset.univ.filter (fun v : A × B × C × D => P v.1 v.2.1 ∧ Q v.2.2.1 v.2.2.2)).card =
      Fintype.card A*n*Fintype.card C*m := by
  have hi (a : A) (b : B) (c : C) (d : D) :
      (if P a b ∧ Q c d then 1 else 0 : ℕ)=(if P a b then 1 else 0)*(if Q c d then 1 else 0) := by
    by_cases hp : P a b <;> by_cases hq : Q c d <;> simp [hp,hq]
  have hp (a : A) : (∑ b : B,if P a b then 1 else 0)=n := by
    simpa only [Finset.card_filter] using hP a
  have hq (c : C) : (∑ d : D,if Q c d then 1 else 0)=m := by
    simpa only [Finset.card_filter] using hQ c
  have hd (a : A) (b : B) (c : C) :
      (∑ d : D,(if P a b then 1 else 0)*(if Q c d then 1 else 0)) =
      (if P a b then 1 else 0)*m := by
    calc
      _ = (if P a b then 1 else 0)*(∑ d : D,if Q c d then 1 else 0) :=
        (Finset.mul_sum _ _ _).symm
      _ = _ := by rw [hq]
  simp only [Finset.card_filter,Fintype.sum_prod_type,hi]
  simp_rw [hd]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
  have hb (a : A) : (∑ b : B,Fintype.card C*((if P a b then 1 else 0)*m)) =
      Fintype.card C*(n*m) := by
    calc
      _ = Fintype.card C*(∑ b : B,(if P a b then 1 else 0)*m) := (Finset.mul_sum _ _ _).symm
      _ = Fintype.card C*((∑ b : B,if P a b then 1 else 0)*m) :=
        congrArg (fun x => Fintype.card C*x) (Finset.sum_mul _ _ _).symm
      _ = _ := by rw [hp]
  simp_rw [hb]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
  ring

theorem joint_condition_card (w : ℝ) (H qA : ℕ) (beta delta : ∀ t : ℕ,ZMod t) (S : Finset ℕ)
    (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t) :
    (Finset.univ.filter (jointCondition w H qA beta delta S)).card =
      (divisorModulus w H).totient*(∏ t ∈ divisorPrimes w H,(t-(positionResidues S t).card))*
      (coprimeModulus w H).totient*(∏ t ∈ coprimePrimes w H,(t-(positionResidues S t).card)) := by
  have he : Finset.univ.filter (jointCondition w H qA beta delta S) =
      Finset.univ.filter (fun v : FullPattern w H =>
        divisorCondition w H beta S v.1 v.2.1 ∧ coprimeCondition w H qA delta S v.2.2.1 v.2.2.2) := by
    apply Finset.filter_congr
    rintro ⟨p0,k0,p1,m1⟩ _
    exact joint_condition_split w H qA beta delta S p0 k0 p1 m1
  rw [he,four_coordinate_count _ _ _ _
    (divisor_condition_card w H beta S) (fun p1 => coprime_condition_card w H qA delta S p1 hqA)]
  simp only [ZMod.card_units_eq_totient]

theorem joint_density_split (w : ℝ) (H : ℕ) (S : Finset ℕ) :
    jointDensity (divisorPrimes w H) S*jointDensity (coprimePrimes w H) S =
      jointDensity (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) S := by
  unfold jointDensity divisorPrimes coprimePrimes
  exact Finset.prod_filter_mul_prod_filter_not _ _ _

theorem joint_expectation (w : ℝ) (H qA : ℕ) (beta delta : ∀ t : ℕ,ZMod t) (S : Finset ℕ)
    (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t) :
    expectation w H (fun v => if jointCondition w H qA beta delta S v then 1 else 0) =
      jointDensity (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) S := by
  have h0 : ∀ t ∈ divisorPrimes w H,t.Prime := fun t ht =>
    (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1
  have h1 : ∀ t ∈ coprimePrimes w H,t.Prime := fun t ht =>
    (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1
  have hc : (∑ v : FullPattern w H,if jointCondition w H qA beta delta S v then (1 : ℝ) else 0) =
      ((Finset.univ.filter (jointCondition w H qA beta delta S)).card : ℝ) := by
    simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  have hT0 : (divisorModulus w H : ℝ) ≠ 0 := by exact_mod_cast (divisorModulus_pos w H).ne'
  have hT1 : (coprimeModulus w H : ℝ) ≠ 0 := by exact_mod_cast (coprimeModulus_pos w H).ne'
  have hP0 : ((divisorModulus w H).totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (divisorModulus_pos w H)).ne'
  have hP1 : ((coprimeModulus w H).totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (coprimeModulus_pos w H)).ne'
  rw [expectation,← Finset.mul_sum,hc,joint_condition_card w H qA beta delta S hqA]
  simp only [Nat.cast_mul]
  rw [product_allowed_eq_density _ S h0,product_allowed_eq_density _ S h1]
  change weight w H*(((divisorModulus w H).totient : ℝ)*
    ((divisorModulus w H : ℝ)*jointDensity (divisorPrimes w H) S)*
    ((coprimeModulus w H).totient : ℝ)*
    ((coprimeModulus w H : ℝ)*jointDensity (coprimePrimes w H) S)) = _
  rw [← joint_density_split w H S]
  unfold weight
  field_simp

end ErdosLargePatternLaw



open _root_.Filter
namespace ErdosLargePatternLaw
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceMoments ErdosRandomVariance

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem single_expectation (w : ℝ) (H qA : ℕ) (beta delta : ∀ t : ℕ,ZMod t) (j : ℕ)
    (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t) :
    expectation w H (indicator w H qA beta delta j) =
      sieveProduct (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) := by
  have h := joint_expectation w H qA beta delta {j} hqA
  have he : (fun v => if jointCondition w H qA beta delta {j} v then (1 : ℝ) else 0) =
      indicator w H qA beta delta j := by
    funext v
    simp only [jointCondition,Finset.mem_singleton,forall_eq,indicator]
  rw [he,jointDensity_singleton] at h
  exact h

theorem pair_expectation (w : ℝ) (H qA : ℕ) (beta delta : ∀ t : ℕ,ZMod t) (i j : ℕ)
    (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t) :
    expectation w H (fun v => indicator w H qA beta delta i v*indicator w H qA beta delta j v) =
      pairKernel (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) i j := by
  have h := joint_expectation w H qA beta delta {i,j} hqA
  have he : (fun v => indicator w H qA beta delta i v*indicator w H qA beta delta j v) =
      (fun v => if jointCondition w H qA beta delta {i,j} v then 1 else 0) := by
    funext v
    simp only [jointCondition,Finset.forall_mem_insert,Finset.mem_singleton,forall_eq,indicator]
    by_cases hi : survives w H qA beta delta i v <;>
      by_cases hj : survives w H qA beta delta j v <;> simp [hi,hj]
  rw [he,h,jointDensity_pair]

theorem uniform_pattern_chebyshev (a eta tau : ℝ) (ha : 0 < a) (heta : 0 < eta) (htau : 0 < tau) :
    ∀ᶠ w : ℝ in atTop,1 < w ∧ ∀ (H qA : ℕ) (beta delta : ∀ t : ℕ,ZMod t),
      (∀ t ∈ coprimePrimes w H,qA.Coprime t) → ∀ J : ℕ,w^a ≤ (J : ℝ) →
        (∑ v : FullPattern w H with eta*((J : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊) ≤
          |(survivorCount w H qA J beta delta v : ℝ)-(J : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊|,
            weight w H) ≤ tau := by
  have heps : 0 < tau*eta^2 := mul_pos htau (sq_pos_of_pos heta)
  filter_upwards [stable_source_chebyshev a (tau*eta^2) ha heps] with w hw
  refine ⟨hw.1,?_⟩
  intro H qA beta delta hqA J hJ
  have hcut : variancePrimes w=LargePrimeDeletion.cutoffPrimes ⌊w⌋₊ := by
    ext p
    simp only [variancePrimes,LargePrimeDeletion.mem_cutoffPrimes,Finset.mem_filter,Finset.mem_Ioc]
    exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨h.1.pos,h.2⟩,h.1⟩⟩
  have hs (j : ℕ) := single_expectation w H qA beta delta j hqA
  have hp (i j : ℕ) := pair_expectation w H qA beta delta i j hqA
  have hh := hw.2 J hJ (FullPattern w H) Finset.univ (fun _ => weight w H)
    (indicator w H qA beta delta) 0 eta (fun _ _ => (weight_positive w H).le)
    (le_refl _) zero_le_one heta (fun j _ v _ => indicator_binary w H qA beta delta j v)
    (by simpa only [add_zero] using (weight_sum w H).le)
    (fun j _ => by simpa only [sub_zero,one_mul,hcut,expectation,weightedMoment] using (hs j).ge)
    (fun j _ => by simpa only [add_zero,one_mul,hcut,expectation,weightedMoment] using (hs j).le)
    (fun i _ j _ _ => by simpa only [add_zero,one_mul,hcut,expectation,weightedMoment] using (hp i j).le)
  have hV : sieveProduct (variancePrimes w)=SmallSieveFinite.smallEuler ⌊w⌋₊ := by
    rw [hcut]
    simp only [sieveProduct,SmallSieveFinite.smallEuler,one_div]
  have hb : (tau*eta^2+4*0)/eta^2=tau := by
    field_simp [heta.ne']
    ring
  simpa only [hV,hb,indicatorSum,← count_eq_indicator_sum] using hh

end ErdosLargePatternLaw


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


namespace ErdosVarianceWeighted
open ErdosInverseCells
attribute [local instance] Classical.propDecidable

theorem subset_card_of_fraction (A P : Finset ℕ) (hAP : A ⊆ P) (rho : ℝ)
    (hfrac : (A.card : ℝ)/(P.card : ℝ) ≤ rho) : (A.card : ℝ) ≤ rho*(P.card : ℝ) := by
  by_cases hP : P.card = 0
  · have hP0 := Finset.card_eq_zero.mp hP
    have hA0 : A = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun a ha => by simpa [hP0] using hAP ha)
    simp only [hA0,Finset.card_empty,Nat.cast_zero,hP,mul_zero,le_refl]
  · have hPC : (0 : ℝ) < P.card := by exact_mod_cast Nat.pos_of_ne_zero hP
    exact (div_le_iff₀ hPC).mp hfrac

theorem harmonic_transfer (A P : Finset ℕ) (hAP : A ⊆ P) (R theta rho : ℝ)
    (hR : 0 < R) (htheta : 0 ≤ theta) (hrho : 0 ≤ rho)
    (hbin : ∀ p ∈ P,R < (p : ℝ) ∧ (p : ℝ) ≤ (1+theta)*R)
    (hcard : (A.card : ℝ) ≤ rho*(P.card : ℝ)) :
    harmonicMass A ≤ rho*(1+theta)*harmonicMass P := by
  have htop : 0 < (1+theta)*R := by positivity
  have hupper : harmonicMass A ≤ (A.card : ℝ)/R := by
    calc
      _ ≤ ∑ _p ∈ A,R⁻¹ := by
        apply Finset.sum_le_sum
        intro p hp
        have h := (hbin p (hAP hp)).1
        exact (inv_le_inv₀ (hR.trans h) hR).mpr h.le
      _ = _ := by rw [Finset.sum_const,nsmul_eq_mul];ring
  have hlower : (P.card : ℝ)/((1+theta)*R) ≤ harmonicMass P := by
    calc
      _ = ∑ _p ∈ P,((1+theta)*R)⁻¹ := by rw [Finset.sum_const,nsmul_eq_mul];ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p hp
        have h := hbin p hp
        exact (inv_le_inv₀ htop (hR.trans h.1)).mpr h.2
  calc
    _ ≤ (A.card : ℝ)/R := hupper
    _ ≤ (rho*(P.card : ℝ))/R := div_le_div_of_nonneg_right hcard hR.le
    _ = rho*(1+theta)*((P.card : ℝ)/((1+theta)*R)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hlower (by positivity)

theorem harmonic_transfer_two (A P : Finset ℕ) (hAP : A ⊆ P) (R theta rho : ℝ)
    (hR : 0 < R) (htheta : 0 ≤ theta) (htheta1 : theta ≤ 1) (hrho : 0 ≤ rho)
    (hbin : ∀ p ∈ P,R < (p : ℝ) ∧ (p : ℝ) ≤ (1+theta)*R)
    (hcard : (A.card : ℝ) ≤ rho*(P.card : ℝ)) :
    harmonicMass A ≤ 2*rho*harmonicMass P := by
  have hh := harmonic_transfer A P hAP R theta rho hR htheta hrho hbin hcard
  have hc := harmonicMass_nonneg P
  have hmul := mul_le_mul_of_nonneg_left (show 1+theta ≤ 2 by linarith) (mul_nonneg hrho hc)
  nlinarith

end ErdosVarianceWeighted


namespace ErdosVarianceSmallPrime
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceEffective ErdosVarianceCommon
  ErdosVarianceMoments ErdosVarianceUniformMoments ErdosInverseCells ErdosRandomVariance
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem common_deviation_mem_primeEvent (P : Finset ℕ) (J : ℕ) (w : ℝ)
    (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hPLarge : ∀ p ∈ P,w < (p : ℝ))
    (hQLarge : ∀ t ∈ qf.primeFactors,w < (t : ℝ)) (p : ℕ) [NeZero p]
    (hpGood : p ∈ goodPrimes P (effectiveModulus a r qf)) (eta : ℝ)
    (hdev : eta*((J : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊) ≤
      |((commonSurvivors J w a r qf p (Finset.mem_filter.mp hpGood).2).card : ℝ)-
        (J : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊|) :
    p ∈ actualPrimeEvent P w (effectiveModulus a r qf) (effectiveIntercept a r qf) hw hP hPLarge
      (modelBadEvent J w (effectiveModulus a r qf) (alignedCofactor (fun t => (a t : ℤ)) r qf)
        (effectiveIntercept a r qf) (actualDivisorTarget a qf) (actualCoprimeTarget a r) eta) := by
  apply Finset.mem_image.mpr
  refine ⟨⟨p,hpGood⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
  change eta*((J : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊) ≤
    |(∑ j ∈ Finset.range J,actualModelIndicator w a r qf j
      (primePoint P w (effectiveModulus a r qf) (effectiveIntercept a r qf) hw hP hPLarge ⟨p,hpGood⟩))-
        (J : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊|
  rw [← common_card_eq_model_sum P J w a r qf hq hw hP hPLarge hQLarge p hpGood]
  exact hdev

end ErdosVarianceSmallPrime



namespace ErdosVarianceSmallPrime
open NumberTheoryLean ErdosInverseCounts ErdosInverseAlignment ErdosVarianceCommon
attribute [local instance] Classical.propDecidable

theorem mem_badAligningPrimes (P : Finset ℕ) (Y : ℕ) (w : ℝ) (a : ℕ → ℕ)
    (r : ℚ) (qf : ℕ) (eps : ℝ) (p : ℕ) :
    p ∈ badAligningPrimes P Y w a r qf eps ↔ p ∈ P ∧
      aligns (fun t => (a t : ℤ)) r p ∧
      eps < |(modulusCount Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) a (p*qf) : ℝ)/
        referenceCount Y w p qf-1| := Finset.mem_filter

end ErdosVarianceSmallPrime



namespace ErdosVarianceLargePrime
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceEffective ErdosVarianceCommon
  ErdosVarianceMoments ErdosVarianceLargeMap
attribute [local instance] Classical.propDecidable

theorem common_deviation_mem_full_event (P : Finset ℕ) (J : ℕ) (w : ℝ)
    (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hPLarge : ∀ p ∈ P,w < (p : ℝ))
    (hQLarge : ∀ t ∈ qf.primeFactors,w < (t : ℝ)) (p : ℕ) [NeZero p]
    (hpGood : p ∈ goodPrimes P (effectiveModulus a r qf)) (eta : ℝ)
    (hdev : eta*((J : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊) ≤
      |((commonSurvivors J w a r qf p (Finset.mem_filter.mp hpGood).2).card : ℝ)-
        (J : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊|) :
    p ∈ fullPrimeEvent P w (effectiveModulus a r qf) (effectiveIntercept a r qf) hw hP hPLarge
      (fullPatternBadEvent J w (effectiveModulus a r qf) (alignedCofactor (fun t => (a t : ℤ)) r qf)
        (actualDivisorTarget a qf) (actualCoprimeTarget a r) eta) := by
  apply Finset.mem_image.mpr
  refine ⟨⟨p,hpGood⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
  change eta*((J : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊) ≤
    |(ErdosLargePatternLaw.survivorCount w (effectiveModulus a r qf)
      (alignedCofactor (fun t => (a t : ℤ)) r qf) J (actualDivisorTarget a qf) (actualCoprimeTarget a r)
      (actualFullPattern P w (effectiveModulus a r qf) (effectiveIntercept a r qf) hw hP hPLarge ⟨p,hpGood⟩) : ℝ)-
        (J : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊|
  rw [full_count_eq_common P J w a r qf hq hw hP hPLarge hQLarge p hpGood]
  exact hdev

end ErdosVarianceLargePrime


section

open _root_.Filter
namespace ErdosVarianceSmallPrime
open NumberTheoryLean ErdosInverseBoxHeight ErdosInversePrimeBin ErdosInverseEuler
  ErdosVarianceSmallModel ErdosVarianceEffective ErdosVarianceCommon ErdosVarianceMoments
  ErdosVarianceUniformMoments ErdosInverseAlignment
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem source_small_H_bad_prime_fraction (alpha aStar eps sigma : ℝ)
    (halpha : 0 < alpha) (ha : 0 < aStar) (heps : 0 < eps) (hsigma : 0 < sigma) :
    ∃ Cs : ℝ,0 < Cs ∧ ∃ xi0 : ℝ,0 < xi0 ∧ xi0 ≤ 1 ∧
      ∀ xi : ℝ,0 < xi → xi ≤ xi0 → ∀ᶠ z : ℝ in atTop,
      ∀ (R theta : ℝ) (a : ℕ → ℕ) (r : ℚ) (qf : ℕ),Squarefree qf →
        z^alpha ≤ R → xi/4 ≤ theta → theta ≤ xi →
        (∀ t ∈ qf.primeFactors,sourceW z < (t : ℝ)) →
        (∀ p ∈ primeBin R theta,qf.Coprime p ∧
          3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*qf))/Real.log (sourceW z)) →
        (effectiveModulus a r qf : ℝ) ≤ R^((4 : ℝ)/5) →
        effectiveSize a r qf R/(effectiveModulus a r qf : ℝ) ≤ (sourceZ z)^12 →
        (sourceW z)^Cs ≤ effectiveSize a r qf R →
        ((badAligningPrimes (primeBin R theta) (sourceY z) (sourceW z) a r qf eps).card : ℝ)/
          ((primeBin R theta).card : ℝ) ≤ sigma := by
  obtain ⟨C,hC,hdom⟩ := source_effective_point_domination alpha halpha
  obtain ⟨Cs,hCs,hmodel⟩ := uniform_model_chebyshev_jb247 (5*aStar/8) (eps/2) (sigma/C)
    (by positivity) (by positivity) (div_pos hsigma hC)
  obtain ⟨xi0,hxi0,hxi01,hcommon⟩ := source_actual_bad_to_common_jb247 aStar eps ha heps
  refine ⟨Cs,hCs,xi0,hxi0,hxi01,?_⟩
  intro xi hxi hxib
  have hxi1 := hxib.trans hxi01
  filter_upwards [hdom xi hxi hxi1,hcommon xi hxi hxib,
    sourceW_tendsto_atTop.eventually (hmodel xi hxi),eventually_gt_atTop (0 : ℝ)]
    with z hzdom hzcommon hzmodel hz0
  intro R theta a r qf hq hRlo hthetal hthetau hQLarge hgeometry hHsmall hratio hhard
  have hR : 0 < R := (Real.rpow_pos_of_pos hz0 alpha).trans_le hRlo
  have htheta : 0 ≤ theta := (by positivity : (0 : ℝ) ≤ xi/4).trans hthetal
  let P := primeBin R theta
  let H := effectiveModulus a r qf
  let C0 := effectiveIntercept a r qf
  let qA := alignedCofactor (fun t => (a t : ℤ)) r qf
  let beta := actualDivisorTarget a qf
  let delta := actualCoprimeTarget a r
  let J := commonLength (sourceY z) qf R xi
  let E := modelBadEvent J (sourceW z) H qA C0 beta delta (eps/2)
  obtain ⟨hw,hP,hPLarge,hdomE⟩ := hzdom R theta a r qf hq hRlo hthetal hthetau hHsmall hratio
  have hHp : 0 < H := effectiveModulus_pos a r qf
  have hC0 : Int.gcd C0 (H : ℤ) = 1 := effective_coordinates_gcd a r qf hq
  have hqA : ∀ t ∈ coprimePrimes (sourceW z) H,qA.Coprime t := by
    intro t ht
    have hc := LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1
    have htw := (Nat.le_floor_iff hw).mp hc.2
    exact aligned_coefficient_coprime_small a r qf hq (sourceW z) hQLarge t hc.1 htw
  have hY : xi*(sourceW z)^Cs ≤ modelLength R xi (H : ℝ) (C0 : ℝ) := by
    exact (mul_le_mul_of_nonneg_left hhard hxi.le).trans
      (modelLength_bounds R xi (H : ℝ) (C0 : ℝ) hR hxi.le hxi1 (by exact_mod_cast hHp)).2
  have hmap (p : ℕ) (hp : p ∈ badAligningPrimes P (sourceY z) (sourceW z) a r qf eps) :
      (sourceW z)^(5*aStar/8) ≤ (J : ℝ) ∧
      p ∈ actualPrimeEvent P (sourceW z) H C0 hw hP hPLarge E := by
    obtain ⟨hpP,halign,hbad⟩ := (mem_badAligningPrimes P (sourceY z) (sourceW z) a r qf eps p).mp hp
    have hprime := hP p hpP
    let : NeZero p := ⟨hprime.ne_zero⟩
    have hqp := (hgeometry p hpP).1
    have hgood : p ∈ goodPrimes P H := Finset.mem_filter.mpr
      ⟨hpP,aligned_isolated_coprime_effective a r qf hq p hprime hqp halign⟩
    have hbin := (mem_primeBin hR.le htheta p).mp hpP
    have hpu : (p : ℝ) ≤ (1+xi)*R := hbin.2.2.trans (by nlinarith)
    have hh := hzcommon a r qf hq p hprime hqp (Finset.mem_filter.mp hgood).2 R hR
      hbin.2.1 hpu (hPLarge p hpP) hQLarge (hgeometry p hpP).2 halign hbad
    refine ⟨hh.1,?_⟩
    exact common_deviation_mem_primeEvent P J (sourceW z) a r qf hq hw hP hPLarge hQLarge p hgood
      (eps/2) hh.2.le
  by_cases hempty : badAligningPrimes P (sourceY z) (sourceW z) a r qf eps = ∅
  · change ((badAligningPrimes P (sourceY z) (sourceW z) a r qf eps).card : ℝ)/(P.card : ℝ) ≤ sigma
    rw [hempty,Finset.card_empty,Nat.cast_zero,zero_div]
    exact hsigma.le
  obtain ⟨p,hp⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hJ := (hmap p hp).1
  have hmass : modelMass R xi (sourceW z) H C0 E ≤ sigma/C :=
    hzmodel.2 R hR H qA hHp C0 hC0 beta delta hqA hY J hJ
  have hsub : badAligningPrimes P (sourceY z) (sourceW z) a r qf eps ⊆
      actualPrimeEvent P (sourceW z) H C0 hw hP hPLarge E := fun p hp => (hmap p hp).2
  have hcard : ((badAligningPrimes P (sourceY z) (sourceW z) a r qf eps).card : ℝ) ≤
      (actualPrimeEvent P (sourceW z) H C0 hw hP hPLarge E).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hh := (div_le_div_of_nonneg_right hcard (Nat.cast_nonneg P.card)).trans
    ((hdomE E).trans (mul_le_mul_of_nonneg_left hmass hC.le))
  have hc : C*(sigma/C) = sigma := by field_simp
  exact hh.trans_eq hc

end ErdosVarianceSmallPrime

end

section

open _root_.Filter
namespace ErdosVarianceLargePrime
open NumberTheoryLean ErdosInverseBoxHeight ErdosInversePrimeBin ErdosInverseEuler
  ErdosVarianceSmallModel ErdosVarianceEffective ErdosVarianceCommon ErdosVarianceMoments
  ErdosVarianceLargeMap ErdosVarianceSmallPrime ErdosInverseAlignment
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem source_large_H_bad_prime_fraction (alpha aStar eps sigma : ℝ)
    (halpha : 0 < alpha) (ha : 0 < aStar) (heps : 0 < eps) (hsigma : 0 < sigma) :
    ∃ xi0 : ℝ,0 < xi0 ∧ xi0 ≤ 1 ∧ ∀ xi : ℝ,0 < xi → xi ≤ xi0 → ∀ᶠ z : ℝ in atTop,
      ∀ (R theta : ℝ) (a : ℕ → ℕ) (r : ℚ) (qf : ℕ),Squarefree qf →
        z^alpha ≤ R → xi/4 ≤ theta → theta ≤ xi →
        (∀ t ∈ qf.primeFactors,sourceW z < (t : ℝ)) →
        (∀ p ∈ primeBin R theta,qf.Coprime p ∧
          3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*qf))/Real.log (sourceW z)) →
        R^((4 : ℝ)/5) ≤ (effectiveModulus a r qf : ℝ) →
        (effectiveModulus a r qf : ℝ) ≤ R*(sourceZ z)^11 →
        effectiveSize a r qf R/(effectiveModulus a r qf : ℝ) ≤ (sourceZ z)^12 →
        ((badAligningPrimes (primeBin R theta) (sourceY z) (sourceW z) a r qf eps).card : ℝ)/
          ((primeBin R theta).card : ℝ) ≤ sigma := by
  obtain ⟨C,hC,hdom⟩ := source_full_pattern_domination_jb247 alpha halpha
  have hmodel := ErdosLargePatternLaw.uniform_pattern_chebyshev (5*aStar/8) (eps/2) (sigma/(2*C))
    (by positivity) (by positivity) (by positivity)
  obtain ⟨xi0,hxi0,hxi01,hcommon⟩ := source_actual_bad_to_common_jb247 aStar eps ha heps
  refine ⟨xi0,hxi0,hxi01,?_⟩
  intro xi hxi hxib
  have hxi1 := hxib.trans hxi01
  filter_upwards [hdom xi hxi hxi1 (sigma/2) (by positivity),hcommon xi hxi hxib,
    sourceW_tendsto_atTop.eventually hmodel] with z hzdom hzcommon hzmodel
  intro R theta a r qf hq hRlo hthetal hthetau hQLarge hgeometry hHlarge hHupper hratio
  have hR1 : 1 < R := (Real.one_lt_rpow hzdom.1 halpha).trans_le hRlo
  have hR : 0 < R := by linarith
  have htheta : 0 ≤ theta := (by positivity : (0 : ℝ) ≤ xi/4).trans hthetal
  let P := primeBin R theta
  let H := effectiveModulus a r qf
  let C0 := effectiveIntercept a r qf
  let qA := alignedCofactor (fun t => (a t : ℤ)) r qf
  let beta := actualDivisorTarget a qf
  let delta := actualCoprimeTarget a r
  let J := commonLength (sourceY z) qf R xi
  let E := fullPatternBadEvent J (sourceW z) H qA beta delta (eps/2)
  have hH1 : (1 : ℝ) < H := (Real.one_lt_rpow hR1 (by norm_num : (0 : ℝ) < 4/5)).trans_le hHlarge
  have hH2 : 2 ≤ H := by
    have hh : 1 < H := by exact_mod_cast hH1
    omega
  have hC0 : Int.gcd C0 (H : ℤ) = 1 := effective_coordinates_gcd a r qf hq
  obtain ⟨hw,hP,hPLarge,hdomE⟩ := hzdom.2 R theta hRlo hthetal hthetau H C0 hH2 hC0 hHlarge hHupper hratio
  have hqA : ∀ t ∈ coprimePrimes (sourceW z) H,qA.Coprime t := by
    intro t ht
    have hc := LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1
    exact aligned_coefficient_coprime_small a r qf hq (sourceW z) hQLarge t hc.1 ((Nat.le_floor_iff hw).mp hc.2)
  have hmap (p : ℕ) (hp : p ∈ badAligningPrimes P (sourceY z) (sourceW z) a r qf eps) :
      (sourceW z)^(5*aStar/8) ≤ (J : ℝ) ∧ p ∈ fullPrimeEvent P (sourceW z) H C0 hw hP hPLarge E := by
    obtain ⟨hpP,halign,hbad⟩ := (mem_badAligningPrimes P (sourceY z) (sourceW z) a r qf eps p).mp hp
    have hprime := hP p hpP
    let : NeZero p := ⟨hprime.ne_zero⟩
    have hqp := (hgeometry p hpP).1
    have hgood : p ∈ goodPrimes P H := Finset.mem_filter.mpr
      ⟨hpP,aligned_isolated_coprime_effective a r qf hq p hprime hqp halign⟩
    have hbin := (mem_primeBin hR.le htheta p).mp hpP
    have hpu : (p : ℝ) ≤ (1+xi)*R := hbin.2.2.trans (by nlinarith)
    have hh := hzcommon a r qf hq p hprime hqp (Finset.mem_filter.mp hgood).2 R hR
      hbin.2.1 hpu (hPLarge p hpP) hQLarge (hgeometry p hpP).2 halign hbad
    exact ⟨hh.1,common_deviation_mem_full_event P J (sourceW z) a r qf hq hw hP hPLarge hQLarge p hgood
      (eps/2) hh.2.le⟩
  by_cases hempty : badAligningPrimes P (sourceY z) (sourceW z) a r qf eps = ∅
  · change ((badAligningPrimes P (sourceY z) (sourceW z) a r qf eps).card : ℝ)/(P.card : ℝ) ≤ sigma
    rw [hempty,Finset.card_empty,Nat.cast_zero,zero_div]
    exact hsigma.le
  obtain ⟨p,hp⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hJ := (hmap p hp).1
  have hmass : patternEventWeight (sourceW z) H E ≤ sigma/(2*C) :=
    hzmodel.2 H qA beta delta hqA J hJ
  have hsub : badAligningPrimes P (sourceY z) (sourceW z) a r qf eps ⊆
      fullPrimeEvent P (sourceW z) H C0 hw hP hPLarge E := fun p hp => (hmap p hp).2
  have hcard : ((badAligningPrimes P (sourceY z) (sourceW z) a r qf eps).card : ℝ) ≤
      (fullPrimeEvent P (sourceW z) H C0 hw hP hPLarge E).card := by exact_mod_cast Finset.card_le_card hsub
  have hh := (div_le_div_of_nonneg_right hcard (Nat.cast_nonneg P.card)).trans
    ((hdomE E).trans (add_le_add (mul_le_mul_of_nonneg_left hmass hC.le) le_rfl))
  have hc : C*(sigma/(2*C))+sigma/2 = sigma := by field_simp <;> ring
  exact hh.trans_eq hc

end ErdosVarianceLargePrime

end

section

open _root_.Filter
namespace ErdosVarianceLargePrime
open NumberTheoryLean ErdosInverseBoxHeight ErdosInversePrimeBin ErdosInverseEuler
  ErdosVarianceEffective ErdosVarianceSmallPrime
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem source_hard_bad_prime_fraction (alpha aStar eps sigma Cmin : ℝ)
    (halpha : 0 < alpha) (ha : 0 < aStar) (heps : 0 < eps) (hsigma : 0 < sigma) :
    ∃ Cs : ℝ,0 < Cs ∧ Cmin ≤ Cs ∧ ∃ xi0 : ℝ,0 < xi0 ∧ xi0 ≤ 1 ∧
      ∀ xi : ℝ,0 < xi → xi ≤ xi0 → ∀ᶠ z : ℝ in atTop,
      ∀ (R theta : ℝ) (a : ℕ → ℕ) (r : ℚ) (qf : ℕ),Squarefree qf →
        z^alpha ≤ R → xi/4 ≤ theta → theta ≤ xi →
        (∀ t ∈ qf.primeFactors,sourceW z < (t : ℝ)) →
        (∀ p ∈ primeBin R theta,qf.Coprime p ∧
          3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*qf))/Real.log (sourceW z)) →
        (effectiveModulus a r qf : ℝ) ≤ R*(sourceZ z)^11 →
        effectiveSize a r qf R/(effectiveModulus a r qf : ℝ) ≤ (sourceZ z)^12 →
        (sourceW z)^Cs ≤ effectiveSize a r qf R →
        ((badAligningPrimes (primeBin R theta) (sourceY z) (sourceW z) a r qf eps).card : ℝ)/
          ((primeBin R theta).card : ℝ) ≤ sigma := by
  obtain ⟨Cs0,hCs0,xiS,hxiS,hxiS1,hsmall⟩ := source_small_H_bad_prime_fraction alpha aStar eps sigma halpha ha heps hsigma
  obtain ⟨xiL,hxiL,hxiL1,hlarge⟩ := source_large_H_bad_prime_fraction alpha aStar eps sigma halpha ha heps hsigma
  let Cs := max Cs0 (max 1 Cmin)
  have hCs : 0 < Cs := hCs0.trans_le (le_max_left _ _)
  have hCmin : Cmin ≤ Cs := (le_max_right 1 Cmin).trans (le_max_right _ _)
  refine ⟨Cs,hCs,hCmin,min xiS xiL,lt_min hxiS hxiL,(min_le_left _ _).trans hxiS1,?_⟩
  intro xi hxi hxib
  have hxS := hxib.trans (min_le_left xiS xiL)
  have hxL := hxib.trans (min_le_right xiS xiL)
  filter_upwards [hsmall xi hxi hxS,hlarge xi hxi hxL,sourceW_tendsto_atTop.eventually_ge_atTop 1]
    with z hzsmall hzlarge hW
  intro R theta a r qf hq hRlo hthetal hthetau hQLarge hgeometry hHupper hratio hhard
  by_cases hcase : (effectiveModulus a r qf : ℝ) ≤ R^((4 : ℝ)/5)
  · have hhard0 : (sourceW z)^Cs0 ≤ effectiveSize a r qf R :=
      (Real.rpow_le_rpow_of_exponent_le hW (le_max_left Cs0 (max 1 Cmin))).trans hhard
    exact hzsmall R theta a r qf hq hRlo hthetal hthetau hQLarge hgeometry hcase hratio hhard0
  · exact hzlarge R theta a r qf hq hRlo hthetal hthetau hQLarge hgeometry
      (le_of_lt (lt_of_not_ge hcase)) hHupper hratio

end ErdosVarianceLargePrime

end


namespace ErdosVarianceWeighted
open NumberTheoryLean ErdosInverseBoxHeight ErdosInversePrimeBin ErdosVarianceEffective ErdosVarianceSmallPrime
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem guardedHardPrimes_subset (z R theta : ℝ) (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (Cs eps : ℝ) :
    guardedHardPrimes z R theta a r qf Cs eps ⊆ primeBin R theta := by
  unfold guardedHardPrimes
  split_ifs
  · exact Finset.filter_subset _ _
  · exact Finset.empty_subset _

theorem rawHardPrimeUnion_subset (Q : Finset ℚ) (z R theta : ℝ) (a : ℕ → ℕ) (qf : ℕ) (Cs eps : ℝ) :
    rawHardPrimeUnion Q z R theta a qf Cs eps ⊆ primeBin R theta := by
  exact Finset.biUnion_subset.mpr (fun r _ => guardedHardPrimes_subset z R theta a r qf Cs eps)

theorem rawHardPrimeUnion_card (Q : Finset ℚ) (z R theta : ℝ) (a : ℕ → ℕ) (qf : ℕ) (Cs eps sigma : ℝ)
    (h : ∀ r ∈ Q,((guardedHardPrimes z R theta a r qf Cs eps).card : ℝ) ≤
      sigma*((primeBin R theta).card : ℝ)) :
    ((rawHardPrimeUnion Q z R theta a qf Cs eps).card : ℝ) ≤
      sigma*(Q.card : ℝ)*((primeBin R theta).card : ℝ) := by
  have hc := Finset.card_biUnion_le (s := Q) (t := fun r => guardedHardPrimes z R theta a r qf Cs eps)
  calc
    _ ≤ ∑ r ∈ Q,((guardedHardPrimes z R theta a r qf Cs eps).card : ℝ) := by exact_mod_cast hc
    _ ≤ ∑ _r ∈ Q,sigma*((primeBin R theta).card : ℝ) := Finset.sum_le_sum h
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul];ring

end ErdosVarianceWeighted


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceGuardedHardCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
namespace ErdosVarianceWeighted
open NumberTheoryLean ErdosInverseBoxHeight ErdosInversePrimeBin ErdosVarianceEffective ErdosVarianceSmallPrime
  ErdosVarianceLargePrime
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem source_guarded_hard_count (alpha aStar eps sigma Cmin : ℝ)
    (halpha : 0 < alpha) (ha : 0 < aStar) (heps : 0 < eps) (hsigma : 0 < sigma) :
    ∃ Cs : ℝ,0 < Cs ∧ Cmin ≤ Cs ∧ ∃ xi0 : ℝ,0 < xi0 ∧ xi0 ≤ 1 ∧
      ∀ xi : ℝ,0 < xi → xi ≤ xi0 → ∀ᶠ z : ℝ in atTop,
      ∀ (R theta : ℝ) (a : ℕ → ℕ) (qf : ℕ),Squarefree qf →
        z^alpha ≤ R → xi/4 ≤ theta → theta ≤ xi →
        (∀ t ∈ qf.primeFactors,sourceW z < (t : ℝ)) →
        (∀ p ∈ primeBin R theta,qf.Coprime p ∧
          3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*qf))/Real.log (sourceW z)) →
        ∀ r : ℚ,((guardedHardPrimes z R theta a r qf Cs eps).card : ℝ) ≤
          sigma*((primeBin R theta).card : ℝ) := by
  obtain ⟨Cs,hCs,hCmin,xi0,hxi0,hxi01,hsource⟩ :=
    source_hard_bad_prime_fraction alpha aStar eps sigma Cmin halpha ha heps hsigma
  refine ⟨Cs,hCs,hCmin,xi0,hxi0,hxi01,?_⟩
  intro xi hxi hxib
  filter_upwards [hsource xi hxi hxib] with z hz
  intro R theta a qf hq hRlo hthetal hthetau hQLarge hgeometry r
  by_cases hg : hardCandidate z R a r qf Cs
  · have hb := hz R theta a r qf hq hRlo hthetal hthetau hQLarge hgeometry hg.1 hg.2.1 hg.2.2
    rw [guardedHardPrimes,ite_eq_left hg]
    exact subset_card_of_fraction _ _ (Finset.filter_subset _ _) sigma hb
  · simp only [guardedHardPrimes,ite_eq_right hg,Finset.card_empty,Nat.cast_zero]
    positivity

end ErdosVarianceWeighted

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_SourceRawPrimeMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
namespace ErdosVarianceWeighted
open NumberTheoryLean ErdosInverseBoxHeight ErdosInversePrimeBin ErdosVarianceEffective ErdosInverseCells
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem source_raw_hard_prime_mass (alpha aStar eps tau Cmin : ℝ) (F : ℕ)
    (halpha : 0 < alpha) (ha : 0 < aStar) (heps : 0 < eps) (htau : 0 < tau) :
    ∃ Cs : ℝ,0 < Cs ∧ Cmin ≤ Cs ∧ ∃ xi0 : ℝ,0 < xi0 ∧ xi0 ≤ 1 ∧
      ∀ xi : ℝ,0 < xi → xi ≤ xi0 → ∀ᶠ z : ℝ in atTop,
      ∀ (R theta : ℝ) (a : ℕ → ℕ) (qf : ℕ),Squarefree qf →
        z^alpha ≤ R → xi/4 ≤ theta → theta ≤ xi →
        (∀ t ∈ qf.primeFactors,sourceW z < (t : ℝ)) →
        (∀ p ∈ primeBin R theta,qf.Coprime p ∧
          3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*qf))/Real.log (sourceW z)) →
      ∀ Q : Finset ℚ,Q.card ≤ F →
        harmonicMass (rawHardPrimeUnion Q z R theta a qf Cs eps) ≤ tau*harmonicMass (primeBin R theta) := by
  let sigma := tau/(2*((F : ℝ)+1))
  have hsigma : 0 < sigma := by dsimp [sigma] <;> positivity
  obtain ⟨Cs,hCs,hCmin,xi0,hxi0,hxi01,hcount⟩ :=
    source_guarded_hard_count alpha aStar eps sigma Cmin halpha ha heps hsigma
  refine ⟨Cs,hCs,hCmin,xi0,hxi0,hxi01,?_⟩
  intro xi hxi hxib
  filter_upwards [hcount xi hxi hxib,eventually_gt_atTop (1 : ℝ)] with z hz hz1
  intro R theta a qf hq hRlo hthetal hthetau hQLarge hgeometry Q hQ
  have hR : 0 < R := (Real.rpow_pos_of_pos (by linarith : 0 < z) alpha).trans_le hRlo
  have htheta : 0 ≤ theta := (by positivity : (0 : ℝ) ≤ xi/4).trans hthetal
  have htheta1 : theta ≤ 1 := hthetau.trans (hxib.trans hxi01)
  have hcard := rawHardPrimeUnion_card Q z R theta a qf Cs eps sigma
    (fun r _ => hz R theta a qf hq hRlo hthetal hthetau hQLarge hgeometry r)
  have hm := harmonic_transfer_two (rawHardPrimeUnion Q z R theta a qf Cs eps) (primeBin R theta)
    (rawHardPrimeUnion_subset Q z R theta a qf Cs eps) R theta (sigma*(Q.card : ℝ)) hR htheta htheta1
    (by positivity) (fun p hp => ((mem_primeBin hR.le htheta p).mp hp).2) hcard
  have hbudget : 2*(sigma*(Q.card : ℝ)) ≤ tau := by
    have hQr : (Q.card : ℝ) ≤ (F : ℝ)+1 := by
      have hh : (Q.card : ℝ) ≤ F := by exact_mod_cast hQ
      linarith
    have hh := mul_le_mul_of_nonneg_left hQr (show 0 ≤ 2*sigma by positivity)
    have he : (2*sigma)*((F : ℝ)+1) = tau := by dsimp [sigma];field_simp
    nlinarith
  exact hm.trans (mul_le_mul_of_nonneg_right hbudget (harmonicMass_nonneg _))

end ErdosVarianceWeighted

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_SingletonEventMass
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceWeighted
open NumberTheoryLean ErdosCofactorChoices SingletonBinSelection SingletonBinSum CanonicalSubsetBox ErdosInverseCells
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem singleton_event_sum {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (i : Fin n) (hi : m i = 1)
    (E : (Fin n → Finset ℕ) → Prop) :
    (∑ f ∈ (selections P m).filter E,(selectionProduct f : ℝ)⁻¹) =
      ∑ f ∈ selections P (eraseMultiplicity m i),(selectionProduct f : ℝ)⁻¹*
        harmonicMass ((P i).filter (fun p => E (fillSelection f i p))) := by
  have he := singleton_weighted_sum P m i hi (fun f => if E f then (1 : ℝ) else 0)
  have hl : (∑ f ∈ (selections P m).filter E,(selectionProduct f : ℝ)⁻¹) =
      ∑ f ∈ selections P m,(selectionProduct f : ℝ)⁻¹*(if E f then (1 : ℝ) else 0) := by
    simp only [Finset.sum_filter,mul_ite,mul_one,mul_zero]
  rw [hl,he,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _hf
  rw [harmonicMass,Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  split_ifs <;> ring

theorem singleton_total_mass {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (i : Fin n) (hi : m i = 1) :
    selectionMass P m = harmonicMass (P i)*selectionMass P (eraseMultiplicity m i) := by
  have he := singleton_event_sum P m i hi (fun _ => True)
  simp only [Finset.filter_true] at he
  change selectionMass P m = _ at he
  rw [he,← Finset.sum_mul]
  change selectionMass P (eraseMultiplicity m i)*harmonicMass (P i) = _
  ring

theorem singleton_event_mass_bound {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (i : Fin n) (hi : m i = 1)
    (E : (Fin n → Finset ℕ) → Prop) (rho : ℝ)
    (h : ∀ f ∈ selections P (eraseMultiplicity m i),
      harmonicMass ((P i).filter (fun p => E (fillSelection f i p))) ≤ rho*harmonicMass (P i)) :
    (∑ f ∈ (selections P m).filter E,(selectionProduct f : ℝ)⁻¹) ≤ rho*selectionMass P m := by
  rw [singleton_event_sum P m i hi E]
  calc
    _ ≤ ∑ f ∈ selections P (eraseMultiplicity m i),(selectionProduct f : ℝ)⁻¹*(rho*harmonicMass (P i)) := by
      apply Finset.sum_le_sum
      intro f hf
      exact mul_le_mul_of_nonneg_left (h f hf) (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = rho*selectionMass P m := by
      rw [← Finset.sum_mul,singleton_total_mass P m i hi]
      change selectionMass P (eraseMultiplicity m i)*(rho*harmonicMass (P i)) = _
      ring

end ErdosVarianceWeighted

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_GeometricSelectionHardMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosVarianceWeighted
open NumberTheoryLean ErdosCofactorChoices SingletonBinSelection TwoPrimeObservableSum
attribute [local instance] Classical.propDecidable

theorem hardSelection_fill {n : ℕ} (Q : Finset ℚ) (z R theta : ℝ) (a : ℕ → ℕ)
    (i : Fin n) (Cs eps : ℝ) (f : Fin n → Finset ℕ) (he : f i = ∅) (p : ℕ) :
    hardSelection Q z R theta a i Cs eps (fillSelection f i p) ↔
      p ∈ rawHardPrimeUnion Q z R theta a (selectionProduct f) Cs eps := by
  unfold hardSelection
  rw [erase_fill f i p he]
  simp [pickedPrime,fillSelection]

theorem hardSelection_fibre {n : ℕ} (Q : Finset ℚ) (z R theta : ℝ) (a : ℕ → ℕ)
    (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (i : Fin n) (Cs eps : ℝ)
    (hPi : P i = ErdosInversePrimeBin.primeBin R theta)
    (f : Fin n → Finset ℕ) (hf : f ∈ selections P (eraseMultiplicity m i)) :
    (P i).filter (fun p => hardSelection Q z R theta a i Cs eps (fillSelection f i p)) =
      rawHardPrimeUnion Q z R theta a (selectionProduct f) Cs eps := by
  ext p
  rw [Finset.mem_filter,hardSelection_fill Q z R theta a i Cs eps f (erased_coordinate_empty P m i f hf) p,hPi]
  exact and_iff_right_of_imp (fun hp => rawHardPrimeUnion_subset Q z R theta a (selectionProduct f) Cs eps hp)

end ErdosVarianceWeighted


section

open _root_.Filter
namespace ErdosVarianceWeighted
open NumberTheoryLean ErdosInverseBoxHeight ErdosInversePrimeBin ErdosInverseCells ErdosCofactorChoices
  SingletonBinSelection CanonicalSubsetBox
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem source_selection_hard_mass_jb247_oai (alpha aStar eps tau Cmin : ℝ) (F : ℕ)
    (halpha : 0 < alpha) (ha : 0 < aStar) (heps : 0 < eps) (htau : 0 < tau) :
    ∃ Cs : ℝ,0 < Cs ∧ Cmin ≤ Cs ∧ ∃ xi0 : ℝ,0 < xi0 ∧ xi0 ≤ 1 ∧
      ∀ xi : ℝ,0 < xi → xi ≤ xi0 → ∀ᶠ z : ℝ in atTop,
      ∀ (R theta : ℝ),z^alpha ≤ R → xi/4 ≤ theta → theta ≤ xi →
      ∀ (a : ℕ → ℕ) (n : ℕ) (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (i : Fin n),m i = 1 →
        P i = primeBin R theta →
        (∀ f ∈ selections P (eraseMultiplicity m i),Squarefree (selectionProduct f) ∧
          (∀ t ∈ (selectionProduct f).primeFactors,sourceW z < (t : ℝ)) ∧
          (∀ p ∈ P i,(selectionProduct f).Coprime p ∧
            3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*selectionProduct f))/Real.log (sourceW z))) →
      ∀ Q : Finset ℚ,Q.card ≤ F →
        (∑ f ∈ (selections P m).filter (hardSelection Q z R theta a i Cs eps),(selectionProduct f : ℝ)⁻¹) ≤
          tau*selectionMass P m := by
  obtain ⟨Cs,hCs,hCmin,xi0,hxi0,hxi01,hsource⟩ :=
    source_raw_hard_prime_mass alpha aStar eps tau Cmin F halpha ha heps htau
  refine ⟨Cs,hCs,hCmin,xi0,hxi0,hxi01,?_⟩
  intro xi hxi hxib
  filter_upwards [hsource xi hxi hxib] with z hz
  intro R theta hRlo hthetal hthetau a n P m i hi hPi hgeometry Q hQ
  apply singleton_event_mass_bound P m i hi _ tau
  intro f hf
  have hg := hgeometry f hf
  rw [hPi] at hg
  rw [hardSelection_fibre Q z R theta a P m i Cs eps hPi f hf,hPi]
  exact hz R theta a (selectionProduct f) hg.1 hRlo hthetal hthetau hg.2.1 hg.2.2 Q hQ

end ErdosVarianceWeighted

end


open _root_.Filter


end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.ErdosVarianceWeighted.source_selection_hard_mass_jb247_oai := @OAI.Erdos970.ErdosVarianceWeighted.source_selection_hard_mass_jb247_oai
