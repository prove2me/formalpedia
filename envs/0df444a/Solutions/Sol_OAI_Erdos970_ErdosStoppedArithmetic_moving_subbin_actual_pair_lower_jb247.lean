-- Prove2me | solution 1 for OAI.Erdos970.ErdosStoppedArithmetic.moving_subbin_actual_pair_lower_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:56:52.985018+00:00
-- url     : https://prove2.me/submissions/3c7876b1-c493-4ccd-a1d3-95b66df51976

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Analysis.Fourier.FourierTransformDeriv
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
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Logic.Equiv.Prod
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.CircleAverage
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Tactic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Definitions.Def_OAIQ247J007
import Theorems.Thm_Erdos970_Mertens_LogZetaInteg_log_zeta_eq_integ_aux_jb247
import Theorems.Thm_Erdos970_Mertens_sum_M_eq_summand_le_jb247
import Theorems.Thm_OAI_Erdos970_Erdos970Dependency_SiegelWalfisz_moving_signed_prime_multiple_lower_jb247
import Theorems.Thm_OAI_Erdos970_ErdosStoppedTagSieve_tag_prime_sieve_lower_jb247
import Theorems.Thm_OAI_Erdos970_EulerWeightedLower_uniformLowerEnvelope_limit_jb247

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeLaw
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace EulerPrimeLaw

variable {p : ℝ} (hp : 2 ≤ p)
include hp

lemma reciprocal_nonneg : 0 ≤ 1 / p := by positivity
lemma reciprocal_lt_one : 1 / p < 1 := (div_lt_one (by linarith)).2 (by linarith)
omit hp in
lemma incrementProbability_nonneg : 0 ≤ incrementProbability p := by
  unfold incrementProbability
  positivity
lemma incrementProbability_le_one : incrementProbability p ≤ 1 := by
  have h : 1 ≤ (p - 1) ^ 2 := by nlinarith
  exact (div_le_one (by positivity : 0 < (p - 1) ^ 2)).2 h

lemma geometricMass_nonneg (j : ℕ) : 0 ≤ geometricMass p j :=
  mul_nonneg (sub_nonneg.mpr (reciprocal_lt_one hp).le)
    (pow_nonneg (reciprocal_nonneg hp) j)
lemma bernoulliMass_nonneg (b : Bool) : 0 ≤ bernoulliMass p b := by
  cases b <;> simp only [bernoulliMass, Bool.false_eq_true, ↓reduceIte]
  · exact sub_nonneg.mpr (incrementProbability_le_one hp)
  · exact incrementProbability_nonneg (p := p)
lemma jointMass_nonneg (s : Sample) : 0 ≤ jointMass p s :=
  mul_nonneg (bernoulliMass_nonneg hp s.1) (geometricMass_nonneg hp s.2)

theorem geometricMass_hasSum : HasSum (geometricMass p) 1 := by
  have h := (hasSum_geometric_of_lt_one (reciprocal_nonneg hp)
    (reciprocal_lt_one hp)).mul_left (1 - 1 / p)
  change HasSum (fun j : ℕ => (1 - 1 / p) * (1 / p) ^ j) 1
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  exact (mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr (reciprocal_lt_one hp)))).symm

omit hp in
lemma bernoulliMass_hasSum : HasSum (bernoulliMass p) 1 := by
  convert hasSum_fintype (bernoulliMass p) using 1
  all_goals try with_reducible_and_instances rfl
  simp [bernoulliMass]

lemma jointMass_summable : Summable (jointMass p) :=
  (bernoulliMass_hasSum (p := p)).summable.mul_of_nonneg
    (geometricMass_hasSum hp).summable (bernoulliMass_nonneg hp) (geometricMass_nonneg hp)

theorem jointMass_hasSum : HasSum (jointMass p) 1 := by
  apply (jointMass_summable hp).hasSum_iff.mpr
  rw [(jointMass_summable hp).tsum_prod]
  simp only [jointMass, tsum_mul_left, (geometricMass_hasSum hp).tsum_eq, mul_one]
  exact (bernoulliMass_hasSum (p := p)).tsum_eq

lemma event_summable (A : Sample → Prop) [DecidablePred A] :
    Summable (fun s => if A s then jointMass p s else 0) := by
  apply (jointMass_summable hp).of_nonneg_of_le
  · intro s; split_ifs <;> simp_all only [le_refl, jointMass_nonneg hp]
  · intro s; split_ifs <;> simp_all only [le_refl, jointMass_nonneg hp]

theorem lowerExponent_marginal (j : ℕ) :
    (∑' s : Sample, if lowerExponent s = j then jointMass p s else 0) =
      geometricMass p j := by
  rw [(event_summable hp (fun s => lowerExponent s = j)).tsum_prod]
  simp only [lowerExponent, jointMass, tsum_ite_eq, tsum_fintype, Fintype.sum_bool,
    bernoulliMass, Bool.false_eq_true, ↓reduceIte]
  ring

lemma zero_convolution : bernoulliMass p false * geometricMass p 0 = eulerMass p 0 := by
  have hp0 : p ≠ 0 := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  simp only [bernoulliMass, Bool.false_eq_true, ↓reduceIte, incrementProbability,
    geometricMass, pow_zero, mul_one, eulerMass]
  field_simp
  ring

lemma succ_convolution (j : ℕ) :
    bernoulliMass p false * geometricMass p (j + 1) +
      bernoulliMass p true * geometricMass p j = eulerMass p (j + 1) := by
  have hp0 : p ≠ 0 := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  simp only [bernoulliMass, Bool.false_eq_true, ↓reduceIte, incrementProbability,
    geometricMass, eulerMass, pow_succ]
  field_simp
  ring

theorem upperExponent_marginal (j : ℕ) :
    (∑' s : Sample, if upperExponent s = j then jointMass p s else 0) = eulerMass p j := by
  rw [(event_summable hp (fun s => upperExponent s = j)).tsum_prod]
  simp only [tsum_fintype, Fintype.sum_bool, upperExponent, jointMass, Bool.false_eq_true, ↓reduceIte,
    Nat.add_zero]
  cases j with
  | zero =>
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        tsum_zero, zero_add, tsum_ite_eq]
      exact zero_convolution hp
  | succ j =>
      simp only [Nat.add_left_inj, tsum_ite_eq]
      simpa only [add_comm] using succ_convolution hp j

omit hp in

lemma weighted_log_excess (s : Sample) :
    jointMass p s * ((upperExponent s - lowerExponent s : ℕ) : ℝ) * Real.log p =
      (bernoulliMass p s.1 * (if s.1 then Real.log p else 0)) * geometricMass p s.2 := by
  rcases s with ⟨b, j⟩
  cases b <;> simp [jointMass, upperExponent, lowerExponent, mul_comm, mul_assoc]

lemma log_excess_summable : Summable (fun s : Sample =>
    jointMass p s * ((upperExponent s - lowerExponent s : ℕ) : ℝ) * Real.log p) := by
  have hb : ∀ b : Bool, 0 ≤ bernoulliMass p b * (if b then Real.log p else 0) := by
    intro b
    apply mul_nonneg (bernoulliMass_nonneg hp b)
    split_ifs
    · exact Real.log_nonneg (by linarith)
    · rfl
  have h := (hasSum_fintype (fun b : Bool =>
    bernoulliMass p b * (if b then Real.log p else 0))).summable.mul_of_nonneg
      (geometricMass_hasSum hp).summable hb (geometricMass_nonneg hp)
  exact h.congr (fun s => (weighted_log_excess s).symm)

theorem expected_log_excess :
    (∑' s : Sample, jointMass p s *
      ((upperExponent s - lowerExponent s : ℕ) : ℝ) * Real.log p) =
        Real.log p / (p - 1) ^ 2 := by
  rw [(log_excess_summable hp).tsum_prod]
  simp only [weighted_log_excess, tsum_mul_left, (geometricMass_hasSum hp).tsum_eq,
    mul_one, tsum_fintype, Fintype.sum_bool, bernoulliMass, Bool.false_eq_true,
    ↓reduceIte, mul_zero, add_zero, incrementProbability]
  ring

omit hp in

theorem lowerExponent_le_upperExponent (s : Sample) : lowerExponent s ≤ upperExponent s := by
  exact Nat.le_add_right _ _

end EulerPrimeLaw

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_UniformMoment
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace EulerPrimeLaw

theorem log_excess_le_rpow {p : ℝ} (hp : 2 ≤ p) :
    Real.log p / (p - 1) ^ 2 ≤ 8 * p ^ (-3 / 2 : ℝ) := by
  have hp0 : 0 < p := by linarith
  have hlog : Real.log p ≤ 2 * p ^ (1 / 2 : ℝ) := by
    convert Real.log_le_rpow_div hp0.le (by norm_num : (0 : ℝ) < 1 / 2) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hden : p ^ 2 / 4 ≤ (p - 1) ^ 2 := by nlinarith [sq_nonneg (p - 2)]
  calc
    Real.log p / (p - 1) ^ 2 ≤ (2 * p ^ (1 / 2 : ℝ)) / (p - 1) ^ 2 :=
      div_le_div_of_nonneg_right hlog (sq_nonneg _)
    _ ≤ (2 * p ^ (1 / 2 : ℝ)) / (p ^ 2 / 4) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = 8 * p ^ (-3 / 2 : ℝ) := by
      rw [show (-3 / 2 : ℝ) = 1 / 2 - 2 by norm_num, Real.rpow_sub hp0, Real.rpow_two]
      ring

lemma integerLogMoment_nonneg (n : ℕ) : 0 ≤ integerLogMoment n := by
  cases n with
  | zero => simp [integerLogMoment]
  | succ n =>
      apply div_nonneg _ (sq_nonneg _)
      exact Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))

lemma integerLogMoment_le (n : ℕ) : integerLogMoment n ≤ 8 * (n : ℝ) ^ (-3 / 2 : ℝ) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> norm_num [integerLogMoment]
  · exact log_excess_le_rpow (by exact_mod_cast h)

theorem integerLogMoment_summable : Summable integerLogMoment := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-3 / 2 : ℝ)) := by
    apply Real.summable_nat_rpow.mpr
    norm_num
  exact (hs.mul_left 8).of_nonneg_of_le integerLogMoment_nonneg integerLogMoment_le

theorem finite_log_moment_le (E : Finset ℕ) :
    (∑ p ∈ E, Real.log (p : ℝ) / ((p : ℝ) - 1) ^ 2) ≤ uniformMomentBound := by
  have h := integerLogMoment_summable.sum_le_tsum E (fun n _ => integerLogMoment_nonneg n)
  change (∑ p ∈ E, integerLogMoment p) ≤ 1 + ∑' n : ℕ, integerLogMoment n
  linarith

end EulerPrimeLaw

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ProductRestriction
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace EulerWeightedLower
open Erdos970.EulerPrimeLaw
attribute [local instance] Classical.propDecidable

private lemma hasSum_mul_nonneg {α β : Type*} {f : α → ℝ} {g : β → ℝ}
    {a b : ℝ} (hf : HasSum f a) (hg : HasSum g b)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ y, 0 ≤ g y) :
    HasSum (fun s : α × β => f s.1 * g s.2) (a * b) :=
  HasSum.mul hf hg (Summable.mul_of_nonneg hf.summable hg.summable hfn hgn)

theorem hasSum_fin_product {α : Type*} {n : ℕ} (w : Fin n → α → ℝ)
    (a : Fin n → ℝ) (hw : ∀ i x, 0 ≤ w i x) (hs : ∀ i, HasSum (w i) (a i)) :
    HasSum (fun s : Fin n → α => ∏ i, w i (s i)) (∏ i, a i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ht : HasSum (fun s : Fin n → α => ∏ i : Fin n, w i.succ (s i))
        (∏ i : Fin n, a i.succ) :=
      ih (fun i => w i.succ) (fun i => a i.succ)
      (fun i => hw i.succ) (fun i => hs i.succ)
    have hn : ∀ s : Fin n → α, 0 ≤ ∏ i, w i.succ (s i) := by
      intro s; exact Finset.prod_nonneg (fun i _ => hw i.succ (s i))
    have hprod : HasSum (fun s : α × (Fin n → α) =>
        w 0 s.1 * ∏ i : Fin n, w i.succ (s.2 i)) (a 0 * ∏ i : Fin n, a i.succ) :=
      hasSum_mul_nonneg (f := w 0)
        (g := fun s : Fin n → α => ∏ i : Fin n, w i.succ (s i))
        (a := a 0) (b := ∏ i : Fin n, a i.succ) (hs 0) ht (hw 0) hn
    apply (Fin.consEquiv (fun _ : Fin (n+1) => α)).hasSum_iff.mp
    simpa only [Function.comp_def, Fin.consEquiv_apply, Fin.prod_univ_succ,
      Fin.cons_zero, Fin.cons_succ] using hprod

theorem hasSum_finite_product {ι α : Type*} [Fintype ι]
    (w : ι → α → ℝ) (a : ι → ℝ) (hw : ∀ i x, 0 ≤ w i x)
    (hs : ∀ i, HasSum (w i) (a i)) :
    HasSum (fun s : ι → α => ∏ i, w i (s i)) (∏ i, a i) := by
  let e := (Fintype.equivFin ι).symm
  have h := hasSum_fin_product (fun i => w (e i)) (fun i => a (e i))
    (fun i => hw (e i)) (fun i => hs (e i))
  rw [e.prod_comp a] at h
  apply (Equiv.piCongrLeft (fun _ : ι => α) e).hasSum_iff.mp
  apply h.congr_fun
  intro s
  dsimp only [Function.comp_def]
  rw [← e.prod_comp]
  congr 1
  funext i
  simp [Equiv.piCongrLeft]

theorem product_coordinate_hasSum {ι α : Type*} [Fintype ι]
    (w : ι → α → ℝ) (hw : ∀ i x, 0 ≤ w i x)
    (hs : ∀ i, HasSum (w i) 1) (j : ι) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) {b : ℝ} (hb : HasSum (fun x => w j x * f x) b) :
    HasSum (fun s : ι → α => (∏ i, w i (s i)) * f (s j)) b := by
  classical
  have h := hasSum_finite_product
    (fun i x => w i x * if i = j then f x else 1)
    (fun i => if i = j then b else 1)
    (by intro i x; exact mul_nonneg (hw i x) (by split_ifs; exact hf x; norm_num))
    (by intro i; by_cases hij : i = j
        · subst i; simpa only [ite_true, if_true] using hb
        · simpa only [ite_eq_right hij, mul_one] using hs i)
  simpa only [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ,
    ite_true, if_true] using h

end EulerWeightedLower



namespace EulerWeightedLower
open Erdos970.EulerPrimeLaw
attribute [local instance] Classical.propDecidable

variable (E : Finset ℕ) (hE : ∀ p ∈ E, 2 ≤ p)
include hE

lemma productMass_nonneg (s : Outcomes E) : 0 ≤ productMass E s := by
  apply Finset.prod_nonneg
  intro p _
  exact jointMass_nonneg (by exact_mod_cast hE p p.property) (s p)

theorem productMass_hasSum : HasSum (productMass E) 1 := by
  have h := hasSum_finite_product (fun p : E => jointMass (p : ℝ)) (fun _ => (1 : ℝ))
    (fun p => jointMass_nonneg (by exact_mod_cast hE p p.property))
    (fun p => jointMass_hasSum (by exact_mod_cast hE p p.property))
  change HasSum (fun s : E → Sample => ∏ p : E, jointMass (p : ℝ) (s p)) 1
  simpa only [Finset.prod_const_one] using h

lemma product_event_summable (A : Outcomes E → Prop) :
    Summable (fun s => if A s then productMass E s else 0) := by
  apply (productMass_hasSum E hE).summable.of_nonneg_of_le
  · intro s; split_ifs <;> simp_all only [le_refl, productMass_nonneg E hE]
  · intro s; split_ifs <;> simp_all only [le_refl, productMass_nonneg E hE]

lemma excessLog_nonneg (s : Outcomes E) : 0 ≤ excessLog E s := by
  apply Finset.sum_nonneg
  intro p _
  exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (hE p p.property).trans' (by omega : 1 ≤ 2)))

theorem product_excess_hasSum :
    HasSum (fun s => productMass E s * excessLog E s)
      (∑ p ∈ E, Real.log (p : ℝ) / ((p : ℝ) - 1)^2) := by
  have hlocal (p : E) : HasSum (fun s : Outcomes E => productMass E s *
      (((upperExponent (s p) - lowerExponent (s p) : ℕ) : ℝ) * Real.log (p : ℝ)))
      (Real.log (p : ℝ) / ((p : ℝ)-1)^2) := by
    apply product_coordinate_hasSum (fun q : E => jointMass (q : ℝ))
      (fun q => jointMass_nonneg (by exact_mod_cast hE q q.property))
      (fun q => jointMass_hasSum (by exact_mod_cast hE q q.property)) p
      (fun s => (((upperExponent s - lowerExponent s : ℕ) : ℝ) * Real.log (p : ℝ)))
    · intro s
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (hE p p.property).trans' (by omega : 1 ≤ 2)))
    · have hp : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hE p p.property
      rw [← expected_log_excess hp]
      simpa only [mul_assoc] using (log_excess_summable hp).hasSum
  have h := hasSum_sum (s := Finset.univ) (fun p _ => hlocal p)
  have he : (∑ p : E, Real.log (p : ℝ) / ((p : ℝ)-1)^2) =
      ∑ p ∈ E, Real.log (p : ℝ) / ((p : ℝ)-1)^2 := by
    exact Finset.sum_attach E (fun p : ℕ => Real.log (p : ℝ) / ((p : ℝ)-1)^2)
  rw [he] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext s
  exact Finset.mul_sum _ _ _

theorem product_excess_mean_le :
    (∑' s : Outcomes E, productMass E s * excessLog E s) ≤ uniformMomentBound := by
  rw [(product_excess_hasSum E hE).tsum_eq]
  exact finite_log_moment_le E

theorem excess_tail_le {t : ℝ} (ht : 0 < t) :
    eventMass E (fun s => t < excessLog E s) ≤ uniformMomentBound / t := by
  apply (le_div_iff₀ ht).mpr
  rw [eventMass, ← tsum_mul_right]
  apply le_trans _ (product_excess_mean_le E hE)
  apply Summable.tsum_le_tsum
  · intro s
    by_cases h : t < excessLog E s
    · simp only [ite_eq_left h]
      exact mul_le_mul_of_nonneg_left h.le (productMass_nonneg E hE s)
    · simp only [ite_eq_right h, zero_mul]
      exact mul_nonneg (productMass_nonneg E hE s) (excessLog_nonneg E hE s)
  · exact (product_event_summable E hE _).mul_right t
  · exact (product_excess_hasSum E hE).summable

end EulerWeightedLower



namespace EulerWeightedLower
attribute [local instance] Classical.propDecidable

theorem finite_product_restrict {ι α : Type*} [Fintype ι] (P : ι → Prop)
    (w : ι → α → ℝ) (hw : ∀ i x, 0 ≤ w i x) (hs : ∀ i, HasSum (w i) 1)
    (A : ({i // P i} → α) → Prop) :
    (∑' s : ι → α, if A (fun i => s i) then ∏ i, w i (s i) else 0) =
      ∑' s : {i // P i} → α, if A s then ∏ i : {i // P i}, w i (s i) else 0 := by
  classical
  let e := Equiv.piEquivPiSubtypeProd P (fun _ => α)
  have hsub := hasSum_finite_product (fun i : {i // P i} => w i) (fun _ => (1 : ℝ))
    (fun i => hw i) (fun i => hs i)
  have hcomp := hasSum_finite_product (fun i : {i // ¬P i} => w i) (fun _ => (1 : ℝ))
    (fun i => hw i) (fun i => hs i)
  simp only [Finset.prod_const_one] at hsub hcomp
  have hn (s : {i // P i} → α) : 0 ≤ ∏ i : {i // P i}, w i (s i) :=
    Finset.prod_nonneg (fun i _ => hw i.val (s i))
  have hc (s : {i // ¬P i} → α) : 0 ≤ ∏ i : {i // ¬P i}, w i (s i) :=
    Finset.prod_nonneg (fun i _ => hw i.val (s i))
  have hA : Summable (fun s : {i // P i} → α => if A s then ∏ i : {i // P i}, w i (s i) else 0) := by
    apply hsub.summable.of_nonneg_of_le
    · intro s; split_ifs; exact hn s; rfl
    · intro s; split_ifs; rfl; exact hn s
  have hprod := hA.mul_of_nonneg hcomp.summable
    (by intro s; dsimp only [Pi.zero_apply]; split_ifs; exact hn s; rfl) hc
  calc
    _ = ∑' z : ({i // P i} → α) × ({i // ¬P i} → α),
        (if A z.1 then ∏ i : {i // P i}, w i (z.1 i) else 0) * ∏ i : {i // ¬P i}, w i (z.2 i) := by
      rw [← e.symm.tsum_eq]
      apply tsum_congr
      intro z
      have hsplit := Fintype.prod_subtype_mul_prod_subtype P (fun i => w i (e.symm z i))
      rw [← hsplit]
      have hl (i : {i // P i}) : e.symm z i = z.1 i := by
        simp [e, Equiv.piEquivPiSubtypeProd, i.property]
      have hr (i : {i // ¬P i}) : e.symm z i = z.2 i := by
        simp [e, Equiv.piEquivPiSubtypeProd, i.property]
      simp only [hl, hr]
      by_cases hh : A z.1 <;> simp only [hh, ite_true, if_true, ite_false, if_false, zero_mul]
    _ = _ := by
      rw [hprod.tsum_prod]
      simp only [tsum_mul_left, hcomp.tsum_eq, mul_one]

end EulerWeightedLower


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

end NumberTheoryLean.ReferenceProductsBasics

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_IntegerLaw
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace EulerWeightedLower
open Erdos970.EulerPrimeLaw
attribute [local instance] Classical.propDecidable

variable (E : Finset ℕ) (hE : ∀ p ∈ E, Nat.Prime p)
include hE

lemma integerProduct_pos (k : E → ℕ) : 0 < integerProduct E k := by
  exact Finset.prod_pos (fun p _ => pow_pos (hE p p.property).pos _)

theorem integerProduct_factorization (k : E → ℕ) (q : E) :
    (integerProduct E k).factorization q = k q := by
  classical
  rw [integerProduct, Nat.factorization_prod (S := Finset.univ) (g := fun p : E => (p : ℕ) ^ k p) (fun p _ => pow_ne_zero _ (hE p p.property).ne_zero)]
  simp only [Finsupp.finsetSum_apply]
  have h (p : E) : ((p : ℕ) ^ k p).factorization q = if p = q then k p else 0 := by
    rw [(hE p p.property).factorization_pow]
    simp only [Finsupp.single_apply, Subtype.val_inj]
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]

theorem integerProduct_factorization_outside (k : E → ℕ) {q : ℕ} (hq : q ∉ E) :
    (integerProduct E k).factorization q = 0 := by
  rw [integerProduct, Nat.factorization_prod (S := Finset.univ)
    (g := fun p : E => (p : ℕ) ^ k p) (fun p _ => pow_ne_zero _ (hE p p.property).ne_zero)]
  simp only [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro p _
  rw [(hE p p.property).factorization_pow]
  apply Finsupp.single_eq_of_ne
  intro hpq
  exact hq (hpq ▸ p.property)

theorem integerProduct_support (k : E → ℕ) : (integerProduct E k).primeFactors ⊆ E := by
  intro q hq
  by_contra hn
  have hh : q ∈ (integerProduct E k).factorization.support := by
    simpa only [Nat.support_factorization] using hq
  exact Finsupp.mem_support_iff.mp hh (integerProduct_factorization_outside E hE k hn)

omit hE in

theorem integerProduct_factorization_reconstruct {d : ℕ} (hd : d ≠ 0)
    (hs : d.primeFactors ⊆ E) :
    integerProduct E (fun p => d.factorization p) = d := by
  rw [integerProduct]
  change (∏ p ∈ E.attach, (p : ℕ) ^ d.factorization p) = d
  rw [Finset.prod_attach E (fun p : ℕ => p ^ d.factorization p)]
  calc
    _ = d.factorization.prod (· ^ ·) := by
      symm
      apply Finset.prod_subset
      · simpa only [Nat.support_factorization] using hs
      · intro p _ hp
        have hz : d.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
        simp only [hz, pow_zero]
    _ = d := Nat.prod_factorization_pow_eq_self hd

end EulerWeightedLower


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_CouplingEvent
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace EulerWeightedLower
open Erdos970.EulerPrimeLaw
attribute [local instance] Classical.propDecidable

variable (E : Finset ℕ) (hE : ∀ p ∈ E, Nat.Prime p)
include hE

lemma log_integerProduct (k : E → ℕ) :
    Real.log (integerProduct E k : ℝ) = ∑ p : E, (k p : ℝ) * Real.log (p : ℝ) := by
  rw [integerProduct, Nat.cast_prod]
  rw [Real.log_prod]
  · simp only [Nat.cast_pow, Real.log_pow]
  · intro p _; exact_mod_cast pow_ne_zero (k p) (hE p p.property).ne_zero

theorem upper_log_eq_lower_add_excess (s : Outcomes E) :
    Real.log (upperInteger E s : ℝ) = Real.log (lowerInteger E s : ℝ) + excessLog E s := by
  rw [upperInteger, lowerInteger, log_integerProduct E hE, log_integerProduct E hE]
  unfold excessLog
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [Nat.cast_sub (lowerExponent_le_upperExponent (s p))]
  ring

theorem source_cutoff_implication {P : ℝ} (hP : 1 < P) (s : Outcomes E)
    (hl : (lowerInteger E s : ℝ) ≤ P ^ (94 / 100 : ℝ))
    (hz : excessLog E s ≤ (1 / 100 : ℝ) * Real.log P) :
    (upperInteger E s : ℝ) ≤ P ^ (95 / 100 : ℝ) := by
  have hu : 0 < (upperInteger E s : ℝ) := by
    exact_mod_cast integerProduct_pos E hE (fun p => upperExponent (s p))
  have hl0 : 0 < (lowerInteger E s : ℝ) := by
    exact_mod_cast integerProduct_pos E hE (fun p => lowerExponent (s p))
  apply (Real.log_le_log_iff hu (Real.rpow_pos_of_pos (by linarith) _)).mp
  rw [upper_log_eq_lower_add_excess E hE]
  have hh := Real.log_le_log hl0 hl
  rw [Real.log_rpow (by linarith : 0 < P)] at hh ⊢
  linarith

theorem small_product_coupling_lower {P : ℝ} (hP : 1 < P) :
    eventMass E (fun s => (lowerInteger E s : ℝ) ≤ P ^ (94 / 100 : ℝ)) -
        100 * uniformMomentBound / Real.log P ≤
      eventMass E (fun s => (upperInteger E s : ℝ) ≤ P ^ (95 / 100 : ℝ)) := by
  have htwo : ∀ p ∈ E, 2 ≤ p := fun p hp => (hE p hp).two_le
  let L : Outcomes E → Prop := fun s => (lowerInteger E s : ℝ) ≤ P ^ (94 / 100 : ℝ)
  let U : Outcomes E → Prop := fun s => (upperInteger E s : ℝ) ≤ P ^ (95 / 100 : ℝ)
  let B : Outcomes E → Prop := fun s => (1 / 100 : ℝ) * Real.log P < excessLog E s
  have hi : eventMass E L ≤ eventMass E U + eventMass E B := by
    rw [eventMass, eventMass, eventMass, ← Summable.tsum_add
      (product_event_summable E htwo U) (product_event_summable E htwo B)]
    apply Summable.tsum_le_tsum _ (product_event_summable E htwo L)
      ((product_event_summable E htwo U).add (product_event_summable E htwo B))
    intro s
    have hw := productMass_nonneg E htwo s
    by_cases hl : L s
    · by_cases hz : B s
      · simp only [ite_eq_left hl, ite_eq_left hz]; split_ifs <;> linarith
      · have hu : U s := source_cutoff_implication E hE hP s hl (le_of_not_gt hz)
        simp only [ite_eq_left hl, ite_eq_left hu, ite_eq_right hz, add_zero, le_refl]
    · simp only [ite_eq_right hl]; split_ifs <;> linarith
  have ht := excess_tail_le E htwo (show 0 < (1 / 100 : ℝ) * Real.log P by
    exact mul_pos (by norm_num) (Real.log_pos hP))
  have he : uniformMomentBound / ((1 / 100 : ℝ) * Real.log P) =
      100 * uniformMomentBound / Real.log P := by ring
  rw [he] at ht
  change eventMass E L - _ ≤ eventMass E U
  change eventMass E B ≤ _ at ht
  linarith

end EulerWeightedLower


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ExponentMarginals
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace EulerWeightedLower
open Erdos970.EulerPrimeLaw
attribute [local instance] Classical.propDecidable

lemma product_event_indicator {ι : Type*} [Fintype ι] (A : ι → Prop)
    (w : ι → ℝ) :
    (∏ i, if A i then w i else 0) = if ∀ i, A i then ∏ i, w i else 0 := by
  classical
  by_cases h : ∀ i, A i
  · simp [h]
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

theorem product_marginal (E : Finset ℕ) (hE : ∀ p ∈ E, 2 ≤ p)
    (A : E → Sample → Prop) (a : E → ℝ)
    (ha : ∀ p, (∑' s : Sample, if A p s then jointMass (p : ℝ) s else 0) = a p) :
    eventMass E (fun s => ∀ p, A p (s p)) = ∏ p, a p := by
  have h := hasSum_finite_product (fun p s => if A p s then jointMass (p : ℝ) s else 0)
    a (by intro p s; split_ifs; exact jointMass_nonneg (by exact_mod_cast hE p p.property) s; rfl)
    (by intro p; rw [← ha p]; exact (event_summable (by exact_mod_cast hE p p.property) (A p)).hasSum)
  rw [← h.tsum_eq]
  apply tsum_congr
  intro s
  have he := (product_event_indicator (fun p => A p (s p)) (fun p => jointMass (p : ℝ) (s p))).symm
  by_cases hh : ∀ p, A p (s p)
  · rw [ite_eq_left hh] at he
    rw [ite_eq_left hh]
    exact he
  · rw [ite_eq_right hh] at he
    rw [ite_eq_right hh]
    exact he

theorem upper_vector_marginal (E : Finset ℕ) (hE : ∀ p ∈ E, 2 ≤ p) (k : E → ℕ) :
    eventMass E (fun s => ∀ p, upperExponent (s p) = k p) =
      ∏ p : E, eulerMass (p : ℝ) (k p) := by
  exact product_marginal E hE (fun p s => upperExponent s = k p)
    (fun p => eulerMass (p : ℝ) (k p))
    (by
      intro p
      have hp := upperExponent_marginal (p := (p : ℝ)) (by exact_mod_cast hE p p.property) (k p)
      convert hp using 1
      all_goals try with_reducible_and_instances rfl
      apply tsum_congr
      intro s
      by_cases hh : upperExponent s = k p <;> simp only [hh, ite_true, if_true, ite_false, if_false])

theorem lower_vector_marginal (E : Finset ℕ) (hE : ∀ p ∈ E, 2 ≤ p) (k : E → ℕ) :
    eventMass E (fun s => ∀ p, lowerExponent (s p) = k p) =
      ∏ p : E, geometricMass (p : ℝ) (k p) := by
  exact product_marginal E hE (fun p s => lowerExponent s = k p)
    (fun p => geometricMass (p : ℝ) (k p))
    (by
      intro p
      have hp := lowerExponent_marginal (p := (p : ℝ)) (by exact_mod_cast hE p p.property) (k p)
      convert hp using 1
      all_goals try with_reducible_and_instances rfl
      apply tsum_congr
      intro s
      by_cases hh : lowerExponent s = k p <;> simp only [hh, ite_true, if_true, ite_false, if_false])

end EulerWeightedLower


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_UniformLower
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace EulerWeightedLower
open Erdos970.EulerPrimeLaw
attribute [local instance] Classical.propDecidable

lemma eventMass_congr (E : Finset ℕ) {A B : Outcomes E → Prop}
    (h : ∀ s, A s ↔ B s) : eventMass E A = eventMass E B := by
  apply tsum_congr
  intro s
  simp only [h s]

lemma eulerMass_as_weight {p : ℝ} (hp : 2 ≤ p) (j : ℕ) :
    eulerMass p j = (if j = 0 then (1 - 1 / (p - 1)) else 1) / p ^ j := by
  cases j with
  | zero =>
    simp only [eulerMass, ite_true, if_true, pow_zero, div_one]
    have hp1 : p - 1 ≠ 0 := by linarith
    field_simp
    ring
  | succ j => simp [eulerMass]

variable (E : Finset ℕ) (hE : ∀ p ∈ E, Nat.Prime p)
include hE

theorem product_eq_iff_vector {d : ℕ} (hd : d ≠ 0) (hs : d.primeFactors ⊆ E)
    (k : E → ℕ) :
    integerProduct E k = d ↔ ∀ p, k p = d.factorization p := by
  constructor
  · intro hh p
    rw [← hh, integerProduct_factorization E hE]
  · intro hh
    rw [show k = (fun p : E => d.factorization p) from funext hh]
    exact integerProduct_factorization_reconstruct E hd hs

theorem upper_integer_mass {d : ℕ} (hd : d ≠ 0) (hs : d.primeFactors ⊆ E) :
    eventMass E (fun s => upperInteger E s = d) = paperWeight E d / (d : ℝ) := by
  calc
    _ = eventMass E (fun s => ∀ p, upperExponent (s p) = d.factorization p) :=
      eventMass_congr E (fun s => product_eq_iff_vector E hE hd hs (fun p => upperExponent (s p)))
    _ = ∏ p : E, eulerMass (p : ℝ) (d.factorization p) :=
      upper_vector_marginal E (fun p hp => (hE p hp).two_le) _
    _ = (∏ p : E, if d.factorization p = 0 then (1-1/((p : ℝ)-1)) else 1) /
        (∏ p : E, (p : ℝ) ^ d.factorization p) := by
      rw [← Finset.prod_div_distrib]
      apply Finset.prod_congr rfl
      intro p _
      exact eulerMass_as_weight (by exact_mod_cast (hE p p.property).two_le) _
    _ = paperWeight E d / (d : ℝ) := by
      congr 1
      · unfold paperWeight
        rw [Finset.prod_filter]
        have he : (∏ p : E, if d.factorization p = 0 then (1-1/((p : ℝ)-1)) else 1) =
            ∏ p ∈ E, if d.factorization p = 0 then (1-1/((p : ℝ)-1)) else 1 :=
          Finset.prod_attach E (fun p : ℕ => if d.factorization p = 0 then (1-1/((p : ℝ)-1)) else 1)
        rw [he]
        apply Finset.prod_congr rfl
        intro p hp
        simp only [Nat.factorization_eq_zero_iff, hd, hE p hp, not_true_eq_false,
          or_false, false_or]
      · have hh := congrArg (fun n : ℕ => (n : ℝ)) (integerProduct_factorization_reconstruct E hd hs)
        simpa only [integerProduct, Nat.cast_prod, Nat.cast_pow] using hh

theorem lower_integer_mass {d : ℕ} (hd : d ≠ 0) (hs : d.primeFactors ⊆ E) :
    eventMass E (fun s => lowerInteger E s = d) = ordinaryProduct E / (d : ℝ) := by
  calc
    _ = eventMass E (fun s => ∀ p, lowerExponent (s p) = d.factorization p) :=
      eventMass_congr E (fun s => product_eq_iff_vector E hE hd hs (fun p => lowerExponent (s p)))
    _ = ∏ p : E, geometricMass (p : ℝ) (d.factorization p) :=
      lower_vector_marginal E (fun p hp => (hE p hp).two_le) _
    _ = (∏ p : E, (1 - 1 / (p : ℝ))) / (∏ p : E, (p : ℝ) ^ d.factorization p) := by
      rw [← Finset.prod_div_distrib]
      apply Finset.prod_congr rfl
      intro p _
      simp [geometricMass, div_eq_mul_inv]
    _ = ordinaryProduct E / (d : ℝ) := by
      congr 1
      · exact Finset.prod_attach E (fun p : ℕ => 1 - 1 / (p : ℝ))
      · have hh := congrArg (fun n : ℕ => (n : ℝ)) (integerProduct_factorization_reconstruct E hd hs)
        simpa only [integerProduct, Nat.cast_prod, Nat.cast_pow] using hh

end EulerWeightedLower



namespace EulerWeightedLower
open Erdos970.EulerPrimeLaw
attribute [local instance] Classical.propDecidable

theorem eventMass_finite_values (E : Finset ℕ) (hE : ∀ p ∈ E, 2 ≤ p)
    (f : Outcomes E → ℕ) (D : Finset ℕ) :
    eventMass E (fun s => f s ∈ D) = ∑ d ∈ D, eventMass E (fun s => f s = d) := by
  unfold eventMass
  rw [← Summable.tsum_finsetSum (fun d _ => product_event_summable E hE (fun s => f s = d))]
  apply tsum_congr
  intro s
  have he := Finset.sum_ite_eq D (f s) (fun _ : ℕ => productMass E s)
  convert he.symm using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first
    | (apply Finset.sum_congr rfl; intro d _; split_ifs <;> rfl)
    | (split_ifs <;> rfl)

theorem product_mem_supported_iff (E : Finset ℕ) (hE : ∀ p ∈ E, Nat.Prime p)
    (k : E → ℕ) (N : ℕ) :
    integerProduct E k ∈ supportedIntegers E N ↔ integerProduct E k ≤ N := by
  simp only [supportedIntegers, Finset.mem_filter, Finset.mem_Icc]
  have hp := integerProduct_pos E hE k
  have hs := integerProduct_support E hE k
  exact ⟨fun h => h.1.2, fun h => ⟨⟨hp, h⟩, hs⟩⟩

theorem weightedSmallSum_eq_event (E : Finset ℕ) (hE : ∀ p ∈ E, Nat.Prime p) (N : ℕ) :
    weightedSmallSum E N = eventMass E (fun s => upperInteger E s ≤ N) := by
  unfold weightedSmallSum
  simp only [upperInteger]
  rw [← eventMass_congr E (fun s => product_mem_supported_iff E hE (fun p => upperExponent (s p)) N)]
  rw [eventMass_finite_values E (fun p hp => (hE p hp).two_le)]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨hI, hs⟩ := Finset.mem_filter.mp hd
  exact (upper_integer_mass E hE (by have := (Finset.mem_Icc.mp hI).1; omega) hs).symm

theorem ordinarySmallSum_eq_event (E : Finset ℕ) (hE : ∀ p ∈ E, Nat.Prime p) (N : ℕ) :
    ordinarySmallSum E N = eventMass E (fun s => lowerInteger E s ≤ N) := by
  simp only [lowerInteger]
  rw [← eventMass_congr E (fun s => product_mem_supported_iff E hE (fun p => lowerExponent (s p)) N)]
  rw [eventMass_finite_values E (fun p hp => (hE p hp).two_le)]
  unfold ordinarySmallSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨hI, hs⟩ := Finset.mem_filter.mp hd
  have hm := lower_integer_mass E hE (d := d) (by have := (Finset.mem_Icc.mp hI).1; omega) hs
  calc
    _ = ordinaryProduct E / (d : ℝ) := by ring
    _ = _ := hm.symm

theorem weightedSmallSum_coupling_lower (E : Finset ℕ) (hE : ∀ p ∈ E, Nat.Prime p)
    {P : ℝ} (hP : 1 < P) :
    ordinarySmallSum E ⌊P ^ (94 / 100 : ℝ)⌋₊ - 100 * uniformMomentBound / Real.log P ≤
      weightedSmallSum E ⌊P ^ (95 / 100 : ℝ)⌋₊ := by
  rw [ordinarySmallSum_eq_event E hE, weightedSmallSum_eq_event E hE]
  have he (f : Outcomes E → ℕ) (a : ℝ) :
      eventMass E (fun s => f s ≤ ⌊P ^ a⌋₊) = eventMass E (fun s => (f s : ℝ) ≤ P ^ a) := by
    apply eventMass_congr E
    intro s
    exact Nat.le_floor_iff (Real.rpow_nonneg (by linarith) _)
  rw [he, he]
  exact small_product_coupling_lower E hE hP

end EulerWeightedLower



namespace EulerWeightedLower
open Erdos970.EulerPrimeLaw
attribute [local instance] Classical.propDecidable

theorem finite_product_reindex {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (w : κ → α → ℝ) (A : (κ → α) → Prop) :
    (∑' s : ι → α, if A ((Equiv.piCongrLeft (fun _ : κ => α) e) s)
      then ∏ i, w (e i) (s i) else 0) =
    ∑' s : κ → α, if A s then ∏ i, w i (s i) else 0 := by
  rw [← (Equiv.piCongrLeft (fun _ : κ => α) e).tsum_eq]
  apply tsum_congr
  intro s
  split_ifs
  · rw [← e.prod_comp]
    apply Finset.prod_congr rfl
    intro i _
    simp [Equiv.piCongrLeft]
  · rfl

theorem eventMass_restrict {E F : Finset ℕ} (hEF : E ⊆ F)
    (hF : ∀ p ∈ F, 2 ≤ p) (A : Outcomes E → Prop) :
    eventMass F (fun s => A (restrictOutcomes hEF s)) = eventMass E A := by
  let e := retainedIndexEquiv hEF
  let ep := Equiv.piCongrLeft (fun _ : E => Sample) e
  have h := finite_product_restrict (fun p : F => (p : ℕ) ∈ E)
    (fun p : F => jointMass (p : ℝ))
    (fun p => jointMass_nonneg (by exact_mod_cast hF p p.property))
    (fun p => jointMass_hasSum (by exact_mod_cast hF p p.property))
    (fun s => A (ep s))
  have hr := finite_product_reindex e (fun p : E => jointMass (p : ℝ)) A
  calc
    _ = ∑' s : F → Sample, if A (ep (fun p => s p)) then ∏ p : F, jointMass (p : ℝ) (s p) else 0 := by
      apply tsum_congr
      intro s
      have hh : ep (fun p => s p) = restrictOutcomes hEF s := by
        funext p
        rfl
      simp only [hh, productMass]
    _ = _ := h
    _ = _ := by
      convert hr using 1
      all_goals try with_reducible_and_instances rfl
      all_goals
        apply tsum_congr
        intro s
        split_ifs
        · apply Finset.prod_congr
          · ext i; simp only [Finset.mem_univ]
          · intro i _; rfl
        · rfl

theorem lowerInteger_restrict_le {E F : Finset ℕ} (hEF : E ⊆ F)
    (hF : ∀ p ∈ F, Nat.Prime p) (s : Outcomes F) :
    lowerInteger E (restrictOutcomes hEF s) ≤ lowerInteger F s := by
  let f : ℕ → ℕ := fun p => if hp : p ∈ F then p ^ lowerExponent (s ⟨p, hp⟩) else 1
  have he : lowerInteger E (restrictOutcomes hEF s) = ∏ p ∈ E, f p := by
    rw [lowerInteger, integerProduct, ← Finset.prod_attach E f]
    apply Finset.prod_congr rfl
    intro p _
    simp only [f, dite_eq_left (hEF p.property), restrictOutcomes]
  have hf : lowerInteger F s = ∏ p ∈ F, f p := by
    rw [lowerInteger, integerProduct, ← Finset.prod_attach F f]
    apply Finset.prod_congr rfl
    intro p _
    simp only [f, dite_eq_left p.property]
  rw [he, hf]
  apply Finset.prod_le_prod_of_subset_of_one_le hEF
  · intro p _; exact Nat.zero_le _
  · intro p hp _
    simp only [f, dite_eq_left hp]
    exact one_le_pow₀ (hF p hp).pos

theorem ordinarySmallSum_antitone {E F : Finset ℕ} (hEF : E ⊆ F)
    (hF : ∀ p ∈ F, Nat.Prime p) (N : ℕ) :
    ordinarySmallSum F N ≤ ordinarySmallSum E N := by
  rw [ordinarySmallSum_eq_event F hF,
    ordinarySmallSum_eq_event E (fun p hp => hF p (hEF hp))]
  rw [← eventMass_restrict hEF (fun p hp => (hF p hp).two_le)]
  apply Summable.tsum_le_tsum
  · intro s
    have hn := productMass_nonneg F (fun p hp => (hF p hp).two_le) s
    by_cases h : lowerInteger F s ≤ N
    · have hh := (lowerInteger_restrict_le hEF hF s).trans h
      simp only [ite_eq_left h, ite_eq_left hh, le_refl]
    · simp only [ite_eq_right h]; split_ifs <;> linarith
  · exact product_event_summable F (fun p hp => (hF p hp).two_le) _
  · exact product_event_summable F (fun p hp => (hF p hp).two_le) _

end EulerWeightedLower



namespace EulerWeightedLower
open Erdos970.EulerPrimeLaw _root_.Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

lemma primesThrough_prime {P : ℝ} {p : ℕ} (hp : p ∈ primesThrough P) : Nat.Prime p :=
  (Finset.mem_filter.mp hp).2

lemma ordinaryProduct_nonneg (E : Finset ℕ) (hE : ∀ p ∈ E, Nat.Prime p) :
    0 ≤ ordinaryProduct E := by
  apply Finset.prod_nonneg
  intro p hp
  exact sub_nonneg.mpr (reciprocal_lt_one (by exact_mod_cast (hE p hp).two_le)).le

theorem supportedIntegers_primesThrough {P : ℝ} {N : ℕ} (hN : N ≤ ⌊P⌋₊) :
    supportedIntegers (primesThrough P) N = Finset.Icc 1 N := by
  apply Finset.filter_eq_self.mpr
  intro d hd p hp
  have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
  have hpd : p ≤ d := Nat.le_of_dvd hd0 (Nat.dvd_of_mem_primeFactors hp)
  have hpr := Nat.prime_of_mem_primeFactors hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hpr.pos, hpd.trans ((Finset.mem_Icc.mp hd).2.trans hN)⟩, hpr⟩

lemma harmonic_real_eq (N : ℕ) :
    (harmonic N : ℝ) = ∑ d ∈ Finset.Icc 1 N, 1 / (d : ℝ) := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]

theorem ordinarySmallSum_primesThrough {P : ℝ} {N : ℕ} (hN : N ≤ ⌊P⌋₊) :
    ordinarySmallSum (primesThrough P) N = ordinaryProduct (primesThrough P) * (harmonic N : ℝ) := by
  rw [ordinarySmallSum, supportedIntegers_primesThrough hN, harmonic_real_eq]

theorem weightedSmallSum_uniform_lower {P : ℝ} (hP : 1 < P)
    (E : Finset ℕ) (hE : E ⊆ primesThrough P) :
    uniformLowerEnvelope P ≤ weightedSmallSum E ⌊P ^ (95 / 100 : ℝ)⌋₊ := by
  have hpr : ∀ p ∈ primesThrough P, Nat.Prime p := fun p hp => primesThrough_prime hp
  have hEs : ∀ p ∈ E, Nat.Prime p := fun p hp => hpr p (hE hp)
  have hpow : P ^ (94 / 100 : ℝ) ≤ P := Real.rpow_le_self_of_one_le hP.le (by norm_num)
  have hfloor := Nat.floor_mono hpow
  have hm := ordinarySmallSum_antitone hE hpr ⌊P ^ (94 / 100 : ℝ)⌋₊
  rw [ordinarySmallSum_primesThrough hfloor] at hm
  have hh := log_le_harmonic_floor (P ^ (94 / 100 : ℝ)) (Real.rpow_nonneg (by linarith) _)
  rw [Real.log_rpow (by linarith : 0 < P)] at hh
  have hl := mul_le_mul_of_nonneg_left hh (ordinaryProduct_nonneg _ hpr)
  have hc := weightedSmallSum_coupling_lower E hEs hP
  unfold uniformLowerEnvelope
  nlinarith

theorem weightedSmallSum_eventually_uniform {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ P : ℝ in atTop, ∀ E : Finset ℕ, E ⊆ primesThrough P →
      Real.exp (-Real.eulerMascheroniConstant) * ((94 / 100 : ℝ) - ε) ≤
        weightedSmallSum E ⌊P ^ (95 / 100 : ℝ)⌋₊ := by
  have hgap : Real.exp (-Real.eulerMascheroniConstant) * ((94 / 100 : ℝ) - ε) <
      Real.exp (-Real.eulerMascheroniConstant) * (94 / 100 : ℝ) := by
    nlinarith [Real.exp_pos (-Real.eulerMascheroniConstant)]
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    uniformLowerEnvelope_limit_jb247.eventually (lt_mem_nhds hgap)] with P hP hbound
  intro E hE
  exact hbound.le.trans (weightedSmallSum_uniform_lower hP E hE)

end EulerWeightedLower


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeIntervalFlags
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology
open ErdosPrimeInputs.PrimeCountAbel (logarithmicIntegral)

lemma exponential_log_cube_tendsto {K : ℝ} (hK : 0 < K) :
    Tendsto (fun w:ℝ => Real.exp (K*(Real.log w)^3)) atTop atTop :=
  Real.tendsto_exp_atTop.comp
    (Filter.Tendsto.const_mul_atTop hK ((tendsto_pow_atTop (by decide : (3:ℕ)≠0)).comp Real.tendsto_log_atTop))

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_WeightedPrimeMultiplePairs
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace Erdos970Dependency.SiegelWalfisz
open _root_.Finset
open scoped Topology

lemma mem_primeMultiplesIn (d : ℕ) (P x y : ℝ) (m : ℤ) :
    m ∈ primeMultiplesIn d P x y ↔ x < (m:ℝ) ∧ (m:ℝ) < y ∧
      ∃ ell : ℕ, ell.Prime ∧ P < (ell:ℝ) ∧ (m=(d:ℤ)*ell ∨ m= -((d:ℤ)*ell)) := by
  classical
  constructor
  · intro hm
    exact (mem_filter.mp hm).2
  · intro hm
    apply mem_filter.mpr
    exact ⟨mem_Icc.mpr ⟨Int.ceil_le.mpr hm.1.le,Int.le_floor.mpr hm.2.1.le⟩,hm⟩

end Erdos970Dependency.SiegelWalfisz



namespace ErdosStoppedArithmetic
open Erdos970Dependency.SiegelWalfisz
attribute [local instance] Classical.propDecidable

theorem large_prime_factor_unique (d e p q : ℕ) (he : 0 < e) (hp : p.Prime) (hq : q.Prime)
    (hep : e < p) (heq : d*p=e*q) : d=e ∧ p=q := by
  have hpd : p ∣ e*q := heq ▸ Nat.dvd_mul_left p d
  have hpeq : p=q := by
    rcases hp.dvd_mul.mp hpd with hpe | hpq
    · have hh := Nat.le_of_dvd he hpe
      omega
    · rcases (Nat.dvd_prime hq).mp hpq with h | h
      · exact (hp.ne_one h).elim
      · exact h
  refine ⟨?_,hpeq⟩
  rw [hpeq] at heq
  exact mul_right_cancel₀ hq.ne_zero heq

theorem prime_multiple_natAbs (d : ℕ) (P x y : ℝ) (m : ℤ)
    (hm : m ∈ primeMultiplesIn d P x y) :
    ∃ p : ℕ,p.Prime ∧ P < (p : ℝ) ∧ m.natAbs=d*p := by
  obtain ⟨_hx,_hy,p,hp,hP,hpos|hneg⟩ := (mem_primeMultiplesIn d P x y m).mp hm
  · exact ⟨p,hp,hP,by rw [hpos,Int.natAbs_mul,Int.natAbs_natCast,Int.natAbs_natCast]⟩
  · exact ⟨p,hp,hP,by rw [hneg,Int.natAbs_neg,Int.natAbs_mul,Int.natAbs_natCast,Int.natAbs_natCast]⟩

theorem prime_multiple_factors_disjoint (P x y : ℝ) (d e : ℕ) (he : 0 < e)
    (heP : (e : ℝ) ≤ P) (hne : d ≠ e) :
    Disjoint (primeMultiplesIn d P x y) (primeMultiplesIn e P x y) := by
  apply Finset.disjoint_left.mpr
  intro m hmd hme
  obtain ⟨p,hp,hP,hd⟩ := prime_multiple_natAbs d P x y m hmd
  obtain ⟨q,hq,_hQ,heq⟩ := prime_multiple_natAbs e P x y m hme
  have hep : e < p := by exact_mod_cast heP.trans_lt hP
  exact hne (large_prime_factor_unique d e p q he hp hq hep (hd.symm.trans heq)).1

end ErdosStoppedArithmetic



namespace ErdosStoppedArithmetic
open Erdos970Dependency.SiegelWalfisz
attribute [local instance] Classical.propDecidable

theorem admissible_pair_card_rows (T : Finset ℕ) (M : Finset ℤ) (good : ℕ → ℤ → Prop) :
    (admissiblePairs T M good).card = ∑ p ∈ T,(M.filter (good p)).card := by
  simp only [admissiblePairs,Finset.card_filter,Finset.product_eq_sprod,Finset.sum_product]

theorem admissible_pair_card_columns (T : Finset ℕ) (M : Finset ℤ) (good : ℕ → ℤ → Prop) :
    (admissiblePairs T M good).card = ∑ m ∈ M,(T.filter (fun p => good p m)).card := by
  rw [admissible_pair_card_rows]
  simp only [Finset.card_filter]
  exact Finset.sum_comm

theorem prime_multiple_pair_sum (P x y : ℝ) (D T : Finset ℕ) (good : ℕ → ℤ → Prop)
    (hD : ∀ d ∈ D,0 < d ∧ (d : ℝ) ≤ P) :
    (admissiblePairs T (D.biUnion (fun d => primeMultiplesIn d P x y)) good).card =
      ∑ d ∈ D,∑ m ∈ primeMultiplesIn d P x y,(T.filter (fun p => good p m)).card := by
  rw [admissible_pair_card_columns]
  apply Finset.sum_biUnion
  intro d hd e he hne
  exact prime_multiple_factors_disjoint P x y d e (hD e he).1 (hD e he).2 hne

theorem prime_multiple_pair_lower (P x y A B : ℝ) (D T : Finset ℕ)
    (good : ℕ → ℤ → Prop) (W : ℕ → ℝ)
    (hD : ∀ d ∈ D,0 < d ∧ (d : ℝ) ≤ P) (hB : 0 ≤ B)
    (hW : ∀ d ∈ D,0 ≤ W d)
    (hM : ∀ d ∈ D,A/(d : ℝ) ≤ ((primeMultiplesIn d P x y).card : ℝ))
    (hTag : ∀ d ∈ D,∀ m ∈ primeMultiplesIn d P x y,
      B*W d ≤ ((T.filter (fun p => good p m)).card : ℝ)) :
    A*B*(∑ d ∈ D,W d/(d : ℝ)) ≤
      ((admissiblePairs T (D.biUnion (fun d => primeMultiplesIn d P x y)) good).card : ℝ) := by
  rw [prime_multiple_pair_sum P x y D T good hD,Nat.cast_sum]
  have hEach (d : ℕ) (hd : d ∈ D) :
      A*B*(W d/(d : ℝ)) ≤
        ((∑ m ∈ primeMultiplesIn d P x y,(T.filter (fun p => good p m)).card : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    calc
      _ = (A/(d : ℝ))*(B*W d) := by ring
      _ ≤ ((primeMultiplesIn d P x y).card : ℝ)*(B*W d) :=
        mul_le_mul_of_nonneg_right (hM d hd) (mul_nonneg hB (hW d hd))
      _ = ∑ _m ∈ primeMultiplesIn d P x y,B*W d := by rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun m hm => hTag d hd m hm)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum hEach

end ErdosStoppedArithmetic



open _root_.Filter
namespace ErdosStoppedArithmetic
open Erdos970Dependency.SiegelWalfisz Erdos970.EulerWeightedLower
attribute [local instance] Classical.propDecidable

theorem supported_small_factor_bounds (P : ℝ) (hP : 1 < P) (E : Finset ℕ) (d : ℕ)
    (hd : d ∈ supportedIntegers E ⌊P^(95/100 : ℝ)⌋₊) :
    0 < d ∧ (d : ℝ) ≤ P^(19/20 : ℝ) ∧ (d : ℝ) ≤ P := by
  have hi := Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1
  have hh : (d : ℝ) ≤ P^(95/100 : ℝ) := (Nat.le_floor_iff (Real.rpow_nonneg (by linarith) _)).mp hi.2
  have hexp : (95/100 : ℝ)=(19/20 : ℝ) := by norm_num
  refine ⟨hi.1,by simpa only [hexp] using hh,?_⟩
  exact hh.trans (Real.rpow_le_self_of_one_le hP.le (by norm_num))

theorem paper_weight_nonneg (E : Finset ℕ) (hE : ∀ p ∈ E,p.Prime) (d : ℕ) :
    0 ≤ paperWeight E d := by
  unfold paperWeight
  apply Finset.prod_nonneg
  intro p hp
  have hpr := hE p (Finset.mem_filter.mp hp).1
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpr.two_le
  have hden : 0 < (p : ℝ)-1 := by linarith
  have hrec : 1/((p : ℝ)-1) ≤ 1 := (div_le_one hden).mpr (by linarith)
  exact sub_nonneg.mpr hrec

theorem moving_weighted_pair_lower (Cs : ℝ) (hCs : 0 ≤ Cs) :
    ∃ K : ℝ,0 < K ∧ ∀ rho : ℝ,1 < rho → ∀ eps : ℝ,0 < eps → eps < 1 →
      ∃ w0 : ℝ,4 ≤ w0 ∧ ∀ w : ℝ,w0 ≤ w → ∀ P s x y : ℝ,
      Real.exp (K*(Real.log w)^3) ≤ P → P ≤ Real.exp (rho*K*(Real.log w)^3) →
      203/100 ≤ s → s ≤ 219/100 → P^s/2 ≤ y-x → max |x| |y| ≤ 2*w^(Cs+2)*P^s →
      ∀ (E T : Finset ℕ) (good : ℕ → ℤ → Prop) (B : ℝ),E ⊆ primesThrough P → 0 ≤ B →
      (∀ d ∈ supportedIntegers E ⌊P^(95/100 : ℝ)⌋₊,∀ m ∈ primeMultiplesIn d P x y,
        B*paperWeight E d ≤ ((T.filter (fun p => good p m)).card : ℝ)) →
      ((1-eps)*(y-x)/((s+1/50)*Real.log P))*B*
        (Real.exp (-Real.eulerMascheroniConstant)*(94/100-eps)) ≤
        ((admissiblePairs T ((supportedIntegers E ⌊P^(95/100 : ℝ)⌋₊).biUnion
          (fun d => primeMultiplesIn d P x y)) good).card : ℝ) := by
  obtain ⟨K,hK,hPrime⟩ := moving_signed_prime_multiple_lower_jb247 Cs hCs
  refine ⟨K,hK,?_⟩
  intro rho hrho eps heps heps1
  obtain ⟨wS,hwS,hS⟩ := hPrime rho hrho eps heps heps1
  obtain ⟨P0,hP0⟩ := eventually_atTop.mp (weightedSmallSum_eventually_uniform heps)
  obtain ⟨wG,hwG⟩ := eventually_atTop.mp
    ((exponential_log_cube_tendsto hK).eventually_ge_atTop (max 2 P0))
  refine ⟨max wS wG,hwS.trans (le_max_left _ _),?_⟩
  intro w hw P s x y hPlower hPupper hs hsupper hLength hHeight E T good B hE hB hTag
  have hLarge : max 2 P0 ≤ P := (hwG w ((le_max_right _ _).trans hw)).trans hPlower
  have hP2 : 2 ≤ P := (le_max_left _ _).trans hLarge
  have hP : 1 < P := by linarith
  have hPpos : 0 < P := by linarith
  have hlog : 0 < Real.log P := Real.log_pos hP
  have hspos : 0 < s+1/50 := by linarith
  have hLengthPos : 0 < y-x := (by positivity : (0 : ℝ) < P^s/2).trans_le hLength
  let A := (1-eps)*(y-x)/((s+1/50)*Real.log P)
  have hA : 0 ≤ A := by dsimp [A] <;> positivity
  let D := supportedIntegers E ⌊P^(95/100 : ℝ)⌋₊
  have hD (d : ℕ) (hd : d ∈ D) := supported_small_factor_bounds P hP E d hd
  have hpr (p : ℕ) (hp : p ∈ E) : p.Prime := primesThrough_prime (hE hp)
  have hM (d : ℕ) (hd : d ∈ D) : A/(d : ℝ) ≤ ((primeMultiplesIn d P x y).card : ℝ) := by
    have hh := hS w ((le_max_left _ _).trans hw) P s x y d hPlower hPupper hs hsupper
      hLength hHeight (hD d hd).1 (hD d hd).2.1
    have he : A/(d : ℝ)=(1-eps)*(y-x)/((d : ℝ)*(s+1/50)*Real.log P) := by
      dsimp [A]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    exact he.trans_le hh
  have hPairs := prime_multiple_pair_lower P x y A B D T good (paperWeight E)
    (fun d hd => ⟨(hD d hd).1,(hD d hd).2.2⟩) hB (fun d _ => paper_weight_nonneg E hpr d) hM hTag
  have hWeighted := hP0 P ((le_max_right _ _).trans hLarge) E hE
  change A*B*(Real.exp (-Real.eulerMascheroniConstant)*(94/100-eps)) ≤ _
  have hh := mul_le_mul_of_nonneg_left hWeighted (mul_nonneg hA hB)
  exact hh.trans hPairs

end ErdosStoppedArithmetic


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
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_TagSmallPrimeData
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970



namespace ErdosStoppedTagSieve
open ErdosUnitLifts
attribute [local instance] Classical.propDecidable

lemma mem_smallPrimeSet (P : ℝ) (t : ℕ) : t∈smallPrimeSet P ↔ t.Prime ∧ (t:ℝ)<P := by
  simp only [smallPrimeSet,Finset.mem_filter,Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨_,ht⟩,hP⟩
    exact ⟨ht,hP⟩
  · rintro ⟨ht,hP⟩
    have ht0 : (0:ℝ) ≤ t := Nat.cast_nonneg t
    exact ⟨⟨(Nat.le_floor_iff (by linarith)).mpr hP.le,ht⟩,hP⟩

end ErdosStoppedTagSieve


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_TagPairBinding
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
namespace ErdosStoppedArithmetic
open NumberTheoryLean ErdosPrimeInputs.MertensStrong ReferenceProductsBasics ReferenceMertens


theorem eventual_closed_euler_lower_scale (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ P : ℝ in atTop,1 < P ∧
      (1-eps)*primeProduct P ≤ Real.exp (-Real.eulerMascheroniConstant)/Real.log P := by
  have hn := normalization_tendsto_one.eventually (lt_mem_nhds (by linarith : 1-eps < (1 : ℝ)))
  filter_upwards [hn,eventually_gt_atTop (1 : ℝ)] with P hn hP
  have hlog := Real.log_pos hP
  have hV := actual_primeProduct_pos P
  have hnorm : 1-eps ≤ Real.exp (-Real.eulerMascheroniConstant)/(Real.log P*primeProduct P) := hn.le
  have hh := (le_div_iff₀ (mul_pos hlog hV)).mp hnorm
  refine ⟨hP,?_⟩
  apply (le_div_iff₀ hlog).mpr
  nlinarith

theorem stopped_pair_coefficient (N J H D L V E S : ℝ)
    (hN : 0 ≤ N) (hJ : 0 ≤ J) (hD : 0 < D) (hL : 0 < L)
    (hV : 0 ≤ V) (hE : 0 ≤ E) (hS : 0 < S) (hSup : S ≤ (111/50 : ℝ))
    (hH : (999/1000 : ℝ)*D*J ≤ H)
    (hNorm : (999/1000 : ℝ)*V ≤ E/L) :
    (39/100 : ℝ)*N*J*V ≤
      ((999/1000 : ℝ)*H/(S*L))*((19/20 : ℝ)*N/D)*(E*(939/1000 : ℝ)) := by
  let a : ℝ := 999/1000
  let b : ℝ := 19/20
  let c : ℝ := 939/1000
  have hConst : (39/100 : ℝ) ≤ (a^3*b*c)/(111/50 : ℝ) := by norm_num [a,b,c]
  have hHJ : a*J ≤ H/D := by
    apply (le_div_iff₀ hD).mpr
    dsimp [a]
    nlinarith
  have hNorm' : a*V ≤ E/L := hNorm
  have hEL : 0 ≤ E/L := div_nonneg hE hL.le
  calc
    _ ≤ ((a^3*b*c)/(111/50 : ℝ))*(N*J*V) := by
      have hh := mul_le_mul_of_nonneg_right hConst (mul_nonneg (mul_nonneg hN hJ) hV)
      nlinarith only [hh]
    _ = (a^2*b*c*N*J*(a*V))/(111/50 : ℝ) := by ring
    _ ≤ (a^2*b*c*N*J*(E/L))/(111/50 : ℝ) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hNorm'
        (by dsimp [a,b,c] <;> positivity)) (by norm_num)
    _ ≤ (a^2*b*c*N*J*(E/L))/S :=
      div_le_div_of_nonneg_left (by dsimp [a,b,c] <;> positivity) hS hSup
    _ = (a*b*c*N*(a*J)*(E/L))/S := by ring
    _ ≤ (a*b*c*N*(H/D)*(E/L))/S := by
      have hh := mul_le_mul_of_nonneg_left hHJ (show 0 ≤ a*b*c*N by dsimp [a,b,c] <;> positivity)
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hh hEL) hS.le
    _ = _ := by
      dsimp [a,b,c]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring

end ErdosStoppedArithmetic

end

section

open _root_.Filter
namespace ErdosStoppedArithmetic
open Erdos970Dependency.SiegelWalfisz Erdos970.EulerWeightedLower
  NumberTheoryLean.ReferenceProductsBasics ErdosPrimeInputs.MertensStrong

attribute [local instance] Classical.propDecidable

theorem moving_subbin_pair_lower (Cs : ℝ) (hCs : 0 ≤ Cs) :
    ∃ K : ℝ,0 < K ∧ ∀ rho : ℝ,1 < rho → ∃ w0 : ℝ,4 ≤ w0 ∧
      ∀ w : ℝ,w0 ≤ w → ∀ P s x y : ℝ,
      Real.exp (K*(Real.log w)^3) ≤ P → P ≤ Real.exp (rho*K*(Real.log w)^3) →
      203/100 ≤ s → s ≤ 219/100 →
      ∀ D : ℕ,0 < D → (999/1000 : ℝ)*(D : ℝ)*P^s ≤ y-x →
      max |x| |y| ≤ 2*w^(Cs+2)*P^s →
      ∀ (E T : Finset ℕ) (good : ℕ → ℤ → Prop),E ⊆ primesThrough P →
      (∀ d ∈ supportedIntegers E ⌊P^(95/100 : ℝ)⌋₊,∀ m ∈ primeMultiplesIn d P x y,
        ((19/20 : ℝ)*(T.card : ℝ)/(D : ℝ))*paperWeight E d ≤
          ((T.filter (fun p => good p m)).card : ℝ)) →
      (39/100 : ℝ)*(T.card : ℝ)*P^s*primeProduct P ≤
        ((admissiblePairs T ((supportedIntegers E ⌊P^(95/100 : ℝ)⌋₊).biUnion
          (fun d => primeMultiplesIn d P x y)) good).card : ℝ) := by
  obtain ⟨K,hK,hPairs⟩ := moving_weighted_pair_lower Cs hCs
  refine ⟨K,hK,?_⟩
  intro rho hrho
  obtain ⟨wS,hwS,hS⟩ := hPairs rho hrho (1/1000) (by norm_num) (by norm_num)
  obtain ⟨P0,hP0⟩ := eventually_atTop.mp (eventual_closed_euler_lower_scale (1/1000) (by norm_num))
  obtain ⟨wG,hwG⟩ := eventually_atTop.mp ((exponential_log_cube_tendsto hK).eventually_ge_atTop (max 2 P0))
  refine ⟨max wS wG,hwS.trans (le_max_left _ _),?_⟩
  intro w hw P s x y hPlower hPupper hs hsupper D hD hCommon hHeight E T good hE hTag
  have hLarge : max 2 P0 ≤ P := (hwG w ((le_max_right _ _).trans hw)).trans hPlower
  have hP2 : 2 ≤ P := (le_max_left _ _).trans hLarge
  have hP : 1 < P := by linarith
  have hPpos : 0 < P := by linarith
  have hPs : 0 < P^s := Real.rpow_pos_of_pos hPpos _
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hWidth : P^s/2 ≤ y-x := by
    have hh := mul_le_mul_of_nonneg_right hD1 (show 0 ≤ (999/1000 : ℝ)*P^s by positivity)
    nlinarith
  have hB : 0 ≤ (19/20 : ℝ)*(T.card : ℝ)/(D : ℝ) := by positivity
  have hResult := hS w ((le_max_left _ _).trans hw) P s x y hPlower hPupper hs hsupper
    hWidth hHeight E T good ((19/20 : ℝ)*(T.card : ℝ)/(D : ℝ)) hE hB hTag
  have hNorm := (hP0 P ((le_max_right _ _).trans hLarge)).2
  have heps : (1 : ℝ)-1/1000=999/1000 := by norm_num
  have hweight : (94/100 : ℝ)-1/1000=939/1000 := by norm_num
  rw [heps] at hNorm
  rw [heps,hweight] at hResult
  have hCoeff := stopped_pair_coefficient (T.card : ℝ) (P^s) (y-x) (D : ℝ) (Real.log P)
    (primeProduct P) (Real.exp (-Real.eulerMascheroniConstant)) (s+1/50)
    (Nat.cast_nonneg _) hPs.le hDr (Real.log_pos hP) (actual_primeProduct_pos P).le
    (Real.exp_pos _).le (by linarith) (by linarith) hCommon hNorm
  exact hCoeff.trans hResult

end ErdosStoppedArithmetic

end


namespace ErdosStoppedArithmetic
open ErdosStoppedTagSieve Erdos970Dependency.SiegelWalfisz
  Erdos970.EulerWeightedLower ErdosUnitLifts
  NumberTheoryLean.ReferenceProductsBasics ErdosPrimeInputs.MertensStrong

attribute [local instance] Classical.propDecidable

theorem unaligned_subset_primesThrough (P : ℝ) (D : ℕ) (A : ℤ) (residue : ℕ → ℤ) :
    unalignedPrimes P D A residue ⊆ primesThrough P := by
  intro t ht
  obtain ⟨htp,htP⟩ := (mem_smallPrimeSet P t).mp (Finset.mem_filter.mp ht).1
  have hP0 : 0 ≤ P := (Nat.cast_nonneg t).trans htP.le
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_Ioc.mpr ⟨htp.pos,(Nat.le_floor_iff hP0).mpr htP.le⟩,htp⟩

theorem actual_restricted_weight (P : ℝ) (D : ℕ) (A : ℤ) (residue : ℕ → ℤ) (d : ℕ) :
    paperWeight (unalignedPrimes P D A residue) d =
      eulerWeight (restrictedPrimes P D A residue d) := rfl

theorem actual_tag_filter (P R V : ℝ) (r : ℚ) (q : ℕ) (a : ℕ → ℕ) (m : ℤ) :
    (intervalPrimes R V 1 0).filter (fun p => actualTagGood P r q a p m) =
      actualSurvivorPrimes P R V r.den r.num ((q : ℤ)*m) (fun t => (a t : ℤ)) := by
  ext p
  simp only [actualTagGood,actualSurvivorPrimes,Finset.mem_filter,Int.cast_natCast]

theorem moving_subbin_actual_pair_lower_jb247_oai (Cs : ℝ) (hCs : 0 ≤ Cs) :
    ∃ K : ℝ,0 < K ∧ ∀ rho xi : ℝ,1 < rho → 0 < xi →
      ∃ w0 : ℝ,4 ≤ w0 ∧ ∀ w : ℝ,w0 ≤ w → ∀ P s x y R V : ℝ,
      Real.exp (K*(Real.log w)^3) ≤ P → P ≤ Real.exp (rho*K*(Real.log w)^3) →
      203/100 ≤ s → s ≤ 219/100 →
      Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ R →
      xi/(16*w^(2*Cs+10)) ≤ V/R → V/R ≤ w^(-(2*Cs+10)) →
      ∀ r : ℚ,(r.den : ℝ) ≤ w^Cs → ∀ q : ℕ,∀ a : ℕ → ℕ,
      (∀ t ∈ smallPrimeSet P,q.Coprime t) →
      (999/1000 : ℝ)*(r.den : ℝ)*P^s ≤ y-x →
      max |x| |y| ≤ 2*w^(Cs+2)*P^s →
      (39/100 : ℝ)*((intervalPrimes R V 1 0).card : ℝ)*P^s*primeProduct P ≤
        ((admissiblePairs (intervalPrimes R V 1 0)
          ((supportedIntegers (unalignedPrimes P r.den r.num (fun t => (a t : ℤ)))
            ⌊P^(95/100 : ℝ)⌋₊).biUnion (fun d => primeMultiplesIn d P x y))
          (actualTagGood P r q a)).card : ℝ) := by
  obtain ⟨K,hK,hPair⟩ := moving_subbin_pair_lower Cs hCs
  refine ⟨K,hK,?_⟩
  intro rho xi hrho hxi
  obtain ⟨wP,hwP,hP⟩ := hPair rho hrho
  obtain ⟨wT,_hwT,hT⟩ := tag_prime_sieve_lower_jb247 Cs K rho xi (1/20) hCs hK hrho hxi (by norm_num)
  refine ⟨max wP wT,hwP.trans (le_max_left _ _),?_⟩
  intro w hw P s x y R V hPl hPu hs hsU hR hVlo hVhi r hD q a hq hLength hHeight
  apply hP w ((le_max_left _ _).trans hw) P s x y hPl hPu hs hsU r.den r.den_pos
    hLength hHeight _ _ _ (unaligned_subset_primesThrough P r.den r.num _)
  intro d hd m hm
  have hd' := Finset.mem_filter.mp hd
  obtain ⟨ell,hell,hellP,hAbs⟩ := prime_multiple_natAbs d P x y m hm
  have hh := hT w P R V ((le_max_right _ _).trans hw) hPl hPu hR hVlo hVhi
    r.den r.den_pos hD r.num r.reduced (fun t => (a t : ℤ)) q d ell m hq
    (Finset.mem_Icc.mp hd'.1).1 hd'.2 hell hellP hAbs
  rw [actual_tag_filter,actual_restricted_weight]
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ErdosStoppedArithmetic


end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.ErdosStoppedArithmetic.moving_subbin_actual_pair_lower_jb247_oai := @OAI.Erdos970.ErdosStoppedArithmetic.moving_subbin_actual_pair_lower_jb247_oai
