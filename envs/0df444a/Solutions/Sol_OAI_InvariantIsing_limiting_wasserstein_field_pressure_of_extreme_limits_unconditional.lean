-- Prove2me | solution 1 for OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:59:45.288446+00:00
-- url     : https://prove2.me/submissions/c428c926-ee6f-44b4-88e9-74a89e5e30ae

import Mathlib
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Sort
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Order.Lattice
import Mathlib.Order.Disjointed
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Fin.InsertNth
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Representation
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.StrongLaw
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_gaussianLipschitzVariance_proved
import Theorems.Thm_OAI_InvariantIsing_haarPolynomialMoment_log_bound
import Theorems.Thm_OAI_InvariantIsing_limiting_wasserstein_field_pressure_of_extreme_limits
import Theorems.Thm_OAI_InvariantIsing_vectorTerminal_pair_formula

section
-- module Solutions.OAIQ258_II.IsingPerceptron_PoissonCloud
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Poisson Cloud. -/

noncomputable section



 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

 
namespace IsingPerceptron

lemma poisson_probability_generating (r : ℝ≥0) (q : ℝ) :
    (∫ n : ℕ, q ^ n ∂poissonMeasure r) = Real.exp ((r : ℝ) * (q - 1)) := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  calc
    (∑' n : ℕ, (Real.exp (-(r : ℝ)) * (r : ℝ)^n / (n.factorial : ℝ)) * q^n) =
        Real.exp (-(r : ℝ)) * ∑' n : ℕ, ((r : ℝ)*q)^n / (n.factorial : ℝ) := by
      rw [← tsum_mul_left]
      congr 1
      ext n
      rw [mul_pow]
      ring
    _ = Real.exp (-(r : ℝ)) * Real.exp ((r : ℝ)*q) := by
      rw [(NormedSpace.expSeries_div_hasSum_exp ((r : ℝ)*q)).tsum_eq,
        ← Real.exp_eq_exp_ℝ]
    _ = Real.exp ((r : ℝ)*(q-1)) := by rw [← Real.exp_add]; congr 1; ring

variable {E : Type*} [MeasurableSpace E]

lemma measurable_cloudSum {ψ : E → ℝ} (hψ : Measurable ψ) :
    Measurable (cloudSum ψ) := by
  apply measurable_from_prod_countable_right
  intro n
  change Measurable (fun y : ℕ → E => ∑ i : Fin n, ψ (y i))
  exact Finset.measurable_sum (Finset.univ : Finset (Fin n))
    (fun i _ => hψ.comp (measurable_pi_apply (i : ℕ)))

lemma iid_finite_laplace (μ : Measure E) [IsProbabilityMeasure μ]
    {ψ : E → ℝ} (hψ : Measurable ψ) (n : ℕ) :
    (∫ ω : ℕ → E, Real.exp (-(∑ i : Fin n, ψ (ω i)))
      ∂Measure.infinitePi (fun _ : ℕ => μ)) =
    (∫ x, Real.exp (-ψ x) ∂μ)^n := by
  let X : ℕ → (ℕ → E) → ℝ := fun i ω => Real.exp (-ψ (ω i))
  have hind : iIndepFun X (Measure.infinitePi (fun _ : ℕ => μ)) :=
    iIndepFun_infinitePi (fun _ => hψ.neg.exp)
  have hind' : iIndepFun (fun i : Fin n => X i) (Measure.infinitePi (fun _ : ℕ => μ)) :=
    hind.precomp Fin.val_injective
  have hm (i : Fin n) : AEStronglyMeasurable (X i)
      (Measure.infinitePi (fun _ : ℕ => μ)) :=
    ((hψ.neg.exp).comp (measurable_pi_apply (i : ℕ))).aestronglyMeasurable
  have he i : (∫ ω, X i ω ∂Measure.infinitePi (fun _ : ℕ => μ)) =
      ∫ x, Real.exp (-ψ x) ∂μ := by
    have mp := measurePreserving_eval_infinitePi (fun _ : ℕ => μ) i
    exact mp.hasLaw.integral_comp hψ.neg.exp.aestronglyMeasurable
  have hh := hind'.integral_fun_prod_eq_prod_integral hm
  simpa only [X, ← Real.exp_sum, ← Finset.sum_neg_distrib, he, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] using hh

 
theorem finitePoissonCloud_laplace (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    {ψ : E → ℝ} (hψ : Measurable ψ) (hpos : ∀ x, 0 ≤ ψ x) :
    (∫ p, Real.exp (-cloudSum ψ p) ∂finitePoissonCloud r μ) =
      Real.exp ((r : ℝ) * ((∫ x, Real.exp (-ψ x) ∂μ) - 1)) := by
  have hi : Integrable (fun p => Real.exp (-cloudSum ψ p)) (finitePoissonCloud r μ) := by
    apply Integrable.of_bound (measurable_cloudSum hψ |>.neg.exp.aestronglyMeasurable) 1
    apply ae_of_all
    intro p
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (Finset.sum_nonneg (fun _ _ => hpos _))
  rw [finitePoissonCloud, integral_prod _ hi]
  simp_rw [cloudSum, iid_finite_laplace μ hψ]
  exact poisson_probability_generating r _

lemma negExp_injective : Function.Injective negExp := by
  intro x y h
  apply EReal.coe_ennreal_injective
  apply neg_injective
  apply EReal.exp_strictMono.injective
  exact (ENNReal.toReal_eq_toReal_iff' (enegExp_ne_top x) (enegExp_ne_top y)).mp h
lemma negExp_ofReal {x : ℝ} (hx : 0 ≤ x) :
    negExp (ENNReal.ofReal x) = Real.exp (-x) := by
  simp [negExp, enegExp, EReal.coe_ennreal_ofReal, max_eq_left hx,
    ← EReal.coe_neg, Real.exp_nonneg]
lemma enegExp_add (x y : ℝ≥0∞) : enegExp (x+y) = enegExp x * enegExp y := by
  by_cases hx : x = ∞
  · simp [hx]
  by_cases hy : y = ∞
  · simp [hy]
  rw [← ENNReal.ofReal_toReal hx, ← ENNReal.ofReal_toReal hy]
  rw [← ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
  simp only [enegExp, EReal.coe_ennreal_ofReal]
  rw [max_eq_left (by positivity), max_eq_left (by positivity), max_eq_left (by positivity)]
  rw [← EReal.coe_neg, ← EReal.coe_neg, ← EReal.coe_neg, EReal.exp_coe,
    EReal.exp_coe, EReal.exp_coe, neg_add, Real.exp_add,
    ENNReal.ofReal_mul (Real.exp_nonneg _)]
lemma negExp_add (x y : ℝ≥0∞) : negExp (x+y) = negExp x * negExp y := by
  simp only [negExp, enegExp_add, ENNReal.toReal_mul]
lemma negExp_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    negExp (∑ i ∈ s, f i) = ∏ i ∈ s, negExp (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, negExp_add, ih]
lemma negExp_nat_mul (n : ℕ) (x : ℝ≥0∞) : negExp (n*x) = negExp x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, negExp_add, ih, pow_succ]


lemma finiteCloudMeasure_lintegral (p : ℕ × (ℕ → E)) {ψ : E → ℝ≥0∞}
    (hψ : Measurable ψ) : (∫⁻ x, ψ x ∂finiteCloudMeasure p) = ∑ i : Fin p.1, ψ (p.2 i) := by
  simp [finiteCloudMeasure, lintegral_finsetSum_measure, lintegral_dirac' _ hψ]

variable [Nonempty E]


lemma finiteMeasure_mass_normalize (μ : FiniteMeasure E) :
    (μ : Measure E) = (μ.mass : ℝ≥0∞) • (μ.normalize : Measure E) := by
  ext s hs
  simpa using congrArg (fun m : FiniteMeasure E => (m : Measure E) s)
    μ.self_eq_mass_smul_normalize

lemma finitePoissonLaw_laplace (μ : FiniteMeasure E) {ψ : E → ℝ}
    (hψ : Measurable ψ) (hpos : ∀ x, 0 ≤ ψ x) :
    (∫ ν, negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂ν) ∂finitePoissonLaw μ) =
      negExp (∫⁻ x, ENNReal.ofReal (1-Real.exp (-ψ x)) ∂(μ : Measure E)) := by
  have hcost : ∀ x, 0 ≤ 1-Real.exp (-ψ x) := fun x =>
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hpos x)))
  have hi : Integrable (fun x => Real.exp (-ψ x)) (μ.normalize : Measure E) := by
    apply Integrable.of_bound hψ.neg.exp.aestronglyMeasurable 1
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hpos x))
  have hicost : Integrable (fun x => 1-Real.exp (-ψ x)) (μ.normalize : Measure E) :=
    (integrable_const 1).sub hi
  have hmeas : Measurable (fun ν : Measure E => negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂ν)) :=
    continuous_negExp.measurable.comp (Measure.measurable_lintegral hψ.ennreal_ofReal)
  rw [finitePoissonLaw, integral_map measurable_finiteCloudMeasure.aemeasurable
    hmeas.aestronglyMeasurable]
  have hs (p : ℕ × (ℕ → E)) :
      negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂finiteCloudMeasure p) =
        Real.exp (-cloudSum ψ p) := by
    rw [finiteCloudMeasure_lintegral p hψ.ennreal_ofReal,
      ← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
        (fun (i : Fin p.1) _ => hpos (p.2 i)), negExp_ofReal]
    · rfl
    · exact Finset.sum_nonneg (fun i _ => hpos (p.2 i))
  simp_rw [hs]
  rw [finitePoissonCloud_laplace μ.mass _ hψ hpos]
  rw [finiteMeasure_mass_normalize μ, lintegral_smul_measure]
  rw [← ofReal_integral_eq_lintegral_ofReal hicost (ae_of_all _ hcost)]
  rw [smul_eq_mul, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul μ.mass.coe_nonneg,
    negExp_ofReal (mul_nonneg μ.mass.coe_nonneg (integral_nonneg hcost))]
  rw [integral_sub (integrable_const 1) hi, integral_const]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  congr 1
  ring


omit [Nonempty E] in
lemma laplace_partial_tendsto (P : Measure (ℕ → Measure E)) [IsFiniteMeasure P]
    {a : Measure E → ℝ≥0∞} (ha : Measurable a) :
    Tendsto (fun n => ∫ ω, negExp (∑ i : Fin n, a (ω i)) ∂P)
      atTop (𝓝 (∫ ω, negExp (∑' i, a (ω i)) ∂P)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => 1)
  · intro n
    have hm : Measurable (fun ω : ℕ → Measure E => ∑ i : Fin n, a (ω i)) :=
      Finset.measurable_sum (Finset.univ : Finset (Fin n))
        (fun i _ => ha.comp (measurable_pi_apply (i : ℕ)))
    exact (continuous_negExp.measurable.comp hm).aestronglyMeasurable
  · exact integrable_const 1
  · intro n
    exact ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (negExp_nonneg _)]
      exact negExp_le_one _
  · exact ae_of_all _ fun ω => by
      simp_rw [Fin.sum_univ_eq_sum_range (fun i => a (ω i))]
      exact continuous_negExp.continuousAt.tendsto.comp (ENNReal.tendsto_nat_tsum _)

lemma poissonProductLaw_laplace_partial (μ : Measure E) [SFinite μ] {ψ : E → ℝ}
    (hψ : Measurable ψ) (hpos : ∀ x, 0 ≤ ψ x) (n : ℕ) :
    (∫ ω, negExp (∑ i : Fin n, ∫⁻ x, ENNReal.ofReal (ψ x) ∂ω i) ∂poissonProductLaw μ) =
      negExp (∑ i : Fin n, ∫⁻ x, ENNReal.ofReal (1-Real.exp (-ψ x)) ∂sfiniteSeq μ i) := by
  let a : Measure E → ℝ≥0∞ := fun ν => ∫⁻ x, ENNReal.ofReal (ψ x) ∂ν
  let c : E → ℝ≥0∞ := fun x => ENNReal.ofReal (1-Real.exp (-ψ x))
  have ha : Measurable a := Measure.measurable_lintegral hψ.ennreal_ofReal
  have heval : Measurable (fun ν => negExp (a ν)) := continuous_negExp.measurable.comp ha
  have hind : iIndepFun (fun i (ω : ℕ → Measure E) => negExp (a (ω i))) (poissonProductLaw μ) :=
    iIndepFun_infinitePi (fun _ => heval)
  have hh := (hind.precomp Fin.val_injective).integral_fun_prod_eq_prod_integral
    (fun i : Fin n => (heval.comp (measurable_pi_apply (i : ℕ))).aestronglyMeasurable)
  have hei (i : ℕ) :
      (∫ ω, negExp (a (ω i)) ∂poissonProductLaw μ) =
        negExp (∫⁻ x, c x ∂sfiniteSeq μ i) := by
    calc
      _ = ∫ ν, negExp (a ν) ∂poissonComponentLaw μ i :=
        (measurePreserving_eval_infinitePi (poissonComponentLaw μ) i).hasLaw.integral_comp
          heval.aestronglyMeasurable
      _ = _ := finitePoissonLaw_laplace ⟨sfiniteSeq μ i, inferInstance⟩ hψ hpos
  simpa only [negExp_sum, hei] using hh

 

theorem poissonLaw_laplace (μ : Measure E) [SFinite μ] {ψ : E → ℝ}
    (hψ : Measurable ψ) (hpos : ∀ x, 0 ≤ ψ x) :
    (∫ ν, negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂ν) ∂poissonLaw μ) =
      negExp (∫⁻ x, ENNReal.ofReal (1-Real.exp (-ψ x)) ∂μ) := by
  let a : Measure E → ℝ≥0∞ := fun ν => ∫⁻ x, ENNReal.ofReal (ψ x) ∂ν
  let c : E → ℝ≥0∞ := fun x => ENNReal.ofReal (1-Real.exp (-ψ x))
  have ha : Measurable a := Measure.measurable_lintegral hψ.ennreal_ofReal
  have heval : Measurable (fun ν => negExp (a ν)) := continuous_negExp.measurable.comp ha
  have hlim := laplace_partial_tendsto (poissonProductLaw μ) ha
  have hr : Tendsto (fun n => negExp (∑ i : Fin n, ∫⁻ x, c x ∂sfiniteSeq μ i))
      atTop (𝓝 (negExp (∫⁻ x, c x ∂μ))) := by
    have hsum : (∑' i, ∫⁻ x, c x ∂sfiniteSeq μ i) = ∫⁻ x, c x ∂μ := by
      rw [← lintegral_sum_measure, sum_sfiniteSeq]
    simp_rw [Fin.sum_univ_eq_sum_range (fun i => ∫⁻ x, c x ∂sfiniteSeq μ i)]
    rw [← hsum]
    exact continuous_negExp.continuousAt.tendsto.comp (ENNReal.tendsto_nat_tsum _)
  rw [poissonLaw, integral_map measurable_measureSum.aemeasurable
    heval.aestronglyMeasurable]
  change (∫ ω, negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂Measure.sum ω) ∂poissonProductLaw μ) = _
  simp_rw [lintegral_sum_measure]
  exact tendsto_nhds_unique (by
    simpa only [a, poissonProductLaw_laplace_partial μ hψ hpos] using hlim) hr


lemma laplace_finite_coordinates_unique {ι : Type*} [Fintype ι]
    (P Q : Measure (ι → ℝ≥0∞)) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (h : ∀ k : ι → ℕ,
      (∫ x, negExp (∑ i, (k i : ℝ≥0∞) * x i) ∂P) =
      ∫ x, negExp (∑ i, (k i : ℝ≥0∞) * x i) ∂Q) : P = Q := by
  classical
  let g : ι → ((ι → ℝ≥0∞) →ᵇ ℝ) := fun i =>
    negExpBCF.compContinuous ⟨fun x => x i, continuous_apply i⟩
  let ev : MvPolynomial ι ℝ →ₐ[ℝ] ((ι → ℝ≥0∞) →ᵇ ℝ) := MvPolynomial.aeval g
  let A : StarSubalgebra ℝ ((ι → ℝ≥0∞) →ᵇ ℝ) :=
    { ev.range with
      star_mem' := by
        intro f hf
        have hs : star f = f := by ext x; simp
        rw [hs]
        exact hf }
  have hap (i : ι) (x : ι → ℝ≥0∞) : g i x = negExp (x i) := rfl
  have hsep : (A.map (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
    intro x y hxy
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by contrapose! hxy; exact funext hxy
    refine ⟨g i, ?_, ?_⟩
    · refine ⟨(g i).toContinuousMap, ?_, rfl⟩
      exact ⟨g i, ⟨MvPolynomial.X i, by simp [ev]⟩, rfl⟩
    · simpa only [hap] using
        (fun h => hi (negExp_injective h))
  apply ext_of_forall_mem_subalgebra_integral_eq_of_polish hsep
  intro f hf
  obtain ⟨p, rfl⟩ := hf
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simpa only [map_add, BoundedContinuousFunction.coe_add, Pi.add_apply,
      integral_add (BoundedContinuousFunction.integrable _ _) (BoundedContinuousFunction.integrable _ _)]
      using congrArg₂ (· + ·) hp hq
  | monomial k r =>
    have hev (x : ι → ℝ≥0∞) : ev (MvPolynomial.monomial k r) x =
        r * negExp (∑ i, (k i : ℝ≥0∞) * x i) := by
      simp only [ev, MvPolynomial.aeval_monomial]
      rw [negExp_sum]
      simp only [negExp_nat_mul]
      simp [Finsupp.prod_fintype, hap]
    change (∫ x, ev (MvPolynomial.monomial k r) x ∂P) =
      ∫ x, ev (MvPolynomial.monomial k r) x ∂Q
    simp only [hev, integral_const_mul]
    exact congrArg (r * ·) (h fun i => k i)

lemma measure_eq_of_map_eq_comap {E F : Type*} [mE : MeasurableSpace E]
    [mF : MeasurableSpace F] {f : E → F}
    (hf : mE = mF.comap f) {P Q : Measure E} (h : P.map f = Q.map f) : P = Q := by
  have hfm : Measurable f := measurable_iff_comap_le.mpr hf.ge
  ext s hs
  rw [hf] at hs
  obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  exact (Measure.map_apply hfm ht).symm.trans ((congrArg (fun μ : Measure F => μ t) h).trans
    (Measure.map_apply hfm ht))

omit [Nonempty E] in
lemma measurable_measureCoordinates : Measurable (measureCoordinates (E := E)) :=
  Measurable.of_eval fun coordinate => Measure.measurable_coe coordinate.2

omit [Nonempty E] in
lemma measureSpace_eq_comap_coordinates :
    (inferInstance : MeasurableSpace (Measure E)) =
      MeasurableSpace.comap measureCoordinates (inferInstance : MeasurableSpace
        ({s : Set E // MeasurableSet s} → ℝ≥0∞)) := by
  apply le_antisymm
  · let m := MeasurableSpace.comap (measureCoordinates (E := E)) inferInstance
    have hc : @Measurable (Measure E) _ m _ measureCoordinates :=
      measurable_iff_comap_le.mpr le_rfl
    have hi : @Measurable (Measure E) (Measure E) m Measure.instMeasurableSpace id := by
      apply @Measure.measurable_of_measurable_coe E (Measure E) _ m id
      intro s hs
      change @Measurable (Measure E) ℝ≥0∞ m _
        (fun ν => measureCoordinates ν ⟨s, hs⟩)
      exact (measurable_pi_apply ⟨s, hs⟩).comp hc
    simpa only [MeasurableSpace.comap_id] using hi.comap_le
  · exact measurable_measureCoordinates.comap_le

omit [Nonempty E] in
 
theorem randomMeasure_laplace_unique (P Q : Measure (Measure E))
    [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (h : ∀ ψ : E → ℝ, Measurable ψ → (∀ x, 0 ≤ ψ x) →
      (∫ ν, negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂ν) ∂P) =
      ∫ ν, negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂ν) ∂Q) : P = Q := by
  classical
  apply measure_eq_of_map_eq_comap measureSpace_eq_comap_coordinates
  apply IsProjectiveLimit.unique (P := fun I =>
    (P.map measureCoordinates).map I.restrict) (fun _ => rfl)
  intro I
  change (Q.map measureCoordinates).map I.restrict = (P.map measureCoordinates).map I.restrict
  rw [Measure.map_map I.measurable_restrict
      measurable_measureCoordinates,
    Measure.map_map I.measurable_restrict
      measurable_measureCoordinates]
  let e : Measure E → (I → ℝ≥0∞) := fun ν i => ν i.1.1
  have he : Measurable e := Measurable.of_eval fun coordinate =>
    Measure.measurable_coe coordinate.1.2
  change Q.map e = P.map e
  apply laplace_finite_coordinates_unique
  intro k
  let ψ : E → ℝ := fun x => ∑ i : I, i.1.1.indicator (fun _ => (k i : ℝ)) x
  have hposi (i : I) (x : E) : 0 ≤ i.1.1.indicator (fun _ => (k i : ℝ)) x := by
    apply indicator_nonneg
    intro _ _
    positivity
  have hpos (x : E) : 0 ≤ ψ x := Finset.sum_nonneg (fun i _ => hposi i x)
  have hm : Measurable ψ := Finset.measurable_sum _ (fun i _ =>
    measurable_const.indicator i.1.2)
  have hoint (ν : Measure E) :
      (∫⁻ x, ENNReal.ofReal (ψ x) ∂ν) = ∑ i : I, (k i : ℝ≥0∞) * e ν i := by
    have ho (x : E) : ENNReal.ofReal (ψ x) =
        ∑ i : I, i.1.1.indicator (fun _ => (k i : ℝ≥0∞)) x := by
      change ENNReal.ofReal (∑ i : I, i.1.1.indicator (fun _ => (k i : ℝ)) x) = _
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hposi i x)]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hx : x ∈ i.1.1 <;> simp [hx]
    simp_rw [ho]
    rw [lintegral_finsetSum _ (fun i _ => measurable_const.indicator i.1.2)]
    apply Finset.sum_congr rfl
    intro i _
    rw [lintegral_indicator i.1.2, lintegral_const, Measure.restrict_apply_univ]
  have hcm : Measurable (fun x : I → ℝ≥0∞ => negExp (∑ i, (k i : ℝ≥0∞) * x i)) :=
    continuous_negExp.measurable.comp (Finset.measurable_sum _
      (fun i _ => measurable_const.mul (measurable_pi_apply i)))
  rw [integral_map he.aemeasurable hcm.aestronglyMeasurable,
    integral_map he.aemeasurable hcm.aestronglyMeasurable]
  simpa only [hoint] using (h ψ hm hpos).symm

end IsingPerceptron

 
namespace IsingPerceptron

 

theorem poissonLaw_map {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Nonempty E] [Nonempty F] (μ : Measure E) [SFinite μ] {T : E → F}
    (hT : Measurable T) [SFinite (μ.map T)] :
    (poissonLaw μ).map (fun ν => ν.map T) = poissonLaw (μ.map T) := by
  apply randomMeasure_laplace_unique
  intro ψ hψ hpos
  have hm : Measurable (fun ν : Measure F => negExp (∫⁻ y, ENNReal.ofReal (ψ y) ∂ν)) :=
    continuous_negExp.measurable.comp (Measure.measurable_lintegral hψ.ennreal_ofReal)
  rw [integral_map (Measure.measurable_map T hT).aemeasurable hm.aestronglyMeasurable]
  simp_rw [lintegral_map hψ.ennreal_ofReal hT]
  rw [poissonLaw_laplace μ (ψ := fun x => ψ (T x)) (hψ.comp hT) (fun x => hpos (T x)),
    poissonLaw_laplace (μ.map T) hψ hpos,
    lintegral_map (by fun_prop) hT]

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_LabeledSampling
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Labeled Sampling. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron
open Function

lemma measurable_lintegral_pointwiseFinite {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] (κ : Kernel A B) (hκ : ∀ a, IsFiniteMeasure (κ a))
    {f : A × B → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun a => ∫⁻ b, f (a,b) ∂κ a) := by
  classical
  let F : ℕ → SimpleFunc (A × B) ℝ≥0∞ := SimpleFunc.eapprox f
  have h : ∀ a b, ⨆ n, F n (a,b) = f (a,b) :=
    fun a b => SimpleFunc.iSup_eapprox_apply hf (a,b)
  simp_rw [← h]
  have he (a : A) : (∫⁻ b, ⨆ n, F n (a,b) ∂κ a) =
      ⨆ n, ∫⁻ b, F n (a,b) ∂κ a := by
    rw [lintegral_iSup]
    · exact fun n => (F n).measurable.comp measurable_prodMk_left
    · exact fun i j hij b => SimpleFunc.monotone_eapprox f hij _
  simp_rw [he]
  refine Measurable.iSup fun n => ?_
  refine SimpleFunc.induction (motive := fun g =>
    Measurable (fun a => ∫⁻ b, g (a,b) ∂κ a)) ?_ ?_ (F n)
  · intro c t ht
    have hi (a : A) : (∫⁻ b, t.indicator (fun _ => c) (a,b) ∂κ a) =
        c * κ a (Prod.mk a ⁻¹' t) := by
      simp_rw [← indicator_comp_right (Prod.mk a)]
      rw [lintegral_indicator (ht.preimage measurable_prodMk_left)]
      simp only [Function.comp_apply, lintegral_const, Measure.restrict_apply_univ]
    change Measurable (fun a => ∫⁻ b, t.indicator (fun _ => c) (a,b) ∂κ a)
    simp_rw [hi]
    exact measurable_const.mul (Kernel.measurable_kernel_prodMk_left_of_finite ht hκ)
  · intro g₁ g₂ _ hm₁ hm₂
    simp only [SimpleFunc.coe_add, Pi.add_apply]
    have ha (a : A) : (∫⁻ b, g₁ (a,b) + g₂ (a,b) ∂κ a) =
        (∫⁻ b, g₁ (a,b) ∂κ a) + ∫⁻ b, g₂ (a,b) ∂κ a :=
      lintegral_add_left (g₁.measurable.comp measurable_prodMk_left) _
    simp_rw [ha]
    exact hm₁.add hm₂


lemma finitePartKernel_finite {E : Type*} [MeasurableSpace E] (ν : Measure E) :
    IsFiniteMeasure (finitePartKernel ν) := by
  by_cases h : ν univ < ∞
  · change IsFiniteMeasure (if ν univ < ∞ then ν else 0)
    simp only [ite_eq_left h]
    exact ⟨h⟩
  · change IsFiniteMeasure (if ν univ < ∞ then ν else 0)
    simp only [ite_eq_right h]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma measurable_finitePart_lintegral {E : Type*} [MeasurableSpace E]
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun ν : Measure E => ∫⁻ x, F (x,ν) ∂finitePartKernel ν) :=
  measurable_lintegral_pointwiseFinite finitePartKernel finitePartKernel_finite
    (hF.comp measurable_swap)

lemma infinitePi_indep_eval_rest {ι E : Type*} [MeasurableSpace E]
    (P : ι → Measure E) [∀ i, IsProbabilityMeasure (P i)] (i : ι) :
    IndepFun (fun ω : ι → E => ω i)
      (fun ω : ι → E => fun j : {j : ι // j ≠ i} => ω j) (Measure.infinitePi P) := by
  let m : ι → MeasurableSpace (ι → E) := fun j =>
    MeasurableSpace.comap (fun ω => ω j) inferInstance
  have hi : iIndep m (Measure.infinitePi P) :=
    iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)
  have h := indep_iSup_of_disjoint (m := m) (fun j => (measurable_pi_apply j).comap_le) hi
    (S := {i}) (T := {j | j ≠ i}) (by simp)
  change Indep (MeasurableSpace.comap (fun ω : ι → E => ω i) inferInstance)
    (MeasurableSpace.comap (fun ω : ι → E => fun j : {j : ι // j ≠ i} => ω j)
      inferInstance) (Measure.infinitePi P)
  rw [MeasurableSpace.comap_process_pi, iSup_subtype]
  simpa only [Set.mem_singleton_iff, iSup_iSup_eq_left, Set.mem_ofPred_eq, m] using h

lemma infinitePi_eval_rest_map {ι E : Type*} [MeasurableSpace E]
    (P : ι → Measure E) [∀ i, IsProbabilityMeasure (P i)] (i : ι) :
    (Measure.infinitePi P).map (fun ω : ι → E =>
      (ω i, fun j : {j : ι // j ≠ i} => ω j)) =
      (P i).prod (Measure.infinitePi (fun j : {j : ι // j ≠ i} => P j)) := by
  have hmap := IndepFun.map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable
    (Measurable.of_eval fun j : {j : ι // j ≠ i} =>
      measurable_pi_apply (j : ι)).aemeasurable (infinitePi_indep_eval_rest P i)
  rw [Measure.infinitePi_map_eval,
    Measure.map_infinitePi_infinitePi_of_inj Subtype.val_injective] at hmap
  exact hmap

lemma measureSum_eq_eval_add_rest {E : Type*} [MeasurableSpace E]
    (ω : ℕ → Measure E) (i : ℕ) :
    Measure.sum ω = ω i + Measure.sum (fun j : {j : ℕ // j ≠ i} => ω j) := by
  classical
  ext s hs
  simp only [Measure.sum_apply _ hs, Measure.add_apply]
  rw [ENNReal.tsum_eq_add_tsum_ite i]
  congr 1
  trans ∑' j : ℕ, {j : ℕ | j ≠ i}.indicator (fun j => ω j s) j
  · apply tsum_congr
    intro j
    by_cases h : j = i <;> simp [h]
  · exact (tsum_subtype {j : ℕ | j ≠ i} (fun j => ω j s)).symm

variable {E : Type*} [MeasurableSpace E]

lemma measurable_atomCloud (n : ℕ) : Measurable (atomCloud (E := E) (n := n)) := by
  exact Finset.measurable_sum _ (fun i _ => Measure.measurable_dirac.comp
    (measurable_pi_apply i))

lemma atomCloud_insertNth {n : ℕ} (i : Fin (n+1)) (x : E) (ω : Fin n → E) :
    atomCloud (i.insertNth x ω) = Measure.dirac x + atomCloud ω := by
  classical
  rw [atomCloud, Fin.sum_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  rfl

lemma atomCloud_lintegral {n : ℕ} (ω : Fin n → E) {f : E → ℝ≥0∞}
    (hf : Measurable f) : (∫⁻ x, f x ∂atomCloud ω) = ∑ i, f (ω i) := by
  simp [atomCloud, lintegral_finsetSum_measure, lintegral_dirac' _ hf]

lemma iid_point_insertion (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) (n : ℕ) (i : Fin (n+1)) :
    (∫⁻ ω : Fin (n+1) → E, F (ω i, atomCloud ω) ∂Measure.pi (fun _ => μ)) =
      ∫⁻ x, ∫⁻ ω : Fin n → E, F (x, Measure.dirac x + atomCloud ω)
        ∂Measure.pi (fun _ => μ) ∂μ := by
  have hm : Measurable (fun p : E × (Fin n → E) =>
      F (p.1, Measure.dirac p.1 + atomCloud p.2)) :=
    hF.comp (measurable_fst.prodMk ((Measure.measurable_dirac.comp measurable_fst).add
      ((measurable_atomCloud n).comp measurable_snd)))
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) i).symm
    |>.lintegral_comp (hF.comp ((measurable_pi_apply i).prodMk
      (measurable_atomCloud (n+1))))
  simp only [Function.comp_apply] at h
  have he (p : E × (Fin n → E)) :
      F (((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E) i).symm p) i,
        atomCloud ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E) i).symm p)) =
      F (p.1, Measure.dirac p.1 + atomCloud p.2) := by
    change F ((i.insertNth (α := fun _ => E) p.1 p.2) i,
      atomCloud (i.insertNth (α := fun _ => E) p.1 p.2)) = _
    rw [Fin.insertNth_apply_same, atomCloud_insertNth]
  simp_rw [he] at h
  exact h.symm.trans (lintegral_prod _ hm.aemeasurable)

lemma iid_sum_point_insertion (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) (n : ℕ) :
    (∫⁻ ω : Fin (n+1) → E, ∑ i, F (ω i, atomCloud ω) ∂Measure.pi (fun _ => μ)) =
      (n+1 : ℝ≥0∞) * ∫⁻ x, ∫⁻ ω : Fin n → E, F (x, Measure.dirac x + atomCloud ω)
        ∂Measure.pi (fun _ => μ) ∂μ := by
  rw [lintegral_finsetSum Finset.univ (f := fun i (ω : Fin (n+1) → E) => F (ω i, atomCloud ω)) (fun i _ =>
    (hF.comp ((measurable_pi_apply i).prodMk (measurable_atomCloud (n+1)))))]
  simp only [iid_point_insertion μ hF n, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

lemma poissonWeight_succ (r : ℝ≥0) (n : ℕ) :
    poissonWeight r (n+1) * (n+1 : ℝ≥0∞) = r * poissonWeight r n := by
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn1 : (n+1 : ℝ) ≠ 0 := by positivity
  have he : (Real.exp (-(r : ℝ)) * (r : ℝ)^(n+1) / ((n+1).factorial : ℝ)) * (n+1) =
      (r : ℝ) * (Real.exp (-(r : ℝ)) * (r : ℝ)^n / (n.factorial : ℝ)) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp
  have hh := congrArg ENNReal.ofReal he
  simpa only [poissonWeight, ENNReal.ofReal_mul (by positivity :
      0 ≤ Real.exp (-(r : ℝ)) * (r : ℝ)^(n+1) / ((n+1).factorial : ℝ)),
    ENNReal.ofReal_add (by positivity : 0 ≤ (n : ℝ)) (by positivity : 0 ≤ (1 : ℝ)),
    ENNReal.ofReal_natCast, ENNReal.ofReal_one, ENNReal.ofReal_mul r.coe_nonneg,
    ENNReal.ofReal_coe_nnreal] using hh

lemma iid_restrict_lintegral (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ)
    {H : (Fin n → E) → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ ω : ℕ → E, H (fun i => ω i) ∂Measure.infinitePi (fun _ : ℕ => μ)) =
      ∫⁻ ω : Fin n → E, H ω ∂Measure.pi (fun _ => μ) := by
  have hp : MeasurePreserving (fun ω : ℕ → E => fun i : Fin n => ω i)
      (Measure.infinitePi (fun _ : ℕ => μ)) (Measure.pi (fun _ : Fin n => μ)) := by
    refine ⟨Measurable.of_eval fun index => measurable_pi_apply (index : ℕ), ?_⟩
    rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective, Measure.infinitePi_eq_pi]
  exact hp.lintegral_comp hH

lemma lintegral_finitePoissonCloud (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    {H : Measure E → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ p, H (finiteCloudMeasure p) ∂finitePoissonCloud r μ) =
      ∑' n, poissonWeight r n * ∫⁻ ω : Fin n → E, H (atomCloud ω)
        ∂Measure.pi (fun _ => μ) := by
  rw [finitePoissonCloud, lintegral_prod (fun p => H (finiteCloudMeasure p)) (hH.comp measurable_finiteCloudMeasure).aemeasurable]
  have hi (n : ℕ) :
      (∫⁻ ω : ℕ → E, H (finiteCloudMeasure (n, ω))
        ∂Measure.infinitePi (fun _ : ℕ => μ)) =
      ∫⁻ ω : Fin n → E, H (atomCloud ω) ∂Measure.pi (fun _ => μ) :=
    iid_restrict_lintegral μ n (hH.comp (measurable_atomCloud n))
  simp_rw [hi]
  rw [poissonMeasure, lintegral_sum_measure]
  simp [lintegral_smul_measure, poissonWeight, smul_eq_mul, lintegral_dirac]

 

theorem finitePoissonCloud_insertion (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F)
    :
    (∫⁻ p, ∫⁻ x, F (x, finiteCloudMeasure p) ∂finitePartKernel (finiteCloudMeasure p)
      ∂finitePoissonCloud r μ) =
      r * ∫⁻ x, ∫⁻ p, F (x, Measure.dirac x + finiteCloudMeasure p)
        ∂finitePoissonCloud r μ ∂μ := by
  rw [lintegral_finitePoissonCloud r μ (measurable_finitePart_lintegral hF)]
  have hm (x : E) : Measurable (fun ν : Measure E => F (x, Measure.dirac x + ν)) :=
    hF.comp (measurable_const.prodMk (measurable_const.add measurable_id))
  simp_rw [lintegral_finitePoissonCloud r μ (hm _)]
  have hi (n : ℕ) (ω : Fin n → E) : (∫⁻ x, F (x, atomCloud ω) ∂finitePartKernel (atomCloud ω)) =
      ∑ i, F (ω i, atomCloud ω) := by
    have hfin : IsFiniteMeasure (atomCloud ω) := by unfold atomCloud; infer_instance
    have he : finitePartKernel (atomCloud ω) = atomCloud ω :=
      ite_eq_left (measure_lt_top _ _)
    rw [he]
    exact atomCloud_lintegral ω (hF.comp (measurable_id.prodMk measurable_const))
  simp_rw [hi]
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Fin.sum_univ_zero, lintegral_zero, mul_zero, zero_add]
  simp_rw [iid_sum_point_insertion μ hF, ← mul_assoc, poissonWeight_succ]
  simp_rw [mul_assoc]
  rw [ENNReal.tsum_mul_left]
  congr 1
  have hmj (n : ℕ) : Measurable (fun p : E × (Fin n → E) =>
      F (p.1, Measure.dirac p.1 + atomCloud p.2)) :=
    hF.comp (measurable_fst.prodMk ((Measure.measurable_dirac.comp measurable_fst).add
      ((measurable_atomCloud n).comp measurable_snd)))
  have hmi (n : ℕ) : Measurable (fun x => ∫⁻ ω : Fin n → E,
      F (x, Measure.dirac x + atomCloud ω) ∂Measure.pi (fun _ => μ)) :=
    (hmj n).lintegral_prod_right
  rw [lintegral_tsum]
  · apply tsum_congr
    intro n
    rw [lintegral_const_mul _ (hmi n)]
  · intro n
    exact (measurable_const.mul (hmi n)).aemeasurable

lemma measurable_measureSum_countable {ι : Type*} [Countable ι] :
    Measurable (Measure.sum : (ι → Measure E) → Measure E) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Measure.sum_apply _ hs]
  exact Measurable.tsum fun i => (Measure.measurable_coe hs).comp (measurable_pi_apply i)

lemma measurable_finitePart_param {A : Type*} [MeasurableSpace A]
    {N : A → Measure E} (hN : Measurable N) {F : A × E → ℝ≥0∞}
    (hF : Measurable F) :
    Measurable (fun a => ∫⁻ x, F (a,x) ∂finitePartKernel (N a)) := by
  let κ : Kernel A E := ⟨fun a => finitePartKernel (N a),
    finitePartKernel.measurable.comp hN⟩
  exact measurable_lintegral_pointwiseFinite κ
    (fun a => finitePartKernel_finite (N a)) hF

variable [Nonempty E]

lemma finitePoissonLaw_finite (μ : FiniteMeasure E) :
    ∀ᵐ ν ∂finitePoissonLaw μ, ν univ < ∞ := by
  rw [finitePoissonLaw, ae_map_iff measurable_finiteCloudMeasure.aemeasurable
    (measurableSet_lt (Measure.measurable_coe MeasurableSet.univ) measurable_const)]
  exact ae_of_all _ fun p => by
    have : IsFiniteMeasure (finiteCloudMeasure p) := by
      unfold finiteCloudMeasure
      first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
    exact measure_lt_top _ _

lemma finitePoissonLaw_insertion (μ : FiniteMeasure E)
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ ν, ∫⁻ x, F (x,ν) ∂finitePartKernel ν ∂finitePoissonLaw μ) =
      ∫⁻ x, ∫⁻ ν, F (x,Measure.dirac x + ν) ∂finitePoissonLaw μ ∂(μ : Measure E) := by
  have hm (x : E) : Measurable (fun ν : Measure E => F (x,Measure.dirac x + ν)) :=
    hF.comp (measurable_const.prodMk (measurable_const.add measurable_id))
  rw [finitePoissonLaw, lintegral_map (measurable_finitePart_lintegral hF)
    measurable_finiteCloudMeasure]
  simp_rw [lintegral_map (hm _) measurable_finiteCloudMeasure]
  rw [finiteMeasure_mass_normalize μ, lintegral_smul_measure, smul_eq_mul]
  exact finitePoissonCloud_insertion μ.mass _ hF

 
lemma poissonComponent_insertion (μ : Measure E) [SFinite μ] (i : ℕ)
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ ω, ∫⁻ x, F (x, Measure.sum ω) ∂finitePartKernel (ω i)
      ∂poissonProductLaw μ) =
      ∫⁻ x, ∫⁻ ω, F (x, Measure.dirac x + Measure.sum ω)
        ∂poissonProductLaw μ ∂sfiniteSeq μ i := by
  let R := {j : ℕ // j ≠ i}
  let P := poissonComponentLaw μ
  let rest : (R → Measure E) → Measure E := Measure.sum
  have hrest : Measurable rest := measurable_measureSum_countable
  let joint := fun ω : ℕ → Measure E => (ω i, fun j : R => ω j)
  have hjoint : Measurable joint := (measurable_pi_apply i).prodMk
    (Measurable.of_eval fun index : R => measurable_pi_apply (index : ℕ))
  have hjlaw : (poissonProductLaw μ).map joint =
      (P i).prod (Measure.infinitePi (fun j : R => P j)) :=
    infinitePi_eval_rest_map P i
  have hI : Measurable (fun p : Measure E × (R → Measure E) =>
      ∫⁻ x, F (x,p.1 + rest p.2) ∂finitePartKernel p.1) := by
    apply measurable_finitePart_param measurable_fst (F := fun p => F (p.2,p.1.1 + rest p.1.2))
    exact hF.comp (measurable_snd.prodMk
      ((measurable_fst.comp measurable_fst).add
        (hrest.comp (measurable_snd.comp measurable_fst))))
  have hR (x : E) : Measurable (fun p : Measure E × (R → Measure E) =>
      F (x,Measure.dirac x + (p.1 + rest p.2))) :=
    hF.comp (measurable_const.prodMk (measurable_const.add
      (measurable_fst.add (hrest.comp measurable_snd))))
  have he (ω : ℕ → Measure E) : Measure.sum ω = (joint ω).1 + rest (joint ω).2 :=
    measureSum_eq_eval_add_rest ω i
  simp_rw [he]
  rw [← lintegral_map hI hjoint, hjlaw,
    lintegral_prod_symm _ hI.aemeasurable]
  simp_rw [← lintegral_map (hR _) hjoint, hjlaw]
  have hFp (ω : R → Measure E) : Measurable (fun p : E × Measure E =>
      F (p.1,p.2 + rest ω)) :=
    hF.comp (measurable_fst.prodMk (measurable_snd.add measurable_const))
  have hins (ω : R → Measure E) :
      (∫⁻ ν, ∫⁻ x, F (x,ν + rest ω) ∂finitePartKernel ν ∂P i) =
        ∫⁻ x, ∫⁻ ν, F (x,Measure.dirac x + ν + rest ω) ∂P i ∂sfiniteSeq μ i :=
    finitePoissonLaw_insertion ⟨sfiniteSeq μ i, inferInstance⟩ (hFp ω)
  simp_rw [hins]
  have hJ : Measurable (fun p : (R → Measure E) × E =>
      ∫⁻ ν, F (p.2,Measure.dirac p.2 + ν + rest p.1) ∂P i) := by
    have hm : Measurable (fun p : ((R → Measure E) × E) × Measure E =>
        F (p.1.2,Measure.dirac p.1.2 + p.2 + rest p.1.1)) :=
      hF.comp ((measurable_snd.comp measurable_fst).prodMk
        (((Measure.measurable_dirac.comp (measurable_snd.comp measurable_fst)).add
          measurable_snd).add (hrest.comp (measurable_fst.comp measurable_fst))))
    exact hm.lintegral_prod_right
  rw [lintegral_lintegral_swap hJ.aemeasurable]
  congr 1
  funext x
  rw [lintegral_prod_symm _ (hR x).aemeasurable]
  simp only [add_assoc]

lemma poissonProductLaw_finite (μ : Measure E) [SFinite μ] :
    ∀ᵐ ω ∂poissonProductLaw μ, ∀ i, ω i univ < ∞ := by
  rw [ae_all_iff]
  intro i
  have h := finitePoissonLaw_finite (⟨sfiniteSeq μ i, inferInstance⟩ : FiniteMeasure E)
  have he : (poissonProductLaw μ).map (fun ω => ω i) = poissonComponentLaw μ i :=
    Measure.infinitePi_map_eval _ i
  change ∀ᵐ ν ∂poissonComponentLaw μ i, ν univ < ∞ at h
  rw [← he] at h
  exact (ae_map_iff (measurable_pi_apply i).aemeasurable
    (measurableSet_lt (Measure.measurable_coe MeasurableSet.univ) measurable_const)).mp h

 
theorem poissonProductLaw_insertion (μ : Measure E) [SFinite μ]
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ ω, ∫⁻ x, F (x, Measure.sum ω) ∂Measure.sum ω ∂poissonProductLaw μ) =
      ∫⁻ x, ∫⁻ ω, F (x, Measure.dirac x + Measure.sum ω)
        ∂poissonProductLaw μ ∂μ := by
  have ha : (fun ω : ℕ → Measure E => ∫⁻ x, F (x,Measure.sum ω) ∂Measure.sum ω) =ᵐ[
      poissonProductLaw μ] (fun ω => ∑' i, ∫⁻ x, F (x,Measure.sum ω) ∂finitePartKernel (ω i)) := by
    filter_upwards [poissonProductLaw_finite μ] with ω hω
    rw [lintegral_sum_measure]
    apply tsum_congr
    intro i
    rw [show finitePartKernel (ω i) = ω i from ite_eq_left (hω i)]
  rw [lintegral_congr_ae ha, lintegral_tsum]
  · simp_rw [poissonComponent_insertion μ _ hF]
    rw [← lintegral_sum_measure, sum_sfiniteSeq]
  · intro i
    apply Measurable.aemeasurable
    apply measurable_finitePart_param (measurable_pi_apply i)
      (F := fun p => F (p.2,Measure.sum p.1))
    exact hF.comp (measurable_snd.prodMk (measurable_measureSum.comp measurable_fst))

lemma poissonProductLaw_mean_count (μ : Measure E) [SFinite μ]
    {s : Set E} (hs : MeasurableSet s) :
    (∫⁻ ω, Measure.sum ω s ∂poissonProductLaw μ) = μ s := by
  have hF : Measurable (fun p : E × Measure E => s.indicator (fun _ => (1 : ℝ≥0∞)) p.1) :=
    (measurable_const.indicator hs).comp measurable_fst
  have h := poissonProductLaw_insertion μ hF
  simpa only [lintegral_indicator_const hs, one_mul, lintegral_const,
    measure_univ, mul_one] using h

lemma poissonLaw_mean_count (μ : Measure E) [SFinite μ]
    {s : Set E} (hs : MeasurableSet s) :
    (∫⁻ ν, ν s ∂poissonLaw μ) = μ s := by
  rw [poissonLaw, lintegral_map (Measure.measurable_coe hs) measurable_measureSum]
  exact poissonProductLaw_mean_count μ hs

omit [Nonempty E] in
lemma measurable_measureRestrict {s : Set E} (hs : MeasurableSet s) :
    Measurable (fun ν : Measure E => ν.restrict s) := by
  apply Measure.measurable_of_measurable_coe
  intro t ht
  simp only [Measure.restrict_apply ht]
  exact Measure.measurable_coe (ht.inter hs)



lemma sigmaPart_eq_ae (μ : Measure E) [SigmaFinite μ] :
    ∀ᵐ ν ∂poissonLaw μ, sigmaPart μ ν = ν := by
  have ha : ∀ n, ∀ᵐ ν ∂poissonLaw μ,
      ν (disjointed (spanningSets μ) n) < ∞ := by
    intro n
    have hm := MeasurableSet.disjointed (measurableSet_spanningSets μ) n
    apply ae_lt_top (Measure.measurable_coe hm)
    rw [poissonLaw_mean_count μ hm]
    exact ((measure_mono (disjointed_subset _ _)).trans_lt
      (measure_spanningSets_lt_top μ n)).ne
  filter_upwards [ae_all_iff.mpr ha] with ν hν
  unfold sigmaPart
  calc
    _ = Measure.sum (fun n => ν.restrict (disjointed (spanningSets μ) n)) := by
      congr 1
      funext n
      apply ite_eq_left
      simpa only [Measure.restrict_apply_univ] using hν n
    _ = ν := sum_restrict_disjointed_spanningSets ν μ

omit [Nonempty E] in
lemma measurable_sigmaPart_param (μ : Measure E) [SigmaFinite μ]
    {A : Type*} [MeasurableSpace A] {N : A → Measure E} (hN : Measurable N)
    {F : A × E → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun a => ∫⁻ x, F (a,x) ∂sigmaPart μ (N a)) := by
  simp only [sigmaPart, lintegral_sum_measure]
  apply Measurable.tsum
  intro n
  exact measurable_finitePart_param
    ((measurable_measureRestrict (MeasurableSet.disjointed (measurableSet_spanningSets μ) n)).comp hN) hF

end IsingPerceptron


end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_MapWithDensityEquiv
attribute [-instance] _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.powerIntensity_nullSingleton _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Map With Density Equiv. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma map_withDensity_equiv {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (e : E ≃ᵐ F) (μ : Measure E) {w : E → ℝ≥0∞} (hw : Measurable w) :
    (μ.withDensity w).map e = (μ.map e).withDensity (w ∘ e.symm) := by
  apply Measure.ext_of_lintegral
  intro f hf
  calc
    _ = ∫⁻ x, w x * f (e x) ∂μ := by
      rw [lintegral_map hf e.measurable]
      exact lintegral_withDensity_eq_lintegral_mul μ hw
        (show Measurable (fun x => f (e x)) from hf.comp e.measurable)
    _ = ∫⁻ x, (w (e.symm x) * f x) ∂μ.map e := by
      simpa only [Pi.mul_apply, Function.comp_apply, e.symm_apply_apply] using
        (lintegral_map (μ := μ) ((hw.comp e.symm.measurable).mul hf) e.measurable).symm
    _ = _ := (lintegral_withDensity_eq_lintegral_mul _
      (hw.comp e.symm.measurable) hf).symm

lemma measurable_powerIntensityDensity (b : ℝ) : Measurable (powerIntensityDensity b) := by
  unfold powerIntensityDensity
  apply Measurable.ennreal_ofReal
  apply Measurable.ite (measurableSet_lt measurable_const measurable_id)
  · fun_prop
  · fun_prop

lemma powerIntensityDensity_scale {b c : ℝ} (hc : 0 < c) (x : ℝ) :
    ENNReal.ofReal c⁻¹ * powerIntensityDensity b (c⁻¹ * x) =
      ENNReal.ofReal (c ^ b) * powerIntensityDensity b x := by
  have hpos : 0 < c⁻¹ * x ↔ 0 < x := mul_pos_iff_of_pos_left (inv_pos.mpr hc)
  unfold powerIntensityDensity
  by_cases hx : 0 < x
  · simp only [ite_eq_left hx, ite_eq_left (hpos.mpr hx)]
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le b)]
    congr 1
    rw [Real.mul_rpow (inv_nonneg.mpr hc.le) hx.le,
      Real.inv_rpow hc.le, ← Real.rpow_neg hc.le]
    have he : c⁻¹ * c ^ (-(-1-b)) = c ^ b := by
      rw [show -(-1-b) = b + 1 by ring, Real.rpow_add hc]
      simp only [Real.rpow_one]
      field_simp
    calc
       c⁻¹ * (b * (c ^ (-(-1-b)) * x ^ (-1-b))) =
           b * (c⁻¹ * c ^ (-(-1-b))) * x ^ (-1-b) := by ring
       _ = c ^ b * (b * x ^ (-1-b)) := by rw [he]; ring
  · simp only [ite_eq_right hx, ite_eq_right (fun h => hx (hpos.mp h)), ENNReal.ofReal_zero,
      mul_zero]

theorem map_powerIntensity_mul {b c : ℝ} (hc : 0 < c) :
    (powerIntensity b).map (fun x => c*x) =
      ENNReal.ofReal (c ^ b) • powerIntensity b := by
  let e := MeasurableEquiv.mulLeft₀ c hc.ne'
  have hm := map_withDensity_equiv e volume (measurable_powerIntensityDensity b)
  change (volume.withDensity (powerIntensityDensity b)).map e = _
  rw [hm]
  change (volume.map (fun x => c*x)).withDensity
    (fun x => powerIntensityDensity b (c⁻¹*x)) = _
  unfold powerIntensity
  rw [Real.map_volume_mul_left hc.ne', abs_of_pos (inv_pos.mpr hc),
    withDensity_smul_measure, ← withDensity_smul (ENNReal.ofReal c⁻¹)
      (show Measurable (fun x => powerIntensityDensity b (c⁻¹*x)) from
        (measurable_powerIntensityDensity b).comp (measurable_const_mul c⁻¹)),
    ← withDensity_smul (ENNReal.ofReal (c^b)) (measurable_powerIntensityDensity b)]
  congr 1
  funext x
  exact powerIntensityDensity_scale hc x

lemma poissonLaw_congr {E : Type*} [MeasurableSpace E] [Nonempty E]
    {μ ν : Measure E} [SFinite μ] [SFinite ν] (h : μ = ν) : poissonLaw μ = poissonLaw ν := by
  subst ν
  rfl

open Set

lemma integrable_power_min {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    Integrable (fun x : ℝ => min 1 (max x 0)) (powerIntensity b) := by
  rw [powerIntensity, integrable_withDensity_iff (measurable_powerIntensityDensity b)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  have hi : IntegrableOn (fun x : ℝ => x ^ (-b)) (Ioc 0 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num)).mpr (by linarith)
  have hj : IntegrableOn (fun x : ℝ => x ^ (-1-b)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have H₁ : Integrable ((Ioc (0:ℝ) 1).indicator (fun x => b * x ^ (-b))) :=
    (integrable_indicator_iff measurableSet_Ioc).mpr (hi.const_mul b)
  have H₂ : Integrable ((Ioi (1:ℝ)).indicator (fun x => b * x ^ (-1-b))) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr (hj.const_mul b)
  have H := H₁.add H₂
  apply H.congr
  apply ae_of_all
  intro x
  symm
  simp only [Pi.add_apply]
  by_cases hx : 0 < x
  · simp only [powerIntensityDensity, ite_eq_left hx,
      ENNReal.toReal_ofReal (mul_nonneg hb.le (Real.rpow_nonneg hx.le _)), max_eq_left hx.le]
    by_cases hx1 : x ≤ 1
    · rw [min_eq_right hx1, indicator_of_mem (show x ∈ Ioc (0:ℝ) 1 from ⟨hx,hx1⟩),
        indicator_of_notMem (show x ∉ Ioi (1:ℝ) from not_lt.mpr hx1), add_zero]
      have hp : x * x ^ (-1-b) = x ^ (-b) := by
        calc
          x * x ^ (-1-b) = x ^ (1 + (-1-b)) := by rw [Real.rpow_add hx, Real.rpow_one]
          _ = x ^ (-b) := by congr 1; ring
      nlinarith [hp]
    · rw [min_eq_left (le_of_lt (lt_of_not_ge hx1)), one_mul,
        indicator_of_notMem (show x ∉ Ioc (0:ℝ) 1 from fun h => hx1 h.2),
        indicator_of_mem (show x ∈ Ioi (1:ℝ) from lt_of_not_ge hx1), zero_add]
  · simp [powerIntensityDensity, hx, max_eq_right (le_of_not_gt hx),
      indicator_of_notMem (show x ∉ Ioi (1:ℝ) from fun h => hx (lt_trans zero_lt_one h))]

lemma measurable_stableLaplaceCost : Measurable stableLaplaceCost := by
  unfold stableLaplaceCost
  fun_prop

lemma stableLaplaceCost_nonneg (x : ℝ) : 0 ≤ stableLaplaceCost x := by
  unfold stableLaplaceCost
  exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (le_max_right _ _)))

lemma stableLaplaceCost_le_min (x : ℝ) : stableLaplaceCost x ≤ min 1 (max x 0) := by
  unfold stableLaplaceCost
  exact le_min (by linarith [Real.exp_pos (-max x 0)])
    (by linarith [Real.add_one_le_exp (-max x 0)])

lemma integrable_stableLaplaceCost {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    Integrable stableLaplaceCost (powerIntensity b) := by
  apply (integrable_power_min hb hb1).mono' measurable_stableLaplaceCost.aestronglyMeasurable
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (stableLaplaceCost_nonneg x)]
    exact stableLaplaceCost_le_min x

lemma stableLaplaceConstant_lt_top {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    stableLaplaceConstant b < ∞ := by
  exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ stableLaplaceCost_nonneg)).mp
    (integrable_stableLaplaceCost hb hb1).hasFiniteIntegral

lemma stableLaplaceConstant_pos {b : ℝ} (hb : 0 < b) : 0 < stableLaplaceConstant b := by
  unfold stableLaplaceConstant powerIntensity
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_powerIntensityDensity b)
    measurable_stableLaplaceCost.ennreal_ofReal]
  apply (lintegral_pos_iff_support ((measurable_powerIntensityDensity b).mul
    measurable_stableLaplaceCost.ennreal_ofReal)).mpr
  have hs : Function.support (powerIntensityDensity b * (fun x => ENNReal.ofReal (stableLaplaceCost x))) =
      Ioi (0:ℝ) := by
    ext x
    by_cases hx : 0 < x
    · have hp : 0 < b * x ^ (-1-b) := mul_pos hb (Real.rpow_pos_of_pos hx _)
      have hc : 0 < 1 - Real.exp (-x) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx))
      simp [Function.mem_support, powerIntensityDensity, stableLaplaceCost, hx,
        max_eq_left hx.le, ne_of_gt (ENNReal.ofReal_pos.mpr hp), ne_of_gt (ENNReal.ofReal_pos.mpr hc)]
    · simp [Function.mem_support, powerIntensityDensity, hx]
  rw [hs]
  simp

end IsingPerceptron

namespace IsingPerceptron

lemma integrable_negExp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {X : Ω → ℝ≥0∞} (hX : Measurable X) : Integrable (fun ω => negExp (X ω)) P := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (continuous_negExp.measurable.comp hX).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    change ‖negExp (X ω)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (negExp_nonneg _)]
    exact negExp_le_one _

lemma measure_zero_of_integral_tests {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {A : Set Ω} (hA : MeasurableSet A)
    {f : ℕ → Ω → ℝ} (hfi : ∀ n, Integrable (f n) P)
    (hfpos : ∀ n ω, 0 ≤ f n ω) (hb : ∀ n ω, ω ∈ A → 1 ≤ f n ω)
    (ht : Tendsto (fun n => ∫ ω, f n ω ∂P) atTop (𝓝 0)) : P A = 0 := by
  apply (measureReal_eq_zero_iff (μ := P) (s := A)).mp
  apply le_antisymm _ measureReal_nonneg
  apply ge_of_tendsto' ht
  intro n
  rw [← integral_indicator_one hA]
  apply integral_mono ((integrable_const (1 : ℝ)).indicator hA) (hfi n)
  intro ω
  by_cases hω : ω ∈ A
  · simpa only [indicator_of_mem hω, Pi.one_apply] using hb n ω hω
  · simpa only [indicator_of_notMem hω] using hfpos n ω

theorem stable_laplace_finite_positive {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ≥0∞}
    (hX : Measurable X) {C b : ℝ} (hC : 0 < C) (hb : 0 < b)
    (hl : ∀ t : ℝ, 0 < t →
      (∫ ω, negExp (ENNReal.ofReal t * X ω) ∂P) = Real.exp (-C * t ^ b)) :
    ∀ᵐ ω ∂P, 0 < X ω ∧ X ω < ∞ := by
  have hi (t : ℝ) : Integrable (fun ω => negExp (ENNReal.ofReal t * X ω)) P :=
    integrable_negExp P (measurable_const.mul hX)
  have hfinite : P {ω | X ω = ∞} = 0 := by
    let t : ℕ → ℝ := fun n => 1 / ((n:ℝ)+1)
    have htpos (n : ℕ) : 0 < t n := by dsimp [t] <;> positivity
    apply measure_zero_of_integral_tests P (hX (measurableSet_singleton ∞))
      (f := fun n ω => 1 - negExp (ENNReal.ofReal (t n) * X ω))
    · intro n
      exact (integrable_const 1).sub (hi (t n))
    · intro n ω
      exact sub_nonneg.mpr (negExp_le_one _)
    · intro n ω hω
      change X ω = ∞ at hω
      simp [hω, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr (htpos n)))]
    · have ht : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      have hr : Tendsto (fun n => (t n)^b) atTop (𝓝 0) := by
        simpa only [Function.comp_def, Real.zero_rpow hb.ne'] using (Real.continuous_rpow_const hb.le).continuousAt.tendsto.comp ht
      have he : Tendsto (fun n => 1 - Real.exp (-C * (t n)^b)) atTop (𝓝 0) := by
        simpa only [Function.comp_def, mul_zero, Real.exp_zero, sub_self] using
          (tendsto_const_nhds (x := (1:ℝ))).sub (Real.continuous_exp.continuousAt.tendsto.comp (hr.const_mul (-C)))
      convert he using 1
      all_goals try with_reducible_and_instances rfl
      ext n
      rw [integral_sub (integrable_const 1) (hi (t n)), hl _ (htpos n), integral_const]
      simp
  have hpositive : P {ω | X ω = 0} = 0 := by
    let t : ℕ → ℝ := fun n => (n:ℝ)+1
    have htpos (n : ℕ) : 0 < t n := by dsimp [t] <;> positivity
    apply measure_zero_of_integral_tests P (hX (measurableSet_singleton 0))
      (f := fun n ω => negExp (ENNReal.ofReal (t n) * X ω))
    · exact fun n => hi (t n)
    · exact fun _ _ => negExp_nonneg _
    · intro n ω hω
      change X ω = 0 at hω
      simp [hω]
    · have ht : Tendsto t atTop atTop := tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
      have hr := (tendsto_rpow_atTop hb).comp ht
      have he := Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (Filter.Tendsto.const_mul_atTop hC hr))
      simpa only [hl _ (htpos _), Function.comp_def, neg_mul] using he
  have hf : ∀ᵐ ω ∂P, X ω ≠ ∞ := by simpa only [ae_iff, not_not] using hfinite
  have hp : ∀ᵐ ω ∂P, X ω ≠ 0 := by simpa only [ae_iff, not_not] using hpositive
  filter_upwards [hf, hp] with ω hf hp
  exact ⟨pos_iff_ne_zero.mpr hp, lt_top_iff_ne_top.mpr hf⟩

lemma stableLaplaceCost_scale (t x : ℝ) (ht : 0 ≤ t) :
    stableLaplaceCost (t*x) = 1-Real.exp (-t * max x 0) := by
  have hm : max (t*x) 0 = t * max x 0 := by
    simpa only [mul_zero] using (mul_max_of_nonneg x 0 ht).symm
  rw [stableLaplaceCost, hm]
  congr 2
  ring

lemma powerIntensity_laplace_scale {b t : ℝ} (ht : 0 < t) :
    (∫⁻ x, ENNReal.ofReal (1-Real.exp (-t * max x 0)) ∂powerIntensity b) =
    ENNReal.ofReal (t^b) * stableLaplaceConstant b := by
  simp_rw [← stableLaplaceCost_scale t _ ht.le]
  rw [← lintegral_map measurable_stableLaplaceCost.ennreal_ofReal
    (measurable_const_mul t), map_powerIntensity_mul ht, lintegral_smul_measure]
  rfl

lemma integrable_exp_neg_mul {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 ≤ X ω) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun ω => Real.exp (-t * X ω)) P := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards [hpos] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hω)

lemma measureReal_mul_le_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {A : Set Ω} (hA : MeasurableSet A)
    {f : Ω → ℝ} (hf : Integrable f P) (hfpos : 0 ≤ᵐ[P] f) (c : ℝ)
    (hc : ∀ᵐ ω ∂P, ω ∈ A → c ≤ f ω) : P.real A * c ≤ ∫ ω, f ω ∂P := by
  rw [← smul_eq_mul, ← integral_indicator_const c hA]
  apply integral_mono_ae ((integrable_const c).indicator hA) hf
  filter_upwards [hfpos, hc] with ω hp hb
  by_cases hω : ω ∈ A
  · simpa only [indicator_of_mem hω] using hb hω
  · simpa only [indicator_of_notMem hω, Pi.zero_apply] using hp

lemma stable_laplace_upper_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 ≤ X ω) {C b : ℝ}
    (hl : ∀ t : ℝ, 0 < t → (∫ ω, Real.exp (-t * X ω) ∂P) = Real.exp (-C*t^b))
    {s : ℝ} (hs : 0 < s) :
    P {ω | s < X ω} ≤ ENNReal.ofReal (C / (1-Real.exp (-1)) * s^(-b)) := by
  have hc : 0 < 1-Real.exp (-1) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hi := integrable_exp_neg_mul P hX hpos (inv_nonneg.mpr hs.le)
  have h := measureReal_mul_le_integral P (measurableSet_lt measurable_const hX)
    ((integrable_const 1).sub hi) (by
      filter_upwards [hpos] with ω hω
      exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith [inv_nonneg.mpr hs.le])))
    (1-Real.exp (-1)) (by
      filter_upwards [] with ω hω
      apply sub_le_sub_left
      apply Real.exp_le_exp.mpr
      have hmul : 1 < s⁻¹ * X ω := by
        rw [← div_eq_inv_mul, lt_div_iff₀ hs]
        simpa using hω
      linarith)
  simp only [Pi.sub_apply] at h
  rw [integral_sub (integrable_const 1) hi, integral_const, hl _ (inv_pos.mpr hs)] at h
  simp only [probReal_univ, smul_eq_mul, one_mul] at h
  have hbnd : P.real {ω | s < X ω} ≤ C / (1-Real.exp (-1)) * s^(-b) := by
    have he := Real.add_one_le_exp (-C * (s⁻¹)^b)
    have hp : (s⁻¹)^b = s^(-b) := by rw [Real.inv_rpow hs.le, Real.rpow_neg hs.le]
    rw [hp] at h he
    apply (le_of_mul_le_mul_right _ hc)
    calc
      _ ≤ 1-Real.exp (-C * s^(-b)) := h
      _ ≤ C * s^(-b) := by linarith
      _ = (C / (1-Real.exp (-1)) * s^(-b)) * (1-Real.exp (-1)) := by field_simp
  rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
  exact ENNReal.ofReal_le_ofReal hbnd

lemma stable_laplace_inverse_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 < X ω) {C b : ℝ}
    (hl : ∀ t : ℝ, 0 < t → (∫ ω, Real.exp (-t * X ω) ∂P) = Real.exp (-C*t^b))
    {s : ℝ} (hs : 0 < s) :
    P {ω | s < (X ω)⁻¹} ≤ ENNReal.ofReal (Real.exp 1 * Real.exp (-C*s^b)) := by
  have hi := integrable_exp_neg_mul P hX (hpos.mono fun _ h => h.le) hs.le
  have h := measureReal_mul_le_integral P (measurableSet_lt measurable_const hX.inv) hi
    (ae_of_all _ fun _ => (Real.exp_pos _).le) (Real.exp (-1)) (by
      filter_upwards [hpos] with ω hp hω
      apply Real.exp_le_exp.mpr
      have hmul : s * X ω < 1 := by
        simpa only [mul_one] using (lt_inv_mul_iff₀' hp).mp (show s < (X ω)⁻¹ * 1 by simpa using hω)
      linarith)
  rw [hl _ hs] at h
  have hbnd : P.real {ω | s < (X ω)⁻¹} ≤ Real.exp 1 * Real.exp (-C*s^b) := by
    apply le_of_mul_le_mul_right _ (Real.exp_pos (-1))
    calc
      _ ≤ Real.exp (-C*s^b) := h
      _ = (Real.exp 1 * Real.exp (-C*s^b)) * Real.exp (-1) := by
        rw [mul_comm (Real.exp 1), mul_assoc, ← Real.exp_add]
        simp
  rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
  exact ENNReal.ofReal_le_ofReal hbnd

lemma integrable_rpow_of_power_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 ≤ X ω)
    {K b r : ℝ} (hK : 0 ≤ K) (hr : 0 < r) (hrb : r < b)
    (htail : ∀ t : ℝ, 0 < t → P {ω | t < X ω} ≤ ENNReal.ofReal (K*t^(-b))) :
    Integrable (fun ω => X ω ^ r) P := by
  have hpow : ∀ᵐ ω ∂P, 0 ≤ X ω ^ r := hpos.mono fun _ h => Real.rpow_nonneg h _
  refine ⟨(hX.pow measurable_const).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hpow, lintegral_rpow_eq_lintegral_meas_lt_mul P hpos hX.aemeasurable hr]
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  let B : ℝ → ℝ := fun t => (Ioc (0:ℝ) 1).indicator (fun u => u^(r-1)) t +
    (Ioi (1:ℝ)).indicator (fun u => K*u^(r-b-1)) t
  have h₁ : IntegrableOn (fun t : ℝ => t^(r-1)) (Ioc 0 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num)).mpr (by linarith)
  have h₂ : IntegrableOn (fun t : ℝ => K*t^(r-b-1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)).const_mul K
  have hB : Integrable B (volume.restrict (Ioi 0)) :=
    (((integrable_indicator_iff measurableSet_Ioc).mpr h₁).add
      ((integrable_indicator_iff measurableSet_Ioi).mpr h₂)).restrict
  have hBpos : ∀ t, 0 ≤ B t := by
    intro t
    apply add_nonneg
    · exact (indicator_nonneg (s := Ioc (0:ℝ) 1) (fun u hu => Real.rpow_nonneg hu.1.le (r-1))) t
    · exact (indicator_nonneg (s := Ioi (1:ℝ)) (fun u hu => mul_nonneg hK (Real.rpow_nonneg (le_trans zero_le_one (le_of_lt hu)) (r-b-1)))) t
  have hfin := (hasFiniteIntegral_iff_ofReal (ae_of_all _ hBpos)).mp hB.hasFiniteIntegral
  apply lt_of_le_of_lt _ hfin
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  by_cases ht1 : t ≤ 1
  · have hb : B t = t^(r-1) := by
      simp only [B, indicator_of_mem (show t ∈ Ioc (0:ℝ) 1 from ⟨ht0,ht1⟩),
        indicator_of_notMem (show t ∉ Ioi (1:ℝ) from not_lt.mpr ht1), add_zero]
    rw [hb]
    exact mul_le_of_le_one_left' prob_le_one
  · have hb : B t = K*t^(r-b-1) := by
      simp only [B, indicator_of_notMem (show t ∉ Ioc (0:ℝ) 1 from fun h => ht1 h.2),
        indicator_of_mem (show t ∈ Ioi (1:ℝ) from lt_of_not_ge ht1), zero_add]
    rw [hb]
    calc
      _ ≤ ENNReal.ofReal (K*t^(-b)) * ENNReal.ofReal (t^(r-1)) :=
        mul_le_mul_of_nonneg_right (htail t ht0) zero_le
      _ = ENNReal.ofReal (K*t^(r-b-1)) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hK (Real.rpow_nonneg ht0.le _)),
          mul_assoc, ← Real.rpow_add ht0]
        rw [show -b + (r-1) = r-b-1 by ring]

lemma integrable_rpow_of_exp_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 ≤ X ω)
    {K C b r : ℝ} (hK : 0 ≤ K) (hC : 0 < C) (hb : 0 < b) (hr : 0 < r)
    (htail : ∀ t : ℝ, 0 < t →
      P {ω | t < X ω} ≤ ENNReal.ofReal (K*Real.exp (-C*t^b))) :
    Integrable (fun ω => X ω ^ r) P := by
  have hpow : ∀ᵐ ω ∂P, 0 ≤ X ω ^ r := hpos.mono fun _ h => Real.rpow_nonneg h _
  refine ⟨(hX.pow measurable_const).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hpow, lintegral_rpow_eq_lintegral_meas_lt_mul P hpos hX.aemeasurable hr]
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  have hi : IntegrableOn (fun t : ℝ => K * (t^(r-1) * Real.exp (-C*t^b))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) hb hC).const_mul K
  have hnonneg : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), 0 ≤ K * (t^(r-1) * Real.exp (-C*t^b)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg hK (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _))
  apply lt_of_le_of_lt _ ((hasFiniteIntegral_iff_ofReal hnonneg).mp hi.hasFiniteIntegral)
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  calc
    _ ≤ ENNReal.ofReal (K*Real.exp (-C*t^b)) * ENNReal.ofReal (t^(r-1)) :=
      mul_le_mul_of_nonneg_right (htail t ht) zero_le
    _ = ENNReal.ofReal (K*(t^(r-1)*Real.exp (-C*t^b))) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hK (Real.exp_nonneg _))]
      congr 1
      ring

lemma log_sq_le_powers {x r : ℝ} (hx : 0 < x) (hr : 0 < r) :
    (Real.log x)^2 ≤ (2/r)^2 * (x^r + (x⁻¹)^r) := by
  have he : 0 < r/2 := by positivity
  have hpow (y : ℝ) (hy : 0 ≤ y) : (y^(r/2)/(r/2))^2 = (2/r)^2 * y^r := by
    rw [div_pow, ← Real.rpow_mul_natCast hy]
    norm_num
    field_simp
  by_cases hlog : 0 ≤ Real.log x
  · have h := (sq_le_sq₀ hlog (div_nonneg (Real.rpow_nonneg hx.le _) he.le)).mpr
      (Real.log_le_rpow_div hx.le he)
    rw [hpow x hx.le] at h
    nlinarith [Real.rpow_nonneg (inv_nonneg.mpr hx.le) r, sq_nonneg (2/r)]
  · have hlog' : 0 ≤ Real.log x⁻¹ := by rw [Real.log_inv]; linarith
    have h := (sq_le_sq₀ hlog' (div_nonneg (Real.rpow_nonneg (inv_nonneg.mpr hx.le) _) he.le)).mpr
      (Real.log_le_rpow_div (inv_nonneg.mpr hx.le) he)
    rw [hpow x⁻¹ (inv_nonneg.mpr hx.le), Real.log_inv, neg_sq] at h
    nlinarith [Real.rpow_nonneg hx.le r, sq_nonneg (2/r)]

theorem integrable_log_sq_of_moments {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {X : Ω → ℝ} (hX : Measurable X)
    (hpos : ∀ᵐ ω ∂P, 0 < X ω) {r : ℝ} (hr : 0 < r)
    (hi : Integrable (fun ω => X ω ^ r) P)
    (hj : Integrable (fun ω => (X ω)⁻¹ ^ r) P) :
    Integrable (fun ω => (Real.log (X ω))^2) P := by
  apply ((hi.add hj).const_mul ((2/r)^2)).mono' ((hX.log.pow_const 2).aestronglyMeasurable)
  filter_upwards [hpos] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact log_sq_le_powers hω hr

lemma stable_positive_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 ≤ X ω) {C b r : ℝ}
    (hC : 0 < C) (hr : 0 < r) (hrb : r < b)
    (hl : ∀ t : ℝ, 0 < t → (∫ ω, Real.exp (-t * X ω) ∂P) = Real.exp (-C*t^b)) :
    Integrable (fun ω => X ω ^ r) P := by
  apply integrable_rpow_of_power_tail P hX hpos (K := C/(1-Real.exp (-1)))
    (div_nonneg hC.le (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num)))) hr hrb
  exact fun _ ht => stable_laplace_upper_tail P hX hpos hl ht

lemma stable_negative_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 < X ω) {C b r : ℝ}
    (hC : 0 < C) (hb : 0 < b) (hr : 0 < r)
    (hl : ∀ t : ℝ, 0 < t → (∫ ω, Real.exp (-t * X ω) ∂P) = Real.exp (-C*t^b)) :
    Integrable (fun ω => (X ω)⁻¹ ^ r) P := by
  apply integrable_rpow_of_exp_tail P hX.inv (hpos.mono fun _ h => (inv_pos.mpr h).le)
    (Real.exp_nonneg 1) hC hb hr
  exact fun _ ht => stable_laplace_inverse_tail P hX hpos hl ht

lemma negExp_eq_exp_toReal {x : ℝ≥0∞} (hx : x ≠ ∞) : negExp x = Real.exp (-x.toReal) := by
  conv_lhs => rw [← ENNReal.ofReal_toReal hx, negExp_ofReal ENNReal.toReal_nonneg]

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_MarkedPartitionNumerator
attribute [-instance] _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseChildKernel_markov _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Marked Partition Numerator. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron
variable {E : Type*} [MeasurableSpace E] [Nonempty E]

lemma poissonLaw_ae_intensity (μ : Measure E) [SFinite μ] {p : E → Prop}
    (hp : MeasurableSet {x | p x}) (h : ∀ᵐ x ∂μ, p x) :
    ∀ᵐ ν ∂poissonLaw μ, ∀ᵐ x ∂ν, p x := by
  have he : (∫⁻ ν, ν {x | ¬ p x} ∂poissonLaw μ) = 0 := by
    exact (poissonLaw_mean_count μ (show MeasurableSet {x | ¬p x} from hp.compl)).trans (ae_iff.mp h)
  have hz := (lintegral_eq_zero_iff (Measure.measurable_coe hp.compl)).mp he
  filter_upwards [hz] with ν hν
  exact ae_iff.mpr hν

lemma weightedPoissonTotal_real_eq_ae (b : ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    {a : E → ℝ≥0∞} (ha : Measurable a) (hfin : ∀ᵐ y ∂μ, a y < ∞) {t : ℝ} (ht : 0 ≤ t) :
    (fun ν => ∫⁻ p : ℝ × E, ENNReal.ofReal (t * max p.1 0 * (a p.2).toReal) ∂ν) =ᵐ[
      poissonLaw ((powerIntensity b).prod μ)]
      (fun ν => ENNReal.ofReal t * weightedPoissonTotal a ν) := by
  have hprod : ∀ᵐ p : ℝ × E ∂(powerIntensity b).prod μ, a p.2 < ∞ :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_lt (ha.comp measurable_snd) measurable_const)).mpr
      (ae_of_all _ fun _ => hfin)
  filter_upwards [poissonLaw_ae_intensity ((powerIntensity b).prod μ)
    (measurableSet_lt (ha.comp measurable_snd) measurable_const) hprod] with ν hν
  rw [weightedPoissonTotal, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [hν] with p hp
  change a p.2 < ∞ at hp
  rw [ENNReal.ofReal_mul (mul_nonneg ht (le_max_right _ _)), ENNReal.ofReal_mul ht,
    ENNReal.ofReal_toReal hp.ne, mul_assoc]

omit [Nonempty E] in
lemma weightedPower_laplace_cost (b : ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    {a : E → ℝ≥0∞} (ha : Measurable a) (hpos : ∀ᵐ y ∂μ, 0 < (a y).toReal)
    {t : ℝ} (ht : 0 < t) :
    (∫⁻ p : ℝ × E, ENNReal.ofReal (1-Real.exp (-(t * max p.1 0 * (a p.2).toReal)))
      ∂(powerIntensity b).prod μ) =
      ENNReal.ofReal (t^b) * (∫⁻ y, ENNReal.ofReal ((a y).toReal^b) ∂μ) *
        stableLaplaceConstant b := by
  rw [lintegral_prod_symm _ (by fun_prop)]
  have he : (fun y => ∫⁻ x, ENNReal.ofReal
      (1-Real.exp (-(t * max x 0 * (a y).toReal))) ∂powerIntensity b) =ᵐ[μ]
      (fun y => ENNReal.ofReal (t^b) * ENNReal.ofReal ((a y).toReal^b) * stableLaplaceConstant b) := by
    filter_upwards [hpos] with y hy
    have hmul (x : ℝ) : t * max x 0 * (a y).toReal = (t*(a y).toReal)*max x 0 := by ring
    simp_rw [hmul]
    have hs := powerIntensity_laplace_scale (b := b) (mul_pos ht hy)
    simp only [neg_mul] at hs ⊢
    rw [hs, Real.mul_rpow ht.le hy.le,
      ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
  rw [lintegral_congr_ae he, lintegral_mul_const _ (by fun_prop),
    lintegral_const_mul _ (by fun_prop)]

lemma weightedPoissonTotal_laplace (b : ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    {a : E → ℝ≥0∞} (ha : Measurable a) (hfin : ∀ᵐ y ∂μ, a y < ∞)
    (hpos : ∀ᵐ y ∂μ, 0 < (a y).toReal) {t : ℝ} (ht : 0 < t) :
    (∫ ν, negExp (ENNReal.ofReal t * weightedPoissonTotal a ν)
      ∂poissonLaw ((powerIntensity b).prod μ)) =
      negExp (ENNReal.ofReal (t^b) * (∫⁻ y, ENNReal.ofReal ((a y).toReal^b) ∂μ) *
        stableLaplaceConstant b) := by
  have h := poissonLaw_laplace ((powerIntensity b).prod μ)
    (ψ := fun p => t * max p.1 0 * (a p.2).toReal) (by fun_prop)
    (fun p => mul_nonneg (mul_nonneg ht.le (le_max_right _ _)) ENNReal.toReal_nonneg)
  rw [weightedPower_laplace_cost b μ ha hpos ht] at h
  rw [← h]
  apply integral_congr_ae
  exact ((weightedPoissonTotal_real_eq_ae b μ ha hfin ht.le).fun_comp negExp).symm

end IsingPerceptron

namespace IsingPerceptron

end IsingPerceptron

namespace IsingPerceptron

lemma rawCascadeLaw_succ (n : ℕ) (b : ℕ → ℝ) :
    (rawCascadeLaw (n+1) b : Measure (RawTree (n+1))) =
      poissonLaw ((powerIntensity (b 0)).prod
        (rawCascadeLaw n (fun i => b (i+1)) : Measure (RawTree n))) := rfl

lemma HasStableTotal.finite_positive {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ≥0∞} {b : ℝ}
    (h : HasStableTotal P X b) (hX : Measurable X) (hb : 0 < b) :
    ∀ᵐ ω ∂P, 0 < X ω ∧ X ω < ∞ := by
  obtain ⟨C, hC, hl⟩ := h
  exact stable_laplace_finite_positive P hX hC hb hl

lemma HasStableTotal.real_laplace {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ≥0∞} {b : ℝ}
    (h : HasStableTotal P X b) (hX : Measurable X) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      (∫ ω, Real.exp (-t * (X ω).toReal) ∂P) = Real.exp (-C*t^b) := by
  have hf := h.finite_positive hX hb
  obtain ⟨C, hC, hl⟩ := h
  refine ⟨C, hC, fun t ht => ?_⟩
  rw [← hl t ht]
  apply integral_congr_ae
  filter_upwards [hf] with ω hω
  rw [negExp_eq_exp_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω.2.ne),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal ht.le, neg_mul]

lemma HasStableTotal.positive_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ≥0∞} {b r : ℝ}
    (h : HasStableTotal P X b) (hX : Measurable X) (hb : 0 < b)
    (hr : 0 < r) (hrb : r < b) : Integrable (fun ω => (X ω).toReal^r) P := by
  obtain ⟨C, hC, hl⟩ := h.real_laplace hX hb
  exact stable_positive_moment P hX.ennreal_toReal
    (ae_of_all _ fun _ => ENNReal.toReal_nonneg) hC hr hrb hl

lemma HasStableTotal.negative_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ≥0∞} {b r : ℝ}
    (h : HasStableTotal P X b) (hX : Measurable X) (hb : 0 < b)
    (hr : 0 < r) : Integrable (fun ω => ((X ω).toReal)⁻¹^r) P := by
  obtain ⟨C, hC, hl⟩ := h.real_laplace hX hb
  apply stable_negative_moment P hX.ennreal_toReal _ hC hb hr hl
  filter_upwards [h.finite_positive hX hb] with ω hω
  exact ENNReal.toReal_pos hω.1.ne' hω.2.ne

lemma weightedPoissonTotal_stable {E : Type*} [MeasurableSpace E] [Nonempty E]
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) (μ : Measure E) [IsProbabilityMeasure μ]
    {a : E → ℝ≥0∞} (ha : Measurable a) (hfin : ∀ᵐ y ∂μ, a y < ∞)
    (hpos : ∀ᵐ y ∂μ, 0 < (a y).toReal)
    (hpay : Integrable (fun y => (a y).toReal^b) μ) :
    HasStableTotal (poissonLaw ((powerIntensity b).prod μ)) (weightedPoissonTotal a) b := by
  let A := ∫⁻ y, ENNReal.ofReal ((a y).toReal^b) ∂μ
  have hA : A < ∞ := by
    exact hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => Real.rpow_nonneg ENNReal.toReal_nonneg _)
      |>.mp hpay.hasFiniteIntegral
  have hApos : 0 < A := by
    apply (lintegral_pos_iff_support (ha.ennreal_toReal.pow_const b |>.ennreal_ofReal)).mpr
    have he : (Function.support (fun y => ENNReal.ofReal ((a y).toReal^b))) =ᵐ[μ] Set.univ := by
      filter_upwards [hpos] with y hy
      apply propext
      change (ENNReal.ofReal ((a y).toReal^b) ≠ 0) ↔ True
      exact iff_true_intro (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hy _)))
    rw [measure_congr he, measure_univ]
    exact zero_lt_one
  let C := A * stableLaplaceConstant b
  have hC : C < ∞ := ENNReal.mul_lt_top hA (stableLaplaceConstant_lt_top hb hb1)
  have hCp : 0 < C := ENNReal.mul_pos hApos.ne' (stableLaplaceConstant_pos hb).ne'
  refine ⟨C.toReal, ENNReal.toReal_pos hCp.ne' hC.ne, fun t ht => ?_⟩
  rw [weightedPoissonTotal_laplace b μ ha hfin hpos ht, mul_assoc]
  change negExp (ENNReal.ofReal (t^b) * C) = _
  rw [negExp_eq_exp_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC.ne),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg ht.le _)]
  congr 1
  ring

lemma CascadeExponents.tail {n : ℕ} {b : ℕ → ℝ} (h : CascadeExponents (n+1) b) :
    CascadeExponents n (fun i => b (i+1)) := by
  exact ⟨fun i hi => h.1 (i+1) (by omega), fun i j hij hj => h.2 (i+1) (j+1) (by omega) (by omega)⟩

theorem rawCascade_total_moments (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) :
    (∀ᵐ T ∂(rawCascadeLaw n b : Measure (RawTree n)),
      0 < rawTreeTotal n T ∧ rawTreeTotal n T < ∞) ∧
    (∀ r : ℝ, 0 < r → (∀ i < n, r < b i) →
      Integrable (fun T => (rawTreeTotal n T).toReal^r) (rawCascadeLaw n b : Measure (RawTree n))) ∧
    (∀ r : ℝ, 0 < r → Integrable (fun T => ((rawTreeTotal n T).toReal)⁻¹^r)
      (rawCascadeLaw n b : Measure (RawTree n))) := by
  induction n generalizing b with
  | zero =>
    refine ⟨ae_of_all _ (fun _ => by simp [rawTreeTotal]), ?_, ?_⟩
    · intro r _ _
      simp [rawTreeTotal]
    · intro r _
      simp [rawTreeTotal]
  | succ n ih =>
    have hi := ih (fun i => b (i+1)) hb.tail
    have hb0 := hb.1 0 (by omega)
    have hpos : ∀ᵐ T ∂(rawCascadeLaw n (fun i => b (i+1)) : Measure (RawTree n)),
        0 < (rawTreeTotal n T).toReal := by
      filter_upwards [hi.1] with T hT
      exact ENNReal.toReal_pos hT.1.ne' hT.2.ne
    have hm := hi.2.1 (b 0) hb0.1 (fun i hi => hb.2 0 (i+1) (by omega) (by omega))
    have hs : HasStableTotal (rawCascadeLaw (n+1) b : Measure (RawTree (n+1)))
        (rawTreeTotal (n+1)) (b 0) :=
      weightedPoissonTotal_stable hb0.1 hb0.2 _ (measurable_rawTreeTotal n)
        (hi.1.mono fun _ h => h.2) hpos hm
    exact ⟨hs.finite_positive (measurable_rawTreeTotal _) hb0.1,
      fun r hr hrb => hs.positive_moment (measurable_rawTreeTotal _) hb0.1 hr (hrb 0 (by omega)),
      fun r hr => hs.negative_moment (measurable_rawTreeTotal _) hb0.1 hr⟩

theorem rawCascade_total_log_square (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) :
    Integrable (fun T => (Real.log (rawTreeTotal n T).toReal)^2)
      (rawCascadeLaw n b : Measure (RawTree n)) := by
  cases n with
  | zero => simp [rawTreeTotal]
  | succ n =>
    have h := rawCascade_total_moments (n+1) b hb
    have hb0 := hb.1 0 (by omega)
    apply integrable_log_sq_of_moments _ (measurable_rawTreeTotal _).ennreal_toReal _
      (show 0 < b 0/2 by linarith) (h.2.1 _ (by linarith) _) (h.2.2 _ (by linarith))
    · filter_upwards [h.1] with T hT
      exact ENNReal.toReal_pos hT.1.ne' hT.2.ne
    · intro i hi
      by_cases h0 : i = 0
      · subst i; linarith
      · have := hb.2 0 i (by omega) hi; linarith

open scoped ProbabilityTheory

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_WeightedPartitionNumeratorIncrement
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseChildKernel_markov _root_.OAI.IsingPerceptron.noiseLeafKernel_markov _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTiltedLeafLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted Partition Numerator Increment. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron
variable (A : Type) [MeasurableSpace A]

variable [Nonempty A]

lemma noiseCascadeLaw_succ (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A) :
    (noiseCascadeLaw A (n+1) b μ : Measure (NoiseTree A (n+1))) =
      poissonLaw ((powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
        (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1))))) := rfl

lemma noiseCascadeLaw_forget (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A) :
    (noiseCascadeLaw A n b μ : Measure (NoiseTree A n)).map (noiseTreeForget A n) = rawCascadeLaw n b := by
  induction n generalizing b μ with
  | zero =>
    change (Measure.dirac (PUnit.unit : PUnit)).map (fun _ => PUnit.unit) = Measure.dirac PUnit.unit
    rw [Measure.map_dirac' measurable_const]
  | succ n ih =>
    rw [noiseCascadeLaw_succ, rawCascadeLaw_succ]
    change (poissonLaw _).map (fun ν => ν.map (fun p : ℝ × (A × NoiseTree A n) => (p.1, noiseTreeForget A n p.2.2))) = _
    rw [poissonLaw_map _ (T := fun p : ℝ × (A × NoiseTree A n) => (p.1, noiseTreeForget A n p.2.2))
      (measurable_fst.prodMk
      ((measurable_noiseTreeForget A n).comp (measurable_snd.comp measurable_snd)))]
    apply poissonLaw_congr
    have he : (fun p : ℝ × (A × NoiseTree A n) => (p.1, noiseTreeForget A n p.2.2)) =
        Prod.map id (fun q : A × NoiseTree A n => noiseTreeForget A n q.2) := rfl
    rw [he, ← Measure.map_prod_map _ _ (f := id)
      (g := fun q : A × NoiseTree A n => noiseTreeForget A n q.2) measurable_id
      ((measurable_noiseTreeForget A n).comp measurable_snd), Measure.map_id]
    congr 1
    change (((μ 0 : Measure A).prod
      (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1))))).map
        (noiseTreeForget A n ∘ Prod.snd) = _
    rw [← Measure.map_map (measurable_noiseTreeForget A n) measurable_snd,
      Measure.map_snd_prod, measure_univ, one_smul, ih]

omit [Nonempty A] in
lemma noiseTreeTotal_succ (n : ℕ) (ν : NoiseTree A (n+1)) :
    noiseTreeTotal A (n+1) ν = ∫⁻ p, ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 ∂ν := by
  change (∫⁻ p, ENNReal.ofReal (max p.1 0) * rawTreeTotal n p.2
    ∂ν.map (fun p => (p.1,noiseTreeForget A n p.2.2))) = _
  rw [lintegral_map]
  · rfl
  · exact (by fun_prop : Measurable (fun p : ℝ × RawTree n => ENNReal.ofReal (max p.1 0))).mul
      ((measurable_rawTreeTotal n).comp measurable_snd)
  · exact measurable_fst.prodMk ((measurable_noiseTreeForget A n).comp (measurable_snd.comp measurable_snd))

end IsingPerceptron

namespace IsingPerceptron

lemma measurable_map_sigmaPart_param {E F P : Type*} [MeasurableSpace E]
    [MeasurableSpace F] [MeasurableSpace P] (μ : Measure E) [SigmaFinite μ]
    {N : P → Measure E} (hN : Measurable N) {G : P × E → F} (hG : Measurable G) :
    Measurable (fun p => (sigmaPart μ (N p)).map (fun x => G (p,x))) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hf : Measurable (fun p : P × E => s.indicator (1 : F → ℝ≥0∞) (G p)) :=
    (measurable_const.indicator hs).comp hG
  convert measurable_sigmaPart_param μ hN hf using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  rw [Measure.map_apply (f := fun x => G (p,x))
    (hG.comp (measurable_const.prodMk measurable_id)) hs]
  exact (lintegral_indicator_one (hs.preimage
    (hG.comp (measurable_const.prodMk measurable_id)))).symm

variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

lemma measurable_noiseTreeDisplace (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i)) :
    Measurable (fun p : S × NoiseTree A n => noiseTreeDisplace n b μ c u p.1 p.2) := by
  induction n generalizing b μ c u with
  | zero => exact measurable_const
  | succ n ih =>
    unfold noiseTreeDisplace
    apply measurable_map_sigmaPart_param _ measurable_snd
      (G := fun p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) =>
        (c 0 (p.1.1,p.2.2.1) * p.2.1,
          noiseTreeDisplace n (fun j => b (j+1)) (fun j => μ (j+1))
            (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (p.1.1,p.2.2.1)) p.2.2.2))
    have hs : Measurable (fun p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) => p.1.1) := by fun_prop
    have ha : Measurable (fun p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) => p.2.2.1) := by fun_prop
    have hx : Measurable (fun p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) => p.2.1) := by fun_prop
    have hv : Measurable (fun p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) => p.2.2.2) := by fun_prop
    exact (((hc 0).comp (hs.prodMk ha)).mul hx).prodMk
      ((ih _ _ (fun i => hc (i+1)) (fun i => hu (i+1))).comp
        (((hu 0).comp (hs.prodMk ha)).prodMk hv))

end IsingPerceptron

namespace IsingPerceptron

lemma map_powerIntensity_subtree {A B C : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (b : ℝ)
    (μ : Measure A) (P : Measure B) (Q : Measure C)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {c : A → ℝ} (hc : Measurable c) (hcpos : ∀ a, 0 < c a)
    (hm : (∫⁻ a, ENNReal.ofReal (c a ^ b) ∂μ) = 1)
    {T : A × B → C} (hT : Measurable T)
    (hLaw : ∀ a, P.map (fun v => T (a,v)) = Q) :
    ((powerIntensity b).prod (μ.prod P)).map
      (fun p : ℝ × (A × B) => (c p.2.1 * p.1,T p.2)) = (powerIntensity b).prod Q := by
  have hF : Measurable (fun p : ℝ × (A × B) => (c p.2.1 * p.1,T p.2)) :=
    ((hc.comp (measurable_fst.comp measurable_snd)).mul measurable_fst).prodMk
      (hT.comp measurable_snd)
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hF, lintegral_prod
    (fun p : ℝ × (A × B) => f (c p.2.1*p.1,T p.2)) (hf.comp hF).aemeasurable]
  have hv (x : ℝ) (a : A) :
      (∫⁻ v, f (c a*x,T (a,v)) ∂P) = ∫⁻ w, f (c a*x,w) ∂Q := by
    rw [← hLaw a, lintegral_map]
    · exact hf.comp (measurable_const.prodMk measurable_id)
    · exact hT.comp (measurable_const.prodMk measurable_id)
  have hp (x : ℝ) : (∫⁻ v : A × B, f (c v.1*x,T v) ∂μ.prod P) =
      ∫⁻ a, ∫⁻ w, f (c a*x,w) ∂Q ∂μ := by
    rw [lintegral_prod (fun v : A × B => f (c v.1*x,T v))
      ((hf.comp hF).comp (measurable_const.prodMk measurable_id)).aemeasurable]
    simp_rw [hv]
  simp_rw [hp]
  have hG : Measurable (fun p : ℝ × A => ∫⁻ w, f (c p.2*p.1,w) ∂Q) :=
    (hf.comp ((((hc.comp (measurable_snd.comp measurable_fst)).mul
      (measurable_fst.comp measurable_fst))).prodMk measurable_snd)).lintegral_prod_right'
  rw [lintegral_lintegral_swap hG.aemeasurable]
  have hx (a : A) : (∫⁻ x, ∫⁻ w, f (c a*x,w) ∂Q ∂powerIntensity b) =
      ENNReal.ofReal (c a ^ b) * (∫⁻ x, ∫⁻ w, f (x,w) ∂Q ∂powerIntensity b) := by
    rw [← lintegral_map hf.lintegral_prod_right' (measurable_const_mul (c a)),
      map_powerIntensity_mul (hcpos a), lintegral_smul_measure]
    rfl
  simp_rw [hx]
  rw [lintegral_mul_const _ (by fun_prop), hm, one_mul,
    ← lintegral_prod _ hf.aemeasurable]

variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

theorem noiseTreeDisplace_law (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (hcpos : ∀ i s a, 0 < c i (s,a))
    (hm : ∀ i s, (∫⁻ a, ENNReal.ofReal (c i (s,a) ^ b i) ∂(μ i : Measure A)) = 1)
    (s : S) :
    (noiseCascadeLaw A n b μ : Measure (NoiseTree A n)).map (noiseTreeDisplace n b μ c u s) =
      rawCascadeLaw n b := by
  induction n generalizing b μ c u s with
  | zero =>
    change (Measure.dirac (PUnit.unit : PUnit)).map (fun _ => PUnit.unit) = Measure.dirac PUnit.unit
    exact Measure.map_dirac' measurable_const _
  | succ n ih =>
    let P : Measure (NoiseTree A n) := noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1))
    let Q : Measure (RawTree n) := rawCascadeLaw n (fun j => b (j+1))
    let I := (powerIntensity (b 0)).prod ((μ 0 : Measure A).prod P)
    let G : A × NoiseTree A n → RawTree n := fun p =>
      noiseTreeDisplace n (fun j => b (j+1)) (fun j => μ (j+1))
        (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (s,p.1)) p.2
    have hG : Measurable G :=
      (measurable_noiseTreeDisplace n _ _ (fun i => hc (i+1)) (fun i => hu (i+1))).comp
        (((hu 0).comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
    have hGLaw (a : A) : P.map (fun v => G (a,v)) = Q :=
      ih _ _ (fun i => hc (i+1)) (fun i => hu (i+1))
        (fun i => hcpos (i+1)) (fun i => hm (i+1)) (u 0 (s,a))
    let T : ℝ × (A × NoiseTree A n) → ℝ × RawTree n :=
      fun p => (c 0 (s,p.2.1) * p.1,G p.2)
    have hT : Measurable T :=
      (((hc 0).comp (measurable_const.prodMk (measurable_fst.comp measurable_snd))).mul
        measurable_fst).prodMk (hG.comp measurable_snd)
    have hI : I.map T = (powerIntensity (b 0)).prod Q :=
      map_powerIntensity_subtree (b 0) (μ 0 : Measure A) P Q (c := fun a => c 0 (s,a))
        ((hc 0).comp (measurable_const.prodMk measurable_id)) (hcpos 0 s) (hm 0 s) hG hGLaw
    rw [noiseCascadeLaw_succ, rawCascadeLaw_succ]
    change (poissonLaw I).map _ = poissonLaw ((powerIntensity (b 0)).prod Q)
    calc
      _ = (poissonLaw I).map (fun ν => ν.map T) := by
        apply Measure.map_congr
        filter_upwards [sigmaPart_eq_ae I] with ν hν
        change (sigmaPart I ν).map T = ν.map T
        rw [hν]
      _ = poissonLaw (I.map T) := poissonLaw_map I hT
      _ = _ := poissonLaw_congr hI

end IsingPerceptron

namespace IsingPerceptron

lemma integrable_of_square {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {f : Ω → ℝ} (hf : Measurable f)
    (hi : Integrable (fun x => (f x)^2) P) : Integrable f P := by
  apply ((integrable_const (1 : ℝ)).add hi).mono' hf.aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs]
  change |f x| ≤ 1+(f x)^2
  have h := sq_nonneg (|f x|-1)
  nlinarith [sq_abs (f x)]

lemma integral_difference_same_law {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure E) [IsProbabilityMeasure Q]
    {X Y : Ω → E} (hX : Measurable X) (hY : Measurable Y)
    (hXL : P.map X = Q) (hYL : P.map Y = Q)
    {g : E → ℝ} (hg : Measurable g) (hg2 : Integrable (fun v => (g v)^2) Q) :
    Integrable (fun ω => g (X ω)-g (Y ω)) P ∧
    (∫ ω, g (X ω)-g (Y ω) ∂P) = 0 ∧
    Integrable (fun ω => (g (X ω)-g (Y ω))^2) P ∧
    (∫ ω, (g (X ω)-g (Y ω))^2 ∂P) ≤ 4 * ∫ v, (g v)^2 ∂Q := by
  have hX2 : Integrable (fun ω => (g (X ω))^2) P := by
    apply (integrable_map_measure (hg.pow_const 2).aestronglyMeasurable hX.aemeasurable).mp
    rw [hXL]
    exact hg2
  have hY2 : Integrable (fun ω => (g (Y ω))^2) P := by
    apply (integrable_map_measure (hg.pow_const 2).aestronglyMeasurable hY.aemeasurable).mp
    rw [hYL]
    exact hg2
  have hXi : Integrable (fun ω => g (X ω)) P := integrable_of_square P (hg.comp hX) hX2
  have hYi : Integrable (fun ω => g (Y ω)) P := integrable_of_square P (hg.comp hY) hY2
  have hdiff : Integrable (fun ω => (g (X ω)-g (Y ω))^2) P := by
    apply ((hX2.add hY2).const_mul 2).mono'
      (((hg.comp hX).sub (hg.comp hY)).pow_const 2).aestronglyMeasurable
    apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (g (X ω)-g (Y ω))^2 ≤ 2*((g (X ω))^2+(g (Y ω))^2)
    nlinarith [sq_nonneg (g (X ω)+g (Y ω))]
  refine ⟨hXi.sub hYi, ?_, hdiff, ?_⟩
  · rw [integral_sub hXi hYi, ← integral_map hX.aemeasurable hg.aestronglyMeasurable,
      ← integral_map hY.aemeasurable hg.aestronglyMeasurable, hXL, hYL, sub_self]
  · calc
      _ ≤ ∫ ω, 2*((g (X ω))^2+(g (Y ω))^2) ∂P :=
        integral_mono hdiff ((hX2.add hY2).const_mul 2) (fun ω => by
          nlinarith [sq_nonneg (g (X ω)+g (Y ω))])
      _ = 4 * ∫ v, (g v)^2 ∂Q := by
        rw [integral_const_mul, integral_add hX2 hY2,
          ← integral_map hX.aemeasurable (hg.pow_const 2).aestronglyMeasurable,
          ← integral_map hY.aemeasurable (hg.pow_const 2).aestronglyMeasurable, hXL, hYL]
        ring

variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

theorem noiseTreeDisplace_log_ratio (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A)
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (hcpos : ∀ i s a, 0 < c i (s,a))
    (hm : ∀ i s, (∫⁻ a, ENNReal.ofReal (c i (s,a) ^ b i) ∂(μ i : Measure A)) = 1)
    (s : S) :
    let L := fun ν : NoiseTree A n =>
      Real.log (rawTreeTotal n (noiseTreeDisplace n b μ c u s ν)).toReal -
        Real.log (noiseTreeTotal A n ν).toReal
    Integrable L (noiseCascadeLaw A n b μ : Measure (NoiseTree A n)) ∧
    (∫ ν, L ν ∂(noiseCascadeLaw A n b μ : Measure (NoiseTree A n))) = 0 ∧
    Integrable (fun ν => (L ν)^2) (noiseCascadeLaw A n b μ : Measure (NoiseTree A n)) ∧
    (∫ ν, (L ν)^2 ∂(noiseCascadeLaw A n b μ : Measure (NoiseTree A n))) ≤
      4 * ∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n)) := by
  exact integral_difference_same_law (noiseCascadeLaw A n b μ : Measure (NoiseTree A n))
    (rawCascadeLaw n b : Measure (RawTree n))
    (X := noiseTreeDisplace n b μ c u s) (Y := noiseTreeForget A n)
    ((measurable_noiseTreeDisplace n b μ hc hu).comp (measurable_const.prodMk measurable_id))
    (measurable_noiseTreeForget A n) (noiseTreeDisplace_law n b μ hc hu hcpos hm s)
    (noiseCascadeLaw_forget A n b μ)
    (Real.measurable_log.comp (measurable_rawTreeTotal n).ennreal_toReal)
    (rawCascade_total_log_square n b hb)

lemma measurable_noiseTreeFactor (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {X : ℕ → S → ℝ} {u : ℕ → S × A → S}
    (hX : ∀ i, Measurable (X i)) (hu : ∀ i, Measurable (u i)) :
    Measurable (fun p : S × NoiseTree A n => noiseTreeFactor n b μ X u p.1 p.2) := by
  induction n generalizing b μ X u with
  | zero => exact (((hX 0).comp measurable_fst).exp).ennreal_ofReal
  | succ n ih =>
    unfold noiseTreeFactor
    apply measurable_sigmaPart_param _ measurable_snd
      (F := fun p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) =>
        ENNReal.ofReal (max p.2.1 0) *
          noiseTreeFactor n (fun j => b (j+1)) (fun j => μ (j+1))
            (fun j => X (j+1)) (fun j => u (j+1)) (u 0 (p.1.1,p.2.2.1)) p.2.2.2)
    exact (by fun_prop : Measurable (fun p : (S × NoiseTree A (n+1)) ×
      (ℝ × (A × NoiseTree A n)) => ENNReal.ofReal (max p.2.1 0))).mul
        ((ih _ _ (fun i => hX (i+1)) (fun i => hu (i+1))).comp
          (((hu 0).comp (by fun_prop)).prodMk (by fun_prop)))

theorem noiseTreeDisplace_total (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {X : ℕ → S → ℝ} {u : ℕ → S × A → S} {c : ℕ → S × A → ℝ}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (htel : ∀ i s a, c i (s,a) = Real.exp (X (i+1) (u i (s,a))-X i s))
    (s : S) (ν : NoiseTree A n) :
    rawTreeTotal n (noiseTreeDisplace n b μ c u s ν) =
      ENNReal.ofReal (Real.exp (-X 0 s)) * noiseTreeFactor n b μ X u s ν := by
  induction n generalizing b μ X u c s with
  | zero =>
    simp only [rawTreeTotal, noiseTreeFactor]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel,
      Real.exp_zero, ENNReal.ofReal_one]
  | succ n ih =>
    let I := (powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
      (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1)) : Measure (NoiseTree A n)))
    let T : ℝ × (A × NoiseTree A n) → ℝ × RawTree n := fun p =>
      (c 0 (s,p.2.1)*p.1,
        noiseTreeDisplace n (fun j => b (j+1)) (fun j => μ (j+1))
          (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (s,p.2.1)) p.2.2)
    have hT : Measurable T :=
      (((hc 0).comp (measurable_const.prodMk (by fun_prop))).mul measurable_fst).prodMk
        ((measurable_noiseTreeDisplace n _ _ (fun i => hc (i+1)) (fun i => hu (i+1))).comp
          (((hu 0).comp (measurable_const.prodMk (by fun_prop))).prodMk (by fun_prop)))
    change (∫⁻ p, ENNReal.ofReal (max p.1 0)*rawTreeTotal n p.2 ∂(sigmaPart I ν).map T) = _
    rw [lintegral_map]
    · change (∫⁻ p, ENNReal.ofReal (max (c 0 (s,p.2.1)*p.1) 0) *
          rawTreeTotal n (T p).2 ∂sigmaPart I ν) = _
      have he (p : ℝ × (A × NoiseTree A n)) :
          ENNReal.ofReal (max (c 0 (s,p.2.1)*p.1) 0) * rawTreeTotal n (T p).2 =
          ENNReal.ofReal (Real.exp (-X 0 s)) * (ENNReal.ofReal (max p.1 0) *
            noiseTreeFactor n (fun j => b (j+1)) (fun j => μ (j+1))
              (fun j => X (j+1)) (fun j => u (j+1)) (u 0 (s,p.2.1)) p.2.2) := by
        dsimp only [T]
        rw [ih _ _ (X := fun j => X (j+1)) (fun i => hc (i+1)) (fun i => hu (i+1)) (fun i => htel (i+1)),
          htel 0 s p.2.1]
        have hh (y x : ℝ) : max (Real.exp y*x) 0 = Real.exp y * max x 0 := by
          rw [mul_max_of_nonneg _ _ (Real.exp_pos _).le, mul_zero]
        rw [hh, ENNReal.ofReal_mul (Real.exp_pos _).le]
        have hex (y z : ℝ) : ENNReal.ofReal (Real.exp (y-z)) * ENNReal.ofReal (Real.exp (-y)) =
            ENNReal.ofReal (Real.exp (-z)) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          congr 2
          ring
        calc
          _ = (ENNReal.ofReal (Real.exp (X 1 (u 0 (s,p.2.1))-X 0 s)) *
              ENNReal.ofReal (Real.exp (-X 1 (u 0 (s,p.2.1))))) *
              (ENNReal.ofReal (max p.1 0) *
                noiseTreeFactor n (fun j => b (j+1)) (fun j => μ (j+1))
                  (fun j => X (j+1)) (fun j => u (j+1)) (u 0 (s,p.2.1)) p.2.2) := by ring
          _ = _ := by rw [hex]
      simp_rw [he]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl
    · exact (by fun_prop : Measurable (fun p : ℝ × RawTree n => ENNReal.ofReal (max p.1 0))).mul
        ((measurable_rawTreeTotal n).comp measurable_snd)
    · exact hT

lemma noiseTreeFactor_total_identity (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {X : ℕ → S → ℝ} {u : ℕ → S × A → S} {c : ℕ → S × A → ℝ}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (htel : ∀ i s a, c i (s,a) = Real.exp (X (i+1) (u i (s,a))-X i s))
    (s : S) (ν : NoiseTree A n) :
    noiseTreeFactor n b μ X u s ν = ENNReal.ofReal (Real.exp (X 0 s)) *
      rawTreeTotal n (noiseTreeDisplace n b μ c u s ν) := by
  rw [noiseTreeDisplace_total n b μ hc hu htel s ν, ← mul_assoc,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
    add_neg_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]

theorem noiseCascade_log_integral (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A)
    {X : ℕ → S → ℝ} {u : ℕ → S × A → S} {c : ℕ → S × A → ℝ}
    (hc : ∀ i, Measurable (c i))
    (hu : ∀ i, Measurable (u i))
    (htel : ∀ i s a, c i (s,a) = Real.exp (X (i+1) (u i (s,a))-X i s))
    (hm : ∀ i s, (∫⁻ a, ENNReal.ofReal (c i (s,a) ^ b i) ∂(μ i : Measure A)) = 1)
    (s : S) :
    let P := (noiseCascadeLaw A n b μ : Measure (NoiseTree A n))
    let L := fun ν : NoiseTree A n => Real.log
      ((noiseTreeFactor n b μ X u s ν).toReal / (noiseTreeTotal A n ν).toReal)
    (∀ᵐ ν ∂P, 0 < noiseTreeFactor n b μ X u s ν ∧ noiseTreeFactor n b μ X u s ν < ∞) ∧
    Integrable L P ∧ (∫ ν, L ν ∂P) = X 0 s ∧
    Integrable (fun ν => (L ν-X 0 s)^2) P ∧
    (∫ ν, (L ν-X 0 s)^2 ∂P) ≤
      4 * ∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n)) := by
  dsimp only
  let P := (noiseCascadeLaw A n b μ : Measure (NoiseTree A n))
  let L := fun ν : NoiseTree A n => Real.log
      ((noiseTreeFactor n b μ X u s ν).toReal / (noiseTreeTotal A n ν).toReal)
  let D := fun ν : NoiseTree A n => Real.log
      (rawTreeTotal n (noiseTreeDisplace n b μ c u s ν)).toReal -
        Real.log (noiseTreeTotal A n ν).toReal
  have hcpos : ∀ i s a, 0 < c i (s,a) := by intro i s a; rw [htel]; exact Real.exp_pos _
  have hT : Measurable (noiseTreeDisplace n b μ c u s) :=
    (measurable_noiseTreeDisplace n b μ hc hu).comp (measurable_const.prodMk measurable_id)
  have hgood : ∀ᵐ ν ∂P, 0 < rawTreeTotal n (noiseTreeDisplace n b μ c u s ν) ∧
      rawTreeTotal n (noiseTreeDisplace n b μ c u s ν) < ∞ := by
    apply ae_of_ae_map (μ := P) (p := fun T : RawTree n =>
      0 < rawTreeTotal n T ∧ rawTreeTotal n T < ∞) hT.aemeasurable
    rw [show P.map (noiseTreeDisplace n b μ c u s) = (rawCascadeLaw n b : Measure (RawTree n)) from
      noiseTreeDisplace_law n b μ hc hu hcpos hm s]
    exact (rawCascade_total_moments n b hb).1
  have hden : ∀ᵐ ν ∂P, 0 < noiseTreeTotal A n ν ∧ noiseTreeTotal A n ν < ∞ := by
    apply ae_of_ae_map (μ := P) (p := fun T : RawTree n =>
      0 < rawTreeTotal n T ∧ rawTreeTotal n T < ∞) (measurable_noiseTreeForget A n).aemeasurable
    rw [show P.map (noiseTreeForget A n) = (rawCascadeLaw n b : Measure (RawTree n)) from
      noiseCascadeLaw_forget A n b μ]
    exact (rawCascade_total_moments n b hb).1
  have he : L =ᵐ[P] fun ν => X 0 s + D ν := by
    filter_upwards [hgood, hden] with ν hν hνd
    have htpos := ENNReal.toReal_pos hν.1.ne' hν.2.ne
    have hdpos := ENNReal.toReal_pos hνd.1.ne' hνd.2.ne
    dsimp only [L, D]
    rw [noiseTreeFactor_total_identity n b μ hc hu htel s ν, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_pos _).le,
      Real.log_div (mul_pos (Real.exp_pos _) htpos).ne' hdpos.ne',
      Real.log_mul (Real.exp_ne_zero _) htpos.ne', Real.log_exp]
    ring
  have h := noiseTreeDisplace_log_ratio n b hb μ hc hu hcpos hm s
  change Integrable D P ∧ (∫ ν, D ν ∂P) = 0 ∧ Integrable (fun ν => (D ν)^2) P ∧ _ at h
  have hi : Integrable L P := ((integrable_const (X 0 s)).add h.1).congr he.symm
  have hec : (fun ν => L ν-X 0 s) =ᵐ[P] D := by
    filter_upwards [he] with ν hν
    rw [hν]
    ring
  have he2 : (fun ν => (L ν-X 0 s)^2) =ᵐ[P] fun ν => (D ν)^2 :=
    hec.fun_comp (fun x : ℝ => x^2)
  refine ⟨?_, hi, ?_, h.2.2.1.congr he2.symm, ?_⟩
  · filter_upwards [hgood] with ν hν
    rw [noiseTreeFactor_total_identity n b μ hc hu htel s ν]
    exact ⟨ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' hν.1.ne',
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hν.2⟩
  · rw [integral_congr_ae he, integral_add (integrable_const _) h.1, integral_const, h.2.1]
    simp [P]
  · rw [integral_congr_ae he2]
    exact h.2.2.2

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_NoiseTreeKeep
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.markedReplicaLaw_probability _root_.OAI.IsingPerceptron.noiseTiltedLeafLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Noise Tree Keep. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma measurable_measure_ae {E : Type*} [MeasurableSpace E] {p : E → Prop}
    (hp : MeasurableSet {x | p x}) : MeasurableSet {ν : Measure E | ∀ᵐ x ∂ν, p x} := by
  simp only [ae_iff]
  exact measurableSet_eq_fun (Measure.measurable_coe hp.compl) measurable_const

lemma normalizeMass_map {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Nonempty E] [Nonempty F] (ν : Measure E) {f : E → F} (hf : Measurable f)
    (hν : 0 < ν univ ∧ ν univ < ∞) :
    (normalizeMass ν).map f = normalizeMass (ν.map f) := by
  have ht : ν.map f univ = ν univ := by rw [Measure.map_apply hf MeasurableSet.univ]; rfl
  rw [normalizeMass, ite_eq_left hν, normalizeMass, ht, ite_eq_left hν,
    Measure.map_smul]

variable (A : Type) [MeasurableSpace A] [Nonempty A]

omit [Nonempty A] in
lemma measurableSet_GoodNoiseTree (n : ℕ) : MeasurableSet {ν | GoodNoiseTree A n ν} := by
  induction n with
  | zero => exact MeasurableSet.univ
  | succ n ih =>
    exact ((measurableSet_lt measurable_const (measurable_noiseTreeTotal A (n+1))).inter
      (measurableSet_lt (measurable_noiseTreeTotal A (n+1)) measurable_const)).inter
        (measurable_measure_ae (ih.preimage (measurable_snd.comp measurable_snd)))

lemma noiseCascade_good (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A) :
    ∀ᵐ ν ∂(noiseCascadeLaw A n b μ : Measure (NoiseTree A n)), GoodNoiseTree A n ν := by
  induction n generalizing b μ with
  | zero => exact ae_of_all _ (fun _ => trivial)
  | succ n ih =>
    have htot : ∀ᵐ ν ∂(noiseCascadeLaw A (n+1) b μ : Measure (NoiseTree A (n+1))),
        0 < noiseTreeTotal A (n+1) ν ∧ noiseTreeTotal A (n+1) ν < ∞ := by
      apply ae_of_ae_map (μ := (noiseCascadeLaw A (n+1) b μ : Measure (NoiseTree A (n+1))))
        (p := fun T : RawTree (n+1) => 0 < rawTreeTotal (n+1) T ∧ rawTreeTotal (n+1) T < ∞)
        (measurable_noiseTreeForget A (n+1)).aemeasurable
      rw [noiseCascadeLaw_forget]
      exact (rawCascade_total_moments (n+1) b hb).1
    have hm : MeasurableSet {p : ℝ × (A × NoiseTree A n) | GoodNoiseTree A n p.2.2} :=
      (measurableSet_GoodNoiseTree A n).preimage (by fun_prop)
    have hdesc : ∀ᵐ p ∂(powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
        (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1)))), GoodNoiseTree A n p.2.2 := by
      apply (Measure.ae_prod_iff_ae_ae hm).mpr
      apply ae_of_all
      intro _
      apply (Measure.ae_prod_iff_ae_ae ((measurableSet_GoodNoiseTree A n).preimage measurable_snd)).mpr
      exact ae_of_all _ (fun _ => ih (fun j => b (j+1)) hb.tail (fun j => μ (j+1)))
    have hc := poissonLaw_ae_intensity _ hm hdesc
    filter_upwards [htot, hc] with ν ht hd
    exact ⟨ht, hd⟩

omit [Nonempty A] in
lemma noiseChildMass_univ (n : ℕ) (ν : NoiseTree A (n+1)) :
    noiseChildMass A n ν univ = noiseTreeTotal A (n+1) ν := by
  rw [noiseTreeTotal_succ]
  simp [noiseChildMass, withDensity_apply]

end IsingPerceptron

namespace IsingPerceptron
open scoped ProbabilityTheory
variable (A : Type) [MeasurableSpace A] [Nonempty A]

lemma noiseLeafKernel_succ (n : ℕ) : noiseLeafKernel A (n+1) =
    ((Kernel.id : Kernel ℝ ℝ) ∥ₖ ((Kernel.id : Kernel A A) ∥ₖ noiseLeafKernel A n)) ∘ₖ
      noiseChildKernel A n := rfl

lemma noiseLeafKernel_step (n : ℕ) (ν : NoiseTree A (n+1))
    {F : NoiseLeaf A (n+1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ v, F v ∂noiseLeafKernel A (n+1) ν) =
      ∫⁻ p, ∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2 ∂noiseChildKernel A n ν := by
  rw [noiseLeafKernel_succ, Kernel.lintegral_comp _ _ _ hF]
  apply lintegral_congr
  intro p
  rw [Kernel.parallelComp_apply, Kernel.id_apply, lintegral_prod _ hF.aemeasurable,
    lintegral_dirac']
  swap
  · exact hF.lintegral_prod_right'
  rw [Kernel.parallelComp_apply, Kernel.id_apply,
    lintegral_prod _ (show AEMeasurable (fun y : A × NoiseLeaf A n => F (p.1,y)) _ from
      (hF.comp measurable_prodMk_left).aemeasurable),
    lintegral_dirac']
  exact (hF.comp measurable_prodMk_left).lintegral_prod_right'

end IsingPerceptron

namespace IsingPerceptron
open scoped ProbabilityTheory
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

omit [Nonempty A] in
lemma measurable_noiseLeafTerminal (n : ℕ) {X : ℕ → S → ℝ} {u : ℕ → S × A → S}
    (hX : ∀ i, Measurable (X i)) (hu : ∀ i, Measurable (u i)) :
    Measurable (fun p : S × NoiseLeaf A n => noiseLeafTerminal n X u p.1 p.2) := by
  induction n generalizing X u with
  | zero => exact (hX 0).comp measurable_fst
  | succ n ih =>
    exact (ih (fun i => hX (i+1)) (fun i => hu (i+1))).comp
      (((hu 0).comp (by fun_prop)).prodMk (by fun_prop))

lemma noiseChildKernel_lintegral (n : ℕ) (ν : NoiseTree A (n+1))
    (hν : 0 < noiseTreeTotal A (n+1) ν ∧ noiseTreeTotal A (n+1) ν < ∞)
    {F : ℝ × (A × NoiseTree A n) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p, F p ∂noiseChildKernel A n ν) = (noiseTreeTotal A (n+1) ν)⁻¹ *
      ∫⁻ p, ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 * F p ∂ν := by
  change (∫⁻ p, F p ∂normalizeMass (noiseChildMass A n ν)) = _
  rw [normalizeMass, ite_eq_left (by simpa only [noiseChildMass_univ] using hν),
    lintegral_smul_measure, smul_eq_mul, noiseChildMass_univ, noiseChildMass]
  congr 1
  exact lintegral_withDensity_eq_lintegral_mul ν
    (show Measurable (fun p : ℝ × (A × NoiseTree A n) =>
      ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2) from
      ((by fun_prop : Measurable (fun p : ℝ × (A × NoiseTree A n) =>
        ENNReal.ofReal (max p.1 0))).mul ((measurable_noiseTreeTotal A n).comp (by fun_prop)))) hF

lemma noiseLeafKernel_lintegral (n : ℕ) (ν : NoiseTree A (n+1))
    (hν : 0 < noiseTreeTotal A (n+1) ν ∧ noiseTreeTotal A (n+1) ν < ∞)
    {F : NoiseLeaf A (n+1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ v, F v ∂noiseLeafKernel A (n+1) ν) = (noiseTreeTotal A (n+1) ν)⁻¹ *
      ∫⁻ p, ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 *
        (∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2) ∂ν := by
  rw [noiseLeafKernel_step A n ν hF]
  apply noiseChildKernel_lintegral n ν hν
  exact (hF.comp (by fun_prop : Measurable (fun p :
      (ℝ × (A × NoiseTree A n)) × NoiseLeaf A n => (p.1.1,(p.1.2.1,p.2))))).lintegral_kernel_prod_right'
    (κ := (noiseLeafKernel A n).comap (fun p : ℝ × (A × NoiseTree A n) => p.2.2) (by fun_prop))

lemma measurable_noiseLeafIntegral (n : ℕ) {X : ℕ → S → ℝ} {u : ℕ → S × A → S}
    (hX : ∀ i, Measurable (X i)) (hu : ∀ i, Measurable (u i)) :
    Measurable (fun p : S × NoiseTree A n => ∫⁻ v,
      ENNReal.ofReal (Real.exp (noiseLeafTerminal n X u p.1 v)) ∂noiseLeafKernel A n p.2) :=
  (((measurable_noiseLeafTerminal n hX hu).comp (by fun_prop : Measurable
    (fun p : (S × NoiseTree A n) × NoiseLeaf A n => (p.1.1,p.2)))).exp.ennreal_ofReal).lintegral_kernel_prod_right'
      (κ := (noiseLeafKernel A n).comap Prod.snd measurable_snd)

theorem noiseTreeFactor_leafIntegral (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A) {X : ℕ → S → ℝ} {u : ℕ → S × A → S}
    (hX : ∀ i, Measurable (X i)) (hu : ∀ i, Measurable (u i)) (s : S) :
    ∀ᵐ ν ∂(noiseCascadeLaw A n b μ : Measure (NoiseTree A n)),
      noiseTreeFactor n b μ X u s ν = noiseTreeTotal A n ν *
        ∫⁻ v, ENNReal.ofReal (Real.exp (noiseLeafTerminal n X u s v)) ∂noiseLeafKernel A n ν := by
  induction n generalizing b μ X u s with
  | zero =>
    apply ae_of_all
    intro ν
    simp [noiseTreeFactor, noiseTreeTotal, rawTreeTotal, noiseLeafTerminal,
      noiseLeafKernel, noiseLeafKernelData, Kernel.const_apply]
  | succ n ih =>
    let bt := fun j => b (j+1)
    let μt := fun j => μ (j+1)
    let Xt := fun j => X (j+1)
    let ut := fun j => u (j+1)
    let P := (noiseCascadeLaw A n bt μt : Measure (NoiseTree A n))
    let I := (powerIntensity (b 0)).prod ((μ 0 : Measure A).prod P)
    let E := fun p : ℝ × (A × NoiseTree A n) =>
      noiseTreeFactor n bt μt Xt ut (u 0 (s,p.2.1)) p.2.2 = noiseTreeTotal A n p.2.2 *
      ∫⁻ v, ENNReal.ofReal (Real.exp (noiseLeafTerminal n Xt ut (u 0 (s,p.2.1)) v))
        ∂noiseLeafKernel A n p.2.2
    have hme : MeasurableSet {p | E p} := by
      apply measurableSet_eq_fun
      · exact (measurable_noiseTreeFactor n bt μt (fun i => hX (i+1))
          (fun i => hu (i+1))).comp (((hu 0).comp (measurable_const.prodMk (by fun_prop))).prodMk (by fun_prop))
      · exact ((measurable_noiseTreeTotal A n).comp (by fun_prop)).mul
          ((measurable_noiseLeafIntegral n (fun i => hX (i+1)) (fun i => hu (i+1))).comp
            (((hu 0).comp (measurable_const.prodMk (by fun_prop))).prodMk (by fun_prop)))
    have he : ∀ᵐ p ∂I, E p := by
      apply (Measure.ae_prod_iff_ae_ae hme).mpr
      apply ae_of_all
      intro x
      apply (Measure.ae_prod_iff_ae_ae (hme.preimage (measurable_const.prodMk measurable_id))).mpr
      apply ae_of_all
      intro a
      exact ih bt hb.tail μt (fun i => hX (i+1)) (fun i => hu (i+1)) (u 0 (s,a))
    have ha := poissonLaw_ae_intensity I hme he
    have hg := noiseCascade_good A n.succ b hb μ
    have hσ := sigmaPart_eq_ae I
    filter_upwards [ha,hg,hσ] with ν hν hg hσ
    rw [noiseTreeFactor]
    change (∫⁻ p, ENNReal.ofReal (max p.1 0) *
      noiseTreeFactor n bt μt Xt ut (u 0 (s,p.2.1)) p.2.2 ∂sigmaPart I ν) = _
    rw [hσ, noiseLeafKernel_lintegral n ν hg.1
      (F := fun v => ENNReal.ofReal (Real.exp (noiseLeafTerminal (n+1) X u s v)))
      (((measurable_noiseLeafTerminal (n+1) hX hu).comp
        (measurable_const.prodMk measurable_id)).exp.ennreal_ofReal)]
    rw [← mul_assoc, ENNReal.mul_inv_cancel hg.1.1.ne' hg.1.2.ne, one_mul]
    apply lintegral_congr_ae
    filter_upwards [hν] with p hp
    rw [hp]
    exact (mul_assoc _ _ _).symm

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_NoiseGibbsRegular
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.markedReplicaLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Noise Gibbs Regular. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

lemma noiseLeafKernel_unnormalized_lintegral (n : ℕ) (ν : NoiseTree A (n+1))
    (hν : 0 < noiseTreeTotal A (n+1) ν ∧ noiseTreeTotal A (n+1) ν < ∞)
    {F : NoiseLeaf A (n+1) → ℝ≥0∞} (hF : Measurable F) :
    noiseTreeTotal A (n+1) ν * (∫⁻ v, F v ∂noiseLeafKernel A (n+1) ν) =
      ∫⁻ p, ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 *
        (∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2) ∂ν := by
  rw [noiseLeafKernel_lintegral n ν hν hF, ← mul_assoc,
    ENNReal.mul_inv_cancel hν.1.ne' hν.2.ne, one_mul]

end IsingPerceptron

namespace IsingPerceptron

lemma normalizeMass_of_probability {E : Type*} [MeasurableSpace E] [Nonempty E]
    (ν : Measure E) [IsProbabilityMeasure ν] : normalizeMass ν = ν := by
  simp [normalizeMass, measure_univ]

lemma normalizeMass_smul {E : Type*} [MeasurableSpace E] [Nonempty E]
    (ν : Measure E) {c : ℝ≥0∞} (hc : 0 < c ∧ c < ∞)
    (hν : 0 < ν univ ∧ ν univ < ∞) : normalizeMass (c • ν) = normalizeMass ν := by
  have ht : 0 < (c • ν) univ ∧ (c • ν) univ < ∞ := by
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ⟨ENNReal.mul_pos hc.1.ne' hν.1.ne', ENNReal.mul_lt_top hc.2 hν.2⟩
  rw [normalizeMass, ite_eq_left ht, normalizeMass, ite_eq_left hν,
    Measure.smul_apply, smul_eq_mul, smul_smul,
    ENNReal.mul_inv (Or.inl hc.1.ne') (Or.inl hc.2.ne)]
  congr 1
  calc
    c⁻¹ * (ν univ)⁻¹ * c = (c⁻¹*c)*(ν univ)⁻¹ := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hc.1.ne' hc.2.ne, one_mul]

end IsingPerceptron

namespace IsingPerceptron

lemma infinitePi_prod_join {ι E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : ι → Measure E) (ν : ι → Measure F)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
      (fun p i => (p.1 i,p.2 i)) = Measure.infinitePi (fun i => (μ i).prod (ν i)) := by
  refine (Measure.isProjectiveLimit_infinitePi (fun i => (μ i).prod (ν i))).unique ?_ |>.symm
  intro I
  have hμ : MeasurePreserving I.restrict (Measure.infinitePi μ) (Measure.pi (fun i : I => μ i)) :=
    ⟨I.measurable_restrict,Measure.infinitePi_map_restrict μ⟩
  have hν : MeasurePreserving I.restrict (Measure.infinitePi ν) (Measure.pi (fun i : I => ν i)) :=
    ⟨I.measurable_restrict,Measure.infinitePi_map_restrict ν⟩
  have hp := hμ.prod hν
  have hs := (measurePreserving_arrowProdEquivProdArrow E F I (fun i => μ i) (fun i => ν i)).symm
  rw [Measure.map_map I.measurable_restrict (by fun_prop)]
  exact (hs.comp hp).map_eq

lemma finitePoissonProduct_laplace_partial {E : Type*} [MeasurableSpace E] [Nonempty E]
    (μ : ℕ → FiniteMeasure E) {ψ : E → ℝ}
    (hψ : Measurable ψ) (hpos : ∀ x, 0 ≤ ψ x) (n : ℕ) :
    (∫ ω, negExp (∑ i : Fin n, ∫⁻ x, ENNReal.ofReal (ψ x) ∂ω i)
      ∂Measure.infinitePi (fun i => finitePoissonLaw (μ i))) =
      negExp (∑ i : Fin n, ∫⁻ x, ENNReal.ofReal (1-Real.exp (-ψ x)) ∂(μ i : Measure E)) := by
  let a : Measure E → ℝ≥0∞ := fun ν => ∫⁻ x, ENNReal.ofReal (ψ x) ∂ν
  let c : E → ℝ≥0∞ := fun x => ENNReal.ofReal (1-Real.exp (-ψ x))
  have ha : Measurable a := Measure.measurable_lintegral hψ.ennreal_ofReal
  have heval : Measurable (fun ν => negExp (a ν)) := continuous_negExp.measurable.comp ha
  have hind := iIndepFun_infinitePi (P := fun i => finitePoissonLaw (μ i)) (fun _ => heval)
  have hh := (hind.precomp Fin.val_injective).integral_fun_prod_eq_prod_integral
    (fun i : Fin n => (heval.comp (measurable_pi_apply (i : ℕ))).aestronglyMeasurable)
  have hei (i : ℕ) :
      (∫ ω, negExp (a (ω i)) ∂Measure.infinitePi (fun j => finitePoissonLaw (μ j))) =
        negExp (∫⁻ x, c x ∂(μ i : Measure E)) := by
    calc
      _ = ∫ ν, negExp (a ν) ∂finitePoissonLaw (μ i) :=
        (measurePreserving_eval_infinitePi (fun j => finitePoissonLaw (μ j)) i).hasLaw.integral_comp
          heval.aestronglyMeasurable
      _ = _ := finitePoissonLaw_laplace (μ i) hψ hpos
  simpa only [negExp_sum, hei] using hh

theorem finitePoissonProduct_sum_law {E : Type*} [MeasurableSpace E] [Nonempty E]
    (μ : ℕ → FiniteMeasure E) :
    (Measure.infinitePi (fun n => finitePoissonLaw (μ n))).map Measure.sum =
      poissonLaw (Measure.sum (fun n => (μ n : Measure E))) := by
  apply randomMeasure_laplace_unique
  intro ψ hψ hpos
  let P := Measure.infinitePi (fun n => finitePoissonLaw (μ n))
  let a : Measure E → ℝ≥0∞ := fun ν => ∫⁻ x, ENNReal.ofReal (ψ x) ∂ν
  let c : E → ℝ≥0∞ := fun x => ENNReal.ofReal (1-Real.exp (-ψ x))
  have ha : Measurable a := Measure.measurable_lintegral hψ.ennreal_ofReal
  have heval : Measurable (fun ν => negExp (a ν)) := continuous_negExp.measurable.comp ha
  have hlim := laplace_partial_tendsto P ha
  have hr : Tendsto (fun n => negExp (∑ i : Fin n, ∫⁻ x, c x ∂(μ i : Measure E)))
      atTop (𝓝 (negExp (∫⁻ x, c x ∂Measure.sum (fun n => (μ n : Measure E))))) := by
    rw [lintegral_sum_measure]
    simp_rw [Fin.sum_univ_eq_sum_range (fun i => ∫⁻ x, c x ∂(μ i : Measure E))]
    exact continuous_negExp.continuousAt.tendsto.comp (ENNReal.tendsto_nat_tsum _)
  rw [poissonLaw_laplace _ hψ hpos,
    integral_map measurable_measureSum.aemeasurable heval.aestronglyMeasurable]
  change (∫ ω, negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂Measure.sum ω) ∂P) = _
  simp_rw [lintegral_sum_measure]
  exact tendsto_nhds_unique (by
    simpa only [a,P,finitePoissonProduct_laplace_partial μ hψ hpos] using hlim) (by simpa only [lintegral_sum_measure] using hr)

lemma finiteCloud_laplace {E : Type*} [MeasurableSpace E] (r : ℝ≥0)
    (ρ : Measure E) [IsProbabilityMeasure ρ] {ψ : E → ℝ}
    (hψ : Measurable ψ) (hpos : ∀ x, 0 ≤ ψ x) :
    (∫ p, negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂finiteCloudMeasure p) ∂finitePoissonCloud r ρ) =
      negExp ((r : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (1-Real.exp (-ψ x)) ∂ρ) := by
  have hcost : ∀ x, 0 ≤ 1-Real.exp (-ψ x) := fun x =>
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hpos x)))
  have hi : Integrable (fun x => Real.exp (-ψ x)) ρ := by
    apply Integrable.of_bound hψ.neg.exp.aestronglyMeasurable 1
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hpos x))
  have hicost : Integrable (fun x => 1-Real.exp (-ψ x)) ρ := (integrable_const 1).sub hi
  have hs (p : ℕ × (ℕ → E)) :
      negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂finiteCloudMeasure p) =
        Real.exp (-cloudSum ψ p) := by
    rw [finiteCloudMeasure_lintegral p hψ.ennreal_ofReal,
      ← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
        (fun (i : Fin p.1) _ => hpos (p.2 i)), negExp_ofReal]
    · rfl
    · exact Finset.sum_nonneg (fun i _ => hpos (p.2 i))
  simp_rw [hs]
  rw [finitePoissonCloud_laplace r ρ hψ hpos,
    ← ofReal_integral_eq_lintegral_ofReal hicost (ae_of_all _ hcost),
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul r.coe_nonneg,
    negExp_ofReal (mul_nonneg r.coe_nonneg (integral_nonneg hcost)),
    integral_sub (integrable_const 1) hi, integral_const]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  congr 1
  ring

lemma finiteCloud_mark_law {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (r : ℝ≥0) (μ : Measure E) (ν : Measure F)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ((finitePoissonCloud r μ).prod (Measure.infinitePi (fun _ : ℕ => ν))).map
      (fun p => (p.1.1,fun i => (p.1.2 i,p.2 i))) = finitePoissonCloud r (μ.prod ν) := by
  have hj : MeasurePreserving (fun p : (ℕ → E) × (ℕ → F) => fun i => (p.1 i,p.2 i))
      ((Measure.infinitePi (fun _ : ℕ => μ)).prod (Measure.infinitePi (fun _ : ℕ => ν)))
      (Measure.infinitePi (fun _ : ℕ => μ.prod ν)) :=
    ⟨by fun_prop,infinitePi_prod_join _ _⟩
  have hp := (MeasurePreserving.id (poissonMeasure r)).prod hj
  have ha := measurePreserving_prodAssoc (poissonMeasure r)
    (Measure.infinitePi (fun _ : ℕ => μ)) (Measure.infinitePi (fun _ : ℕ => ν))
  exact (hp.comp ha).map_eq

lemma finiteCloud_mark_measure_law {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Nonempty E] [Nonempty F] (μ : FiniteMeasure E) (ν : Measure F) [IsProbabilityMeasure ν] :
    ((finitePoissonCloud μ.mass (μ.normalize : Measure E)).prod
      (Measure.infinitePi (fun _ : ℕ => ν))).map
      (fun p => finiteCloudMeasure (p.1.1,fun i => (p.1.2 i,p.2 i))) =
      finitePoissonLaw ⟨(μ : Measure E).prod ν,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ := by
  let ξ : FiniteMeasure (E × F) := ⟨(μ : Measure E).prod ν,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  change _ = finitePoissonLaw ξ
  rw [show (fun p : (ℕ × (ℕ → E)) × (ℕ → F) =>
    finiteCloudMeasure (p.1.1,fun i => (p.1.2 i,p.2 i))) =
    finiteCloudMeasure ∘ (fun p => (p.1.1,fun i => (p.1.2 i,p.2 i))) from rfl,
    ← Measure.map_map measurable_finiteCloudMeasure (by fun_prop),finiteCloud_mark_law]
  apply randomMeasure_laplace_unique
  intro ψ hψ hpos
  have hm : Measurable (fun π : Measure (E × F) => negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂π)) :=
    continuous_negExp.measurable.comp (Measure.measurable_lintegral hψ.ennreal_ofReal)
  rw [integral_map measurable_finiteCloudMeasure.aemeasurable hm.aestronglyMeasurable,
    finiteCloud_laplace _ _ hψ hpos,finitePoissonLaw_laplace ξ hψ hpos]
  change _ = negExp (∫⁻ x, ENNReal.ofReal (1-Real.exp (-ψ x)) ∂(μ : Measure E).prod ν)
  rw [finiteMeasure_mass_normalize μ,Measure.prod_smul_left,lintegral_smul_measure]
  rfl

lemma measurable_labeledMarkedMeasure {E F : Type*} [MeasurableSpace E] [MeasurableSpace F] :
    Measurable (labeledMarkedMeasure (E := E) (F := F)) := by
  apply measurable_measureSum.comp
  apply Measurable.of_eval
  intro n
  apply measurable_finiteCloudMeasure.comp
  fun_prop

theorem labeledMarkedMeasure_law {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Nonempty E] [Nonempty F] (μ : ℕ → FiniteMeasure E)
    (ν : Measure F) [IsProbabilityMeasure ν] :
    ((labeledPoissonLaw μ).prod (Measure.infinitePi (fun _ : ℕ =>
      Measure.infinitePi (fun _ : ℕ => ν)))).map labeledMarkedMeasure =
    poissonLaw ((Measure.sum (fun n => (μ n : Measure E))).prod ν) := by
  let f : (ℕ × (ℕ → E)) × (ℕ → F) → Measure (E × F) :=
    fun p => finiteCloudMeasure (p.1.1,fun i => (p.1.2 i,p.2 i))
  have hf : Measurable f := measurable_finiteCloudMeasure.comp (by fun_prop)
  have hjoin : Measurable (fun p : (ℕ → ℕ × (ℕ → E)) × (ℕ → ℕ → F) => fun n => (p.1 n,p.2 n)) := by
    fun_prop
  have hfpi : Measurable (fun p : ℕ → (ℕ × (ℕ → E)) × (ℕ → F) => fun n => f (p n)) :=
    Measurable.of_eval (fun _ => hf.comp (measurable_pi_apply _))
  have hcomp : (labeledMarkedMeasure (E := E) (F := F)) =
    Measure.sum ∘ (fun p : ℕ → (ℕ × (ℕ → E)) × (ℕ → F) => fun n => f (p n)) ∘
      (fun p : (ℕ → ℕ × (ℕ → E)) × (ℕ → ℕ → F) => fun n => (p.1 n,p.2 n)) := rfl
  rw [hcomp,← Function.comp_assoc,← Measure.map_map (measurable_measureSum.comp hfpi) hjoin,
    labeledPoissonLaw,infinitePi_prod_join,
    ← Measure.map_map measurable_measureSum hfpi,Measure.infinitePi_map_pi _ (fun _ => hf)]
  simp only [f,finiteCloud_mark_measure_law]
  let η : ℕ → FiniteMeasure (E × F) := fun i => ⟨(μ i : Measure E).prod ν,(by first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply measurable_labeledMarkedMeasure <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  change (Measure.infinitePi (fun i => finitePoissonLaw (η i))).map Measure.sum = _
  rw [finitePoissonProduct_sum_law η]
  have hcongr {P Q : Measure (E × F)} [SFinite P] [SFinite Q] (h : P = Q) :
      poissonLaw P = poissonLaw Q := by subst Q; rfl
  apply hcongr
  exact (Measure.prod_sum_left _ _).symm

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ChildLabel
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.cascadeCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedCoordinateLaw_probability _root_.OAI.IsingPerceptron.enrichedCylinderBaseLaw_probability _root_.OAI.IsingPerceptron.enrichedCylinderLaw_probability _root_.OAI.IsingPerceptron.enrichedForestCoordinates_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledLeafEncodable _root_.OAI.IsingPerceptron.labeledSpinReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.markedReplicaLaw_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Child Label. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma intensityComponents_sum {E : Type*} [MeasurableSpace E] (μ : Measure E) [SFinite μ] :
    Measure.sum (fun n => (intensityComponents μ n : Measure E)) = μ :=
  sum_sfiniteSeq μ

lemma labeledLeafMass_lintegral (n : ℕ) (ω : LabeledTree n) (F : LabeledLeaf n → ℝ≥0∞) :
    (∫⁻ v, F v ∂labeledLeafMass n ω) = ∑' v, labeledLeafWeight n ω v * F v := by
  rw [labeledLeafMass,lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _) 
    (measurable_of_countable _),lintegral_count]
  rfl

lemma finiteCloud_tsum_weight (ω : WeightCloud) (F : ChildLabel → ℝ≥0∞) :
    (∑' a, childLabelWeight ω a * F a) =
      ∑' m, ∑ i : Fin (ω m).1, ENNReal.ofReal (max ((ω m).2 i) 0) * F (m,i) := by
  rw [ENNReal.tsum_prod']
  apply tsum_congr
  intro m
  simp only [childLabelWeight,ite_mul,zero_mul]
  rw [tsum_eq_sum (s := Finset.range (ω m).1)]
  · rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    simp only [i.isLt,ite_true, if_true]
  · intro i hi
    exact ite_eq_right (by simpa using hi)

variable (A : Type) [MeasurableSpace A]

@[fun_prop] lemma measurable_labeledNoiseJoin (n : ℕ) : Measurable (labeledNoiseJoin A n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun p : (WeightCloud × (ℕ → ℕ → LabeledTree n)) ×
        (ℕ → ℕ → A × MarkForest A n) => labeledMarkedMeasure (p.1.1,fun m i =>
          ((p.2 m i).1,labeledNoiseJoin A n (p.1.2 m i,(p.2 m i).2))))
    apply measurable_labeledMarkedMeasure.comp
    apply Measurable.prodMk (by fun_prop)
    apply Measurable.of_eval
    intro m
    apply Measurable.of_eval
    intro i
    exact (by fun_prop : Measurable (fun p : LabeledTree (n+1) × MarkForest A (n+1) =>
      (p.2 m i).1)).prodMk (ih.comp (by fun_prop))

lemma infinitePi_prod_join2 {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (ν : Measure F) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ((Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => μ))).prod
      (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => ν)))).map
      (fun p m i => (p.1 m i,p.2 m i)) =
      Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => μ.prod ν)) := by
  rw [show (fun p : (ℕ → ℕ → E) × (ℕ → ℕ → F) => fun m i => (p.1 m i,p.2 m i)) =
      (fun q : ℕ → (ℕ → E) × (ℕ → F) => fun m i => ((q m).1 i,(q m).2 i)) ∘
      (fun p : (ℕ → ℕ → E) × (ℕ → ℕ → F) => fun m => (p.1 m,p.2 m)) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop),infinitePi_prod_join,
    Measure.infinitePi_map_pi _ (f := fun (_ : ℕ) (q : (ℕ → E) × (ℕ → F)) => fun i => (q.1 i,q.2 i))
      (fun _ => by fun_prop)]
  simp_rw [infinitePi_prod_join]

lemma measurePreserving_swap_first_two {E F G : Type*}
    [MeasurableSpace E] [MeasurableSpace F] [MeasurableSpace G]
    (μ : Measure E) (ν : Measure F) (ξ : Measure G)
    [SFinite μ] [SFinite ν] [SFinite ξ] :
    MeasurePreserving (fun p : E × (F × G) => (p.2.1,(p.1,p.2.2)))
      (μ.prod (ν.prod ξ)) (ν.prod (μ.prod ξ)) := by
  exact (measurePreserving_prodAssoc ν μ ξ).comp
    (((Measure.measurePreserving_swap (μ := μ) (ν := ν)).prod (MeasurePreserving.id ξ)).comp
      (measurePreserving_prodAssoc μ ν ξ).symm)

theorem labeledNoiseJoin_law [Nonempty A] (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure A) :
    ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (markForestLaw A n μ)).map (labeledNoiseJoin A n) = noiseCascadeLaw A n b μ := by
  induction n generalizing b μ with
  | zero =>
    change ((Measure.dirac (PUnit.unit : PUnit)).prod (Measure.dirac (PUnit.unit : PUnit))).map
      (fun _ => PUnit.unit) = Measure.dirac PUnit.unit
    rw [Measure.map_const]
    simp
  | succ n ih =>
    let b' := fun j => b (j+1)
    let μ' := fun j => μ (j+1)
    let L : Measure (LabeledTree n) := labeledCascadeLaw n b'
    let M : Measure (MarkForest A n) := markForestLaw A n μ'
    let R : Measure (NoiseTree A n) := noiseCascadeLaw A n b' μ'
    let W := labeledPoissonLaw (intensityComponents (powerIntensity (b 0)))
    have hi : MeasurePreserving (labeledNoiseJoin A n) (L.prod M) R :=
      ⟨measurable_labeledNoiseJoin A n,ih b' μ'⟩
    have hp := ((MeasurePreserving.id (μ 0 : Measure A)).prod hi).comp
      (measurePreserving_swap_first_two L (μ 0 : Measure A) M)
    have hmap : (L.prod ((μ 0 : Measure A).prod M)).map
        (fun p => (p.2.1,labeledNoiseJoin A n (p.1,p.2.2))) = (μ 0 : Measure A).prod R := hp.map_eq
    have hpi : MeasurePreserving
        (fun p : (ℕ → ℕ → LabeledTree n) × (ℕ → ℕ → A × MarkForest A n) =>
          fun m i => ((p.2 m i).1,labeledNoiseJoin A n (p.1 m i,(p.2 m i).2)))
        ((Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => L))).prod
          (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (μ 0 : Measure A).prod M))))
        (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (μ 0 : Measure A).prod R))) := by
      refine ⟨Measurable.of_eval (fun m => Measurable.of_eval (fun i =>
        (by fun_prop : Measurable (fun p : (ℕ → ℕ → LabeledTree n) ×
            (ℕ → ℕ → A × MarkForest A n) => (p.2 m i).1)).prodMk
          ((measurable_labeledNoiseJoin A n).comp (by fun_prop)))),?_⟩
      rw [show (fun p : (ℕ → ℕ → LabeledTree n) × (ℕ → ℕ → A × MarkForest A n) =>
          fun m i => ((p.2 m i).1,labeledNoiseJoin A n (p.1 m i,(p.2 m i).2))) =
          (fun q : ℕ → ℕ → LabeledTree n × (A × MarkForest A n) => fun m i =>
            ((q m i).2.1,labeledNoiseJoin A n ((q m i).1,(q m i).2.2))) ∘
          (fun p => fun m i => (p.1 m i,p.2 m i)) from rfl,
        ← Measure.map_map (by fun_prop) (by fun_prop),infinitePi_prod_join2,
        Measure.infinitePi_map_pi _ (f := fun (_ : ℕ) (q : ℕ → LabeledTree n × (A × MarkForest A n)) => fun i =>
          ((q i).2.1,labeledNoiseJoin A n ((q i).1,(q i).2.2))) (fun _ => by fun_prop)]
      simp_rw [Measure.infinitePi_map_pi _ (f := fun (_ : ℕ) (p : LabeledTree n × (A × MarkForest A n)) =>
        (p.2.1,labeledNoiseJoin A n (p.1,p.2.2))) (fun _ => hp.measurable),hmap]
    have hfull := ((MeasurePreserving.id W).prod hpi).comp
      (measurePreserving_prodAssoc W _ _)
    change ((W.prod (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => L)))).prod
      (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (μ 0 : Measure A).prod M)))).map
      (labeledMarkedMeasure ∘ (fun p => (p.1.1,fun m i =>
        ((p.2 m i).1,labeledNoiseJoin A n (p.1.2 m i,(p.2 m i).2))))) = _
    have hfm : Measurable (fun p : (WeightCloud × (ℕ → ℕ → LabeledTree n)) ×
        (ℕ → ℕ → A × MarkForest A n) => (p.1.1,fun m i =>
          ((p.2 m i).1,labeledNoiseJoin A n (p.1.2 m i,(p.2 m i).2)))) := hfull.measurable
    rw [← Measure.map_map measurable_labeledMarkedMeasure hfm]
    have hfe : ((W.prod (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => L)))).prod
        (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (μ 0 : Measure A).prod M)))).map
        (fun p => (p.1.1,fun m i => ((p.2 m i).1,labeledNoiseJoin A n (p.1.2 m i,(p.2 m i).2)))) =
        W.prod (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (μ 0 : Measure A).prod R))) := hfull.map_eq
    rw [hfe,labeledMarkedMeasure_law,noiseCascadeLaw_succ]
    apply poissonLaw_congr
    rw [intensityComponents_sum]

end IsingPerceptron

namespace IsingPerceptron

lemma infinitePi_option_join {ι A : Type*} [MeasurableSpace A]
    (μ : Measure A) (ν : ι → Measure A) [IsProbabilityMeasure μ]
    [∀ i, IsProbabilityMeasure (ν i)] :
    (μ.prod (Measure.infinitePi ν)).map (fun p : A × (ι → A) => fun i : Option ι =>
      i.elim p.1 p.2) = Measure.infinitePi (fun i : Option ι => i.elim μ ν) := by
  classical
  let ρ : Option ι → Measure A := fun i => i.elim μ ν
  have : ∀ i, IsProbabilityMeasure (ρ i) := fun i => by cases i <;> dsimp [ρ] <;> infer_instance
  change _ = Measure.infinitePi ρ
  refine Measure.eq_infinitePi ρ (fun I t ht => ?_)
  have hm : Measurable (fun p : A × (ι → A) => fun i : Option ι => i.elim p.1 p.2) := by
    apply Measurable.of_eval
    intro i
    cases i <;> dsimp <;> fun_prop
  rw [Measure.map_apply hm (.pi I.countable_toSet (fun i _ => ht i))]
  have he : (fun p : A × (ι → A) => fun i : Option ι => i.elim p.1 p.2) ⁻¹'
      ((I : Set (Option ι)).pi t) =
      (if none ∈ I then t none else Set.univ) ×ˢ ((I.eraseNone : Set ι).pi (fun i => t (some i))) := by
    ext p
    simp only [Set.mem_preimage,Set.mem_pi,Set.mem_prod,Finset.mem_coe,Finset.mem_eraseNone]
    constructor
    · intro h
      constructor
      · split_ifs with hn
        · exact h none hn
        · trivial
      · intro i hi
        exact h (some i) hi
    · rintro ⟨ha,hb⟩ i hi
      cases i with
      | none => simpa only [ite_eq_left hi,Option.elim_none] using ha
      | some i => exact hb i hi
  rw [he,Measure.prod_prod,Measure.infinitePi_pi _ (fun i _ => ht (some i))]
  by_cases hn : none ∈ I
  · rw [ite_eq_left hn,← Finset.prod_erase_mul _ _ hn]
    have her : I.erase none = I.eraseNone.map (Function.Embedding.some) := by
      ext i
      cases i <;> simp
    rw [her,Finset.prod_map,mul_comm]
    rfl
  · rw [ite_eq_right hn,measure_univ,one_mul]
    have her : I = I.eraseNone.map (Function.Embedding.some) := by
      ext i
      cases i <;> simp [hn]
    rw [her,Finset.prod_map]
    simp only [Finset.eraseNone_map_some]
    rfl

lemma infinitePi_option_split {ι A : Type*} [MeasurableSpace A]
    (μ : Measure A) (ν : ι → Measure A) [IsProbabilityMeasure μ]
    [∀ i, IsProbabilityMeasure (ν i)] :
    (Measure.infinitePi (fun i : Option ι => i.elim μ ν)).map
      (fun g => (g none,fun i => g (some i))) = μ.prod (Measure.infinitePi ν) := by
  rw [← infinitePi_option_join μ ν,Measure.map_map (by fun_prop) (by
    apply Measurable.of_eval
    intro i
    cases i <;> dsimp <;> fun_prop)]
  change (μ.prod (Measure.infinitePi ν)).map id = _
  exact Measure.map_id

lemma infinitePi_triple_curry {I J K A : Type*} [MeasurableSpace A]
    (μ : I → J → K → Measure A) [∀ i j k, IsProbabilityMeasure (μ i j k)] :
    (Measure.infinitePi (fun p : I × (J × K) => μ p.1 p.2.1 p.2.2)).map
      (fun g i j k => g (i,j,k)) =
      Measure.infinitePi (fun i => Measure.infinitePi (fun j => Measure.infinitePi (μ i j))) := by
  rw [show (fun g : (I × (J × K)) → A => fun i j k => g (i,j,k)) =
      (fun q : I → (J × K → A) => fun i j k => q i (j,k)) ∘
      (MeasurableEquiv.curry I (J × K) A) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop),Measure.infinitePi_map_curry
      (fun (i : I) (p : J × K) => μ i p.1 p.2)]
  rw [Measure.infinitePi_map_pi _ (f := fun (_ : I) (q : J × K → A) => fun j k => q (j,k))
    (fun _ => by fun_prop)]
  simp only [show (fun q : J × K → A => fun j k => q (j,k)) =
    MeasurableEquiv.curry J K A from rfl,Measure.infinitePi_map_curry]

variable (A : Type) [MeasurableSpace A]

theorem markForestOfCoords_law (n : ℕ) (μ : ℕ → ProbabilityMeasure A) :
    (Measure.infinitePi (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure A))).map
      (markForestOfCoords A n) = markForestLaw A n μ := by
  induction n generalizing μ with
  | zero =>
    change (Measure.infinitePi _).map (fun _ => (PUnit.unit : PUnit)) = Measure.dirac PUnit.unit
    rw [Measure.map_const]
    simp
  | succ n ih =>
    let μ' := fun j => μ (j+1)
    let ν : ForestVertex n → Measure A := fun v => μ' (forestVertexDepth n v)
    have (i : Option (ForestVertex n)) : IsProbabilityMeasure (i.elim (μ 0 : Measure A) ν) := by
      cases i <;> dsimp <;> infer_instance
    have hi : MeasurePreserving (markForestOfCoords A n) (Measure.infinitePi ν)
        (markForestLaw A n μ') := ⟨measurable_markForestOfCoords A n,ih μ'⟩
    have hs : MeasurePreserving (fun g : Option (ForestVertex n) → A =>
        (g none,fun v => g (some v)))
        (Measure.infinitePi (fun v => v.elim (μ 0 : Measure A) ν))
        ((μ 0 : Measure A).prod (Measure.infinitePi ν)) :=
      ⟨by fun_prop,infinitePi_option_split (μ 0 : Measure A) ν⟩
    have hp := ((MeasurePreserving.id (μ 0 : Measure A)).prod hi).comp hs
    have hmap : (Measure.infinitePi (fun v : Option (ForestVertex n) =>
        v.elim (μ 0 : Measure A) ν)).map (fun g =>
          (g none,markForestOfCoords A n (fun v => g (some v)))) =
        (μ 0 : Measure A).prod (markForestLaw A n μ') := hp.map_eq
    have hc : (fun v : ForestVertex (n+1) => (μ (forestVertexDepth (n+1) v) : Measure A)) =
        (fun v : ℕ × (ℕ × Option (ForestVertex n)) => v.2.2.elim (μ 0 : Measure A) ν) := by
      funext v
      rcases v with ⟨m,i,v⟩
      cases v <;> rfl
    rw [hc]
    change (Measure.infinitePi (fun v : ℕ × (ℕ × Option (ForestVertex n)) =>
        v.2.2.elim (μ 0 : Measure A) ν)).map
        ((fun q : ℕ → ℕ → Option (ForestVertex n) → A => fun m i =>
          (q m i none,markForestOfCoords A n (fun v => q m i (some v)))) ∘
          (fun g m i v => g (m,i,v))) = _
    rw [← Measure.map_map (by fun_prop) (by fun_prop),infinitePi_triple_curry
        (fun (_ _ : ℕ) (v : Option (ForestVertex n)) => v.elim (μ 0 : Measure A) ν),
      Measure.infinitePi_map_pi _ (f := fun (_ : ℕ) (q : ℕ → Option (ForestVertex n) → A) =>
        fun i => (q i none,markForestOfCoords A n (fun v => q i (some v)))) (fun _ => by fun_prop)]
    simp_rw [Measure.infinitePi_map_pi _
        (f := fun (_ : ℕ) (g : Option (ForestVertex n) → A) =>
          (g none,markForestOfCoords A n (fun v => g (some v)))) (fun _ => hp.measurable),hmap]
    rfl

end IsingPerceptron

namespace IsingPerceptron

lemma labeledMarkedMeasure_lintegral {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (ω : (ℕ → ℕ × (ℕ → E)) × (ℕ → ℕ → F))
    {G : E × F → ℝ≥0∞} (hG : Measurable G) :
    (∫⁻ p, G p ∂labeledMarkedMeasure ω) =
      ∑' m, ∑ i : Fin (ω.1 m).1, G ((ω.1 m).2 i,ω.2 m i) := by
  simp only [labeledMarkedMeasure,lintegral_sum_measure,finiteCloudMeasure_lintegral _ hG]

lemma labeledMarkedMeasure_ae {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (ω : (ℕ → ℕ × (ℕ → E)) × (ℕ → ℕ → F)) {P : E × F → Prop}
    (hP : MeasurableSet {p | P p}) (h : ∀ᵐ p ∂labeledMarkedMeasure ω, P p) :
    ∀ m (i : Fin (ω.1 m).1), P ((ω.1 m).2 i,ω.2 m i) := by
  intro m i
  have hm := (Measure.ae_sum_iff.mp h) m
  rw [finiteCloudMeasure,← Measure.sum_fintype] at hm
  exact (ae_dirac_iff hP).mp ((Measure.ae_sum_iff.mp hm) i)

variable (A : Type) [MeasurableSpace A] [Nonempty A]

theorem labeledLeafMass_noiseMap (n : ℕ) (ω : LabeledTree n) (z : MarkForest A n)
    (hgood : GoodNoiseTree A n (labeledNoiseJoin A n (ω,z))) :
    (labeledLeafMass n ω).map (labeledNoiseLeaf A n (ω,z)) =
      noiseTreeTotal A n (labeledNoiseJoin A n (ω,z)) •
        noiseLeafKernel A n (labeledNoiseJoin A n (ω,z)) := by
  induction n with
  | zero =>
    apply Measure.ext_of_lintegral
    intro F hF
    rw [lintegral_map' hF.aemeasurable (measurable_of_countable _).aemeasurable,
      labeledLeafMass_lintegral]
    simp [labeledLeafWeight,labeledNoiseLeaf,noiseTreeTotal,
      rawTreeTotal,noiseLeafKernel,noiseLeafKernelData,Kernel.const_apply]
  | succ n ih =>
    apply Measure.ext_of_lintegral
    intro F hF
    rw [lintegral_map' hF.aemeasurable (measurable_of_countable _).aemeasurable,
      labeledLeafMass_lintegral,lintegral_smul_measure,smul_eq_mul,
      noiseLeafKernel_unnormalized_lintegral n _ hgood.1 hF]
    have hinner : Measurable (fun p : ℝ × (A × NoiseTree A n) =>
        ∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2) :=
      (hF.comp (by fun_prop : Measurable (fun p :
        (ℝ × (A × NoiseTree A n)) × NoiseLeaf A n => (p.1.1,(p.1.2.1,p.2))))).lintegral_kernel_prod_right'
        (κ := (noiseLeafKernel A n).comap (fun p : ℝ × (A × NoiseTree A n) => p.2.2) (by fun_prop))
    have hg := labeledMarkedMeasure_ae _
      ((measurableSet_GoodNoiseTree A n).preimage (by fun_prop)) hgood.2
    change (∑' v : ChildLabel × LabeledLeaf n,
      (childLabelWeight ω.1 v.1 * labeledLeafWeight n (ω.2 v.1.1 v.1.2) v.2) *
        F ((ω.1 v.1.1).2 v.1.2,((z v.1.1 v.1.2).1,
          labeledNoiseLeaf A n (ω.2 v.1.1 v.1.2,(z v.1.1 v.1.2).2) v.2))) =
      ∫⁻ p : ℝ × (A × NoiseTree A n), ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 *
        (∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2) ∂
          labeledMarkedMeasure (ω.1,fun m i => ((z m i).1,labeledNoiseJoin A n (ω.2 m i,(z m i).2)))
    have hG : Measurable (fun p : ℝ × (A × NoiseTree A n) =>
        ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 *
          (∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2)) :=
      ((by fun_prop : Measurable (fun p : ℝ × (A × NoiseTree A n) => ENNReal.ofReal (max p.1 0))).mul
        ((measurable_noiseTreeTotal A n).comp (measurable_snd.comp measurable_snd))).mul hinner
    rw [labeledMarkedMeasure_lintegral
      (ω.1,fun m i => ((z m i).1,labeledNoiseJoin A n (ω.2 m i,(z m i).2))) hG]
    rw [ENNReal.tsum_prod']
    simp_rw [mul_assoc,ENNReal.tsum_mul_left]
    rw [finiteCloud_tsum_weight]
    apply tsum_congr
    intro m
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    have he := ih (ω.2 m i) (z m i).2 (hg m i)
    have hFi : Measurable (fun v : NoiseLeaf A n => F ((ω.1 m).2 i,((z m i).1,v))) := by fun_prop
    have hh := congrArg (fun ν : Measure (NoiseLeaf A n) => ∫⁻ v, F ((ω.1 m).2 i,((z m i).1,v)) ∂ν) he
    rw [lintegral_map' hFi.aemeasurable (measurable_of_countable _).aemeasurable,
      labeledLeafMass_lintegral,lintegral_smul_measure,smul_eq_mul] at hh
    exact hh

theorem labeledLeafLaw_noiseMap (n : ℕ) (ω : LabeledTree n) (z : MarkForest A n)
    (hgood : GoodNoiseTree A n (labeledNoiseJoin A n (ω,z)))
    (ht : 0 < noiseTreeTotal A n (labeledNoiseJoin A n (ω,z)) ∧
      noiseTreeTotal A n (labeledNoiseJoin A n (ω,z)) < ∞) :
    (labeledLeafLaw n ω).map (labeledNoiseLeaf A n (ω,z)) =
      noiseLeafKernel A n (labeledNoiseJoin A n (ω,z)) := by
  have hm := labeledLeafMass_noiseMap A n ω z hgood
  have htot : labeledLeafMass n ω Set.univ = noiseTreeTotal A n (labeledNoiseJoin A n (ω,z)) := by
    have he := congrArg (fun ν : Measure (NoiseLeaf A n) => ν Set.univ) hm
    simpa only [Measure.map_apply_of_aemeasurable (measurable_of_countable _).aemeasurable MeasurableSet.univ,
      Set.preimage_univ,Measure.smul_apply,smul_eq_mul,measure_univ,mul_one] using he
  rw [labeledLeafLaw,normalizeMass_map _ (measurable_of_countable _) (by simpa only [htot] using ht),
    hm,normalizeMass_smul _ ht (by simp),normalizeMass_of_probability]

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_MonomialGgAtMinimum
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Monomial Gg At Minimum. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

variable {A : Type*} [MeasurableSpace A]

theorem logMean_normalized_moment (μ : Measure A) [IsProbabilityMeasure μ]
    (F : A → ℝ) {b : ℝ} (hb : b ≠ 0)
    (hi : Integrable (fun a => Real.exp (b*F a)) μ) :
    (∫⁻ a, ENNReal.ofReal ((Real.exp (F a-logMean b μ F))^b) ∂μ) = 1 := by
  let M := ∫ a, Real.exp (b*F a) ∂μ
  have hM : 0 < M := integral_exp_pos μ F hi
  have he a : (Real.exp (F a-logMean b μ F))^b = M⁻¹ * Real.exp (b*F a) := by
    rw [← Real.exp_mul]
    have he' : (F a-logMean b μ F)*b = -Real.log M+b*F a := by
      dsimp only [logMean, M]
      field_simp
      ring
    rw [he', Real.exp_add, Real.exp_neg, Real.exp_log hM]
  simp_rw [he, ENNReal.ofReal_mul (inv_nonneg.mpr hM.le)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun a => (Real.exp_pos _).le)]
  change ENNReal.ofReal M⁻¹ * ENNReal.ofReal M = 1
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hM.le), inv_mul_cancel₀ hM.ne', ENNReal.ofReal_one]

end IsingPerceptron

namespace IsingPerceptron
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]

omit [MeasurableSpace S] in
lemma backwardValue_step (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    (u : ℕ → S × A → S) (F : S → ℝ) {i : ℕ} (hi : i < n) (s : S) :
    backwardValue n b μ u F i s = logMean (b i) (μ i : Measure A)
      (fun a => backwardValue n b μ u F (i+1) (u i (s,a))) := by
  unfold backwardValue
  rw [show n-i = (n-(i+1))+1 by omega, cascadeRecursion]
  simp only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1]

omit [MeasurableSpace S] in
lemma backwardValue_terminal (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    (u : ℕ → S × A → S) (F : S → ℝ) {i : ℕ} (hi : n ≤ i) :
    backwardValue n b μ u F i = F := by
  simp [backwardValue, Nat.sub_eq_zero_of_le hi, cascadeRecursion]

end IsingPerceptron

namespace IsingPerceptron
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

omit [MeasurableSpace S] in
lemma noiseTreeFactor_terminal (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    (X : ℕ → S → ℝ) (u : ℕ → S × A → S) (s : S) (ν : NoiseTree A n) :
    noiseTreeFactor n b μ X u s ν = terminalTreeFactor n b μ u (X n) s ν := by
  induction n generalizing b μ X u s with
  | zero => rfl
  | succ n ih =>
    unfold noiseTreeFactor terminalTreeFactor
    apply lintegral_congr
    intro p
    congr 1
    exact ih _ _ _ _ _ _

omit [MeasurableSpace S] in
lemma terminalTreeFactor_update_congr (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    (F : S → ℝ) {u v : ℕ → S × A → S} (huv : ∀ i < n, u i = v i)
    (s : S) (ν : NoiseTree A n) :
    terminalTreeFactor n b μ u F s ν = terminalTreeFactor n b μ v F s ν := by
  induction n generalizing b μ u v s with
  | zero => rfl
  | succ n ih =>
    unfold terminalTreeFactor
    rw [huv 0 (by omega)]
    apply lintegral_congr
    intro p
    congr 1
    exact ih _ _ (fun i hi => huv (i+1) (by omega)) _ _

omit [MeasurableSpace S] in
lemma backwardValue_treeFactor (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    (F : S → ℝ) (u : ℕ → S × A → S) (s : S) (ν : NoiseTree A n) :
    noiseTreeFactor n b μ (backwardValue n b μ u F) (stoppedUpdate n u) s ν =
      terminalTreeFactor n b μ u F s ν := by
  rw [noiseTreeFactor_terminal, backwardValue_terminal n b μ u F (le_refl n)]
  apply terminalTreeFactor_update_congr
  intro i hi
  funext p
  exact ite_eq_left hi

omit [MeasurableSpace S] [Nonempty A] in
lemma backwardValue_multiplier_moment_admissible (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure A) (u : ℕ → S × A → S) (F : S → ℝ)
    (hb : ∀ i < n, 0 < b i)
    (hadm : ∀ i < n, ∀ s, Integrable (fun a => Real.exp
      (b i * backwardValue n b μ u F (i+1) (u i (s,a)))) (μ i : Measure A))
    (i : ℕ) (s : S) :
    (∫⁻ a, ENNReal.ofReal ((Real.exp
      (backwardValue n b μ u F (i+1) (stoppedUpdate n u i (s,a)) -
        backwardValue n b μ u F i s)) ^ b i) ∂(μ i : Measure A)) = 1 := by
  by_cases hi : i < n
  · simp only [stoppedUpdate, ite_eq_left hi, backwardValue_step n b μ u F hi]
    exact logMean_normalized_moment _ _ (hb i hi).ne' (hadm i hi s)
  · have hni : n ≤ i := by omega
    simp only [stoppedUpdate, ite_eq_right hi,
      backwardValue_terminal n b μ u F hni,
      backwardValue_terminal n b μ u F (show n ≤ i+1 by omega), sub_self,
      Real.exp_zero, Real.one_rpow, ENNReal.ofReal_one, lintegral_const, measure_univ, mul_one]

theorem admissible_noiseCascade_recursion (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A) {u : ℕ → S × A → S} {F : S → ℝ}
    (hu : ∀ i, Measurable (u i)) (hF : Measurable F) (hadm : ∀ i < n, ∀ s, Integrable (fun a => Real.exp
      (b i * backwardValue n b μ u F (i+1) (u i (s,a)))) (μ i : Measure A)) (s : S) :
    let P := (noiseCascadeLaw A n b μ : Measure (NoiseTree A n))
    let L := fun ν => Real.log
      ((terminalTreeFactor n b μ u F s ν).toReal / (noiseTreeTotal A n ν).toReal)
    (∀ᵐ ν ∂P, 0 < terminalTreeFactor n b μ u F s ν ∧ terminalTreeFactor n b μ u F s ν < ∞) ∧
    Integrable L P ∧ (∫ ν, L ν ∂P) = cascadeRecursion n b μ u F s ∧
    Integrable (fun ν => (L ν-cascadeRecursion n b μ u F s)^2) P ∧
    (∫ ν, (L ν-cascadeRecursion n b μ u F s)^2 ∂P) ≤
      4 * ∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n)) := by
  let X := backwardValue n b μ u F
  let v := stoppedUpdate n u
  let c : ℕ → S × A → ℝ := fun i p => Real.exp (X (i+1) (v i p)-X i p.1)
  have hX : ∀ i, Measurable (X i) := measurable_backwardValue n b μ hu hF
  have hv : ∀ i, Measurable (v i) := measurable_stoppedUpdate n hu
  have hc : ∀ i, Measurable (c i) := fun i =>
    (((hX (i+1)).comp (hv i)).sub ((hX i).comp measurable_fst)).exp
  have hm : ∀ i s, (∫⁻ a, ENNReal.ofReal (c i (s,a)^b i) ∂(μ i : Measure A)) = 1 :=
    backwardValue_multiplier_moment_admissible n b μ u F (fun i hi => (hb.1 i hi).1) hadm
  have h := noiseCascade_log_integral n b hb μ hc hv (X := X) (fun _ _ _ => rfl) hm s
  have hX0 : X 0 s = cascadeRecursion n b μ u F s := by simp [X, backwardValue]
  simpa only [X, v, backwardValue_treeFactor, hX0] using h

end IsingPerceptron

namespace IsingPerceptron
variable {S : Type*} [SeminormedAddCommGroup S] [MeasurableSpace S] [MeasurableAdd₂ S]

lemma backwardValue_linearGrowth_moments (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure S)
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure S))
    {F : S → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hb : ∀ i < n, 0 < b i) :
    ∀ i < n, ∀ s, Integrable (fun a => Real.exp
      (b i * backwardValue n b μ (fun _ p => p.1+p.2) F (i+1) (s+a))) (μ i : Measure S) := by
  intro i hi s
  apply integrable_exp_of_linearGrowth _ (hμ i hi)
    ((measurable_backwardValue n b μ (fun _ => measurable_fst.add measurable_snd) hF (i+1)).comp
      (measurable_const.add measurable_id))
  apply HasLinearGrowth.add_left
  unfold backwardValue
  exact cascadeRecursion_linearGrowth _ _ _ (fun j hj => hμ (i+1+j) (by omega)) hF hG
    (fun j hj => hb (i+1+j) (by omega))

end IsingPerceptron

namespace IsingPerceptron

variable {S : Type} [SeminormedAddCommGroup S] [MeasurableSpace S] [MeasurableAdd₂ S]

theorem linearGrowth_noiseCascade_recursion (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure S) (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure S))
    {F : S → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F) (s : S) :
    let u : ℕ → S × S → S := fun _ p => p.1+p.2
    let P := (noiseCascadeLaw S n b μ : Measure (NoiseTree S n))
    let L := fun ν => Real.log
      ((terminalTreeFactor n b μ u F s ν).toReal / (noiseTreeTotal S n ν).toReal)
    (∀ᵐ ν ∂P, 0 < terminalTreeFactor n b μ u F s ν ∧ terminalTreeFactor n b μ u F s ν < ∞) ∧
    Integrable L P ∧ (∫ ν, L ν ∂P) = cascadeRecursion n b μ u F s ∧
    Integrable (fun ν => (L ν-cascadeRecursion n b μ u F s)^2) P ∧
    (∫ ν, (L ν-cascadeRecursion n b μ u F s)^2 ∂P) ≤
      4 * ∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n)) := by
  exact admissible_noiseCascade_recursion n b hb μ (fun _ => measurable_fst.add measurable_snd) hF
    (backwardValue_linearGrowth_moments n b μ hμ hF hG (fun i hi => (hb.1 i hi).1)) s

end IsingPerceptron

namespace IsingPerceptron

lemma logMean_const_add_integrable {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {b : ℝ} {F : A → ℝ}
    (hF : Integrable (fun a => Real.exp (b*F a)) μ) (c : ℝ) :
    Integrable (fun a => Real.exp (b*(c+F a))) μ := by
  simpa only [mul_add,Real.exp_add] using hF.const_mul (Real.exp (b*c))

lemma logMean_abs_sub_le {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] {b : ℝ} (hb : 0 < b)
    {F G : A → ℝ} (hF : Integrable (fun a => Real.exp (b*F a)) μ)
    (hG : Integrable (fun a => Real.exp (b*G a)) μ) {C : ℝ}
    (h : ∀ a, |F a-G a| ≤ C) : |logMean b μ F-logMean b μ G| ≤ C := by
  apply abs_le.mpr
  have hu : logMean b μ F ≤ C+logMean b μ G := by
    rw [← logMean_const_add μ hb.ne' hG C]
    exact logMean_mono μ hb hF (logMean_const_add_integrable hG C)
      (fun a => by linarith [(abs_le.mp (h a)).2])
  have hl : logMean b μ G ≤ C+logMean b μ F := by
    rw [← logMean_const_add μ hb.ne' hF C]
    exact logMean_mono μ hb hG (logMean_const_add_integrable hF C)
      (fun a => by linarith [(abs_le.mp (h a)).1])
  constructor <;> linarith

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_EnrichedFieldCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enriched Field Cap. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

variable {I : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

omit [Fintype I] [MeasurableSingletonClass I] in
lemma finiteLogIntegral_eq_logMean (ν : Measure I) (H : I → ℝ) :
    finiteLogIntegral ν H = logMean 1 ν H := by simp [finiteLogIntegral,logMean]

lemma measurable_finiteLogIntegral (ν : Measure I) : Measurable (finiteLogIntegral ν) := by
  unfold finiteLogIntegral
  have hm : Measurable (fun p : (I → ℝ) × I => Real.exp (p.1 p.2)) :=
    measurable_from_prod_countable_left (fun i => (measurable_pi_apply i).exp)
  exact hm.stronglyMeasurable.integral_prod_right.measurable.log

lemma finiteLogIntegral_lipschitz (ν : Measure I) [IsProbabilityMeasure ν] (H G : I → ℝ) :
    |finiteLogIntegral ν H-finiteLogIntegral ν G| ≤ ‖H-G‖ := by
  rw [finiteLogIntegral_eq_logMean,finiteLogIntegral_eq_logMean]
  apply logMean_abs_sub_le ν (by norm_num)
    (show Integrable (fun x => Real.exp (1*H x)) ν from Integrable.of_finite)
    (show Integrable (fun x => Real.exp (1*G x)) ν from Integrable.of_finite)
  intro x
  simpa only [Pi.sub_apply,Real.norm_eq_abs] using norm_le_pi_norm (H-G) x

lemma finiteLogIntegral_linearGrowth (ν : Measure I) [IsProbabilityMeasure ν] :
    HasLinearGrowth (finiteLogIntegral ν) := by
  refine ⟨0,1,le_rfl,zero_le_one,fun H => ?_⟩
  simpa only [finiteLogIntegral,Pi.zero_apply,Real.exp_zero,integral_const,probReal_univ,
    one_smul,Real.log_one,sub_zero,one_mul,zero_add] using finiteLogIntegral_lipschitz ν H 0

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_VarianceOfConditionalCenterBound
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.cascadeCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedCoordinateLaw_probability _root_.OAI.IsingPerceptron.enrichedCylinderBaseLaw_probability _root_.OAI.IsingPerceptron.enrichedCylinderLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.markedReplicaLaw_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variance Of Conditional Center Bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

omit [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma labeledEnergy_terminal (n : ℕ) (ω : LabeledTree n) (z : MarkForest (I → ℝ) n)
    (γ : LabeledLeaf n) (F : (I → ℝ) → ℝ) (H : I → ℝ) :
    noiseLeafTerminal n (fun _ => F) (fun _ p => p.1 + p.2) H
      (labeledNoiseLeaf (I → ℝ) n (ω,z) γ) = F (labeledEnergy n z γ H) := by
  induction n generalizing H with
  | zero => rfl
  | succ n ih => exact ih _ _ _ _

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_EnergyShift
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Energy Shift. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron


lemma nodeAt_zero (n : ℕ) (γ : LabeledLeaf n) : nodeAt n γ 0 = none := by
  cases n <;> simp [nodeAt]

lemma nodeAt_succ (n : ℕ) (γ : LabeledLeaf n) (i : Fin n) :
    nodeAt n γ i.succ = some (edgeAt n γ i) := by
  cases n with
  | zero => exact i.elim0
  | succ n => simp [nodeAt,edgeAt]

lemma labeledEnergy_edge_sum {I : Type} (n : ℕ) (g : ForestVertex n → I → ℝ)
    (γ : LabeledLeaf n) (H : I → ℝ) (x : I) :
    labeledEnergy n (markForestOfCoords (I → ℝ) n g) γ H x =
      H x + ∑ i : Fin n, g (edgeAt n γ i) x := by
  induction n generalizing H with
  | zero => simp [labeledEnergy]
  | succ n ih =>
    rw [labeledEnergy,markForestOfCoords,ih,Fin.sum_univ_succ]
    simp only [edgeAt,nodeAt_zero,nodeAt_succ,Pi.add_apply]
    ring

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_EnrichedCGF
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.markedReplicaLaw_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enriched C G F. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron
variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

lemma noise_energy_exp_integrable (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (H : I → ℝ) :
    ∀ᵐ T ∂(noiseCascadeLaw (I → ℝ) n b μ : Measure (NoiseTree (I → ℝ) n)),
      Integrable (fun v => Real.exp (noiseLeafTerminal n (fun _ => finiteLogIntegral ν)
        (fun _ p => p.1+p.2) H v)) (noiseLeafKernel (I → ℝ) n T) := by
  have hfin := (linearGrowth_noiseCascade_recursion n b hb μ hμ
    (measurable_finiteLogIntegral ν) (finiteLogIntegral_linearGrowth ν) H).1
  have hfac := noiseTreeFactor_leafIntegral n b hb μ
    (X := fun _ => finiteLogIntegral ν) (u := fun _ p => p.1+p.2)
    (fun _ => measurable_finiteLogIntegral ν) (fun _ => measurable_fst.add measurable_snd) H
  have htot : ∀ᵐ T ∂(noiseCascadeLaw (I → ℝ) n b μ : Measure (NoiseTree (I → ℝ) n)),
      0 < noiseTreeTotal (I → ℝ) n T ∧ noiseTreeTotal (I → ℝ) n T < ∞ := by
    apply ae_of_ae_map (p := fun T : RawTree n => 0 < rawTreeTotal n T ∧ rawTreeTotal n T < ∞)
      (measurable_noiseTreeForget (I → ℝ) n).aemeasurable
    rw [noiseCascadeLaw_forget]
    exact (rawCascade_total_moments n b hb).1
  filter_upwards [hfin,hfac,htot] with T hf he ht
  simp only [noiseTreeFactor_terminal] at he
  have hx : (∫⁻ v, ENNReal.ofReal (Real.exp (noiseLeafTerminal n (fun _ => finiteLogIntegral ν)
      (fun _ p => p.1+p.2) H v)) ∂noiseLeafKernel (I → ℝ) n T) < ∞ := by
    by_contra! hx
    rw [top_le_iff.mp hx, ENNReal.mul_top ht.1.ne'] at he
    exact hf.2.ne he
  constructor
  · exact (((measurable_noiseLeafTerminal n (fun _ => measurable_finiteLogIntegral ν)
      (fun _ => measurable_fst.add measurable_snd)).comp
      (measurable_const.prodMk measurable_id)).exp.aestronglyMeasurable)
  · rw [hasFiniteIntegral_iff_enorm]
    simpa only [Real.enorm_eq_ofReal_abs,abs_of_pos (Real.exp_pos _)] using hx

lemma labeled_energy_exp_integrable (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (H : I → ℝ) :
    ∀ᵐ p ∂((labeledCascadeLaw n b : Measure (LabeledTree n)).prod (markForestLaw (I → ℝ) n μ)),
      Integrable (fun s : I × LabeledLeaf n => Real.exp (labeledEnergy n p.2 s.2 H s.1))
        (labeledSpinReference n ν p.1) := by
  have hp : MeasurePreserving (labeledNoiseJoin (I → ℝ) n)
      ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod (markForestLaw (I → ℝ) n μ))
      (noiseCascadeLaw (I → ℝ) n b μ : Measure (NoiseTree (I → ℝ) n)) :=
    ⟨measurable_labeledNoiseJoin _ _,labeledNoiseJoin_law _ _ _ _⟩
  have hg := hp.quasiMeasurePreserving.tendsto_ae.eventually (noiseCascade_good (I → ℝ) n b hb μ)
  have ht : ∀ᵐ p ∂((labeledCascadeLaw n b : Measure (LabeledTree n)).prod (markForestLaw (I → ℝ) n μ)),
      0 < noiseTreeTotal (I → ℝ) n (labeledNoiseJoin (I → ℝ) n p) ∧
      noiseTreeTotal (I → ℝ) n (labeledNoiseJoin (I → ℝ) n p) < ∞ := by
    apply hp.quasiMeasurePreserving.tendsto_ae.eventually (p := fun T =>
      0 < noiseTreeTotal (I → ℝ) n T ∧ noiseTreeTotal (I → ℝ) n T < ∞)
    apply ae_of_ae_map (p := fun T : RawTree n => 0 < rawTreeTotal n T ∧ rawTreeTotal n T < ∞)
      (measurable_noiseTreeForget (I → ℝ) n).aemeasurable
    rw [noiseCascadeLaw_forget]
    exact (rawCascade_total_moments n b hb).1
  have hi := hp.quasiMeasurePreserving.tendsto_ae.eventually
    (noise_energy_exp_integrable n b hb μ ν hμ H)
  filter_upwards [hg,ht,hi] with p hg ht hi
  have hm : Measurable (fun v => Real.exp (noiseLeafTerminal n (fun _ => finiteLogIntegral ν)
      (fun _ p => p.1+p.2) H v)) :=
    (((measurable_noiseLeafTerminal n (fun _ => measurable_finiteLogIntegral ν)
      (fun _ => measurable_fst.add measurable_snd)).comp
      (measurable_const.prodMk measurable_id)).exp)
  have hl := integrable_map_measure (μ := labeledLeafLaw n p.1) hm.aestronglyMeasurable
    (measurable_of_countable (labeledNoiseLeaf (I → ℝ) n p)).aemeasurable
  rw [labeledLeafLaw_noiseMap (I → ℝ) n p.1 p.2 hg ht] at hl
  have hf : Integrable (fun γ => Real.exp (finiteLogIntegral ν (labeledEnergy n p.2 γ H)))
      (labeledLeafLaw n p.1) := by
    apply (hl.mp hi).congr
    exact ae_of_all _ (fun γ => congrArg Real.exp (labeledEnergy_terminal n p.1 p.2 γ (finiteLogIntegral ν) H))
  change Integrable _ (ν.prod (labeledLeafLaw n p.1))
  change Integrable ((fun s : LabeledLeaf n × I => Real.exp (labeledEnergy n p.2 s.1 H s.2)) ∘ Prod.swap) _
  apply integrable_swap_iff.mpr
  apply (integrable_prod_iff (by exact (measurable_of_countable _).aestronglyMeasurable)).mpr
  constructor
  · exact ae_of_all _ (fun _ => Integrable.of_finite)
  · simpa only [Prod.swap_prod_mk, Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),finiteLogIntegral,
      Real.exp_log (MeasureTheory.integral_exp_pos Integrable.of_finite)] using hf


omit [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma cascadeCoordinates_preserving (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (I → ℝ)) :
    MeasurePreserving (fun p : LabeledTree n × (ForestVertex n → I → ℝ) =>
      (p.1,markForestOfCoords (I → ℝ) n p.2)) (cascadeCoordinateLaw n b μ)
      ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod (markForestLaw (I → ℝ) n μ)) :=
  (MeasurePreserving.id _).prod ⟨measurable_markForestOfCoords _ _,markForestOfCoords_law _ _ _⟩

omit [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma cascadeCoordinateEnergy_eq (n : ℕ) (H : I → ℝ)
    (p : LabeledTree n × (ForestVertex n → I → ℝ)) (s : I × LabeledLeaf n) :
    cascadeCoordinateEnergy n H p s = labeledEnergy n (markForestOfCoords (I → ℝ) n p.2) s.2 H s.1 :=
  (labeledEnergy_edge_sum n p.2 s.2 H s.1).symm

lemma cascadeCoordinate_exp_integrable (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (H : I → ℝ) :
    ∀ᵐ p ∂cascadeCoordinateLaw n b μ,
      Integrable (fun s => Real.exp (cascadeCoordinateEnergy n H p s)) (labeledSpinReference n ν p.1) := by
  simpa only [cascadeCoordinateEnergy_eq] using
    (cascadeCoordinates_preserving n b μ).quasiMeasurePreserving.tendsto_ae.eventually
      (labeled_energy_exp_integrable n b hb μ ν hμ H)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_RetainedDisplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retained Displacement. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma normalizeMass_exp {X : Type*} [MeasurableSpace X] [Nonempty X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ) (hH : Measurable H)
    (he : Integrable (fun x => Real.exp (H x)) ν) :
    normalizeMass (ν.withDensity (fun x => ENNReal.ofReal (Real.exp (H x)))) = ν.tilted H := by
  have hZ : (ν.withDensity (fun x => ENNReal.ofReal (Real.exp (H x)))) univ =
      ENNReal.ofReal (∫ x, Real.exp (H x) ∂ν) := by
    rw [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal he (ae_of_all _ (fun x => (Real.exp_pos _).le))]
  have hpos := _root_.MeasureTheory.integral_exp_pos he
  rw [normalizeMass,ite_eq_left (by rw [hZ]; exact ⟨ENNReal.ofReal_pos.mpr hpos,ENNReal.ofReal_lt_top⟩),
    hZ,Measure.tilted,← withDensity_smul _ hH.exp.ennreal_ofReal]
  congr 1; funext x
  simp only [Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_inv_of_pos hpos,mul_comm]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_Model
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-volume invariant Ising pressure

The spin prior is uniform probability, as in (1.1) and (7.1) of
*All-temperature pressure for orthogonally invariant Ising spin glasses*.
These deterministic comparison lemmas do not assume any asymptotic pressure formula.
-/

noncomputable section

open scoped BigOperators

namespace InvariantIsing

lemma logPartition_eq {X : Type*} [Fintype X] [Nonempty X] (H : X → ℝ) :
    logPartition H = Real.log (∑ x, Real.exp (H x)) - Real.log (Fintype.card X) := by
  have hc : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [logPartition, Real.log_mul (inv_ne_zero hc) (sum_exp_pos H).ne', Real.log_inv]
  ring

/-- Uniform cube entropy is `N log 2`. -/
lemma log_card_spin (N : ℕ) : Real.log (Fintype.card (Spin N)) = N * Real.log 2 := by
  simp only [Spin, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_Rotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ising pressure on an orthogonal spectral orbit

The interaction is defined using a real linear isometry, so orthogonality
is part of its type. The bounds hold pointwise in the rotation; no Haar
or independence assumption is needed for these finite-volume estimates.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace InvariantIsing

@[simp] lemma logPartition_zero {X : Type*} [Fintype X] [Nonempty X] :
    logPartition (fun _ : X => (0 : ℝ)) = 0 := by
  rw [logPartition_eq]
  simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorLabeled
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The finite spectral tensor model on the countable spin/leaf state space.
The Gaussian energy marks are the actual pushforward of the coordinate
marks, and the tilted ancestor-prefix marginal has its cascade value.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

lemma finiteLogIntegral_uniformSpinPrior {N : ℕ} (H : Spin N → ℝ) :
    IsingPerceptron.finiteLogIntegral (uniformSpinPrior N : Measure (Spin N)) H = logPartition H := by
  unfold IsingPerceptron.finiteLogIntegral logPartition
  congr 1
  change (∫ σ, Real.exp (H σ) ∂(PMF.uniformOfFintype (Spin N)).toMeasure) = _
  rw [integral_fintype (Integrable.of_finite)]
  simp only [measureReal_def,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  rw [← Finset.mul_sum]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorPairConditioning
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conditional independent spin residuals at two sampled cascade leaves. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators ENNReal NNReal

namespace InvariantIsing

lemma exp_spinLeafTerminal {N n : ℕ} (H : Spin N × LabeledLeaf n → ℝ) (α : LabeledLeaf n) :
    Real.exp (spinLeafTerminal H α) =
      referencePartition (uniformSpinPrior N : Measure (Spin N)) (fun σ => H (σ, α)) := by
  exact Real.exp_log (integral_exp_pos (Integrable.of_finite))

lemma spinLeafTerminal_exp_integrable {N n : ℕ} (ν : Measure (LabeledLeaf n)) [IsProbabilityMeasure ν]
    (H : Spin N × LabeledLeaf n → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ((uniformSpinPrior N : Measure (Spin N)).prod ν)) :
    Integrable (fun α => Real.exp (spinLeafTerminal H α)) ν := by
  convert he.integral_prod_right using 1
  all_goals try with_reducible_and_instances rfl
  ext α
  exact exp_spinLeafTerminal H α

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityTiltTransport
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized quadratic tilts commute with the Gaussian factor map. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_tilt_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (F : X → Y) (hF : Measurable F)
    (f : Y → ℝ) (hf : Measurable f) :
    (μ.tilted (f ∘ F)).map F = (μ.map F).tilted f := by
  ext s hs
  rw [Measure.map_apply hF hs, tilted_apply_eq_ofReal_integral' _ (hF hs),
    tilted_apply_eq_ofReal_integral' _ hs,
    integral_map hF.aemeasurable hf.exp.aestronglyMeasurable,
    setIntegral_map hs ((hf.exp.div_const _).aestronglyMeasurable) hF.aemeasurable]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSpinSampling
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual spin sampling and Gaussian transitions for the scalar Ising
recursion. The transition kernels remain probabilities at zero variance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma fieldTransitionKernel_eq_tilted (ζ : ℝ) (v : ℝ≥0)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (z : ℝ) :
    fieldTransitionKernel ζ v F hF z = (gaussianReal z v).tilted (fun u => ζ * F u) := by
  exact normalizeMass_exp _ _ (hF.const_mul ζ)
    (integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hG ζ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldGaussianProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A separable scalar cavity tilt preserves independence of the Gaussian
site coordinates. This identifies the actual vector transition law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators NNReal

namespace InvariantIsing

theorem fieldGaussian_product_tilt {N : ℕ} (ζ : ℝ) (v : ℝ≥0)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (z : Fin N → ℝ) :
    (Measure.pi (fun i => gaussianReal (z i) v)).tilted
      (fun y => ζ * ∑ i, F (y i)) =
      Measure.pi (fun i => fieldTransitionKernel ζ v F hF (z i)) := by
  let μ := fun i : Fin N => gaussianReal (z i) v
  let Z := fun i : Fin N => ∫ u, Real.exp (ζ * F u) ∂μ i
  have hZpos (i : Fin N) : 0 < Z i := integral_exp_pos
    (integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments (z i) v) hF hG ζ)
  have hZ : (∫ y, Real.exp (ζ * ∑ i, F (y i)) ∂Measure.pi μ) = ∏ i, Z i := by
    simp_rw [Finset.mul_sum, Real.exp_sum]
    exact integral_fintype_prod_eq_prod (fun _ u => Real.exp (ζ * F u))
  have hS (s : Fin N → Set ℝ) :
      (∫ y in univ.pi s, Real.exp (ζ * ∑ i, F (y i)) ∂Measure.pi μ) =
        ∏ i, ∫ u in s i, Real.exp (ζ * F u) ∂μ i := by
    simp_rw [Finset.mul_sum, Real.exp_sum]
    rw [Measure.restrict_pi_pi]
    exact integral_fintype_prod_eq_prod (fun _ u => Real.exp (ζ * F u))
  apply (Measure.pi_eq (μ := fun i => fieldTransitionKernel ζ v F hF (z i)) ?_).symm
  intro s hs
  change ((Measure.pi μ).tilted (fun y => ζ * ∑ i, F (y i))) (univ.pi s) = _
  rw [tilted_apply_eq_ofReal_integral' _ (MeasurableSet.univ_pi hs), integral_div, hS, hZ]
  rw [← Finset.prod_div_distrib, ENNReal.ofReal_prod_of_nonneg
    (fun i _ => div_nonneg (integral_nonneg (fun u => (Real.exp_pos _).le)) (hZpos i).le)]
  apply Finset.prod_congr rfl
  intro i _
  rw [fieldTransitionKernel_eq_tilted ζ v F hF hG,
    tilted_apply_eq_ofReal_integral' _ (hs i), integral_div]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinFactorization
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeNonempty
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.spinValue_not
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact factorization of the Ising reference at zero interaction. -/

noncomputable section

open scoped BigOperators

namespace InvariantIsing

lemma sum_exp_fieldEnergy {N : ℕ} (c : Fin N → ℝ) :
    (∑ σ : Spin N, Real.exp (fieldEnergy c σ)) = ∏ i, 2 * Real.cosh (c i) := by
  simp only [fieldEnergy, Real.exp_sum]
  rw [← Fintype.prod_sum (fun (i : Fin N) (b : Bool) => Real.exp (c i * spinValue b))]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Fintype.sum_bool]
  norm_num [spinValue, Real.cosh_eq]
  ring

/-- The site factorization used before the backward Gaussian cascade recursion. -/
theorem logPartition_fieldEnergy {N : ℕ} (c : Fin N → ℝ) :
    logPartition (fieldEnergy c) = ∑ i, Real.log (Real.cosh (c i)) := by
  have hcard : (Fintype.card (Spin N) : ℝ) = ∏ _ : Fin N, (2 : ℝ) := by
    simp [Spin]
  have hc : (Fintype.card (Spin N) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [logPartition, sum_exp_fieldEnergy, Finset.prod_mul_distrib, ← hcard,
    ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  exact Real.log_prod (fun i _ => (Real.cosh_pos (c i)).ne')

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldVectorSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual vector spin sampling for independent scalar cavity fields. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators NNReal

namespace InvariantIsing

lemma fieldVectorTransitionKernel_eq_tilted {N : ℕ} (ζ : ℝ) (v : ℝ≥0)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (z : Fin N → ℝ) :
    fieldVectorTransitionKernel N ζ v F hF z =
      (Measure.pi (fun i => gaussianReal (z i) v)).tilted (fun y => ζ * ∑ i, F (y i)) :=
  (fieldGaussian_product_tilt ζ v F hF hG z).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldEnergyCoordinates
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.spinValue_not
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual scalar-field forest as a finite Ising energy-mark forest. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma fieldEnergy_map_norm_le (N : ℕ) (z : Fin N → ℝ) :
    ‖fieldEnergy z‖ ≤ (N : ℝ) * ‖z‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg z))).mpr
  intro σ
  change |∑ i, z i * spinValue (σ i)| ≤ _
  calc
    _ ≤ ∑ i, |z i * spinValue (σ i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |z i| := by simp only [abs_mul, abs_spinValue, mul_one]
    _ ≤ ∑ _ : Fin N, ‖z‖ := Finset.sum_le_sum fun i _ => by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i
    _ = _ := by simp

lemma fieldEnergyMarkLaw_moments (N : ℕ) (hN : 0 < N) (v : ℝ≥0) :
    ExponentialNormMoments (fieldEnergyMarkLaw N v : Measure (Spin N → ℝ)) := by
  intro a
  apply (integrable_map_measure (by fun_prop) (measurable_fieldEnergy_map N).aemeasurable).mpr
  have hi := vectorGaussianLaw_moments hN v (|a| * N)
  apply hi.mono' (((measurable_fieldEnergy_map N).norm.const_mul a).exp.aestronglyMeasurable)
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    a * ‖fieldEnergy z‖ ≤ |a| * ‖fieldEnergy z‖ :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
    _ ≤ |a| * ((N : ℝ) * ‖z‖) :=
      mul_le_mul_of_nonneg_left (fieldEnergy_map_norm_le N z) (abs_nonneg _)
    _ = _ := by ring

theorem fieldEnergyCoordinates_law (N : ℕ) (h : FieldStep) :
    MeasurePreserving (fieldEnergyCoordinates N h) (fieldVectorCoordinateLaw N h)
      (cascadeCoordinateLaw h.depth (chainExponent h.cut)
        (fun i => fieldEnergyMarkLaw N (fieldStepVariance h i))) := by
  have hm : MeasurePreserving
      (fun g : ForestVertex h.depth → Fin N → ℝ => fun a => fieldEnergy (g a))
      (Measure.infinitePi (fun a : ForestVertex h.depth =>
        (vectorGaussianLaw N (fieldStepVariance h (forestVertexDepth h.depth a)) :
          Measure (Fin N → ℝ))))
      (Measure.infinitePi (fun a : ForestVertex h.depth =>
        (fieldEnergyMarkLaw N (fieldStepVariance h (forestVertexDepth h.depth a)) :
          Measure (Spin N → ℝ)))) := by
    refine ⟨Measurable.of_eval (fun a =>
      (measurable_fieldEnergy_map N).comp (measurable_pi_apply a)), ?_⟩
    rw [Measure.infinitePi_map_pi _ (fun _ => measurable_fieldEnergy_map N)]
    rfl
  exact (MeasurePreserving.id (labeledCascadeLaw h.depth (chainExponent h.cut) :
    Measure (LabeledTree h.depth))).prod hm

lemma fieldEnergyCoordinates_energy (N : ℕ) (h : FieldStep)
    (p : LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ))
    (z : Fin N → ℝ) (s : Spin N × LabeledLeaf h.depth) :
    cascadeCoordinateEnergy h.depth (fieldEnergy z) (fieldEnergyCoordinates N h p) s =
      fieldEnergy (fieldVectorEndpoint N h p z s.2) s.1 := by
  change fieldEnergy z s.1 + ∑ i : Fin h.depth, fieldEnergy (p.2 (edgeAt h.depth s.2 i)) s.1 = _
  have he : fieldVectorEndpoint N h p z s.2 =
      z + ∑ i : Fin h.depth, p.2 (edgeAt h.depth s.2 i) := by
    ext j
    simpa only [fieldVectorEndpoint, Pi.add_apply, Finset.sum_apply] using
      labeledEnergy_edge_sum h.depth p.2 s.2 z j
  rw [he]
  simp only [fieldEnergy, Pi.add_apply, Finset.sum_apply, add_mul, Finset.sum_add_distrib,
    Finset.sum_mul]
  rw [Finset.sum_comm]

theorem field_vector_spin_exp_integrable (N : ℕ) (hN : 0 < N) (h : FieldStep)
    (z : Fin N → ℝ) :
    ∀ᵐ p ∂fieldVectorCoordinateLaw N h,
      Integrable (fun s : Spin N × LabeledLeaf h.depth =>
        Real.exp (fieldEnergy (fieldVectorEndpoint N h p z s.2) s.1))
        ((uniformSpinPrior N : Measure (Spin N)).prod (labeledLeafLaw h.depth p.1)) := by
  have he := (fieldEnergyCoordinates_law N h).quasiMeasurePreserving.ae
    (cascadeCoordinate_exp_integrable h.depth (chainExponent h.cut)
      (chainExponent_admissible h.ordered_cut h.first h.last)
      (fun i => fieldEnergyMarkLaw N (fieldStepVariance h i))
      (uniformSpinPrior N : Measure (Spin N))
      (fun i _ => fieldEnergyMarkLaw_moments N hN (fieldStepVariance h i)) (fieldEnergy z))
  filter_upwards [he] with p hp
  change Integrable (fun s => Real.exp (cascadeCoordinateEnergy h.depth (fieldEnergy z)
    (fieldEnergyCoordinates N h p) s))
      ((uniformSpinPrior N : Measure (Spin N)).prod (labeledLeafLaw h.depth p.1)) at hp
  simpa only [fieldEnergyCoordinates_energy] using hp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_MarkEndpointKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint kernels of the finite ancestor-dependent increment chain. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace InvariantIsing
variable {N : ℕ}

lemma markStateKernel_apply (κ : Kernel (Fin N → ℝ) (Fin N → ℝ))
    [IsMarkovKernel κ] (z : Fin N → ℝ) :
    markStateKernel κ z = (κ z).map (fun a => z+a) := by
  rw [markStateKernel,Kernel.map_apply _ (show Measurable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => p.1+p.2) from
    measurable_fst.add measurable_snd), Kernel.prod_apply,Kernel.id_apply,Measure.dirac_prod]
  rw [Measure.map_map (show Measurable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => p.1+p.2) from
    measurable_fst.add measurable_snd) measurable_prodMk_left]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_MarkEndpointIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded endpoint observables of independent and shared ancestor paths. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace InvariantIsing
variable {N : ℕ}

lemma measurable_markPairEndpoint (n : ℕ) (z₁ z₂ : Fin N → ℝ) :
    Measurable (markPairEndpoint n z₁ z₂) := by
  exact (measurable_const.add (Finset.measurable_sum _ fun i _ =>
    (measurable_pi_apply i).fst)).prodMk
    (measurable_const.add (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).snd))

lemma markPairEndpoint_cons (n : ℕ) (z₁ z₂ a₁ a₂ : Fin N → ℝ)
    (w : Fin n → (Fin N → ℝ) × (Fin N → ℝ)) :
    markPairEndpoint (n+1) z₁ z₂ (Fin.cons (a₁,a₂) w) =
      markPairEndpoint n (z₁+a₁) (z₂+a₂) w := by
  simp only [markPairEndpoint,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,add_assoc]

lemma integral_markStateKernel (κ : Kernel (Fin N → ℝ) (Fin N → ℝ))
    [IsMarkovKernel κ] (z : Fin N → ℝ) (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) :
    (∫ y, F y ∂markStateKernel κ z) = ∫ a, F (z+a) ∂κ z := by
  rw [markStateKernel_apply]
  exact integral_map (show AEMeasurable (fun a : Fin N → ℝ => z+a) (κ z) from
    (measurable_const.add measurable_id).aemeasurable) hF.aestronglyMeasurable

lemma integral_markStateParallel (κ : Kernel (Fin N → ℝ) (Fin N → ℝ))
    [IsMarkovKernel κ] (z₁ z₂ : Fin N → ℝ)
    (F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ) (hF : Measurable F)
    {C : ℝ} (hB : ∀ y, |F y| ≤ C) :
    (∫ y, F y ∂(markStateKernel κ ∥ₖ markStateKernel κ) (z₁,z₂)) =
      ∫ a₁, ∫ a₂, F (z₁+a₁,z₂+a₂) ∂κ z₂ ∂κ z₁ := by
  have h₁ : MeasurePreserving (fun a : Fin N → ℝ => z₁+a) (κ z₁) (markStateKernel κ z₁) :=
    ⟨measurable_const.add measurable_id,(markStateKernel_apply κ z₁).symm⟩
  have h₂ : MeasurePreserving (fun a : Fin N → ℝ => z₂+a) (κ z₂) (markStateKernel κ z₂) :=
    ⟨measurable_const.add measurable_id,(markStateKernel_apply κ z₂).symm⟩
  rw [Kernel.parallelComp_apply]
  rw [← (h₁.prod h₂).hasLaw.integral_comp hF.aestronglyMeasurable]
  apply integral_prod
  exact Integrable.of_bound (hF.comp ((measurable_const.add measurable_fst).prodMk
    (measurable_const.add measurable_snd))).aestronglyMeasurable C
    (ae_of_all _ fun p => by
      simpa only [Real.norm_eq_abs,Function.comp_apply] using
        hB (Prod.map (fun a => z₁+a) (fun a => z₂+a) p))

theorem markPairPathMean_independent_endpoint (n : ℕ)
    (κ : ℕ → Kernel (Fin N → ℝ) (Fin N → ℝ)) [∀ i, IsMarkovKernel (κ i)]
    (z₁ z₂ : Fin N → ℝ) (F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ)
    (hF : Measurable F) {C : ℝ} (hB : ∀ y, |F y| ≤ C) :
    markPairPathMean n κ 0 z₁ z₂ (fun w => F (markPairEndpoint n z₁ z₂ w)) =
      ∫ y, F y ∂(markTailEndpointKernel n κ ∥ₖ markTailEndpointKernel n κ) (z₁,z₂) := by
  induction n generalizing κ z₁ z₂ with
  | zero => simp [markPairPathMean,markPairEndpoint,markTailEndpointKernel,Kernel.id_apply]
  | succ n ih =>
    let η := markTailEndpointKernel n (fun i => κ (i+1))
    have hI : Integrable F (((η ∥ₖ η) ∘ₖ
        (markStateKernel (κ 0) ∥ₖ markStateKernel (κ 0))) (z₁,z₂)) :=
      Integrable.of_bound hF.aestronglyMeasurable C
        (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hB p)
    have hH : Measurable (fun p => ∫ y, F y ∂(η ∥ₖ η) p) :=
      hF.stronglyMeasurable.integral_kernel.measurable
    have hHB : ∀ p, |∫ y, F y ∂(η ∥ₖ η) p| ≤ C := by
      intro p
      simpa only [Real.norm_eq_abs,Measure.real,measure_univ,ENNReal.toReal_one,mul_one] using
        (norm_integral_le_of_norm_le_const (f := F) (C := C) (μ := (η ∥ₖ η) p)
          (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hB y))
    rw [markTailEndpointKernel,← Kernel.parallelComp_comp_parallelComp,
      Kernel.integral_comp hI,integral_markStateParallel (κ 0) z₁ z₂ _ hH hHB]
    simp only [markPairPathMean]
    apply integral_congr_ae
    apply ae_of_all
    intro a₁
    apply integral_congr_ae
    apply ae_of_all
    intro a₂
    simp only [markPairEndpoint_cons]
    exact ih (fun i => κ (i+1)) (z₁+a₁) (z₂+a₂)

theorem markPairPathMean_shared_endpoint (n : ℕ)
    (κ : ℕ → Kernel (Fin N → ℝ) (Fin N → ℝ)) [∀ i, IsMarkovKernel (κ i)]
    (d : Fin (n+1)) (z : Fin N → ℝ) (F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ)
    (hF : Measurable F) {C : ℝ} (hB : ∀ y, |F y| ≤ C) :
    markPairPathMean n κ d.val z z (fun w => F (markPairEndpoint n z z w)) =
      ∫ y, F y ∂markPairEndpointKernel n κ d z := by
  induction n generalizing κ z with
  | zero => simp [markPairPathMean,markPairEndpoint,markPairEndpointKernel,
      Kernel.prod_apply,Kernel.id_apply,Measure.dirac_prod_dirac]
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) d
    · simpa only [Fin.val_zero,markPairEndpointKernel,Fin.cases_zero,Kernel.prod_apply,
        Kernel.parallelComp_apply] using
        markPairPathMean_independent_endpoint (n+1) κ z z F hF hB
    · let η := markPairEndpointKernel n (fun i => κ (i+1)) j
      have hI : Integrable F ((η ∘ₖ markStateKernel (κ 0)) z) :=
        Integrable.of_bound hF.aestronglyMeasurable C
          (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hB p)
      have hH : Measurable (fun p => ∫ y, F y ∂η p) :=
        hF.stronglyMeasurable.integral_kernel.measurable
      simp only [markPairEndpointKernel,Fin.cases_succ,Fin.val_succ]
      rw [Kernel.integral_comp hI,integral_markStateKernel (κ 0) z _ hH]
      simp only [markPairPathMean]
      apply integral_congr_ae
      apply ae_of_all
      intro a
      simp only [markPairEndpoint_cons]
      exact ih (fun i => κ (i+1)) j (z+a)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedSpinLog
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricted spin sums retain the original cube mass. A deterministic
map of slices costs its energy error and the logarithm of its largest fiber. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma restrictedSpinLog_univ {N : ℕ} (H : Spin N → ℝ) :
    restrictedSpinLog Finset.univ H = logPartition H := by
  rw [restrictedSpinLog, logPartition_eq, log_card_spin]

lemma restrictedSpinLog_le_full {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (H : Spin N → ℝ) : restrictedSpinLog S H ≤ logPartition H := by
  rw [← restrictedSpinLog_univ]
  exact restrictedSpinLog_mono hS (Finset.subset_univ S) (fun _ _ => le_rfl)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedFieldTerminal
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual constrained-block terminal payoff. Its prior mass is not
renormalized; the Lipschitz and growth estimates include that fixed mass. -/

noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma restrictedFieldTerminal_le_univ {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (z : Fin N → ℝ) : restrictedFieldTerminal S z ≤ ∑ i, Real.log (Real.cosh (z i)) := by
  rw [restrictedFieldTerminal, ← logPartition_fieldEnergy]
  exact restrictedSpinLog_le_full S hS _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedFieldFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unrestricted recursion and its canonical transition are exactly
products of the scalar field recursions. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma vectorGaussian_shift {N : ℕ} (v : ℝ≥0) (z : Fin N → ℝ) :
    MeasurePreserving (fun w : Fin N → ℝ => z + w)
      (vectorGaussianLaw N v : Measure (Fin N → ℝ))
      (Measure.pi (fun i => gaussianReal (z i) v)) := by
  apply measurePreserving_pi
  intro i
  refine ⟨measurable_const.add measurable_id, ?_⟩
  change (gaussianReal 0 v).map (fun x : ℝ => z i + x) = gaussianReal (z i) v
  simpa only [zero_add] using gaussianReal_map_const_add (μ := 0) (v := v) (z i)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_VectorGaussianTransition
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual vector Gaussian transition for a nonseparable terminal,
including constrained spin blocks. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal BigOperators

namespace InvariantIsing

lemma vectorShiftGaussianKernel_apply (N : ℕ) (v : ℝ≥0) (z : Fin N → ℝ) :
    vectorShiftGaussianKernel N v z = Measure.pi (fun i => gaussianReal (z i) v) := by
  have hg : HasLinearGrowth (fun _ : ℝ => (0 : ℝ)) :=
    ⟨0, 0, le_rfl, le_rfl, fun _ => by simp⟩
  rw [vectorShiftGaussianKernel, fieldVectorTransitionKernel_eq_tilted 0 v _ measurable_const hg]
  simp

lemma vectorGaussian_shift_exp_integrable {N : ℕ} (hN : 0 < N) (a : ℝ) (v : ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (z : Fin N → ℝ) :
    Integrable (fun y => Real.exp (a * F y)) (Measure.pi (fun i => gaussianReal (z i) v)) := by
  rw [← (vectorGaussian_shift v z).map_eq]
  apply (integrable_map_measure (hF.const_mul a).exp.aestronglyMeasurable
    (show AEMeasurable (fun w : Fin N → ℝ => z + w) (vectorGaussianLaw N v : Measure (Fin N → ℝ)) from
      (measurable_const.add measurable_id).aemeasurable)).mpr
  exact integrable_exp_of_linearGrowth _ (vectorGaussianLaw_moments hN v)
    (hF.comp (measurable_const.add measurable_id)) (hG.add_left z) a

lemma vectorGaussianTransition_eq_tilted {N : ℕ} (hN : 0 < N) (a : ℝ) (v : ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (z : Fin N → ℝ) :
    vectorGaussianTransition N a v F hF z =
      (Measure.pi (fun i => gaussianReal (z i) v)).tilted (fun y => a * F y) := by
  change normalizeMass ((vectorShiftGaussianKernel N v z).withDensity _) = _
  rw [vectorShiftGaussianKernel_apply]
  exact normalizeMass_exp _ _ (hF.const_mul a)
    (vectorGaussian_shift_exp_integrable hN a v F hF hG z)

lemma vectorGaussianTransition_eq_map {N : ℕ} (hN : 0 < N) (a : ℝ) (v : ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (z : Fin N → ℝ) :
    vectorGaussianTransition N a v F hF z =
      ((vectorGaussianLaw N v : Measure (Fin N → ℝ)).tilted
        (fun w => a * F (z + w))).map (fun w => z + w) := by
  rw [vectorGaussianTransition_eq_tilted hN a v F hF hG z]
  have he := cavity_tilt_map (vectorGaussianLaw N v : Measure (Fin N → ℝ))
    (fun w => z + w) (measurable_const.add measurable_id) (fun y => a * F y) (hF.const_mul a)
  rw [(vectorGaussian_shift v z).map_eq] at he
  exact he.symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_VectorTerminalCascade
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ancestor kernels for the two finite-dimensional Gaussian field terminals. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal ENNReal
namespace InvariantIsing

lemma vectorTerminalMultiplier_moment {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents n b)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (i : ℕ) (z : Fin N → ℝ) :
    (∫⁻ a, ENNReal.ofReal (vectorTerminalMultiplier N n b v F i (z,a)^b i)
      ∂(vectorGaussianLaw N (v i) : Measure (Fin N → ℝ))) = 1 := by
  have hadm := backwardValue_linearGrowth_moments n b (fun j => vectorGaussianLaw N (v j))
    (fun j _ => vectorGaussianLaw_moments hN (v j)) hF hG (fun j hj => (hb.1 j hj).1)
  exact backwardValue_multiplier_moment_admissible n b (fun j => vectorGaussianLaw N (v j))
    (fun _ p => p.1+p.2) F (fun j hj => (hb.1 j hj).1) hadm i z

lemma vectorTerminalAncestorKernel_markov {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents n b)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (i : ℕ) :
    IsMarkovKernel (vectorTerminalAncestorKernel N n b v F hF i) := by
  constructor
  intro z
  constructor
  change ((vectorGaussianLaw N (v i) : Measure (Fin N → ℝ)).withDensity _) Set.univ = 1
  rw [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ]
  exact vectorTerminalMultiplier_moment hN n b v hb F hF hG i z

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_VectorTerminalTransition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized ancestor increments induce the actual Gaussian field transition. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

lemma vectorTerminalBackward_regular {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents n b)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (i : ℕ) :
    Measurable (vectorTerminalBackward N n b v F i) ∧ HasLinearGrowth (vectorTerminalBackward N n b v F i) := by
  refine ⟨measurable_vectorTerminalBackward N n b v F hF i,?_⟩
  exact cascadeRecursion_linearGrowth (n-i) (fun j => b (i+j))
    (fun j => vectorGaussianLaw N (v (i+j)))
    (fun j _ => vectorGaussianLaw_moments hN (v (i+j))) hF hG
    (fun j hj => (hb.1 (i+j) (by omega)).1)

lemma vectorTerminalAncestorKernel_eq_tilted {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents n b)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (i : ℕ) (hi : i < n) (z : Fin N → ℝ) :
    vectorTerminalAncestorKernel N n b v F hF i z =
      (vectorGaussianLaw N (v i) : Measure (Fin N → ℝ)).tilted
        (fun a => b i * vectorTerminalBackward N n b v F (i+1) (z+a)) := by
  have hint := backwardValue_linearGrowth_moments n b (fun j => vectorGaussianLaw N (v j))
    (fun j _ => vectorGaussianLaw_moments hN (v j)) hF hG (fun j hj => (hb.1 j hj).1) i hi z
  have hp := IsingPerceptron.integral_exp_pos (vectorGaussianLaw N (v i) : Measure (Fin N → ℝ))
    (fun a => vectorTerminalBackward N n b v F (i+1) (z+a)) hint
  have hd : vectorTerminalAncestorKernel N n b v F hF i z =
      (vectorGaussianLaw N (v i) : Measure (Fin N → ℝ)).withDensity
        (fun a => ENNReal.ofReal (Real.exp (b i *
          (vectorTerminalBackward N n b v F (i+1) (z+a) - vectorTerminalBackward N n b v F i z)))) := by
    change Measure.withDensity _ _ = _
    congr 1
    funext a
    simp only [vectorTerminalMultiplier,vectorTerminalUpdate,stoppedUpdate,hi,ite_true, if_true,← Real.exp_mul]
    rw [mul_comm]
  have hs : vectorTerminalBackward N n b v F i z =
      logMean (b i) (vectorGaussianLaw N (v i) : Measure (Fin N → ℝ))
        (fun a => vectorTerminalBackward N n b v F (i+1) (z+a)) :=
    backwardValue_step n b (fun j => vectorGaussianLaw N (v j)) (fun _ p => p.1+p.2) F hi z
  rw [hd,hs]
  unfold Measure.tilted
  congr 1
  funext a
  congr 1
  have hx (x y : ℝ) : b i * (x - Real.log y / b i) = b i*x - Real.log y := by
    field_simp [(hb.1 i hi).1.ne']
  rw [logMean,hx,Real.exp_sub,Real.exp_log hp]

lemma vectorTerminalAncestorKernel_add {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents n b)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (i : ℕ) (hi : i < n) (z : Fin N → ℝ) :
    (vectorTerminalAncestorKernel N n b v F hF i z).map (fun a => z+a) =
      vectorGaussianTransition N (b i) (v i) (vectorTerminalBackward N n b v F (i+1))
        (measurable_vectorTerminalBackward N n b v F hF (i+1)) z := by
  rw [vectorTerminalAncestorKernel_eq_tilted hN n b v hb F hF hG i hi z]
  exact (vectorGaussianTransition_eq_map hN (b i) (v i) _
    (measurable_vectorTerminalBackward N n b v F hF (i+1))
    (vectorTerminalBackward_regular hN n b v hb F hF hG (i+1)).2 z).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_VectorTerminalShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing the first level preserves every later conditional ancestor kernel. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

lemma vectorTerminalBackward_shift (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (i : ℕ) :
    vectorTerminalBackward N (n+1) b v F (i+1) =
      vectorTerminalBackward N n (fun j => b (j+1)) (fun j => v (j+1)) F i := by
  simp only [vectorTerminalBackward,backwardValue,Nat.add_sub_add_right]
  congr 1 <;> simp only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

lemma vectorTerminalAncestorKernel_shift (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (i : ℕ) :
    vectorTerminalAncestorKernel N (n+1) b v F hF (i+1) =
      vectorTerminalAncestorKernel N n (fun j => b (j+1)) (fun j => v (j+1)) F hF i := by
  ext z : 1
  change Measure.withDensity _ _ = Measure.withDensity _ _
  congr 1
  funext a
  simp only [vectorTerminalMultiplier,vectorTerminalUpdate,stoppedUpdate,
    Nat.add_lt_add_iff_right,vectorTerminalBackward_shift]

lemma vectorTerminalBackward_one (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) :
    vectorTerminalBackward N (n+1) b v F 1 =
      cascadeRecursion n (fun i => b (i+1)) (fun i => vectorGaussianLaw N (v (i+1)))
        (fun _ p => p.1+p.2) F := by
  simp only [vectorTerminalBackward,backwardValue,Nat.add_sub_cancel,Nat.add_comm 1]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_ProbabilityMedian
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Existence of a median for every real probability law, including laws with atoms. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace InvariantIsing

theorem probability_real_median (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ∃ m : ℝ, (1/2:ℝ) ≤ ν.real (Iic m) ∧ (1/2:ℝ) ≤ ν.real (Ici m) := by
  let F := cdf ν
  let S : Set ℝ := {x | (1/2:ℝ) ≤ F x}
  have htop : ∃ x : ℝ, (1/2:ℝ) < F x := by
    have h := (tendsto_cdf_atTop ν).eventually (lt_mem_nhds (by norm_num : (1/2:ℝ) < 1))
    exact h.exists
  have hbot : ∃ x : ℝ, F x < (1/2:ℝ) := by
    have h := (tendsto_cdf_atBot ν).eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))
    exact h.exists
  obtain ⟨b,hb⟩ := hbot
  have hne : S.Nonempty := by obtain ⟨x,hx⟩ := htop; exact ⟨x,hx.le⟩
  have hbb : BddBelow S := by
    refine ⟨b,?_⟩
    intro x hx
    by_contra h
    have hm := (monotone_cdf ν) (le_of_not_ge h)
    change (1/2:ℝ) ≤ F x at hx
    exact (not_le_of_gt hb) (hx.trans hm)
  let m := sInf S
  have hright (x : ℝ) (hx : m < x) : (1/2:ℝ) ≤ F x := by
    obtain ⟨y,hy,hyx⟩ := exists_lt_of_csInf_lt hne hx
    exact hy.trans ((monotone_cdf ν) hyx.le)
  have hleft (x : ℝ) (hx : x < m) : F x < (1/2:ℝ) := by
    by_contra h
    have hxS : x ∈ S := le_of_not_gt h
    exact (not_le_of_gt hx) (csInf_le hbb hxS)
  have hfm : (1/2:ℝ) ≤ F m := by
    apply ge_of_tendsto ((F.right_continuous m).mono Ioi_subset_Ici_self)
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hright x hx
  have hfl : Function.leftLim F m ≤ (1/2:ℝ) := by
    apply le_of_tendsto (F.mono.tendsto_leftLim m)
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hleft x hx).le
  refine ⟨m,?_,?_⟩
  · simpa only [F,cdf_eq_real] using hfm
  · have he : ν (Ici m) = ENNReal.ofReal (1-Function.leftLim F m) := by
      rw [← measure_cdf ν]
      exact (cdf ν).measure_Ici (tendsto_cdf_atTop ν) m
    rw [Measure.real,he,ENNReal.toReal_ofReal (by linarith)]
    linarith

theorem measurable_median {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f) :
    ∃ m : ℝ, (1/2:ℝ) ≤ μ.real {ω | f ω ≤ m} ∧ (1/2:ℝ) ≤ μ.real {ω | m ≤ f ω} := by
  haveI : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  obtain ⟨m,hm1,hm2⟩ := probability_real_median (μ.map f)
  refine ⟨m,?_,?_⟩
  · rw [map_measureReal_apply hf measurableSet_Iic] at hm1
    exact hm1
  · rw [map_measureReal_apply hf measurableSet_Ici] at hm2
    exact hm2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianMedianTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conversion of two Gaussian tails about a center to tails about any median. -/
noncomputable section
open MeasureTheory Set
namespace InvariantIsing

theorem gaussian_median_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (c m k : ℝ) (hk : 0 < k)
    (hm1 : (1/2:ℝ) ≤ μ.real {ω | f ω ≤ m})
    (hm2 : (1/2:ℝ) ≤ μ.real {ω | m ≤ f ω})
    (hplus : ∀ r > 0, μ.real {ω | r ≤ f ω-c} ≤ Real.exp (-k*r^2))
    (hminus : ∀ r > 0, μ.real {ω | r ≤ c-f ω} ≤ Real.exp (-k*r^2))
    {r : ℝ} (hr : 0 < r) :
    μ.real {ω | r ≤ |f ω-m|} ≤ Real.exp 1*Real.exp (-k*r^2/8) := by
  let a := Real.sqrt (2/k)
  have ha : 0 < a := Real.sqrt_pos.mpr (div_pos (by norm_num) hk)
  have ha2 : a^2 = 2/k := Real.sq_sqrt (div_pos (by norm_num) hk).le
  have hka : k*a^2 = 2 := by rw [ha2]; field_simp
  have hexp : Real.exp (-2) < (1/2:ℝ) := by
    have he := Real.add_one_le_exp (2:ℝ)
    have hp := Real.exp_pos (-2)
    have hm : Real.exp (-2)*Real.exp 2 = 1 := by rw [← Real.exp_add]; norm_num
    nlinarith
  have hpa : μ.real {ω | a ≤ f ω-c} < (1/2:ℝ) := by
    have h := hplus a ha
    have he : -k*a^2 = -(2:ℝ) := by nlinarith [hka]
    rw [he] at h
    exact h.trans_lt hexp
  have hma : μ.real {ω | a ≤ c-f ω} < (1/2:ℝ) := by
    have h := hminus a ha
    have he : -k*a^2 = -(2:ℝ) := by nlinarith [hka]
    rw [he] at h
    exact h.trans_lt hexp
  have hmc : |m-c| ≤ a := by
    apply abs_le.mpr
    constructor
    · by_contra h
      have hs : {ω | f ω ≤ m} ⊆ {ω | a ≤ c-f ω} := by
        intro ω hω
        simp only [mem_ofPred_eq] at *
        linarith
      exact (not_lt_of_ge (hm1.trans (measureReal_mono hs))) hma
    · by_contra h
      have hs : {ω | m ≤ f ω} ⊆ {ω | a ≤ f ω-c} := by
        intro ω hω
        simp only [mem_ofPred_eq] at *
        linarith
      exact (not_lt_of_ge (hm2.trans (measureReal_mono hs))) hpa
  by_cases hsmall : r ≤ 2*a
  · have hkr : k*r^2/8 ≤ 1 := by
      have hsq : r^2 ≤ 4*a^2 := by nlinarith
      have hm := mul_le_mul_of_nonneg_left hsq hk.le
      nlinarith [hka]
    have hex : 1 ≤ Real.exp 1*Real.exp (-k*r^2/8) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by linarith)
    exact measureReal_le_one.trans hex
  · have hhalf : 0 < r/2 := half_pos hr
    have hs : {ω | r ≤ |f ω-m|} ⊆ {ω | r/2 ≤ |f ω-c|} := by
      intro ω hω
      have htri : |f ω-m| ≤ |f ω-c|+|m-c| := by
        simpa only [sub_add_sub_cancel,abs_sub_comm c m] using abs_add_le (f ω-c) (c-m)
      simp only [mem_ofPred_eq] at *
      linarith
    have he : {ω | r/2 ≤ |f ω-c|} =
        {ω | r/2 ≤ f ω-c} ∪ {ω | r/2 ≤ c-f ω} := by
      ext ω
      simp only [mem_ofPred_eq,mem_union,le_abs,neg_sub]
    have ht : μ.real {ω | r/2 ≤ |f ω-c|} ≤ 2*Real.exp (-k*(r/2)^2) := by
      rw [he]
      have hu := measureReal_union_le (μ := μ) {ω | r/2 ≤ f ω-c} {ω | r/2 ≤ c-f ω}
      linarith [hplus (r/2) hhalf,hminus (r/2) hhalf]
    calc
      _ ≤ μ.real {ω | r/2 ≤ |f ω-c|} := measureReal_mono hs
      _ ≤ 2*Real.exp (-k*(r/2)^2) := ht
      _ ≤ Real.exp 1*Real.exp (-k*r^2/8) := by
        apply mul_le_mul
        · simpa only [show (1:ℝ)+1=2 by norm_num] using Real.add_one_le_exp (1:ℝ)
        · apply Real.exp_le_exp.mpr
          nlinarith [mul_nonneg hk.le (sq_nonneg r)]
        · exact (Real.exp_pos _).le
        · exact (Real.exp_pos _).le

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_DerivativeComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A derivative comparison obtained from pointwise increments. -/
noncomputable section
open Filter
open scoped Topology
namespace InvariantIsing

theorem norm_derivative_le_of_increment_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → E} {g : ℝ → F} {f' : E} {g' : F} {x L : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x)
    (h : ∀ t, ‖f t-f x‖ ≤ L*‖g t-g x‖) : ‖f'‖ ≤ L*‖g'‖ := by
  apply le_of_tendsto_of_tendsto hf.tendsto_slope.norm (hg.tendsto_slope.norm.const_mul L)
  apply Eventually.of_forall
  intro t
  simp only [slope_def_module,norm_smul]
  calc
    ‖(t-x)⁻¹‖*‖f t-f x‖ ≤ ‖(t-x)⁻¹‖*(L*‖g t-g x‖) :=
      mul_le_mul_of_nonneg_left (h t) (norm_nonneg _)
    _ = L*(‖(t-x)⁻¹‖*‖g t-g x‖) := by ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarFrobeniusBracket
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact Frobenius bracket contraction for the special orthogonal algebra. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

lemma matrixFrobeniusPair_self {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    matrixFrobeniusPair A A = ∑ i, ∑ j, (A i j)^2 := by
  simp only [matrixFrobeniusPair,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,
    Matrix.transpose_apply,pow_two]
  exact Finset.sum_comm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPlaneFrame
attribute [-simp] _root_.OAI.InvariantIsing.matrixPolynomialDerivation_plane_X
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coordinate-plane frame identities in the skew matrix space. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

lemma planeGenerator_swap {N : ℕ} (i j : Fin N) :
    planeGenerator j i = -planeGenerator i j := by
  simp only [planeGenerator,neg_sub]

lemma sum_entry_planeGenerator {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    (∑ i, ∑ j, A i j • planeGenerator i j) = A-A.transpose := by
  classical
  ext k l
  simp only [Matrix.sum_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
    planeGenerator,Matrix.single_apply,mul_sub,Finset.sum_sub_distrib]
  simp [ite_and,Matrix.transpose_apply]

lemma matrixFrobeniusPair_eq_sum {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℝ) :
    matrixFrobeniusPair A B = ∑ i, ∑ j, A i j*B i j := by
  simp only [matrixFrobeniusPair,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,
    Matrix.transpose_apply]
  exact Finset.sum_comm

/-- A linear functional on skew matrices is represented by its plane coordinates. -/
lemma plane_functional_representation {N : ℕ}
    (ell : Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] ℝ)
    (B : Matrix (Fin N) (Fin N) ℝ) (hB : B.transpose = -B) :
    matrixFrobeniusPair (Matrix.of fun i j => ell (planeGenerator i j)) B = 2*ell B := by
  have h := congrArg ell (sum_entry_planeGenerator B)
  simp only [map_sum,map_smul,map_sub,hB,map_neg,smul_eq_mul] at h
  rw [matrixFrobeniusPair_eq_sum]
  calc
    (∑ i, ∑ j, ell (planeGenerator i j)*B i j) =
        ∑ i, ∑ j, B i j*ell (planeGenerator i j) := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _; ring
    _ = 2*ell B := by linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialCurve
attribute [-instance] _root_.OAI.InvariantIsing.haarPolynomialSpace_finite
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialCoordinateEval_apply _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixPolynomialOperator_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluation of polynomial Lie derivatives on genuine matrix curves. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

theorem hasDerivAt_matrixPolynomialEval {N : ℕ}
    (p : MatrixPolynomial N) (M : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (A : Matrix (Fin N) (Fin N) ℝ) (t : ℝ)
    (hM : ∀ i j, HasDerivAt (fun s => M s i j) ((A*M t) i j) t) :
    HasDerivAt (fun s => matrixPolynomialEval (M s) p)
      (matrixPolynomialEval (M t) (matrixPolynomialDerivation A p)) t := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using hasDerivAt_const t c
  | add p q hp hq =>
    convert hp.add hq using 1
    all_goals try with_reducible_and_instances rfl
    all_goals simp only [map_add]
    all_goals rfl
  | mul_X p ij hp =>
    rcases ij with ⟨i,j⟩
    have hx : matrixPolynomialEval (M t)
        (matrixPolynomialDerivation A (X (i,j))) = (A*M t) i j := by
      simp only [matrixPolynomialDerivation_X,map_sum,map_smul,
        matrixPolynomialEval_X,smul_eq_mul,Matrix.mul_apply]
    convert hp.mul (hM i j) using 1
    all_goals try with_reducible_and_instances rfl
    · simp only [map_mul,matrixPolynomialEval_X]
      rfl
    · rw [Derivation.leibniz,smul_eq_mul,smul_eq_mul,map_add,map_mul,map_mul,
        hx,matrixPolynomialEval_X]
      ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarContinuousDerivative
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact domination for continuous derivatives along actual Haar rotations. -/
noncomputable section
open Matrix MeasureTheory
namespace InvariantIsing

lemma continuous_haar_integrable {N : ℕ} (μ : Measure (SpecialOrthogonal N)) [IsFiniteMeasure μ]
    (f : SpecialOrthogonal N → ℝ) (hf : Continuous f) : Integrable f μ := by
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.measurable.aestronglyMeasurable B
    (ae_of_all μ fun U => hB U (Set.mem_univ U))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialKernel
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite polynomial averaging kernels on the actual special orthogonal group. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory
open scoped BigOperators
namespace InvariantIsing

lemma continuous_haarKernelAtom {N : ℕ} (a : Option (Fin N × Fin N)) :
    Continuous (fun V : SpecialOrthogonal N => haarKernelAtom V a) := by
  cases a with
  | none => exact continuous_const
  | some ij =>
    exact (continuous_apply ij.2).comp
      ((continuous_apply ij.1).comp continuous_subtype_val)

lemma haarKernelBase_sum {N : ℕ} (U V : SpecialOrthogonal N) :
    haarKernelBase U V = ∑ a : Option (Fin N × Fin N),
      haarKernelAtom V a * haarPolynomialValue (haarPolynomialAtom a) U := by
  simp only [Fintype.sum_option,haarKernelAtom,haarPolynomialAtom,
    haarPolynomialValue,map_one,mul_one,matrixPolynomialEval_X,Fintype.sum_prod_type]
  unfold haarKernelBase
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem haarKernelAverage_value {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsFiniteMeasure μ] (f : SpecialOrthogonal N → ℝ) (hf : Continuous f)
    (n : ℕ) (U : SpecialOrthogonal N) :
    haarPolynomialValue (haarKernelAverage μ f n) U =
      ∫ V, f V * (haarKernelBase U V)^n ∂μ := by
  have hi (w : Fin n → Option (Fin N × Fin N)) :
      Integrable (fun V => f V * ∏ k, haarKernelAtom V (w k)) μ :=
    continuous_haar_integrable μ _ (hf.mul (continuous_finsetProd _ fun k _ =>
      continuous_haarKernelAtom (w k)))
  simp only [haarKernelAverage,haarPolynomialValue,map_sum,map_smul,
    smul_eq_mul,haarPolynomialWord,map_prod]
  simp_rw [← integral_mul_const]
  rw [← integral_finsetSum _ (fun w _ => (hi w).mul_const _)]
  apply integral_congr_ae
  exact ae_of_all μ fun V => by
    change (∑ w : Fin n → Option (Fin N × Fin N),
      (f V * ∏ k, haarKernelAtom V (w k)) *
        ∏ k, matrixPolynomialEval (U : Matrix (Fin N) (Fin N) ℝ) (haarPolynomialAtom (w k))) =
      f V * haarKernelBase U V ^ n
    rw [haarKernelBase_sum,Fintype.sum_pow]
    simp only [Finset.mul_sum,Finset.prod_mul_distrib,mul_assoc]
    rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarKernelGeometry
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The averaging kernel peaks exactly at coincident orthogonal matrices. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory
open scoped BigOperators
namespace InvariantIsing

lemma specialOrthogonal_sum_sq {N : ℕ} (U : SpecialOrthogonal N) :
    (∑ i, ∑ j, ((U : Matrix (Fin N) (Fin N) ℝ) i j)^2) = N := by
  rw [← matrixFrobeniusPair_self]
  unfold matrixFrobeniusPair
  rw [(Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mp
    (Matrix.mem_specialOrthogonalGroup_iff.mp U.property).1]
  simp

lemma haarKernelBase_dist {N : ℕ} (U V : SpecialOrthogonal N) :
    haarKernelBase U V = 2*N-(frobeniusDistance U V)^2/2 := by
  have hU := specialOrthogonal_sum_sq U
  have hV := specialOrthogonal_sum_sq V
  rw [frobeniusDistance,Real.sq_sqrt (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg _)]
  have hsum : (∑ i, ∑ j, ((U : Matrix (Fin N) (Fin N) ℝ) i j-
      (V : Matrix (Fin N) (Fin N) ℝ) i j)^2) = 2*N-
      2*(∑ i, ∑ j, (U : Matrix (Fin N) (Fin N) ℝ) i j*
        (V : Matrix (Fin N) (Fin N) ℝ) i j) := by
    simp only [sub_sq,Finset.sum_add_distrib,Finset.sum_sub_distrib]
    simp_rw [mul_assoc,← Finset.mul_sum]
    rw [hU,hV]
    ring
  rw [hsum]
  unfold haarKernelBase
  ring

lemma haarKernelBase_nonneg {N : ℕ} (U V : SpecialOrthogonal N) :
    0 ≤ haarKernelBase U V := by
  have h := Finset.sum_nonneg (s := Finset.univ) (fun i _ =>
    Finset.sum_nonneg (s := Finset.univ) (fun j _ =>
      sq_nonneg ((U : Matrix (Fin N) (Fin N) ℝ) i j+
        (V : Matrix (Fin N) (Fin N) ℝ) i j)))
  simp only [add_sq,Finset.sum_add_distrib] at h
  simp_rw [mul_assoc,← Finset.mul_sum] at h
  rw [specialOrthogonal_sum_sq U,specialOrthogonal_sum_sq V] at h
  unfold haarKernelBase
  linarith

lemma haarKernelBase_self {N : ℕ} (U : SpecialOrthogonal N) :
    haarKernelBase U U = 2*N := by
  unfold haarKernelBase
  simp_rw [← pow_two]
  rw [specialOrthogonal_sum_sq]
  ring

lemma haarKernelBase_mul_left {N : ℕ} (W U V : SpecialOrthogonal N) :
    haarKernelBase (W*U) (W*V) = haarKernelBase U V := by
  have he : matrixFrobeniusPair
      ((W : Matrix (Fin N) (Fin N) ℝ)*(U : Matrix (Fin N) (Fin N) ℝ))
      ((W : Matrix (Fin N) (Fin N) ℝ)*(V : Matrix (Fin N) (Fin N) ℝ)) =
      matrixFrobeniusPair (U : Matrix (Fin N) (Fin N) ℝ)
        (V : Matrix (Fin N) (Fin N) ℝ) := by
    unfold matrixFrobeniusPair
    rw [Matrix.transpose_mul,mul_assoc,← mul_assoc (W : Matrix (Fin N) (Fin N) ℝ).transpose,
      (Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mp
        (Matrix.mem_specialOrthogonalGroup_iff.mp W.property).1,one_mul]
  unfold haarKernelBase
  rw [← matrixFrobeniusPair_eq_sum,← matrixFrobeniusPair_eq_sum]
  exact congrArg (fun x : ℝ => N+x) he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarFrobeniusGeometry
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unnormalized Frobenius geometry for the averaging and tangent estimates. -/
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.Frobenius
namespace InvariantIsing

lemma frobenius_norm_sq {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    ‖A‖^2 = matrixFrobeniusPair A A := by
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two,Real.norm_eq_abs,sq_abs]
  have hs : 0 ≤ ∑ i : Fin N, ∑ j : Fin N, (A i j)^2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [← Real.sqrt_eq_rpow,Real.sq_sqrt hs,matrixFrobeniusPair_self]

lemma frobeniusDistance_eq_norm {N : ℕ} (U V : SpecialOrthogonal N) :
    frobeniusDistance U V = ‖(U : Matrix (Fin N) (Fin N) ℝ)-V‖ := by
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two,Real.norm_eq_abs,sq_abs,Matrix.sub_apply]
  exact Real.sqrt_eq_rpow _

lemma frobenius_norm_mul_orthogonal {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (U : SpecialOrthogonal N) : ‖A*(U : Matrix (Fin N) (Fin N) ℝ)‖ = ‖A‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [frobenius_norm_sq,frobenius_norm_sq]
  unfold matrixFrobeniusPair
  rw [Matrix.transpose_mul,Matrix.trace_mul_cycle]
  rw [mul_assoc A U (U : Matrix (Fin N) (Fin N) ℝ).transpose,
    (Matrix.mem_orthogonalGroup_iff (Fin N) ℝ).mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp U.property).1,mul_one,Matrix.trace_mul_comm]

lemma frobeniusDistance_mul_left {N : ℕ} (W U V : SpecialOrthogonal N) :
    frobeniusDistance (W*U) (W*V) = frobeniusDistance U V := by
  have h := congrArg (fun x : ℝ => 2*N-x) (haarKernelBase_mul_left W U V)
  rw [haarKernelBase_dist,haarKernelBase_dist] at h
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mp
  change (frobeniusDistance (W*U) (W*V))^2 = (frobeniusDistance U V)^2
  linarith

lemma frobeniusDistance_comm {N : ℕ} (U V : SpecialOrthogonal N) :
    frobeniusDistance U V = frobeniusDistance V U := by
  rw [frobeniusDistance_eq_norm,frobeniusDistance_eq_norm,← norm_neg,neg_sub]

lemma frobeniusDistance_mul_right {N : ℕ} (U V W : SpecialOrthogonal N) :
    frobeniusDistance (U*W) (V*W) = frobeniusDistance U V := by
  rw [frobeniusDistance_eq_norm,frobeniusDistance_eq_norm]
  change ‖(U : Matrix (Fin N) (Fin N) ℝ)*W-(V : Matrix (Fin N) (Fin N) ℝ)*W‖ = _
  rw [← sub_mul,frobenius_norm_mul_orthogonal]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarLipschitzContinuity
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frobenius-Lipschitz observables are continuous in the matrix-group topology. -/
noncomputable section
open Matrix Filter
open scoped Topology
namespace InvariantIsing

lemma continuous_frobeniusDistance_right {N : ℕ} (U : SpecialOrthogonal N) :
    Continuous (fun V => frobeniusDistance V U) := by
  have he (i j : Fin N) : Continuous (fun V : SpecialOrthogonal N =>
      (V : Matrix (Fin N) (Fin N) ℝ) i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  unfold frobeniusDistance
  apply Real.continuous_sqrt.comp
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    ((he i j).sub continuous_const).pow 2

lemma frobeniusDistance_self {N : ℕ} (U : SpecialOrthogonal N) : frobeniusDistance U U = 0 := by
  simp [frobeniusDistance]

theorem continuous_of_frobenius_lipschitz {N : ℕ} (f : SpecialOrthogonal N → ℝ) (L : ℝ)
    (hf : ∀ U V, |f U-f V| ≤ L*frobeniusDistance U V) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro U
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun V => norm_nonneg _) (fun V => by simpa only [Real.norm_eq_abs] using hf V U)
  have hh := ((continuous_frobeniusDistance_right U).tendsto U).const_mul L
  simpa only [frobeniusDistance_self,mul_zero] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarKernelConvolution
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Haar convolution by a positive polynomial kernel preserves Lipschitz constants. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Set
open scoped BigOperators
namespace InvariantIsing

lemma continuous_haarKernelBase {N : ℕ} (U : SpecialOrthogonal N) :
    Continuous (haarKernelBase U) := by
  unfold haarKernelBase
  apply continuous_const.add
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact continuous_const.mul ((continuous_apply j).comp
    ((continuous_apply i).comp continuous_subtype_val))

lemma haarKernelMass_pos {N : ℕ} (hN : 0 < N) (μ : Measure (SpecialOrthogonal N))
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] (n : ℕ) :
    0 < haarKernelMass μ n := by
  apply integral_pos_of_integrable_nonneg_nonzero (x := (1 : SpecialOrthogonal N))
    ((continuous_haarKernelBase 1).pow n)
    (continuous_haar_integrable μ _ ((continuous_haarKernelBase 1).pow n))
    (fun V => pow_nonneg (haarKernelBase_nonneg 1 V) n)
  change (haarKernelBase 1 1)^n ≠ 0
  rw [haarKernelBase_self]
  exact (pow_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hN)) n).ne'

lemma haarKernelAverage_convolution {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] (f : SpecialOrthogonal N → ℝ)
    (hf : Continuous f) (n : ℕ) (U : SpecialOrthogonal N) :
    haarPolynomialValue (haarKernelAverage μ f n) U =
      ∫ V, f (U*V)*(haarKernelBase 1 V)^n ∂μ := by
  rw [haarKernelAverage_value μ f hf]
  have h := integral_mul_left_eq_self (μ := μ)
    (fun V => f V*(haarKernelBase U V)^n) U
  rw [← h]
  apply integral_congr_ae
  exact ae_of_all μ fun V => by
    dsimp only
    rw [show haarKernelBase U (U*V) = haarKernelBase 1 V by
      simpa only [mul_one] using haarKernelBase_mul_left U 1 V]

theorem haarKernelApprox_lipschitz {N : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (f : SpecialOrthogonal N → ℝ) (hf : Continuous f) (L : ℝ)
    (hL : ∀ U V, |f U-f V| ≤ L*frobeniusDistance U V) (n : ℕ)
    (U V : SpecialOrthogonal N) :
    |haarPolynomialValue (haarKernelApprox μ f n) U-
      haarPolynomialValue (haarKernelApprox μ f n) V| ≤ L*frobeniusDistance U V := by
  have hZ := haarKernelMass_pos hN μ n
  let k (W : SpecialOrthogonal N) := (haarKernelBase 1 W)^n
  have hk : Continuous k := (continuous_haarKernelBase 1).pow n
  have hi (U : SpecialOrthogonal N) : Integrable (fun W => f (U*W)*k W) μ :=
    continuous_haar_integrable μ _ ((hf.comp (continuous_const.mul continuous_id)).mul hk)
  have he (U : SpecialOrthogonal N) : haarPolynomialValue (haarKernelApprox μ f n) U =
      (haarKernelMass μ n)⁻¹*(∫ W, f (U*W)*k W ∂μ) := by
    simp only [haarKernelApprox,haarPolynomialValue,map_smul,smul_eq_mul]
    change (haarKernelMass μ n)⁻¹*haarPolynomialValue (haarKernelAverage μ f n) U = _
    rw [haarKernelAverage_convolution μ f hf]
  rw [he U,he V,← mul_sub,abs_mul,abs_of_pos (inv_pos.mpr hZ),← integral_sub (hi U) (hi V)]
  apply (inv_mul_le_iff₀ hZ).mpr
  calc
    |∫ W, (f (U*W)*k W-f (V*W)*k W) ∂μ| ≤
        ∫ W, |f (U*W)*k W-f (V*W)*k W| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ W, (L*frobeniusDistance U V)*k W ∂μ := by
      apply integral_mono
      · exact ((hi U).sub (hi V)).abs
      · exact (continuous_haar_integrable μ _ hk).const_mul _
      · intro W
        dsimp only
        rw [← sub_mul,abs_mul,abs_of_nonneg (pow_nonneg (haarKernelBase_nonneg 1 W) n)]
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (haarKernelBase_nonneg 1 W) n)
        exact (hL (U*W) (V*W)).trans_eq (by rw [frobeniusDistance_mul_right])
    _ = haarKernelMass μ n*(L*frobeniusDistance U V) := by
      rw [integral_const_mul,mul_comm]
      rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarKernelMass
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative concentration of the positive polynomial kernels near the identity. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Set Filter
open scoped Topology
namespace InvariantIsing

lemma haarKernelMass_lower {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] (b : ℝ) (hb : 0 ≤ b) (n : ℕ) :
    μ.real {V | b < haarKernelBase 1 V} * b^n ≤ haarKernelMass μ n := by
  let S : Set (SpecialOrthogonal N) := {V | b < haarKernelBase 1 V}
  have hS : MeasurableSet S := measurableSet_lt measurable_const (continuous_haarKernelBase 1).measurable
  have hi : Integrable (S.indicator (fun _ => b^n)) μ := (integrable_const _).indicator hS
  have hk := continuous_haar_integrable μ _ ((continuous_haarKernelBase 1).pow n)
  have hle : (∫ V, S.indicator (fun _ => b^n) V ∂μ) ≤ haarKernelMass μ n := by
    apply integral_mono hi hk
    intro V
    by_cases hV : V ∈ S
    · rw [Set.indicator_of_mem hV]
      exact pow_le_pow_left₀ hb hV.le n
    · rw [Set.indicator_of_notMem hV]
      exact pow_nonneg (haarKernelBase_nonneg 1 V) n
  simpa only [integral_indicator_const _ hS,smul_eq_mul] using hle

lemma haarKernel_superlevel_pos {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] {b : ℝ} (hb : b < 2*N) :
    0 < μ.real {V | b < haarKernelBase 1 V} := by
  have hm : 0 < μ {V | b < haarKernelBase 1 V} := IsOpen.measure_pos μ
    (isOpen_lt continuous_const (continuous_haarKernelBase 1))
    ⟨1,by simpa only [mem_ofPred_eq,haarKernelBase_self] using hb⟩
  exact ENNReal.toReal_pos hm.ne' (measure_ne_top μ _)

theorem haarKernelMass_ratio_tendsto_zero {N : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (a : ℝ) (ha : 0 ≤ a) (haN : a < 2*N) :
    Tendsto (fun n : ℕ => a^n/haarKernelMass μ n) atTop (𝓝 0) := by
  let b := (a+2*N)/2
  have hab : a < b := by dsimp [b] <;> linarith
  have hbN : b < 2*N := by dsimp [b] <;> linarith
  have hb : 0 < b := ha.trans_lt hab
  let m := μ.real {V | b < haarKernelBase 1 V}
  have hm : 0 < m := haarKernel_superlevel_pos μ hbN
  have hr : a/b < 1 := (div_lt_one hb).mpr hab
  have hlim : Tendsto (fun n : ℕ => (a/b)^n/m) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg ha hb.le) hr).div_const m
  apply squeeze_zero (fun n => div_nonneg (pow_nonneg ha n) (haarKernelMass_pos hN μ n).le) _ hlim
  intro n
  have hl := haarKernelMass_lower μ b hb.le n
  have hZ := haarKernelMass_pos hN μ n
  have hp := pow_pos hb n
  rw [div_pow]
  apply (div_le_div_iff₀ hZ hm).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hp).mpr
  calc
    (a^n*m)*b^n = a^n*(m*b^n) := by ring
    _ ≤ a^n*haarKernelMass μ n := mul_le_mul_of_nonneg_left hl (pow_nonneg ha n)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarKernelApproximation
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialCoordinateEval_apply _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixPolynomialOperator_apply _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform approximation by positive polynomial Haar convolution. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Set Filter
open scoped Topology
namespace InvariantIsing

theorem haarKernelApprox_error {N : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (f : SpecialOrthogonal N → ℝ) (hf : Continuous f) (B ε a : ℝ)
    (hB : 0 ≤ B) (hfB : ∀ V, |f V| ≤ B) (hε : 0 ≤ ε) (ha : 0 ≤ a)
    (hloc : ∀ U V, a < haarKernelBase 1 V → |f (U*V)-f U| ≤ ε)
    (n : ℕ) (U : SpecialOrthogonal N) :
    |haarPolynomialValue (haarKernelApprox μ f n) U-f U| ≤
      ε+2*B*(a^n/haarKernelMass μ n) := by
  let Z := haarKernelMass μ n
  let k (V : SpecialOrthogonal N) := (haarKernelBase 1 V)^n
  have hZ : 0 < Z := haarKernelMass_pos hN μ n
  have hk : Continuous k := (continuous_haarKernelBase 1).pow n
  have hi : Integrable (fun V => (f (U*V)-f U)*k V) μ :=
    continuous_haar_integrable μ _ (((hf.comp (continuous_const.mul continuous_id)).sub continuous_const).mul hk)
  have he : haarPolynomialValue (haarKernelApprox μ f n) U-f U =
      Z⁻¹*(∫ V, (f (U*V)-f U)*k V ∂μ) := by
    simp only [haarKernelApprox,haarPolynomialValue,map_smul,smul_eq_mul]
    change Z⁻¹*haarPolynomialValue (haarKernelAverage μ f n) U-f U = _
    rw [haarKernelAverage_convolution μ f hf]
    have he' : (∫ V, (f (U*V)-f U)*k V ∂μ) =
        (∫ V, f (U*V)*k V ∂μ)-f U*Z := by
      simp_rw [sub_mul]
      have hi1 : Integrable (fun V => f (U*V)*k V) μ :=
        continuous_haar_integrable μ _ ((hf.comp (continuous_const.mul continuous_id)).mul hk)
      have hi2 : Integrable (fun V => f U*k V) μ :=
        (continuous_haar_integrable μ _ hk).const_mul (f U)
      rw [integral_sub hi1 hi2,integral_const_mul]
      rfl
    rw [he']
    dsimp only [k]
    field_simp
  have hb (V : SpecialOrthogonal N) :
      |(f (U*V)-f U)*k V| ≤ ε*k V+2*B*a^n := by
    rw [abs_mul,abs_of_nonneg (pow_nonneg (haarKernelBase_nonneg 1 V) n)]
    by_cases hV : a < haarKernelBase 1 V
    · have hh := mul_le_mul_of_nonneg_right (hloc U V hV)
        (pow_nonneg (haarKernelBase_nonneg 1 V) n)
      have ht : 0 ≤ 2*B*a^n := by positivity
      exact hh.trans (le_add_of_nonneg_right ht)
    · have hbd : |f (U*V)-f U| ≤ 2*B := (abs_sub (f (U*V)) (f U)).trans (by linarith [hfB (U*V),hfB U])
      have hpow : k V ≤ a^n := pow_le_pow_left₀ (haarKernelBase_nonneg 1 V) (le_of_not_gt hV) n
      have hh := mul_le_mul hbd hpow (pow_nonneg (haarKernelBase_nonneg 1 V) n) (by positivity : 0 ≤ 2*B)
      have ht : 0 ≤ ε*k V := mul_nonneg hε (pow_nonneg (haarKernelBase_nonneg 1 V) n)
      exact hh.trans (le_add_of_nonneg_left ht)
  rw [he,abs_mul,abs_of_pos (inv_pos.mpr hZ)]
  have hI : |∫ V, (f (U*V)-f U)*k V ∂μ| ≤ ε*Z+2*B*a^n := by
    calc
      _ ≤ ∫ V, |(f (U*V)-f U)*k V| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ V, ε*k V+2*B*a^n ∂μ :=
        integral_mono hi.abs (((continuous_haar_integrable μ _ hk).const_mul ε).add (integrable_const _)) hb
      _ = ε*Z+2*B*a^n := by
        rw [integral_add ((continuous_haar_integrable μ _ hk).const_mul ε) (integrable_const _),integral_const_mul]
        simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
        rfl
  calc
    _ ≤ Z⁻¹*(ε*Z+2*B*a^n) := mul_le_mul_of_nonneg_left hI (inv_pos.mpr hZ).le
    _ = ε+2*B*(a^n/Z) := by field_simp

theorem haarKernelApprox_uniform {N : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (f : SpecialOrthogonal N → ℝ) (hf : Continuous f) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ U V, |f U-f V| ≤ L*frobeniusDistance U V) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ U,
      |haarPolynomialValue (haarKernelApprox μ f n) U-f U| ≤ ε := by
  intro ε hε
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  have hfB (V : SpecialOrthogonal N) : |f V| ≤ B := by simpa only [Real.norm_eq_abs] using hB V (mem_univ V)
  have hB0 : 0 ≤ B := (abs_nonneg (f 1)).trans (hfB 1)
  let δ := ε/(2*L)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hL)
  have hδeq : L*δ = ε/2 := by dsimp [δ]; field_simp
  let a := max 0 (2*N-δ^2/2)
  have ha : 0 ≤ a := le_max_left _ _
  have haN : a < 2*N := max_lt (by positivity) (by nlinarith [sq_pos_of_pos hδ])
  have hloc (U V : SpecialOrthogonal N) (hV : a < haarKernelBase 1 V) :
      |f (U*V)-f U| ≤ ε/2 := by
    have hda : 2*N-δ^2/2 < haarKernelBase 1 V := (le_max_right _ _).trans_lt hV
    rw [haarKernelBase_dist] at hda
    have hd : frobeniusDistance 1 V < δ := by nlinarith [Real.sqrt_nonneg (∑ i, ∑ j, ((1 : Matrix (Fin N) (Fin N) ℝ) i j-(V : Matrix (Fin N) (Fin N) ℝ) i j)^2)]
    have hh := hLip (U*V) (U*1)
    rw [frobeniusDistance_mul_left,mul_one,frobeniusDistance_comm V 1] at hh
    have hh' := mul_lt_mul_of_pos_left hd hL
    rw [hδeq] at hh'
    exact hh.trans hh'.le
  have ht : Tendsto (fun n : ℕ => 2*B*(a^n/haarKernelMass μ n)) atTop (𝓝 0) := by
    simpa using (haarKernelMass_ratio_tendsto_zero hN μ a ha haN).const_mul (2*B)
  filter_upwards [ht.eventually (gt_mem_nhds (by linarith : (0:ℝ) < ε/2))] with n hn U
  have hh := haarKernelApprox_error hN μ f hf B (ε/2) a hB0 hfB (by positivity) ha hloc n U
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarFunctionalCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sum of squared Lie brackets, with the precise dimension factor. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

lemma planeFunctionalMatrix_skew {N : ℕ}
    (ell : Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] ℝ) :
    (planeFunctionalMatrix ell).transpose = -planeFunctionalMatrix ell := by
  ext i j
  change ell (planeGenerator j i) = -ell (planeGenerator i j)
  rw [planeGenerator_swap,map_neg]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_SpecialSkewRotation
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.haarPolynomialSpace_finite _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponentiating an arbitrary real skew matrix in the physical group. -/
noncomputable section
open Matrix
open scoped Matrix Matrix.Norms.Frobenius
namespace InvariantIsing

lemma hasDerivAt_specialSkewRotation {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.transpose = -A) (U : SpecialOrthogonal N) :
    HasDerivAt (fun t => ((specialSkewRotation A hA t*U : SpecialOrthogonal N) :
      Matrix (Fin N) (Fin N) ℝ)) (A*(U : Matrix (Fin N) (Fin N) ℝ)) 0 := by
  convert (hasDerivAt_exp_smul_const' A (0:ℝ)).mul_const
    (U : Matrix (Fin N) (Fin N) ℝ) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | simp only [zero_smul,NormedSpace.exp_zero,mul_one]

lemma hasDerivAt_specialSkewRotation_polynomial {N : ℕ} (p : MatrixPolynomial N)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.transpose = -A) (U : SpecialOrthogonal N) :
    HasDerivAt (fun t => matrixPolynomialEval
      ((specialSkewRotation A hA t*U : SpecialOrthogonal N) : Matrix (Fin N) (Fin N) ℝ) p)
      (matrixPolynomialEval (U : Matrix (Fin N) (Fin N) ℝ)
        (matrixPolynomialDerivation A p)) 0 := by
  have hd := hasDerivAt_specialSkewRotation A hA U
  have hh := hasDerivAt_matrixPolynomialEval p
    (fun t => ((specialSkewRotation A hA t*U : SpecialOrthogonal N) : Matrix (Fin N) (Fin N) ℝ))
    A 0 (fun i j => by
      rw [specialSkewRotation_zero,one_mul]
      convert (haarMatrixCoordinate i j).hasFDerivAt.comp_hasDerivAt 0 hd using 1 <;> rfl)
  simpa only [specialSkewRotation_zero,one_mul] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarLipschitzGradient
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Frobenius-Lipschitz polynomial has dimension-free carré-du-champ control. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators Matrix.Norms.Frobenius
namespace InvariantIsing

theorem haarPolynomial_direction_le_lipschitz {N : ℕ} (p : MatrixPolynomial N)
    (L : ℝ) (hp : ∀ U V, |haarPolynomialValue p U-haarPolynomialValue p V| ≤
      L*frobeniusDistance U V) (U : SpecialOrthogonal N)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.transpose = -A) :
    |matrixPolynomialEval (U : Matrix (Fin N) (Fin N) ℝ)
      (matrixPolynomialDerivation A p)| ≤ L*‖A‖ := by
  have hf := hasDerivAt_specialSkewRotation_polynomial p A hA U
  have hg := hasDerivAt_specialSkewRotation A hA U
  have hh := norm_derivative_le_of_increment_bound hf hg (fun t => by
    simpa only [specialSkewRotation_zero,one_mul,Real.norm_eq_abs,← frobeniusDistance_eq_norm,
      haarPolynomialValue]
      using hp (specialSkewRotation A hA t*U) U)
  simpa only [Real.norm_eq_abs,frobenius_norm_mul_orthogonal] using hh

theorem haarPolynomial_gamma_le_lipschitz {N : ℕ} (p : MatrixPolynomial N)
    (L : ℝ) (hL : 0 ≤ L)
    (hp : ∀ U V, |haarPolynomialValue p U-haarPolynomialValue p V| ≤
      L*frobeniusDistance U V) (U : SpecialOrthogonal N) :
    haarPolynomialValue (haarPolynomialGamma p p) U ≤ 4*L^2 := by
  let ell := matrixPolynomialDifferential p (U : Matrix (Fin N) (Fin N) ℝ)
  let A := planeFunctionalMatrix ell
  have hA : A.transpose = -A := planeFunctionalMatrix_skew ell
  have hrepr := plane_functional_representation ell A hA
  have hsq : ‖A‖^2 = haarPolynomialValue (haarPolynomialGamma p p) U := by
    rw [frobenius_norm_sq,matrixFrobeniusPair_self]
    simp only [A,planeFunctionalMatrix,haarPolynomialValue,haarPolynomialGamma,map_sum,map_mul,pow_two]
    rfl
  have he : ‖A‖^2 = 2*ell A := by
    rw [frobenius_norm_sq]
    exact hrepr
  have hd : |ell A| ≤ L*‖A‖ := haarPolynomial_direction_le_lipschitz p L hp U A hA
  have hn : ‖A‖ ≤ 2*L := by nlinarith [norm_nonneg A,le_abs_self (ell A)]
  rw [← hsq]
  nlinarith [norm_nonneg A]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialMoment
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential moments and their derivatives for polynomial observables on SO(N). -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Filter Set
open scoped Topology
namespace InvariantIsing

lemma haarPolynomialMoment_pos {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsProbabilityMeasure μ] (p : MatrixPolynomial N) (t : ℝ) :
    0 < haarPolynomialMoment μ p t :=
  integral_exp_pos (continuous_haar_integrable μ _
    (Real.continuous_exp.comp (continuous_const.mul (continuous_haarPolynomialValue p))))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarUniformMomentLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing polynomial Haar moments through uniform approximation. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Filter Set
open scoped Topology
namespace InvariantIsing

theorem haar_uniform_polynomial_tendsto {N : ℕ} (p : ℕ → MatrixPolynomial N)
    (f : SpecialOrthogonal N → ℝ)
    (hu : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ U, |haarPolynomialValue (p n) U-f U| ≤ ε)
    (U : SpecialOrthogonal N) :
    Tendsto (fun n => haarPolynomialValue (p n) U) atTop (𝓝 (f U)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hu (ε/2) (half_pos hε)] with n hn
  rw [Real.dist_eq]
  exact (hn U).trans_lt (half_lt_self hε)

theorem haar_uniform_polynomial_integrals {N : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsFiniteMeasure μ]
    (p : ℕ → MatrixPolynomial N) (f : SpecialOrthogonal N → ℝ) (hf : Continuous f)
    (hu : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ U, |haarPolynomialValue (p n) U-f U| ≤ ε) :
    Tendsto (fun n => ∫ U, haarPolynomialValue (p n) U ∂μ) atTop (𝓝 (∫ U, f U ∂μ)) ∧
    ∀ t : ℝ, Tendsto (fun n => haarPolynomialMoment μ (p n) t) atTop
      (𝓝 (∫ U, Real.exp (t*f U) ∂μ)) := by
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  have hb : ∀ᶠ n : ℕ in atTop, ∀ U, |haarPolynomialValue (p n) U| ≤ B+1 := by
    filter_upwards [hu 1 zero_lt_one] with n hn U
    have hbu : |f U| ≤ B := by simpa only [Real.norm_eq_abs] using hB U (mem_univ U)
    calc
      |haarPolynomialValue (p n) U| ≤ |haarPolynomialValue (p n) U-f U|+|f U| := by
        simpa only [sub_add_cancel] using abs_add_le (haarPolynomialValue (p n) U-f U) (f U)
      _ ≤ B+1 := by linarith [hn U]
  constructor
  · refine tendsto_integral_filter_of_dominated_convergence (fun _ => B+1)
      (Eventually.of_forall fun n => (continuous_haarPolynomialValue (p n)).measurable.aestronglyMeasurable)
      ?_ (integrable_const _) ?_
    · filter_upwards [hb] with n hn
      exact ae_of_all μ fun U => by simpa only [Real.norm_eq_abs] using hn U
    · exact ae_of_all μ fun U => haar_uniform_polynomial_tendsto p f hu U
  · intro t
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => Real.exp (|t| *(B+1)))
      (Eventually.of_forall fun n => (Real.continuous_exp.comp (continuous_const.mul
        (continuous_haarPolynomialValue (p n)))).measurable.aestronglyMeasurable)
      ?_ (integrable_const _) ?_
    · filter_upwards [hb] with n hn
      apply ae_of_all
      intro U
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      calc
        t*haarPolynomialValue (p n) U ≤ |t*haarPolynomialValue (p n) U| := le_abs_self _
        _ = |t| * |haarPolynomialValue (p n) U| := abs_mul _ _
        _ ≤ |t| *(B+1) := mul_le_mul_of_nonneg_left (hn U) (abs_nonneg _)
    · exact ae_of_all μ fun U => Real.continuous_exp.continuousAt.tendsto.comp
        ((haar_uniform_polynomial_tendsto p f hu U).const_mul t)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarLipschitzMoment
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential moments for all continuous Frobenius-Lipschitz observables. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Filter
open scoped Topology
namespace InvariantIsing

theorem haar_lipschitz_moment_bound {N : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (f : SpecialOrthogonal N → ℝ) (hf : Continuous f) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ U V, |f U-f V| ≤ L*frobeniusDistance U V) {t : ℝ} (ht : 0 < t) :
    (∫ U, Real.exp (t*f U) ∂μ) ≤
      Real.exp ((∫ U, f U ∂μ)*t+(4*L^2)/(2*((N:ℝ)-2))*t^2) := by
  have hN0 : 0 < N := by omega
  let p : ℕ → MatrixPolynomial N := haarKernelApprox μ f
  have hu := haarKernelApprox_uniform hN0 μ f hf L hL hLip
  obtain ⟨hmean,hmoment⟩ := haar_uniform_polynomial_integrals μ p f hf hu
  have hG (n : ℕ) (U : SpecialOrthogonal N) :
      haarPolynomialValue (haarPolynomialGamma (p n) (p n)) U ≤ 4*L^2 :=
    haarPolynomial_gamma_le_lipschitz (p n) L hL.le
      (haarKernelApprox_lipschitz hN0 μ f hf L hLip n) U
  have hbound (n : ℕ) : haarPolynomialMoment μ (p n) t ≤
      Real.exp ((∫ U, haarPolynomialValue (p n) U ∂μ)*t+(4*L^2)/(2*((N:ℝ)-2))*t^2) := by
    have hh := Real.exp_le_exp.mpr
      (haarPolynomialMoment_log_bound hN μ (p n) (4*L^2) (by positivity) (hG n) ht)
    rwa [Real.exp_log (haarPolynomialMoment_pos μ (p n) t)] at hh
  exact le_of_tendsto_of_tendsto (hmoment t)
    (Real.continuous_exp.continuousAt.tendsto.comp ((hmean.mul_const t).add_const _))
    (Eventually.of_forall hbound)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarLipschitzTail
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian tails about the Haar mean for arbitrary Lipschitz observables. -/
noncomputable section
open Matrix MeasureTheory Set
namespace InvariantIsing

theorem haar_lipschitz_chernoff {N : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (f : SpecialOrthogonal N → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ U V, |f U-f V| ≤ L*frobeniusDistance U V)
    (r β : ℝ) (hβ : 0 < β) :
    μ.real {U | r ≤ f U-(∫ V, f V ∂μ)} ≤
      Real.exp ((4*L^2)/(2*((N:ℝ)-2))*β^2-β*r) := by
  have hf := continuous_of_frobenius_lipschitz f L hLip
  let m := ∫ V, f V ∂μ
  let A := (4*L^2)/(2*((N:ℝ)-2))
  let F (U : SpecialOrthogonal N) := Real.exp (β*(f U-m))
  have hfi : Integrable F μ := continuous_haar_integrable μ _
    (Real.continuous_exp.comp (continuous_const.mul (hf.sub continuous_const)))
  have hmoment := haar_lipschitz_moment_bound hN μ f hf L hL hLip hβ
  have hI : (∫ U, F U ∂μ) ≤ Real.exp (A*β^2) := by
    have he : (∫ U, F U ∂μ) = Real.exp (-β*m)*(∫ U, Real.exp (β*f U) ∂μ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all μ fun U => by
        change Real.exp (β*(f U-m)) = Real.exp (-β*m)*Real.exp (β*f U)
        rw [← Real.exp_add]
        congr 1
        ring
    rw [he]
    calc
      _ ≤ Real.exp (-β*m)*Real.exp (m*β+A*β^2) :=
        mul_le_mul_of_nonneg_left hmoment (Real.exp_pos _).le
      _ = Real.exp (A*β^2) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hset : {U | Real.exp (β*r) ≤ F U} = {U | r ≤ f U-m} := by
    ext U
    simp only [mem_ofPred_eq,F,Real.exp_le_exp]
    exact mul_le_mul_iff_right₀ hβ
  have hm := mul_meas_ge_le_integral_of_nonneg (ae_of_all μ fun U => (Real.exp_pos _).le)
    hfi (Real.exp (β*r))
  rw [hset] at hm
  have hb : μ.real {U | r ≤ f U-m} ≤ Real.exp (A*β^2)/Real.exp (β*r) := by
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    nlinarith [hm]
  simpa only [Real.exp_sub] using hb

theorem haar_lipschitz_upper_tail {N : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (f : SpecialOrthogonal N → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ U V, |f U-f V| ≤ L*frobeniusDistance U V) {r : ℝ} (hr : 0 < r) :
    μ.real {U | r ≤ f U-(∫ V, f V ∂μ)} ≤
      Real.exp (-((N:ℝ)-2)*r^2/(8*L^2)) := by
  have hρ : 0 < (N:ℝ)-2 := by exact_mod_cast (show 0 < (N:ℤ)-2 by omega)
  have hC : 0 < 4*L^2 := by positivity
  have hb : 0 < ((N:ℝ)-2)*r/(4*L^2) := div_pos (mul_pos hρ hr) hC
  have h := haar_lipschitz_chernoff hN μ f L hL hLip r (((N:ℝ)-2)*r/(4*L^2)) hb
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  field_simp
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarTwoSidedTail
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both one-sided tails and the centered absolute deviation. -/
noncomputable section
open Matrix MeasureTheory Set
namespace InvariantIsing

theorem haar_lipschitz_lower_tail {N : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (f : SpecialOrthogonal N → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ U V, |f U-f V| ≤ L*frobeniusDistance U V) {r : ℝ} (hr : 0 < r) :
    μ.real {U | r ≤ (∫ V, f V ∂μ)-f U} ≤
      Real.exp (-((N:ℝ)-2)*r^2/(8*L^2)) := by
  have hh := haar_lipschitz_upper_tail hN μ (fun U => -f U) L hL
    (fun U V => by simpa only [neg_sub_neg,abs_sub_comm] using hLip U V) hr
  simpa only [integral_neg,sub_neg_eq_add,neg_add_eq_sub] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarConcentrationInput
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The exact Gromov--Milman specialization used by the pressure proof. The proof
uses the actual polynomial heat operator on SO(N), its proved curvature bound,
positive polynomial convolution, and the scalar entropy argument.
-/
noncomputable section
open Matrix MeasureTheory
namespace InvariantIsing

theorem haarConcentration_proved : HaarConcentrationInput := by
  refine ⟨Real.exp 1,1/192,Real.exp_pos _,by norm_num,?_⟩
  intro N hN μ hμ hμinv f hf L hL hLip
  let : IsProbabilityMeasure μ := hμ
  let : μ.IsMulLeftInvariant := hμinv
  obtain ⟨m,hm1,hm2⟩ := measurable_median μ f hf
  refine ⟨m,hm1,hm2,?_⟩
  intro r hr
  let k := ((N:ℝ)-2)/(8*L^2)
  have hρ : 0 < (N:ℝ)-2 := by exact_mod_cast (show 0 < (N:ℤ)-2 by omega)
  have hk : 0 < k := div_pos hρ (by positivity)
  have hplus (s : ℝ) (hs : 0 < s) :
      μ.real {U | s ≤ f U-(∫ V, f V ∂μ)} ≤ Real.exp (-k*s^2) := by
    have hh := haar_lipschitz_upper_tail hN μ f L hL hLip hs
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    dsimp only [k]
    ring
  have hminus (s : ℝ) (hs : 0 < s) :
      μ.real {U | s ≤ (∫ V, f V ∂μ)-f U} ≤ Real.exp (-k*s^2) := by
    have hh := haar_lipschitz_lower_tail hN μ f L hL hLip hs
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    dsimp only [k]
    ring
  apply (gaussian_median_tail μ f (∫ V, f V ∂μ) m k hk hm1 hm2 hplus hminus hr).trans
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
  have hdim : (N:ℝ) ≤ 3*((N:ℝ)-2) := by
    have hn : (3:ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hnum : -3*((N:ℝ)-2)*r^2 ≤ -(N:ℝ)*r^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdim) (sq_nonneg r)]
  calc
    -k*r^2/8 = (-3*((N:ℝ)-2)*r^2)/(192*L^2) := by dsimp only [k] <;> ring
    _ ≤ (-(N:ℝ)*r^2)/(192*L^2) := div_le_div_of_nonneg_right hnum (by positivity)
    _ = -(1/192)*(N:ℝ)*r^2/L^2 := by ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedAncestorEndpoint
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ancestor increments for the constrained terminal give its physical endpoint kernels. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

lemma restrictedAncestor_state {N : ℕ} (hN : 0 < N) (S : Finset (Spin N)) (hS : S.Nonempty)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents (n+1) b) :
    markStateKernel (vectorTerminalAncestorKernel N (n+1) b v (restrictedFieldTerminal S)
      (continuous_restrictedFieldTerminal S hS).measurable 0) =
    vectorGaussianTransition N (b 0) (v 0)
      (restrictedFieldRecursion S n (fun i => b (i+1)) (fun i => v (i+1)))
      (restrictedFieldRecursion_regular hN S hS n _ _
        (fun i hi => (hb.1 (i+1) (by omega)).1)).1 := by
  let := vectorTerminalAncestorKernel_markov hN (n+1) b v hb (restrictedFieldTerminal S)
    (continuous_restrictedFieldTerminal S hS).measurable (restrictedFieldTerminal_linearGrowth S hS) 0
  ext z : 1
  rw [markStateKernel_apply,vectorTerminalAncestorKernel_add hN (n+1) b v hb
    (restrictedFieldTerminal S) (continuous_restrictedFieldTerminal S hS).measurable
    (restrictedFieldTerminal_linearGrowth S hS) 0 (by omega)]
  simp only [zero_add,vectorTerminalBackward_one,restrictedFieldRecursion]

lemma restrictedAncestor_tail {N : ℕ} (hN : 0 < N) (S : Finset (Spin N)) (hS : S.Nonempty)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents n b) :
    markTailEndpointKernel n (vectorTerminalAncestorKernel N n b v (restrictedFieldTerminal S)
      (continuous_restrictedFieldTerminal S hS).measurable) =
    restrictedTailEndpointKernel hN S hS n b v (fun i hi => (hb.1 i hi).1) := by
  induction n generalizing b v with
  | zero => rfl
  | succ n ih =>
    have hbs : CascadeExponents n (fun i => b (i+1)) := hb.tail
    have hs : (fun i => vectorTerminalAncestorKernel N (n+1) b v (restrictedFieldTerminal S)
        (continuous_restrictedFieldTerminal S hS).measurable (i+1)) =
        vectorTerminalAncestorKernel N n (fun i => b (i+1)) (fun i => v (i+1))
          (restrictedFieldTerminal S) (continuous_restrictedFieldTerminal S hS).measurable :=
      funext fun i => vectorTerminalAncestorKernel_shift N n b v _ _ i
    rw [markTailEndpointKernel,hs,ih _ _ hbs,restrictedAncestor_state hN S hS n b v hb]
    rfl

lemma restrictedAncestor_pair {N : ℕ} (hN : 0 < N) (S : Finset (Spin N)) (hS : S.Nonempty)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents n b) (d : Fin (n+1)) :
    markPairEndpointKernel n (vectorTerminalAncestorKernel N n b v (restrictedFieldTerminal S)
      (continuous_restrictedFieldTerminal S hS).measurable) d =
    restrictedPairEndpointKernel hN S hS n b v (fun i hi => (hb.1 i hi).1) d := by
  induction n generalizing b v with
  | zero => rfl
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) d
    · simp only [markPairEndpointKernel,restrictedPairEndpointKernel,Fin.cases_zero,
        restrictedAncestor_tail hN S hS (n+1) b v hb]
    · have hbs : CascadeExponents n (fun i => b (i+1)) := hb.tail
      have hs : (fun i => vectorTerminalAncestorKernel N (n+1) b v (restrictedFieldTerminal S)
          (continuous_restrictedFieldTerminal S hS).measurable (i+1)) =
          vectorTerminalAncestorKernel N n (fun i => b (i+1)) (fun i => v (i+1))
            (restrictedFieldTerminal S) (continuous_restrictedFieldTerminal S hS).measurable :=
        funext fun i => vectorTerminalAncestorKernel_shift N n b v _ _ i
      simp only [markPairEndpointKernel,restrictedPairEndpointKernel,Fin.cases_succ]
      rw [hs,ih _ _ hbs,restrictedAncestor_state hN S hS n b v hb]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedTerminalIntegrability
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual ordinary and constrained field terminals have integrable Gibbs weights. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal BigOperators
namespace InvariantIsing

theorem restrictedTerminal_exp_integrable_ae {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (z : Fin N → ℝ) :
    ∀ᵐ p ∂vectorTerminalCoordinateLaw N h.depth (chainExponent h.cut) (fieldStepVariance h),
      Integrable (fun α => Real.exp (restrictedFieldTerminal S
        (labeledEnergy h.depth (markForestOfCoords (Fin N → ℝ) h.depth p.2) α z)))
        (labeledLeafLaw h.depth p.1) := by
  filter_upwards [field_vector_spin_exp_integrable N hN h z] with p hp
  have hi := spinLeafTerminal_exp_integrable (labeledLeafLaw h.depth p.1)
    (fun s : Spin N × LabeledLeaf h.depth => Real.exp 0 * fieldEnergy (fieldVectorEndpoint N h p z s.2) s.1) (by simpa using hp)
  have hfull : Integrable (fun α => Real.exp (∑ j, Real.log (Real.cosh (fieldVectorEndpoint N h p z α j))))
      (labeledLeafLaw h.depth p.1) := by
    convert hi using 1
    all_goals try with_reducible_and_instances rfl
    funext α
    congr 1
    simp only [spinLeafTerminal,Real.exp_zero,one_mul]
    rw [finiteLogIntegral_uniformSpinPrior,logPartition_fieldEnergy]
  apply hfull.mono' (measurable_of_countable _).aestronglyMeasurable
  apply ae_of_all
  intro α
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (restrictedFieldTerminal_le_univ S hS _)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedFieldPairInput
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constrained vector terminal specialization of the joint marked-cascade theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

lemma markPairEndpoint_coordinates {N n : ℕ} (g : ForestVertex n → Fin N → ℝ)
    (z : Fin N → ℝ) (α β : LabeledLeaf n) :
    markPairEndpoint n z z (fun i => (g (edgeAt n α i),g (edgeAt n β i))) =
      (labeledEnergy n (markForestOfCoords (Fin N → ℝ) n g) α z,
        labeledEnergy n (markForestOfCoords (Fin N → ℝ) n g) β z) := by
  apply Prod.ext <;> funext j <;>
    simp only [markPairEndpoint,Pi.add_apply,Finset.sum_apply,labeledEnergy_edge_sum]

lemma restrictedFieldTiltedPairMean_eq_vector {N : ℕ} (S : Finset (Spin N))
    (h : FieldStep) (z : Fin N → ℝ)
    (Φ : ℕ × ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ) :
    restrictedFieldTiltedPairMean S h z Φ =
    vectorTerminalPairMean N h.depth (chainExponent h.cut) (fieldStepVariance h)
      (restrictedFieldTerminal S) z
      (fun p => Φ (p.1,markPairEndpoint h.depth z z p.2)) := by
  unfold restrictedFieldTiltedPairMean vectorTerminalPairMean
  simp only [markPairEndpoint_coordinates]
  rfl

theorem panchenkoTalagrandRestrictedFieldPair_proved : PanchenkoTalagrandRestrictedFieldPairInput := by
  intro N hN S hS h z Φ hΦ hbounded
  obtain ⟨C,hB⟩ := hbounded
  let b := chainExponent h.cut
  let v := fieldStepVariance h
  have hb : CascadeExponents h.depth b := chainExponent_admissible h.ordered_cut h.first h.last
  let F := restrictedFieldTerminal S
  have hF : Measurable F := (continuous_restrictedFieldTerminal S hS).measurable
  have hG : HasLinearGrowth F := restrictedFieldTerminal_linearGrowth S hS
  have hD : Measurable (fun p : ℕ × (Fin h.depth → (Fin N → ℝ) × (Fin N → ℝ)) =>
      Φ (p.1,markPairEndpoint h.depth z z p.2)) :=
    hΦ.comp (measurable_fst.prodMk ((measurable_markPairEndpoint h.depth z z).comp measurable_snd))
  rw [restrictedFieldTiltedPairMean_eq_vector,
    vectorTerminal_pair_formula hN h.depth b v hb F hF hG z
      (restrictedTerminal_exp_integrable_ae hN S hS h z) _ hD (fun p => hB _)]
  apply integral_congr_ae
  apply ae_of_all
  intro α
  let κ := vectorTerminalAncestorKernel N h.depth b v F hF
  let : ∀ i, IsMarkovKernel (κ i) := fun i =>
    vectorTerminalAncestorKernel_markov hN h.depth b v hb F hF hG i
  change markPairPathMean h.depth κ (fieldCommonLevel h α).val z z
    (fun w => Φ ((fieldCommonLevel h α).val,markPairEndpoint h.depth z z w)) = _
  calc
    _ = ∫ y, Φ ((fieldCommonLevel h α).val,y) ∂markPairEndpointKernel h.depth κ
        (fieldCommonLevel h α) z :=
      markPairPathMean_shared_endpoint h.depth κ (fieldCommonLevel h α) z
        (fun y => Φ ((fieldCommonLevel h α).val,y))
        (hΦ.comp (measurable_const.prodMk measurable_id)) (fun y => hB _)
    _ = _ := by
      rw [restrictedAncestor_pair hN S hS h.depth b v hb (fieldCommonLevel h α)]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Unconditional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Limiting invariant Ising pressure, magnetic fields, and Gaussian patterns. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology
universe u
namespace InvariantIsing

theorem limiting_wasserstein_field_pressure_of_extreme_limits_unconditional_oai :
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : (N : ℕ) → Ω → Orthogonal N) (_hU : ∀ N, Measurable (U N))
    (_hHaar : ∀ N, (P.map (U N)).IsMulRightInvariant)
    (eig : (N : ℕ) → Fin N → ℝ) (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (_hcompact : IsCompact (ν : Measure ℝ).support)
    (_hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (_ha : a∈(ν : Measure ℝ).support) (_hb : b∈(ν : Measure ℝ).support)
    (_hmin : Tendsto (fun k => spectralMinimum (eig (k+1))) atTop (𝓝 a))
    (_hmax : Tendsto (fun k => spectralMaximum (eig (k+1))) atTop (𝓝 b))
    (_hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν))
    (field : (N : ℕ) → Fin N → ℝ) (ξ : ProbabilityMeasure ℝ)
    (_hξ : Integrable (fun x : ℝ => x) (ξ : Measure ℝ))
    (_hw : Tendsto (fun k => fieldWassersteinOne (empiricalSpectralLaw (Nat.succ_pos k) (field (k+1))) ξ)
      atTop (𝓝 0)),
    Tendsto (fun N => ∫ ω, rotatedPressure (eig N) (matrixRotation (U N ω)⁻¹) (field N) ∂P)
      atTop (𝓝 (magneticFieldFunctional (ν : Measure ℝ) b ξ)) ∧
    ∀ᵐ ω ∂P, Tendsto (fun N => rotatedPressure (eig N) (matrixRotation (U N ω)⁻¹) (field N))
      atTop (𝓝 (magneticFieldFunctional (ν : Measure ℝ) b ξ)) :=
  @limiting_wasserstein_field_pressure_of_extreme_limits haarConcentration_proved gaussianLipschitzVariance_proved panchenkoTalagrandRestrictedFieldPair_proved

end InvariantIsing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional_oai.{u_1} := @OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional_oai.{u_1}
