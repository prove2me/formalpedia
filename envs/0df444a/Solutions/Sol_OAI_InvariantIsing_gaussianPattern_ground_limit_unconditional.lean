-- Prove2me | solution 1 for OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:57:35.132036+00:00
-- url     : https://prove2.me/submissions/0fd4f0ab-9754-41b2-913f-64d77e605848

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
import Theorems.Thm_OAI_InvariantIsing_davidsonSzarek_proved
import Theorems.Thm_OAI_InvariantIsing_gaussianLipschitzVariance_proved
import Theorems.Thm_OAI_InvariantIsing_gaussianPattern_ground_limit
import Theorems.Thm_OAI_InvariantIsing_haarPolynomialMoment_log_bound
import Theorems.Thm_OAI_InvariantIsing_marchenkoPastur_proved
import Theorems.Thm_OAI_InvariantIsing_panchenkoTalagrandFieldPair_proved

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

theorem gaussianPattern_ground_limit_unconditional_oai :
  ∀ (α : ℝ) (_hα : 0 < α)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (_hZ : ∀ N, Measurable (Z N)) (_hlaw : ∀ N, HasLaw (Z N) (stdGaussian _) P)
    (ε : ℝ),
    ∃ e : ℝ,
      TendstoInMeasure P (fun k ω => gaussianPatternGroundEnergy ε (Z (k+1) ω)) atTop (fun _ => e) ∧
      Tendsto (fun k => eLpNorm (fun ω => gaussianPatternGroundEnergy ε (Z (k+1) ω)-e) 1 P)
        atTop (𝓝 0) ∧
      Tendsto (fun k => ∫ ω, gaussianPatternGroundEnergy ε (Z (k+1) ω) ∂P) atTop (𝓝 e) ∧
      Tendsto (fun β => gaussianPatternLimit α (ε*β)/β) atTop (𝓝 e) :=
  fun α hα => @gaussianPattern_ground_limit haarConcentration_proved gaussianLipschitzVariance_proved panchenkoTalagrandFieldPair_proved α hα (marchenkoPastur_proved α hα) (davidsonSzarek_proved α hα)

end InvariantIsing

end

end OAI
end

theorem solution.{u} : type_of% @OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional_oai.{u} := @OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional_oai.{u}
