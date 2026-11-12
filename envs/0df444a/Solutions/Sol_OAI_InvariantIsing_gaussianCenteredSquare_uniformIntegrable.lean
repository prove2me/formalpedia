-- Prove2me | solution 1 for OAI.InvariantIsing.gaussianCenteredSquare_uniformIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:16:46.180994+00:00
-- url     : https://prove2.me/submissions/2f6e7782-2713-4373-90ae-c2e1ad3ccdb0

import Mathlib
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
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
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Sort
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
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
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.HeineCantor
import Theorems.Thm_OAI_InvariantIsing_gaussianLipschitzVariance_proved

section
-- module Solutions.OAIQ258_II.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- d13f23b's `HasLaw.memLp_comp` (InvariantIsing CavityGaussianRows, q251). -/
theorem _root_.ProbabilityTheory.HasLaw.memLp_comp {Ω 𝓧 E : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}
    [NormedAddCommGroup E] {P : MeasureTheory.Measure Ω} {μ : MeasureTheory.Measure 𝓧} {X : Ω → 𝓧} {f : 𝓧 → E}
    {p : ENNReal} (hX : ProbabilityTheory.HasLaw X μ P) (hf : MeasureTheory.MemLp f p μ) :
    MeasureTheory.MemLp (f ∘ X) p P := by
  have h : MeasureTheory.MemLp f p (P.map X) := hX.map_eq ▸ hf
  exact (MeasureTheory.memLp_map_measure_iff h.aestronglyMeasurable hX.aemeasurable).1 h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianPatternSingularVariance
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dimension-free Gaussian variance for the physical rectangular operator norm. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace InvariantIsing

lemma finiteGaussian_lipschitz_variance {ι : Type*} [Fintype ι] {L : ℝ≥0}
    {f : EuclideanSpace ℝ ι → ℝ} (hf : LipschitzWith L f) :
    variance f (stdGaussian (EuclideanSpace ℝ ι)) ≤ (L : ℝ)^2 := by
  let e : EuclideanSpace ℝ (Fin (Fintype.card ι)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin ι).symm
  have hh : LipschitzWith L (f ∘ e) := by simpa only [mul_one] using hf.comp e.lipschitz
  have hv := gaussianLipschitzVariance_proved (Fintype.card ι) L (f ∘ e) hh
  have hm := stdGaussian_map e
  rw [← hm,variance_map hf.continuous.aemeasurable e.continuous.aemeasurable]
  exact hv

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianSingularFluctuation
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered Gaussian singular-value fluctuations vanish after square-root dimension scaling. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace InvariantIsing

lemma finiteGaussian_lipschitz_memLp_two {ι : Type*} [Fintype ι] {L : ℝ≥0}
    {f : EuclideanSpace ℝ ι → ℝ} (hf : LipschitzWith L f) :
    MemLp f 2 (stdGaussian (EuclideanSpace ℝ ι)) := by
  have hi : MemLp (fun x : EuclideanSpace ℝ ι => x) 2 (stdGaussian _) :=
    IsGaussian.memLp_id _ 2 (by norm_num)
  have hc : LipschitzWith L (fun x => f x-f 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm,sub_sub_sub_cancel_right] using hf.dist_le_mul x y
  have hh := (hc.comp_memLp (by simp) hi).add
    (memLp_const (f 0) : MemLp (fun _ : EuclideanSpace ℝ ι => f 0) 2 (stdGaussian _))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianCenteredSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scaled centered Gaussian squares are uniformly integrable using variance alone. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace InvariantIsing

lemma finiteGaussian_centeredSquare_integrable {ι : Type*} [Fintype ι]
    {f : EuclideanSpace ℝ ι → ℝ} (hf : LipschitzWith 1 f)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → EuclideanSpace ℝ ι) (hZ : HasLaw Z (stdGaussian _) P) (r : ℝ) :
    Integrable (fun ω => (f (Z ω)-(∫ x, f x ∂stdGaussian _))^2/r) P := by
  have h := (hZ.memLp_comp (finiteGaussian_lipschitz_memLp_two hf)).sub
    (memLp_const (∫ x, f x ∂stdGaussian _))
  exact h.integrable_sq.div_const r

lemma finiteGaussian_centeredSquare_L1_bound {ι : Type*} [Fintype ι]
    {f : EuclideanSpace ℝ ι → ℝ} (hf : LipschitzWith 1 f)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → EuclideanSpace ℝ ι) (hZ : HasLaw Z (stdGaussian _) P)
    (r : ℝ) (hr : 0 < r) :
    eLpNorm (fun ω => (f (Z ω)-(∫ x, f x ∂stdGaussian _))^2/r) 1 P ≤
      ENNReal.ofReal (1/r) := by
  have hi := finiteGaussian_centeredSquare_integrable hf P Z hZ r
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm hi]
  have he : (∫ ω, ‖(f (Z ω)-(∫ x, f x ∂stdGaussian _))^2/r‖ ∂P) =
      variance f (stdGaussian _)/r := by
    have hn (ω) : ‖(f (Z ω)-(∫ x, f x ∂stdGaussian _))^2/r‖ =
        (f (Z ω)-(∫ x, f x ∂stdGaussian _))^2/r :=
      Real.norm_of_nonneg (div_nonneg (sq_nonneg _) hr.le)
    simp_rw [hn]
    rw [integral_div]
    have h := hZ.integral_comp (f := fun y => (f y-(∫ x, f x ∂stdGaussian _))^2)
      ((hf.continuous.sub continuous_const).pow 2).aestronglyMeasurable
    rw [show (∫ ω, (f (Z ω)-(∫ x, f x ∂stdGaussian _))^2 ∂P) =
        ∫ y, (f y-(∫ x, f x ∂stdGaussian _))^2 ∂stdGaussian _ from h]
    rw [← variance_eq_integral hf.continuous.aemeasurable]
  rw [he]
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ hr.le
  simpa only [NNReal.coe_one,one_pow] using finiteGaussian_lipschitz_variance hf

theorem gaussianCenteredSquare_uniformIntegrable_oai {ι : ℕ → Type*} [∀ k, Fintype (ι k)]
    (f : (k : ℕ) → EuclideanSpace ℝ (ι k) → ℝ) (hf : ∀ k, LipschitzWith 1 (f k))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (k : ℕ) → Ω → EuclideanSpace ℝ (ι k))
    (hZ : ∀ k, HasLaw (Z k) (stdGaussian _) P) :
    UniformIntegrable (fun k ω =>
      (f k (Z k ω)-(∫ x, f k x ∂stdGaussian _))^2/(k+1)) 1 P := by
  have hi k := finiteGaussian_centeredSquare_integrable (hf k) P (Z k) (hZ k) (k+1)
  have hb k := finiteGaussian_centeredSquare_L1_bound (hf k) P (Z k) (hZ k) (k+1)
    (by positivity)
  have ht : Tendsto (fun k : ℕ => ENNReal.ofReal (1/(k+1 : ℝ))) atTop (𝓝 0) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [ENNReal.ofReal_zero,Function.comp_def] using h
  refine ⟨fun k => (hi k).aestronglyMeasurable, unifIntegrable_of_tendsto_Lp_zero le_rfl (by simp)
    (fun k => memLp_one_iff_integrable.mpr (hi k)) (tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds ht (fun _ => zero_le) hb),1,?_⟩
  intro k
  apply (hb k).trans
  apply ENNReal.ofReal_le_one.mpr
  exact (div_le_one (by positivity : (0 : ℝ) < k+1)).mpr (by have := Nat.cast_nonneg (α := ℝ) k; linarith)

end InvariantIsing

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.InvariantIsing.gaussianCenteredSquare_uniformIntegrable_oai.{u_1, u_2} := @OAI.InvariantIsing.gaussianCenteredSquare_uniformIntegrable_oai.{u_1, u_2}
