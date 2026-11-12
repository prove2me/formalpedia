-- Prove2me | solution 1 for OAI.InvariantIsing.gaussianNorm_lower_mean
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:16:48.197091+00:00
-- url     : https://prove2.me/submissions/0e7d538a-3840-4432-a3b4-d1fd3ecf62b5

import Mathlib
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import Definitions.Def_OAIQ258002
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
/-- d13f23b's `HasLaw.memLp`: a variable whose law has `id` in `L^p` is in `L^p`. -/
theorem _root_.ProbabilityTheory.HasLaw.memLp {Ω E : Type*} {mΩ : MeasurableSpace Ω} {mE : MeasurableSpace E}
    [NormedAddCommGroup E] {P : MeasureTheory.Measure Ω} {μ : MeasureTheory.Measure E} {X : Ω → E}
    {p : ENNReal} (hX : ProbabilityTheory.HasLaw X μ P) (hμ : MeasureTheory.MemLp id p μ) :
    MeasureTheory.MemLp X p P := hX.memLp_comp hμ
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
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianCoordinateNorm
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact second moments and the square-root dimension bound for coordinate Gaussian norms. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace InvariantIsing
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma gaussianCoordinate_memLp (i : ι) :
    MemLp (fun g : ι → ℝ => g i) 2 (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  exact (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).hasLaw.memLp
    (IsGaussian.memLp_id _ 2 (by norm_num))

lemma gaussianCoordinate_sq_integral (i : ι) :
    (∫ g : ι → ℝ, (g i)^2 ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) = 1 := by
  have he : (∫ g : ι → ℝ, (g i)^2 ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      ∫ x : ℝ, x^2 ∂gaussianReal 0 1 := by
    simpa only [Function.comp_def,Function.eval] using
      (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).hasLaw.integral_comp
        (f := fun x : ℝ => x^2) (by fun_prop)
  rw [he]
  have hv := variance_of_integral_eq_zero (μ := gaussianReal 0 1)
    (X := id) (by fun_prop) (by simp)
  simpa only [variance_id_gaussianReal,NNReal.coe_one,id_eq] using hv.symm

lemma gaussianCoordinateVector_sq_integral (e : κ → ι) :
    (∫ g, ‖gaussianCoordinateVector e g‖^2
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) = Fintype.card κ := by
  simp only [gaussianCoordinateVector,EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum _ (fun j _ => (gaussianCoordinate_memLp (e j)).integrable_sq)]
  simp only [gaussianCoordinate_sq_integral,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianNormLowerMean
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The matching lower mean bound for a finite-dimensional Gaussian norm. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace InvariantIsing

lemma gaussianNorm_sq_integral {ι : Type*} [Fintype ι] :
    (∫ z : EuclideanSpace ℝ ι, ‖z‖^2 ∂stdGaussian _) = Fintype.card ι := by
  have hZ : HasLaw (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι)
      (stdGaussian _) (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    ⟨(PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).measurable.aemeasurable,map_pi_eq_stdGaussian⟩
  rw [← hZ.integral_comp (f := fun z => ‖z‖^2) (by fun_prop)]
  exact gaussianCoordinateVector_sq_integral (id : ι → ι)

lemma gaussianNorm_lower_mean_oai {ι : Type*} [Fintype ι] :
    Real.sqrt ((Fintype.card ι : ℝ)-1) ≤ ∫ z : EuclideanSpace ℝ ι, ‖z‖ ∂stdGaussian _ := by
  have hL : LipschitzWith 1 (norm : EuclideanSpace ℝ ι → ℝ) := lipschitzWith_one_norm
  have hv := finiteGaussian_lipschitz_variance hL
  rw [variance_eq_sub (finiteGaussian_lipschitz_memLp_two hL)] at hv
  change (∫ z : EuclideanSpace ℝ ι, ‖z‖^2 ∂stdGaussian _) - _ ≤ (1 : ℝ)^2 at hv
  rw [gaussianNorm_sq_integral] at hv
  have hn : 0 ≤ ∫ z : EuclideanSpace ℝ ι, ‖z‖ ∂stdGaussian _ := integral_nonneg (fun z => norm_nonneg z)
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact hn
  · nlinarith

end InvariantIsing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.InvariantIsing.gaussianNorm_lower_mean_oai.{u_1} := @OAI.InvariantIsing.gaussianNorm_lower_mean_oai.{u_1}
