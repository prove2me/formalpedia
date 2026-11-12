-- Prove2me | solution 1 for OAI.InvariantIsing.finiteGaussian_centered_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:16:44.933516+00:00
-- url     : https://prove2.me/submissions/9f42317f-994e-4a79-b155-9f4fc0e34aa4

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
import Theorems.Thm_OAI_InvariantIsing_gaussianLipschitzVariance_proved

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

lemma finiteGaussian_lipschitz_tail {ι : Type*} [Fintype ι]
    {f : EuclideanSpace ℝ ι → ℝ} (hf : LipschitzWith 1 f)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : Ω → EuclideanSpace ℝ ι) (hZ : HasLaw Z (stdGaussian _) P)
    (r t : ℝ) (hr : 0 < r) (ht : 0 < t) :
    P {ω | t ≤ |(f (Z ω)-(∫ x, f x ∂stdGaussian _))/r|} ≤
      ENNReal.ofReal (1/(r^2*t^2)) := by
  have hset : {ω | t ≤ |(f (Z ω)-(∫ x, f x ∂stdGaussian _))/r|} =
      {ω | t*r ≤ |f (Z ω)-(∫ x, f x ∂stdGaussian _)|} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [abs_div,abs_of_pos hr,le_div_iff₀ hr]
  have hm : MeasurableSet {x : EuclideanSpace ℝ ι | t*r ≤ |f x-(∫ y, f y ∂stdGaussian _)|} :=
    (isClosed_le continuous_const ((hf.continuous.sub continuous_const).abs)).measurableSet
  rw [hset,hZ.measure_eq hm]
  have hc := meas_ge_le_variance_div_sq (finiteGaussian_lipschitz_memLp_two hf) (mul_pos ht hr)
  refine hc.trans (ENNReal.ofReal_le_ofReal ?_)
  have hv : variance f (stdGaussian _) ≤ 1 := by
    simpa only [NNReal.coe_one,one_pow] using finiteGaussian_lipschitz_variance hf
  calc
    _ ≤ 1/(t*r)^2 := div_le_div_of_nonneg_right hv (sq_nonneg _)
    _ = 1/(r^2*t^2) := by ring

theorem finiteGaussian_centered_tendsto_oai {ι : ℕ → Type*} [∀ k, Fintype (ι k)]
    (f : (k : ℕ) → EuclideanSpace ℝ (ι k) → ℝ) (hf : ∀ k, LipschitzWith 1 (f k))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : (k : ℕ) → Ω → EuclideanSpace ℝ (ι k))
    (hZ : ∀ k, HasLaw (Z k) (stdGaussian _) P) :
    TendstoInMeasure P (fun k ω =>
      (f k (Z k ω)-(∫ x, f k x ∂stdGaussian _))/Real.sqrt (k+1)) atTop (fun _ => 0) := by
  apply tendstoInMeasure_iff_dist.mpr
  intro ε hε
  have hbound (k : ℕ) : P {ω | ε ≤ dist
      ((f k (Z k ω)-(∫ x, f k x ∂stdGaussian _))/Real.sqrt (k+1)) 0} ≤
      ENNReal.ofReal (1/((k+1 : ℝ)*ε^2)) := by
    have hk : (0 : ℝ) < k+1 := by positivity
    simpa only [dist_zero_right,Real.norm_eq_abs,Real.sq_sqrt hk.le] using
      finiteGaussian_lipschitz_tail (hf k) P (Z k) (hZ k) (Real.sqrt (k+1)) ε
        (Real.sqrt_pos.2 hk) hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _ (fun _ => zero_le) hbound
  have ht : Tendsto (fun k : ℕ => (1 : ℝ)/((k+1 : ℝ)*ε^2)) atTop (𝓝 0) := by
    have ha : Tendsto (fun k : ℕ => (k+1 : ℝ)) atTop atTop := by
      simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
        (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
    have hn : Tendsto (fun k : ℕ => (k+1 : ℝ)*ε^2) atTop atTop :=
      ha.atTop_mul_const (sq_pos_of_pos hε)
    exact tendsto_const_nhds.div_atTop hn
  simpa only [ENNReal.ofReal_zero,Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht

end InvariantIsing

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.InvariantIsing.finiteGaussian_centered_tendsto_oai.{u_1, u_2} := @OAI.InvariantIsing.finiteGaussian_centered_tendsto_oai.{u_1, u_2}
