-- Prove2me | solution 1 for OAI.InvariantIsing.gaussianLipschitzVariance_proved
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:16:47.186203+00:00
-- url     : https://prove2.me/submissions/b270a015-6f2e-459f-ad01-d1cf89b7c771

import Mathlib
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
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
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import Definitions.Def_OAIQ258001
import Definitions.Def_OAIQ258002

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianSmoothing
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized smoothing preserves the precise scalar Lipschitz constant. -/
noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped NNReal Convolution ContDiff
namespace InvariantIsing

lemma gaussianSmooth_lipschitz {d : ℕ} {L : ℝ≥0}
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LipschitzWith L f) :
    LipschitzWith L (gaussianSmooth φ f) := by
  have hi (x : EuclideanSpace ℝ (Fin d)) :
      Integrable (fun a => φ.normed volume a * f (x-a)) := by
    simpa only [ConvolutionExistsAt, lsmul_apply, smul_eq_mul] using
      (φ.hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ)
        φ.continuous_normed hf.continuous.locallyIntegrable x)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖(∫ a, φ.normed volume a * f (x-a)) -
    (∫ a, φ.normed volume a * f (y-a))‖ ≤ (L : ℝ)*dist x y
  rw [← integral_sub (hi x) (hi y)]
  calc
    _ ≤ ∫ a, φ.normed volume a * ((L : ℝ)*dist x y) := by
      apply norm_integral_le_of_norm_le (φ.integrable_normed.mul_const _)
      filter_upwards [] with a
      rw [← mul_sub, norm_mul, Real.norm_of_nonneg (φ.nonneg_normed a)]
      apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed a)
      simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using
        hf.dist_le_mul (x-a) (y-a)
    _ = _ := by rw [integral_mul_const, φ.integral_normed, one_mul]

lemma gaussianSmooth_test {d : ℕ} {L : ℝ≥0}
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LipschitzWith L f)
    (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (gaussianSmooth φ f) ∧ HasCompactSupport (gaussianSmooth φ f) := by
  exact ⟨φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
    φ.contDiff_normed hf.continuous.locallyIntegrable,
    φ.hasCompactSupport_normed.convolution (lsmul ℝ ℝ) hc⟩

lemma gaussianSmooth_dist_le {d : ℕ} {L : ℝ≥0}
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LipschitzWith L f)
    (x : EuclideanSpace ℝ (Fin d)) :
    dist (gaussianSmooth φ f x) (f x) ≤ (L : ℝ)*φ.rOut := by
  apply φ.dist_normed_convolution_le hf.continuous.aestronglyMeasurable
  intro y hy
  exact (hf.dist_le_mul y x).trans
    (mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hy).le L.coe_nonneg)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianLipschitzIntegrability
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square integrability of the actual Lipschitz observables in the Gaussian input. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace InvariantIsing

lemma gaussian_lipschitz_memLp_two {d : ℕ} {L : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LipschitzWith L f) :
    MemLp f 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have hi : MemLp (fun x : EuclideanSpace ℝ (Fin d) => x) 2
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := IsGaussian.memLp_id _ 2 (by norm_num)
  have hc : LipschitzWith L (fun x => f x-f 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using hf.dist_le_mul x y
  have hh := (hc.comp_memLp (by simp) hi).add
    (memLp_const (f 0) : MemLp (fun _ : EuclideanSpace ℝ (Fin d) => f 0) 2
      (stdGaussian (EuclideanSpace ℝ (Fin d))))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp

lemma gaussian_lipschitz_integrable {d : ℕ} {L : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LipschitzWith L f) :
    Integrable f (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
  (gaussian_lipschitz_memLp_two hf).integrable (by norm_num)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.KLS_Sobolev_TestFunctions
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.LeanBlast.KLS.blMomentDeriv_zero _root_.OAI.LeanBlast.KLS.blMoment_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory InnerProductSpace
open scoped ContDiff

namespace LeanBlast.KLS

variable {n : ℕ} {f : Space n → ℝ}

theorem IsTestFunction.continuous (hf : IsTestFunction f) : Continuous f :=
  hf.1.continuous

theorem IsTestFunction.continuous_gradient (hf : IsTestFunction f) :
    Continuous (gradient f) := by
  exact (toDual ℝ (Space n)).symm.continuous.comp
    (hf.1.continuous_fderiv (by simp))

theorem IsTestFunction.hasCompactSupport_gradient (hf : IsTestFunction f) :
    HasCompactSupport (gradient f) := by
  exact (hf.2.fderiv ℝ).comp_left
    (g := (toDual ℝ (Space n)).symm) (by simp)

theorem IsTestFunction.integrable_gradient_sq (hf : IsTestFunction f)
    (μ : Measure (Space n)) [IsFiniteMeasure μ] :
    Integrable (fun x => ‖gradient f x‖ ^ 2) μ := by
  have hsupport := HasCompactSupport.comp_left (f := gradient f)
    (g := fun vector : Space n => ‖vector‖ ^ 2) hf.hasCompactSupport_gradient (by simp)
  exact (hf.continuous_gradient.norm.pow 2).integrable_of_hasCompactSupport hsupport

theorem norm_gradient_eq_norm_fderiv (f : Space n → ℝ) (x : Space n) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ :=
  (toDual ℝ (Space n)).symm.norm_map _

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ258_II.KLS_Measures_PotentialMeasure
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff

namespace LeanBlast.KLS

variable {n : ℕ}

theorem potentialPartition_pos {V : Space n → ℝ}
    (hV : Integrable (fun x => Real.exp (-V x))) : 0 < potentialPartition V :=
  integral_exp_pos hV

theorem isProbabilityMeasure_potentialMeasure {V : Space n → ℝ}
    (hV : Integrable (fun x => Real.exp (-V x))) :
    IsProbabilityMeasure (potentialMeasure V) :=
  isProbabilityMeasure_tilted hV

theorem integral_potentialMeasure (V g : Space n → ℝ) :
    (∫ x, g x ∂potentialMeasure V) =
      (∫ x, Real.exp (-V x) * g x) / potentialPartition V := by
  rw [potentialMeasure, integral_tilted]
  simp only [smul_eq_mul]
  simp_rw [div_mul_eq_mul_div]
  simpa only [div_eq_mul_inv, potentialPartition] using
    integral_mul_const (potentialPartition V)⁻¹ (fun x => Real.exp (-V x) * g x)

theorem integrable_potentialMeasure_iff {V : Space n → ℝ}
    (hV : Integrable (fun x => Real.exp (-V x))) (g : Space n → ℝ) :
    Integrable g (potentialMeasure V) ↔ Integrable (fun x => Real.exp (-V x) * g x) := by
  simpa only [potentialMeasure, smul_eq_mul] using integrable_tilted_iff hV g

theorem variance_eq_integral_sq_sub_sq (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    {h : Space n → ℝ} (hh : Integrable h μ) (hh2 : Integrable (fun x => (h x) ^ 2) μ) :
    variance μ h = (∫ x, (h x) ^ 2 ∂μ) - (∫ x, h x ∂μ) ^ 2 := by
  unfold variance expectation
  have heq : (fun x => (h x - ∫ y, h y ∂μ) ^ 2) =
      fun x => ((h x) ^ 2 - (2 * ∫ y, h y ∂μ) * h x) + (∫ y, h y ∂μ) ^ 2 := by
    funext x
    ring
  rw [heq]
  rw [integral_add (f := fun x => h x ^ 2 - (2 * ∫ y, h y ∂μ) * h x)
    (g := fun _ => (∫ y, h y ∂μ) ^ 2)
    (hh2.sub (hh.const_mul _)) (integrable_const _)]
  rw [integral_sub (f := fun x => h x ^ 2) (g := fun x => (2 * ∫ y, h y ∂μ) * h x)
    hh2 (hh.const_mul _), integral_const_mul, integral_const]
  simp only [probReal_univ, one_smul]
  ring

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ258_II.KLS_Stein_SteinHessianDefs
attribute [-simp] _root_.OAI.LeanBlast.KLS.blMomentDeriv_zero _root_.OAI.LeanBlast.KLS.blMoment_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Matrix
open scoped BigOperators ContDiff

namespace LeanBlast.KLS

theorem hessianMatrix_isSymm {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ 2 f x) : (hessianMatrix f x).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  exact (hf.isSymmSndFDerivAt (by norm_num)).eq _ _

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ258_II.KLS_Regularization_RegularPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace LeanBlast.KLS

theorem IsRegularPotential.hessian_pos {n : ℕ} {V : Space n → ℝ} {t t' : ℝ}
    (hV : IsRegularPotential V t t') (x : Space n) {v : Space n} (hv : v ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ V) x v v :=
  (mul_pos hV.lower_pos (sq_pos_of_pos (norm_pos_iff.mpr hv))).trans_le (hV.lower_bound x v)

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ258_II.KLS_Convexity_PrekopaLeindler
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Pointwise Topology

namespace AsymptoticStatistics

private theorem prekopaLeindler_1d_levelInclusion
    {f g h : ℝ → ℝ≥0∞}
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y))
    {α : ℝ≥0∞} (hα_pos : 0 < α) (hα_top : α ≠ ⊤) :
    t • {x | α < f x} + (1 - t) • {y | α < g y} ⊆ {z | α < h z} := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  rintro z hz
  rw [Set.mem_add] at hz
  obtain ⟨_, hu, _, hv, rfl⟩ := hz
  rw [Set.mem_smul_set] at hu hv
  obtain ⟨x, hx, rfl⟩ := hu
  obtain ⟨y, hy, rfl⟩ := hv

  simp only [smul_eq_mul, Set.mem_ofPred_eq] at hx hy ⊢

  have h_alpha_split : α = α ^ t * α ^ (1 - t) := by
    rw [← ENNReal.rpow_add t (1 - t) hα_pos.ne' hα_top]
    have ht_one : t + (1 - t) = (1 : ℝ) := by ring
    rw [ht_one, ENNReal.rpow_one]

  have h1 : α ^ t < f x ^ t := ENNReal.rpow_lt_rpow hx ht_pos
  have h2 : α ^ (1 - t) < g y ^ (1 - t) := ENNReal.rpow_lt_rpow hy h1t_pos

  have h3 : α ^ t * α ^ (1 - t) < f x ^ t * g y ^ (1 - t) := ENNReal.mul_lt_mul h1 h2

  calc α = α ^ t * α ^ (1 - t) := h_alpha_split
    _ < f x ^ t * g y ^ (1 - t) := h3
    _ ≤ h (t * x + (1 - t) * y) := h_le x y

private lemma oneDim_brunn_minkowski_compact_le
    {K_A K_B : Set ℝ}
    (hA_compact : IsCompact K_A) (hB_compact : IsCompact K_B)
    (hA_ne : K_A.Nonempty) (hB_ne : K_B.Nonempty) :
    volume K_A + volume K_B ≤ volume (K_A + K_B) := by

  set a := sSup K_A with ha_def
  set b := sInf K_B with hb_def
  have ha_mem : a ∈ K_A := hA_compact.sSup_mem hA_ne
  have hb_mem : b ∈ K_B := hB_compact.sInf_mem hB_ne
  have hA_le_a : ∀ x ∈ K_A, x ≤ a :=
    fun x hx => le_csSup hA_compact.bddAbove hx
  have hB_ge_b : ∀ y ∈ K_B, b ≤ y :=
    fun y hy => csInf_le hB_compact.bddBelow hy

  set U : Set ℝ := K_A + {b} with hU_def
  set V : Set ℝ := {a} + K_B with hV_def

  have hU_sub_AB : U ⊆ K_A + K_B := by
    rintro _ ⟨x, hx, _, rfl, rfl⟩
    exact ⟨x, hx, b, hb_mem, rfl⟩
  have hV_sub_AB : V ⊆ K_A + K_B := by
    rintro _ ⟨_, rfl, y, hy, rfl⟩
    exact ⟨a, ha_mem, y, hy, rfl⟩

  have hU_vol : volume U = volume K_A := by
    rw [hU_def, Set.add_singleton, Set.image_add_right]
    exact MeasureTheory.measure_preimage_add_right volume (-b) K_A

  have hV_vol : volume V = volume K_B := by
    rw [hV_def, Set.singleton_add, Set.image_add_left]
    exact MeasureTheory.measure_preimage_add volume (-a) K_B

  have hU_sub_Iic : U ⊆ Set.Iic (a + b) := by
    rintro _ ⟨x, hx, _, rfl, rfl⟩
    have := hA_le_a x hx
    simp only [Set.mem_Iic]
    linarith

  have hV_sub_Ici : V ⊆ Set.Ici (a + b) := by
    rintro _ ⟨_, rfl, y, hy, rfl⟩
    have := hB_ge_b y hy
    simp only [Set.mem_Ici]
    linarith

  have h_inter_sub : U ∩ V ⊆ {a + b} := by
    rintro z ⟨hzU, hzV⟩
    have h1 := hU_sub_Iic hzU
    have h2 := hV_sub_Ici hzV
    simp only [Set.mem_Iic] at h1
    simp only [Set.mem_Ici] at h2
    simp only [Set.mem_singleton_iff]
    linarith

  have h_inter_zero : volume (U ∩ V) = 0 := by
    apply le_antisymm _ (by positivity)
    calc volume (U ∩ V)
        ≤ volume ({a + b} : Set ℝ) := MeasureTheory.measure_mono h_inter_sub
      _ = 0 := MeasureTheory.measure_singleton (a + b)

  have hV_meas : MeasurableSet V := by
    rw [hV_def, Set.singleton_add, Set.image_add_left]
    exact (hB_compact.measurableSet).preimage (measurable_const_add (-a))
  have h_inc_excl : volume (U ∪ V) + volume (U ∩ V) = volume U + volume V :=
    MeasureTheory.measure_union_add_inter U hV_meas

  have h_union_sub : U ∪ V ⊆ K_A + K_B := Set.union_subset hU_sub_AB hV_sub_AB
  have h_union_le : volume (U ∪ V) ≤ volume (K_A + K_B) :=
    MeasureTheory.measure_mono h_union_sub

  calc volume K_A + volume K_B
      = volume U + volume V := by rw [hU_vol, hV_vol]
    _ = volume (U ∪ V) + volume (U ∩ V) := h_inc_excl.symm
    _ = volume (U ∪ V) + 0 := by rw [h_inter_zero]
    _ = volume (U ∪ V) := add_zero _
    _ ≤ volume (K_A + K_B) := h_union_le

private theorem oneDim_brunn_minkowski_le
    {A B C : Set ℝ}
    (hA_meas : MeasurableSet A) (hB_meas : MeasurableSet B)
    (_hC_meas : MeasurableSet C)
    (hA_ne : A.Nonempty) (hB_ne : B.Nonempty)
    (hAB_sub : A + B ⊆ C) :
    volume A + volume B ≤ volume C := by

  by_cases hA_zero : volume A = 0
  · obtain ⟨a₀, ha₀⟩ := hA_ne
    have h_aB_sub_C : ({a₀} : Set ℝ) + B ⊆ C := fun z ⟨_, rfl, y, hy, hyz⟩ =>
      hAB_sub ⟨a₀, ha₀, y, hy, hyz⟩
    have h_aB_eq : volume (({a₀} : Set ℝ) + B) = volume B := by
      rw [Set.singleton_add, Set.image_add_left]
      exact MeasureTheory.measure_preimage_add volume (-a₀) B
    rw [hA_zero, zero_add]
    calc volume B = volume (({a₀} : Set ℝ) + B) := h_aB_eq.symm
      _ ≤ volume C := MeasureTheory.measure_mono h_aB_sub_C

  by_cases hB_zero : volume B = 0
  · obtain ⟨b₀, hb₀⟩ := hB_ne
    have h_Ab_sub_C : A + ({b₀} : Set ℝ) ⊆ C := fun z ⟨x, hx, _, rfl, hxz⟩ =>
      hAB_sub ⟨x, hx, b₀, hb₀, hxz⟩
    have h_Ab_eq : volume (A + ({b₀} : Set ℝ)) = volume A := by
      rw [Set.add_singleton, Set.image_add_right]
      exact MeasureTheory.measure_preimage_add_right volume (-b₀) A
    rw [hB_zero, add_zero]
    calc volume A = volume (A + ({b₀} : Set ℝ)) := h_Ab_eq.symm
      _ ≤ volume C := MeasureTheory.measure_mono h_Ab_sub_C

  by_cases hA_top : volume A = ⊤
  · obtain ⟨b₀, hb₀⟩ := hB_ne
    suffices h_C_top : volume C = ⊤ by
      rw [hA_top, h_C_top]; exact le_top
    apply top_le_iff.mp
    have h_inner :
        volume A = ⨆ (K : Set ℝ), ⨆ (_ : K ⊆ A), ⨆ (_ : IsCompact K), volume K :=
      MeasureTheory.Measure.InnerRegularWRT.measure_eq_iSup
        MeasureTheory.Measure.InnerRegular.innerRegular hA_meas
    calc (⊤ : ℝ≥0∞)
        = volume A := hA_top.symm
      _ = ⨆ (K : Set ℝ), ⨆ (_ : K ⊆ A), ⨆ (_ : IsCompact K), volume K := h_inner
      _ ≤ volume C := by
          refine iSup_le fun K_A => iSup_le fun hK_A_sub => iSup_le fun _ => ?_
          have h_KA_b0_sub : K_A + ({b₀} : Set ℝ) ⊆ C :=
            fun z ⟨x, hx, _, rfl, hxz⟩ => hAB_sub ⟨x, hK_A_sub hx, b₀, hb₀, hxz⟩
          have h_KA_b0_eq : volume (K_A + ({b₀} : Set ℝ)) = volume K_A := by
            rw [Set.add_singleton, Set.image_add_right]
            exact MeasureTheory.measure_preimage_add_right volume (-b₀) K_A
          calc volume K_A
              = volume (K_A + ({b₀} : Set ℝ)) := h_KA_b0_eq.symm
            _ ≤ volume C := MeasureTheory.measure_mono h_KA_b0_sub

  by_cases hB_top : volume B = ⊤
  · obtain ⟨a₀, ha₀⟩ := hA_ne
    suffices h_C_top : volume C = ⊤ by
      rw [hB_top, h_C_top]; exact le_top
    apply top_le_iff.mp
    have h_inner :
        volume B = ⨆ (K : Set ℝ), ⨆ (_ : K ⊆ B), ⨆ (_ : IsCompact K), volume K :=
      MeasureTheory.Measure.InnerRegularWRT.measure_eq_iSup
        MeasureTheory.Measure.InnerRegular.innerRegular hB_meas
    calc (⊤ : ℝ≥0∞)
        = volume B := hB_top.symm
      _ = ⨆ (K : Set ℝ), ⨆ (_ : K ⊆ B), ⨆ (_ : IsCompact K), volume K := h_inner
      _ ≤ volume C := by
          refine iSup_le fun K_B => iSup_le fun hK_B_sub => iSup_le fun _ => ?_
          have h_a0_KB_sub : ({a₀} : Set ℝ) + K_B ⊆ C :=
            fun z ⟨_, rfl, y, hy, hyz⟩ => hAB_sub ⟨a₀, ha₀, y, hK_B_sub hy, hyz⟩
          have h_a0_KB_eq : volume (({a₀} : Set ℝ) + K_B) = volume K_B := by
            rw [Set.singleton_add, Set.image_add_left]
            exact MeasureTheory.measure_preimage_add volume (-a₀) K_B
          calc volume K_B
              = volume (({a₀} : Set ℝ) + K_B) := h_a0_KB_eq.symm
            _ ≤ volume C := MeasureTheory.measure_mono h_a0_KB_sub

  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _hC_top

  set δ : ℝ≥0∞ := (ε : ℝ≥0∞) / 2 with hδ_def
  have hδ_pos : (0 : ℝ≥0∞) < δ := by
    rw [hδ_def]
    refine ENNReal.div_pos ?_ (by norm_num)
    exact_mod_cast hε.ne'
  have hδ_ne : δ ≠ 0 := hδ_pos.ne'
  have hδ_le : δ ≤ ε := by
    rw [hδ_def]; exact ENNReal.half_le_self

  obtain ⟨K_A, hK_A_sub, hK_A_compact, hK_A_lt⟩ :=
    hA_meas.exists_isCompact_lt_add hA_top hδ_ne
  obtain ⟨K_B, hK_B_sub, hK_B_compact, hK_B_lt⟩ :=
    hB_meas.exists_isCompact_lt_add hB_top hδ_ne

  rcases K_A.eq_empty_or_nonempty with hKA_empty | hKA_ne
  ·
    rw [hKA_empty, MeasureTheory.measure_empty, zero_add] at hK_A_lt

    have hA_le_ε : volume A ≤ (ε : ℝ≥0∞) := le_trans hK_A_lt.le hδ_le

    obtain ⟨a₀, ha₀⟩ := hA_ne
    have h_aB_sub_C : ({a₀} : Set ℝ) + B ⊆ C := fun z ⟨_, rfl, y, hy, hyz⟩ =>
      hAB_sub ⟨a₀, ha₀, y, hy, hyz⟩
    have h_aB_eq : volume (({a₀} : Set ℝ) + B) = volume B := by
      rw [Set.singleton_add, Set.image_add_left]
      exact MeasureTheory.measure_preimage_add volume (-a₀) B
    have hB_le_C : volume B ≤ volume C := by
      rw [← h_aB_eq]; exact MeasureTheory.measure_mono h_aB_sub_C
    calc volume A + volume B ≤ (ε : ℝ≥0∞) + volume C := add_le_add hA_le_ε hB_le_C
      _ = volume C + (ε : ℝ≥0∞) := add_comm _ _
  rcases K_B.eq_empty_or_nonempty with hKB_empty | hKB_ne
  ·
    rw [hKB_empty, MeasureTheory.measure_empty, zero_add] at hK_B_lt
    have hB_le_ε : volume B ≤ (ε : ℝ≥0∞) := le_trans hK_B_lt.le hδ_le
    obtain ⟨b₀, hb₀⟩ := hB_ne
    have h_Ab_sub_C : A + ({b₀} : Set ℝ) ⊆ C := fun z ⟨x, hx, _, rfl, hxz⟩ =>
      hAB_sub ⟨x, hx, b₀, hb₀, hxz⟩
    have h_Ab_eq : volume (A + ({b₀} : Set ℝ)) = volume A := by
      rw [Set.add_singleton, Set.image_add_right]
      exact MeasureTheory.measure_preimage_add_right volume (-b₀) A
    have hA_le_C : volume A ≤ volume C := by
      rw [← h_Ab_eq]; exact MeasureTheory.measure_mono h_Ab_sub_C
    exact add_le_add hA_le_C hB_le_ε
  ·
    have hKAB_sub : K_A + K_B ⊆ C :=
      fun z ⟨x, hx, y, hy, hxyz⟩ =>
        hAB_sub ⟨x, hK_A_sub hx, y, hK_B_sub hy, hxyz⟩
    have h_compact_bm := oneDim_brunn_minkowski_compact_le
      hK_A_compact hK_B_compact hKA_ne hKB_ne
    have h_KAKB_le_C : volume (K_A + K_B) ≤ volume C :=
      MeasureTheory.measure_mono hKAB_sub

    have h_2δ_le_ε : (2 : ℝ≥0∞) * δ ≤ (ε : ℝ≥0∞) := by
      rw [hδ_def]; exact ENNReal.mul_div_le
    calc volume A + volume B
        ≤ (volume K_A + δ) + (volume K_B + δ) := by gcongr
      _ = (volume K_A + volume K_B) + (δ + δ) := by ring
      _ = (volume K_A + volume K_B) + 2 * δ := by ring
      _ ≤ volume C + 2 * δ := by
          gcongr
          exact le_trans h_compact_bm h_KAKB_le_C
      _ ≤ volume C + (ε : ℝ≥0∞) := by gcongr

private theorem prekopaLeindler_1d_levelMeasureBound
    {f g h : ℝ → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y))
    {α : ℝ≥0∞} (hα_pos : 0 < α) (hα_top : α ≠ ⊤)
    (hA_ne : ({x | α < f x} : Set ℝ).Nonempty)
    (hB_ne : ({y | α < g y} : Set ℝ).Nonempty) :
    ENNReal.ofReal t * volume {x | α < f x}
      + ENNReal.ofReal (1 - t) * volume {y | α < g y}
      ≤ volume {z | α < h z} := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  set A : Set ℝ := {x | α < f x} with hA_def
  set B : Set ℝ := {y | α < g y} with hB_def
  set C : Set ℝ := {z | α < h z} with hC_def

  have hA_meas : MeasurableSet A := hf_meas measurableSet_Ioi
  have hB_meas : MeasurableSet B := hg_meas measurableSet_Ioi
  have hC_meas : MeasurableSet C := hh_meas measurableSet_Ioi

  have h_incl : t • A + (1 - t) • B ⊆ C :=
    prekopaLeindler_1d_levelInclusion ht_pos ht_lt h_le hα_pos hα_top

  have htA_meas : MeasurableSet (t • A) :=
    hA_meas.const_smul_of_ne_zero ht_pos.ne'
  have h1tB_meas : MeasurableSet ((1 - t) • B) :=
    hB_meas.const_smul_of_ne_zero h1t_pos.ne'

  have htA_ne : (t • A).Nonempty := Set.smul_set_nonempty.mpr hA_ne
  have h1tB_ne : ((1 - t) • B).Nonempty := Set.smul_set_nonempty.mpr hB_ne

  have h_bm : volume (t • A) + volume ((1 - t) • B) ≤ volume C :=
    oneDim_brunn_minkowski_le htA_meas h1tB_meas hC_meas htA_ne h1tB_ne h_incl

  have h_finrank : Module.finrank ℝ ℝ = 1 := CommSemiring.finrank_self ℝ
  have h_smul_t : volume (t • A) = ENNReal.ofReal t * volume A := by
    rw [Measure.addHaar_smul_of_nonneg volume ht_pos.le A, h_finrank, pow_one]
  have h_smul_1t : volume ((1 - t) • B) = ENNReal.ofReal (1 - t) * volume B := by
    rw [Measure.addHaar_smul_of_nonneg volume h1t_pos.le B, h_finrank, pow_one]
  rw [← h_smul_t, ← h_smul_1t]
  exact h_bm

private theorem lintegral_eq_lintegral_meas_lt_ennreal
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x = ∫⁻ α in Ioi (0 : ℝ), volume {x | ENNReal.ofReal α < f x} := by

  set fN : ℕ → ℝ → ℝ≥0∞ := fun n x => f x ⊓ (n : ℝ≥0∞) with hfN_def
  have hfN_meas : ∀ n, Measurable (fN n) :=
    fun n => hf.inf measurable_const
  have hfN_lt_top : ∀ n x, fN n x ≠ ⊤ :=
    fun n x => ne_top_of_le_ne_top ENNReal.coe_ne_top inf_le_right
  have hfN_mono : Monotone fN := by
    intro m n hmn x
    exact inf_le_inf_left _ (by exact_mod_cast hmn)
  have hfN_iSup_eq : ∀ x, ⨆ n, fN n x = f x := fun x => by
    simp only [fN]
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]

  have hLHS : ∫⁻ x, f x = ⨆ n, ∫⁻ x, fN n x := by
    rw [← MeasureTheory.lintegral_iSup hfN_meas hfN_mono]
    exact MeasureTheory.lintegral_congr fun x => (hfN_iSup_eq x).symm

  have h_per_n : ∀ n, ∫⁻ x, fN n x =
      ∫⁻ α in Ioi (0 : ℝ), volume {x | ENNReal.ofReal α < fN n x} := by
    intro n
    have h_eq : ∫⁻ x, fN n x = ∫⁻ x, ENNReal.ofReal ((fN n x).toReal) :=
      MeasureTheory.lintegral_congr fun x => (ENNReal.ofReal_toReal (hfN_lt_top n x)).symm
    rw [h_eq, MeasureTheory.lintegral_eq_lintegral_meas_lt volume
        (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
        ((hfN_meas n).ennreal_toReal.aemeasurable)]

    apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi
    intro α hα
    have hα_nn : (0 : ℝ) ≤ α := le_of_lt hα
    change volume {x | α < (fN n x).toReal}
        = volume {x | ENNReal.ofReal α < fN n x}
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hα_nn).mpr h
      rwa [ENNReal.ofReal_toReal (hfN_lt_top n x)] at this
    · have h' : ENNReal.ofReal α < ENNReal.ofReal ((fN n x).toReal) := by
        rwa [ENNReal.ofReal_toReal (hfN_lt_top n x)]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hα_nn).mp h'

  have h_set_mono : ∀ α : ℝ,
      Monotone fun n : ℕ => {x | ENNReal.ofReal α < fN n x} := by
    intro α m n hmn x hx
    exact lt_of_lt_of_le hx (hfN_mono hmn x)
  have h_set_iUnion : ∀ α : ℝ,
      ⋃ n : ℕ, {x | ENNReal.ofReal α < fN n x}
        = {x | ENNReal.ofReal α < f x} := by
    intro α
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨fun ⟨n, hn⟩ => lt_of_lt_of_le hn (le_trans inf_le_left le_rfl), ?_⟩
    intro hx
    rw [← hfN_iSup_eq x] at hx
    exact lt_iSup_iff.mp hx

  have h_meas_vol : ∀ n,
      Measurable fun α : ℝ => volume {x | ENNReal.ofReal α < fN n x} := by
    intro n

    have h_set_meas : MeasurableSet
        {p : ℝ × ℝ | ENNReal.ofReal p.1 < fN n p.2} :=
      measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
        ((hfN_meas n).comp measurable_snd)

    exact measurable_measure_prodMk_left h_set_meas
  have hRHS : ∫⁻ α in Ioi (0 : ℝ), volume {x | ENNReal.ofReal α < f x}
        = ⨆ n, ∫⁻ α in Ioi (0 : ℝ), volume {x | ENNReal.ofReal α < fN n x} := by
    rw [show (fun α => volume {x | ENNReal.ofReal α < f x})
          = fun α => ⨆ n, volume {x | ENNReal.ofReal α < fN n x} from
        funext fun α => by rw [← h_set_iUnion α,
          (h_set_mono α).measure_iUnion]]
    exact MeasureTheory.lintegral_iSup (fun n => h_meas_vol n)
      (fun m n hmn α => MeasureTheory.measure_mono (h_set_mono α hmn))
  rw [hLHS, hRHS]
  exact iSup_congr h_per_n

private theorem ennreal_geom_mean_le_arith_mean2_weighted
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (a b : ℝ≥0∞) :
    a ^ t * b ^ (1 - t) ≤ ENNReal.ofReal t * a + ENNReal.ofReal (1 - t) * b := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  by_cases ha : a = ⊤
  · subst ha
    have h_rhs : ENNReal.ofReal t * ⊤ + ENNReal.ofReal (1 - t) * b = ⊤ := by
      have : ENNReal.ofReal t ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero]; linarith
      simp [ENNReal.mul_top this]
    rw [h_rhs]; exact le_top
  by_cases hb : b = ⊤
  · subst hb
    have h_rhs : ENNReal.ofReal t * a + ENNReal.ofReal (1 - t) * ⊤ = ⊤ := by
      have : ENNReal.ofReal (1 - t) ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero]; linarith
      simp [ENNReal.mul_top this]
    rw [h_rhs]; exact le_top

  set A : ℝ := a.toReal with hA_def
  set B : ℝ := b.toReal with hB_def
  have hA_nn : (0 : ℝ) ≤ A := ENNReal.toReal_nonneg
  have hB_nn : (0 : ℝ) ≤ B := ENNReal.toReal_nonneg
  have hofa : ENNReal.ofReal A = a := ENNReal.ofReal_toReal ha
  have hofb : ENNReal.ofReal B = b := ENNReal.ofReal_toReal hb
  have h_real : A ^ t * B ^ (1 - t) ≤ t * A + (1 - t) * B :=
    Real.geom_mean_le_arith_mean2_weighted ht_pos.le h1t_pos.le hA_nn hB_nn
      (by linarith)
  have hAt_nn : (0 : ℝ) ≤ A ^ t := Real.rpow_nonneg hA_nn t
  have hBt_nn : (0 : ℝ) ≤ B ^ (1 - t) := Real.rpow_nonneg hB_nn (1 - t)
  calc a ^ t * b ^ (1 - t)
      = ENNReal.ofReal A ^ t * ENNReal.ofReal B ^ (1 - t) := by rw [hofa, hofb]
    _ = ENNReal.ofReal (A ^ t) * ENNReal.ofReal (B ^ (1 - t)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hA_nn ht_pos.le,
            ENNReal.ofReal_rpow_of_nonneg hB_nn h1t_pos.le]
    _ = ENNReal.ofReal (A ^ t * B ^ (1 - t)) := by
        rw [← ENNReal.ofReal_mul hAt_nn]
    _ ≤ ENNReal.ofReal (t * A + (1 - t) * B) := ENNReal.ofReal_le_ofReal h_real
    _ = ENNReal.ofReal (t * A) + ENNReal.ofReal ((1 - t) * B) :=
        ENNReal.ofReal_add (mul_nonneg ht_pos.le hA_nn)
          (mul_nonneg h1t_pos.le hB_nn)
    _ = ENNReal.ofReal t * a + ENNReal.ofReal (1 - t) * b := by
        rw [ENNReal.ofReal_mul ht_pos.le, ENNReal.ofReal_mul h1t_pos.le,
            hofa, hofb]

private theorem prekopaLeindler_1d_arithBound
    {f g h : ℝ → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y))
    (h_ess_eq : essSup f volume = essSup g volume) :
    ENNReal.ofReal t * (∫⁻ x, f x) + ENNReal.ofReal (1 - t) * (∫⁻ y, g y)
      ≤ ∫⁻ z, h z := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  set M : ℝ≥0∞ := essSup f volume with hM_def

  have h_pos_meas : ∀ {φ : ℝ → ℝ≥0∞}, essSup φ volume = M →
      ∀ {β : ℝ≥0∞}, β < M → 0 < volume {x | β < φ x} := by
    intro φ hφ_ess β hβ
    by_contra h_neg
    rw [not_lt, nonpos_iff_eq_zero] at h_neg
    have h_ae : φ ≤ᵐ[volume] fun _ => β := by
      rw [Filter.EventuallyLE, MeasureTheory.ae_iff]
      simpa using h_neg
    have : essSup φ volume ≤ β := essSup_le_of_ae_le β h_ae
    rw [hφ_ess] at this
    exact absurd this (not_le.mpr hβ)

  have h_null_meas : ∀ {φ : ℝ → ℝ≥0∞}, essSup φ volume = M →
      ∀ {β : ℝ≥0∞}, M ≤ β → volume {x | β < φ x} = 0 := by
    intro φ hφ_ess β hβ
    have h_essSup_le : essSup φ volume ≤ β := hφ_ess.trans_le hβ

    have h_sub : {x | β < φ x} ⊆ {x | essSup φ volume < φ x} :=
      fun x hx => lt_of_le_of_lt h_essSup_le hx
    refine le_antisymm ?_ (by positivity)
    calc volume {x | β < φ x}
        ≤ volume {x | essSup φ volume < φ x} := MeasureTheory.measure_mono h_sub
      _ = 0 := meas_essSup_lt

  let volF : ℝ → ℝ≥0∞ := fun α => volume {x | ENNReal.ofReal α < f x}
  let volG : ℝ → ℝ≥0∞ := fun α => volume {y | ENNReal.ofReal α < g y}
  let volH : ℝ → ℝ≥0∞ := fun α => volume {z | ENNReal.ofReal α < h z}
  have hvolF_meas : Measurable volF :=
    measurable_measure_prodMk_left
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
        (hf_meas.comp measurable_snd))
  have hvolG_meas : Measurable volG :=
    measurable_measure_prodMk_left
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
        (hg_meas.comp measurable_snd))

  have h_pointwise : ∀ α : ℝ, 0 < α →
      ENNReal.ofReal t * volF α + ENNReal.ofReal (1 - t) * volG α ≤ volH α := by
    intro α hα
    have hα_pos_e : (0 : ℝ≥0∞) < ENNReal.ofReal α :=
      ENNReal.ofReal_pos.mpr hα
    have hα_top : ENNReal.ofReal α ≠ ⊤ := ENNReal.ofReal_ne_top
    by_cases hαM : ENNReal.ofReal α < M
    ·
      have hA_pos : 0 < volume {x | ENNReal.ofReal α < f x} :=
        h_pos_meas hM_def.symm hαM
      have hB_pos : 0 < volume {y | ENNReal.ofReal α < g y} :=
        h_pos_meas (h_ess_eq.symm.trans hM_def.symm) hαM
      have hA_ne : ({x | ENNReal.ofReal α < f x} : Set ℝ).Nonempty :=
        MeasureTheory.nonempty_of_measure_ne_zero hA_pos.ne'
      have hB_ne : ({y | ENNReal.ofReal α < g y} : Set ℝ).Nonempty :=
        MeasureTheory.nonempty_of_measure_ne_zero hB_pos.ne'
      exact prekopaLeindler_1d_levelMeasureBound hf_meas hg_meas hh_meas
        ht_pos ht_lt h_le hα_pos_e hα_top hA_ne hB_ne
    ·
      rw [not_lt] at hαM
      have hf_null : volF α = 0 := h_null_meas hM_def.symm hαM
      have hg_null : volG α = 0 := h_null_meas (h_ess_eq.symm.trans hM_def.symm) hαM
      change ENNReal.ofReal t * volF α + ENNReal.ofReal (1 - t) * volG α ≤ volH α
      rw [hf_null, hg_null, mul_zero, mul_zero, zero_add]
      positivity

  rw [lintegral_eq_lintegral_meas_lt_ennreal hf_meas,
      lintegral_eq_lintegral_meas_lt_ennreal hg_meas,
      lintegral_eq_lintegral_meas_lt_ennreal hh_meas]

  change ENNReal.ofReal t * (∫⁻ α in Ioi (0:ℝ), volF α)
       + ENNReal.ofReal (1 - t) * (∫⁻ α in Ioi (0:ℝ), volG α)
       ≤ ∫⁻ α in Ioi (0:ℝ), volH α

  rw [← MeasureTheory.lintegral_const_mul _ hvolF_meas,
      ← MeasureTheory.lintegral_const_mul _ hvolG_meas]

  rw [← MeasureTheory.lintegral_add_left (hvolF_meas.const_mul _)]

  exact MeasureTheory.setLIntegral_mono'
    measurableSet_Ioi (fun α hα => h_pointwise α hα)

private theorem prekopaLeindler_1d_essBdd
    {f g h : ℝ → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y))
    (hMf_top : essSup f volume ≠ ⊤) (hMg_top : essSup g volume ≠ ⊤) :
    (∫⁻ x, f x) ^ t * (∫⁻ y, g y) ^ (1 - t) ≤ ∫⁻ z, h z := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  set Mf := essSup f volume with hMf_def
  set Mg := essSup g volume with hMg_def

  by_cases hMf_zero : Mf = 0
  · have hf_int_zero : ∫⁻ x, f x = 0 := by
      rw [MeasureTheory.lintegral_eq_zero_iff hf_meas]
      filter_upwards [ENNReal.ae_le_essSup f] with x hx
      rw [← hMf_def, hMf_zero] at hx
      exact le_antisymm hx (by positivity)
    rw [hf_int_zero, ENNReal.zero_rpow_of_pos ht_pos, zero_mul]
    positivity

  by_cases hMg_zero : Mg = 0
  · have hg_int_zero : ∫⁻ y, g y = 0 := by
      rw [MeasureTheory.lintegral_eq_zero_iff hg_meas]
      filter_upwards [ENNReal.ae_le_essSup g] with y hy
      rw [← hMg_def, hMg_zero] at hy
      exact le_antisymm hy (by positivity)
    rw [hg_int_zero, ENNReal.zero_rpow_of_pos h1t_pos, mul_zero]
    positivity

  set c : ℝ≥0∞ := Mg / Mf with hc_def
  have hc_pos : (0 : ℝ≥0∞) < c := ENNReal.div_pos hMg_zero hMf_top
  have hc_top : c ≠ ⊤ := by
    rw [hc_def]
    exact (ENNReal.div_lt_top hMg_top hMf_zero).ne
  have hcMf_eq_Mg : c * Mf = Mg := by
    rw [hc_def, ENNReal.div_mul_cancel hMf_zero hMf_top]

  set f' : ℝ → ℝ≥0∞ := fun x => c * f x with hf'_def
  set h' : ℝ → ℝ≥0∞ := fun z => c ^ t * h z with hh'_def
  have hf'_meas : Measurable f' := hf_meas.const_mul c
  have hh'_meas : Measurable h' := hh_meas.const_mul (c ^ t)

  have hf'_essSup : essSup f' volume = Mg := by
    change essSup (fun x => c * f x) volume = Mg
    rw [ENNReal.essSup_const_mul, hcMf_eq_Mg]

  have h_le' : ∀ x y : ℝ,
      f' x ^ t * g y ^ (1 - t) ≤ h' (t * x + (1 - t) * y) := by
    intro x y
    change (c * f x) ^ t * g y ^ (1 - t) ≤ c ^ t * h (t * x + (1 - t) * y)
    rw [ENNReal.mul_rpow_of_nonneg _ _ ht_pos.le, mul_assoc]
    gcongr
    exact h_le x y

  have h_amgm := ennreal_geom_mean_le_arith_mean2_weighted ht_pos ht_lt
    (∫⁻ x, f' x) (∫⁻ y, g y)
  have h_arith := prekopaLeindler_1d_arithBound hf'_meas hg_meas hh'_meas
    ht_pos ht_lt h_le' (hf'_essSup.trans hMg_def.symm)
  have h_pl_rescaled :
      (∫⁻ x, f' x) ^ t * (∫⁻ y, g y) ^ (1 - t) ≤ ∫⁻ z, h' z :=
    le_trans h_amgm h_arith

  rw [show ∫⁻ x, f' x = c * ∫⁻ x, f x from
        MeasureTheory.lintegral_const_mul c hf_meas,
      show ∫⁻ z, h' z = c ^ t * ∫⁻ z, h z from
        MeasureTheory.lintegral_const_mul (c ^ t) hh_meas,
      ENNReal.mul_rpow_of_nonneg _ _ ht_pos.le, mul_assoc] at h_pl_rescaled

  have hct_ne_zero : c ^ t ≠ 0 := (ENNReal.rpow_pos hc_pos hc_top).ne'
  have hct_ne_top : c ^ t ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg ht_pos.le hc_top).ne

  rw [mul_comm (c ^ t) _, mul_comm (c ^ t) _] at h_pl_rescaled
  exact (ENNReal.mul_le_mul_iff_left hct_ne_zero hct_ne_top).mp h_pl_rescaled

theorem prekopaLeindler_1d
    {f g h : ℝ → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y)) :
    (∫⁻ x, f x) ^ t * (∫⁻ y, g y) ^ (1 - t) ≤ ∫⁻ z, h z := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt

  set fN : ℕ → ℝ → ℝ≥0∞ := fun n x => f x ⊓ (n : ℝ≥0∞) with hfN_def
  set gN : ℕ → ℝ → ℝ≥0∞ := fun n y => g y ⊓ (n : ℝ≥0∞) with hgN_def
  have hfN_meas : ∀ n, Measurable (fN n) := fun n => hf_meas.inf measurable_const
  have hgN_meas : ∀ n, Measurable (gN n) := fun n => hg_meas.inf measurable_const
  have hfN_essSup_top : ∀ n, essSup (fN n) volume ≠ ⊤ := fun n => by
    have h_le_n : essSup (fN n) volume ≤ (n : ℝ≥0∞) :=
      essSup_le_of_ae_le _ (Filter.Eventually.of_forall fun _ => inf_le_right)
    exact ne_of_lt (lt_of_le_of_lt h_le_n ENNReal.coe_lt_top)
  have hgN_essSup_top : ∀ n, essSup (gN n) volume ≠ ⊤ := fun n => by
    have h_le_n : essSup (gN n) volume ≤ (n : ℝ≥0∞) :=
      essSup_le_of_ae_le _ (Filter.Eventually.of_forall fun _ => inf_le_right)
    exact ne_of_lt (lt_of_le_of_lt h_le_n ENNReal.coe_lt_top)

  have h_le_N : ∀ n m, ∀ x y : ℝ,
      fN n x ^ t * gN m y ^ (1 - t) ≤ h (t * x + (1 - t) * y) := by
    intro n m x y
    calc fN n x ^ t * gN m y ^ (1 - t)
        ≤ f x ^ t * g y ^ (1 - t) := by
          gcongr <;> exact inf_le_left
      _ ≤ h (t * x + (1 - t) * y) := h_le x y

  have h_per_nm : ∀ n m,
      (∫⁻ x, fN n x) ^ t * (∫⁻ y, gN m y) ^ (1 - t) ≤ ∫⁻ z, h z := fun n m =>
    prekopaLeindler_1d_essBdd (hfN_meas n) (hgN_meas m) hh_meas ht_pos ht_lt
      (h_le_N n m) (hfN_essSup_top n) (hgN_essSup_top m)

  have hfN_mono : Monotone fun n => ∫⁻ x, fN n x := by
    intro n m hnm
    apply MeasureTheory.lintegral_mono
    intro x; exact inf_le_inf_left _ (by exact_mod_cast hnm)
  have hgN_mono : Monotone fun m => ∫⁻ y, gN m y := by
    intro n m hnm
    apply MeasureTheory.lintegral_mono
    intro y; exact inf_le_inf_left _ (by exact_mod_cast hnm)
  have hfN_iSup : ⨆ n, ∫⁻ x, fN n x = ∫⁻ x, f x := by
    rw [← MeasureTheory.lintegral_iSup hfN_meas (fun n m hnm x =>
      inf_le_inf_left _ (by exact_mod_cast hnm))]
    apply MeasureTheory.lintegral_congr
    intro x
    simp only [fN]
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  have hgN_iSup : ⨆ m, ∫⁻ y, gN m y = ∫⁻ y, g y := by
    rw [← MeasureTheory.lintegral_iSup hgN_meas (fun n m hnm y =>
      inf_le_inf_left _ (by exact_mod_cast hnm))]
    apply MeasureTheory.lintegral_congr
    intro y
    simp only [gN]
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]

  have h_rpow_iSup : ∀ (a : ℕ → ℝ≥0∞) (p : ℝ), 0 ≤ p → Monotone a →
      (⨆ n, a n) ^ p = ⨆ n, a n ^ p := by
    intro a p hp ha_mono
    have h_tendsto : Filter.Tendsto a Filter.atTop (𝓝 (⨆ n, a n)) :=
      tendsto_atTop_iSup ha_mono
    have h_tendsto_pow : Filter.Tendsto (fun n => a n ^ p) Filter.atTop
        (𝓝 ((⨆ n, a n) ^ p)) :=
      (ENNReal.continuous_rpow_const.tendsto _).comp h_tendsto
    have ha_pow_mono : Monotone (fun n => a n ^ p) := fun n m hnm =>
      ENNReal.rpow_le_rpow (ha_mono hnm) hp
    exact tendsto_nhds_unique h_tendsto_pow (tendsto_atTop_iSup ha_pow_mono)
  rw [← hfN_iSup, ← hgN_iSup]

  rw [h_rpow_iSup _ t ht_pos.le hfN_mono,
      h_rpow_iSup _ (1 - t) h1t_pos.le hgN_mono]

  rw [ENNReal.iSup_mul]
  refine iSup_le fun n => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun m => ?_

  exact h_per_nm n m

theorem prekopaLeindler.{u}
    {ι : Type u} [Fintype ι]
    {f g h : (ι → ℝ) → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ι → ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t • x + (1 - t) • y)) :
    (∫⁻ x, f x) ^ t * (∫⁻ y, g y) ^ (1 - t) ≤ ∫⁻ z, h z := by

  suffices H : ∀ (κ : Type u) [Fintype κ] (f g h : (κ → ℝ) → ℝ≥0∞),
      Measurable f → Measurable g → Measurable h →
      ∀ {s : ℝ}, 0 < s → s < 1 →
      (∀ x y : κ → ℝ, f x ^ s * g y ^ (1 - s) ≤ h (s • x + (1 - s) • y)) →
      (∫⁻ x, f x) ^ s * (∫⁻ y, g y) ^ (1 - s) ≤ ∫⁻ z, h z by
    exact H ι f g h hf_meas hg_meas hh_meas ht_pos ht_lt h_le
  intro κ _Fκ
  refine Fintype.induction_empty_option
    (P := fun κ [Fintype κ] => ∀ (f g h : (κ → ℝ) → ℝ≥0∞),
      Measurable f → Measurable g → Measurable h →
      ∀ {s : ℝ}, 0 < s → s < 1 →
      (∀ x y : κ → ℝ, f x ^ s * g y ^ (1 - s) ≤ h (s • x + (1 - s) • y)) →
      (∫⁻ x, f x) ^ s * (∫⁻ y, g y) ^ (1 - s) ≤ ∫⁻ z, h z) ?_ ?_ ?_ κ
  ·

    intro α β _Fβ e IH f g h hf hg hh s hs hs1 hle
    let : Fintype α := Fintype.ofEquiv β e.symm
    set ψ : (β → ℝ) ≃ᵐ (α → ℝ) :=
      MeasurableEquiv.piCongrLeft (fun _ : α => ℝ) e.symm with hψ_def

    have hψ_smul : ∀ x y : α → ℝ,
        ψ.symm (s • x + (1 - s) • y) = s • ψ.symm x + (1 - s) • ψ.symm y := fun _ _ => rfl

    have h_vol_fwd : (volume : Measure (β → ℝ)).map ψ = (volume : Measure (α → ℝ)) := by
      conv_lhs => rw [MeasureTheory.volume_pi]
      conv_rhs => rw [MeasureTheory.volume_pi]
      exact MeasureTheory.Measure.pi_map_piCongrLeft e.symm (fun _ : α => volume)
    have h_vol : (volume : Measure (α → ℝ)).map ψ.symm = (volume : Measure (β → ℝ)) := by
      rw [← h_vol_fwd, MeasurableEquiv.map_symm_map]

    have hf' : Measurable (f ∘ ψ.symm) := hf.comp ψ.symm.measurable
    have hg' : Measurable (g ∘ ψ.symm) := hg.comp ψ.symm.measurable
    have hh' : Measurable (h ∘ ψ.symm) := hh.comp ψ.symm.measurable
    have hle' : ∀ x y : α → ℝ,
        (f ∘ ψ.symm) x ^ s * (g ∘ ψ.symm) y ^ (1 - s)
        ≤ (h ∘ ψ.symm) (s • x + (1 - s) • y) := by
      intro x y
      change f (ψ.symm x) ^ s * g (ψ.symm y) ^ (1 - s) ≤ h (ψ.symm (s • x + (1 - s) • y))
      rw [hψ_smul x y]
      exact hle (ψ.symm x) (ψ.symm y)

    have hf_int : ∫⁻ y, f y = ∫⁻ x, f (ψ.symm x) := by
      conv_lhs => rw [show (volume : Measure (β → ℝ))
          = (volume : Measure (α → ℝ)).map ψ.symm from h_vol.symm]
      exact MeasureTheory.lintegral_map hf ψ.symm.measurable
    have hg_int : ∫⁻ y, g y = ∫⁻ x, g (ψ.symm x) := by
      conv_lhs => rw [show (volume : Measure (β → ℝ))
          = (volume : Measure (α → ℝ)).map ψ.symm from h_vol.symm]
      exact MeasureTheory.lintegral_map hg ψ.symm.measurable
    have hh_int : ∫⁻ y, h y = ∫⁻ x, h (ψ.symm x) := by
      conv_lhs => rw [show (volume : Measure (β → ℝ))
          = (volume : Measure (α → ℝ)).map ψ.symm from h_vol.symm]
      exact MeasureTheory.lintegral_map hh ψ.symm.measurable
    rw [hf_int, hg_int, hh_int]
    exact IH (f ∘ ψ.symm) (g ∘ ψ.symm) (h ∘ ψ.symm) hf' hg' hh' hs hs1 hle'
  ·

    intro f g h hf_meas hg_meas hh_meas s hs_pos hs_lt h_le
    have h_volume : (volume : Measure (PEmpty → ℝ))
        = Measure.dirac (fun a : PEmpty => isEmptyElim a) :=
      Measure.volume_pi_eq_dirac _
    rw [h_volume, lintegral_dirac' _ hf_meas, lintegral_dirac' _ hg_meas,
        lintegral_dirac' _ hh_meas]
    have h_pl := h_le (fun a => isEmptyElim a) (fun a => isEmptyElim a)
    have h_smul : s • (fun a : PEmpty => isEmptyElim a : PEmpty → ℝ)
                  + (1 - s) • (fun a : PEmpty => isEmptyElim a : PEmpty → ℝ)
                = (fun a : PEmpty => isEmptyElim a : PEmpty → ℝ) := by
      funext a; exact isEmptyElim a
    rwa [h_smul] at h_pl
  ·

    intro α _Fα IH f g h hf hg hh s hs hs1 hle
    let E : ((i : Option α) → ℝ) ≃ᵐ ((i : α) → ℝ) × ℝ :=
      MeasurableEquiv.piOptionEquivProd (fun _ : Option α => ℝ)

    have hE_none : ∀ (x' : α → ℝ) (u : ℝ),
        E.symm (x', u) none = u := fun _ _ => rfl
    have hE_some : ∀ (x' : α → ℝ) (u : ℝ) (a : α),
        E.symm (x', u) (some a) = x' a := fun _ _ _ => rfl

    have hE_smul : ∀ (x' y' : α → ℝ) (u v : ℝ),
        s • E.symm (x', u) + (1 - s) • E.symm (y', v)
        = E.symm (s • x' + (1 - s) • y', s * u + (1 - s) * v) := by
      intro x' y' u v
      funext i
      cases i with
      | none =>
        simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
        change s * u + (1 - s) * v = s * u + (1 - s) * v
        rfl
      | some a =>
        simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
        change s * x' a + (1 - s) * y' a = s * x' a + (1 - s) * y' a
        rfl

    have h_vol : ((volume : Measure (α → ℝ)).prod (volume : Measure ℝ)).map E.symm
        = (volume : Measure (Option α → ℝ)) := by
      conv_rhs => rw [MeasureTheory.volume_pi]
      conv_lhs => rw [show (volume : Measure (α → ℝ))
          = MeasureTheory.Measure.pi (fun _ : α => volume) from MeasureTheory.volume_pi]
      exact MeasureTheory.Measure.pi_map_piOptionEquivProd
        (fun _ : Option α => volume)

    set F : ℝ → ℝ≥0∞ := fun u => ∫⁻ x' : α → ℝ, f (E.symm (x', u)) with hF_def
    set G : ℝ → ℝ≥0∞ := fun v => ∫⁻ y' : α → ℝ, g (E.symm (y', v)) with hG_def
    set H_marg : ℝ → ℝ≥0∞ := fun w => ∫⁻ z' : α → ℝ, h (E.symm (z', w)) with hH_def

    have hf_comp : Measurable (fun p : (α → ℝ) × ℝ => f (E.symm p)) :=
      hf.comp E.symm.measurable
    have hg_comp : Measurable (fun p : (α → ℝ) × ℝ => g (E.symm p)) :=
      hg.comp E.symm.measurable
    have hh_comp : Measurable (fun p : (α → ℝ) × ℝ => h (E.symm p)) :=
      hh.comp E.symm.measurable
    have hF_meas : Measurable F := Measurable.lintegral_prod_left' hf_comp
    have hG_meas : Measurable G := Measurable.lintegral_prod_left' hg_comp
    have hH_marg_meas : Measurable H_marg := Measurable.lintegral_prod_left' hh_comp

    have h_FGH_le : ∀ u v : ℝ,
        F u ^ s * G v ^ (1 - s) ≤ H_marg (s * u + (1 - s) * v) := by
      intro u v
      have hf_slice : Measurable (fun x' : α → ℝ => f (E.symm (x', u))) :=
        hf.comp (E.symm.measurable.comp (measurable_id.prodMk measurable_const))
      have hg_slice : Measurable (fun y' : α → ℝ => g (E.symm (y', v))) :=
        hg.comp (E.symm.measurable.comp (measurable_id.prodMk measurable_const))
      have hh_slice : Measurable (fun z' : α → ℝ =>
          h (E.symm (z', s * u + (1 - s) * v))) :=
        hh.comp (E.symm.measurable.comp (measurable_id.prodMk measurable_const))
      have h_slice_le : ∀ x' y' : α → ℝ,
          f (E.symm (x', u)) ^ s * g (E.symm (y', v)) ^ (1 - s)
          ≤ h (E.symm (s • x' + (1 - s) • y', s * u + (1 - s) * v)) := by
        intro x' y'
        have h_pl := hle (E.symm (x', u)) (E.symm (y', v))
        rw [hE_smul] at h_pl
        exact h_pl
      exact IH _ _ _ hf_slice hg_slice hh_slice hs hs1 h_slice_le

    have h_1d := prekopaLeindler_1d hF_meas hG_meas hH_marg_meas hs hs1 h_FGH_le

    have h_int_split : ∀ (k : (Option α → ℝ) → ℝ≥0∞), Measurable k →
        ∫⁻ z, k z = ∫⁻ u : ℝ, ∫⁻ x' : α → ℝ, k (E.symm (x', u)) := by
      intro k hk
      conv_lhs => rw [show (volume : Measure (Option α → ℝ))
          = ((volume : Measure (α → ℝ)).prod (volume : Measure ℝ)).map E.symm
        from h_vol.symm]
      rw [MeasureTheory.lintegral_map hk E.symm.measurable]
      exact MeasureTheory.lintegral_prod_symm' _ (hk.comp E.symm.measurable)
    rw [h_int_split f hf, h_int_split g hg, h_int_split h hh]
    exact h_1d

end AsymptoticStatistics

end OAI
end

section
-- module Solutions.OAIQ258_II.KLS_Convexity_Prekopa
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace LeanBlast.KLS

theorem prekopaLeindler_space {n : ℕ} {f g h : Space n → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hfg : ∀ x y : Space n,
      f x ^ t * g y ^ (1 - t) ≤ h (t • x + (1 - t) • y)) :
    (∫⁻ x, f x) ^ t * (∫⁻ y, g y) ^ (1 - t) ≤ ∫⁻ z, h z := by
  have he := PiLp.volume_preserving_toLp (Fin n)
  have hp := AsymptoticStatistics.prekopaLeindler
    (hf.comp he.measurable) (hg.comp he.measurable) (hh.comp he.measurable)
    ht0 ht1 (fun x y => hfg (WithLp.toLp 2 x) (WithLp.toLp 2 y))
  simpa only [Function.comp_apply, he.lintegral_comp hf, he.lintegral_comp hg,
    he.lintegral_comp hh] using hp

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ258_II.KLS_Convexity_PrekopaReal
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
attribute [-simp] _root_.OAI.LeanBlast.KLS.blMomentDeriv_zero _root_.OAI.LeanBlast.KLS.blMoment_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace LeanBlast.KLS

theorem prekopaLeindler_integral {n : ℕ} {f g h : Space n → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hh0 : ∀ x, 0 ≤ h x)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfi : Integrable f) (hgi : Integrable g) (hhi : Integrable h)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hfg : ∀ x y : Space n,
      f x ^ t * g y ^ (1 - t) ≤ h (t • x + (1 - t) • y)) :
    (∫ x, f x) ^ t * (∫ y, g y) ^ (1 - t) ≤ ∫ z, h z := by
  have hp := prekopaLeindler_space hf.ennreal_ofReal hg.ennreal_ofReal hh.ennreal_ofReal
    ht0 ht1 (fun x y => by
      rw [ENNReal.ofReal_rpow_of_nonneg (hf0 x) ht0.le,
        ENNReal.ofReal_rpow_of_nonneg (hg0 y) (sub_pos.mpr ht1).le,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (hf0 x) t)]
      exact ENNReal.ofReal_le_ofReal (hfg x y))
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ hf0),
    ← ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hg0),
    ← ofReal_integral_eq_lintegral_ofReal hhi (ae_of_all _ hh0)] at hp
  rw [ENNReal.ofReal_rpow_of_nonneg (integral_nonneg hf0) ht0.le,
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg hg0) (sub_pos.mpr ht1).le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (integral_nonneg hf0) t)] at hp
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hh0)).mp hp

theorem concaveOn_log_integral {E : Type*} [AddCommGroup E] [Module ℝ E]
    {n : ℕ} {S : Set E} (hS : Convex ℝ S) (f : E → Space n → ℝ)
    (hf0 : ∀ u ∈ S, ∀ x, 0 ≤ f u x)
    (hf : ∀ u ∈ S, Measurable (f u))
    (hfi : ∀ u ∈ S, Integrable (f u))
    (hpos : ∀ u ∈ S, 0 < ∫ x, f u x)
    (hjoint : ∀ u ∈ S, ∀ v ∈ S, ∀ x y, ∀ t : ℝ, 0 < t → t < 1 →
      f u x ^ t * f v y ^ (1 - t) ≤ f (t • u + (1 - t) • v) (t • x + (1 - t) • y)) :
    ConcaveOn ℝ S (fun u => Real.log (∫ x, f u x)) := by
  refine ⟨hS, ?_⟩
  intro u hu v hv a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simp [ha0, hb1]
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simp [hb0, ha1]
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hba : 1 - a = b := by linarith
  have huv : a • u + b • v ∈ S := hS hu hv ha hb hab
  have hp := prekopaLeindler_integral (hf0 u hu) (hf0 v hv) (hf0 _ huv)
    (hf u hu) (hf v hv) (hf _ huv) (hfi u hu) (hfi v hv) (hfi _ huv)
    ha' (by linarith) (by
      intro x y
      simpa only [hba] using hjoint u hu v hv x y a ha' (by linarith))
  rw [hba] at hp
  apply (Real.le_log_iff_exp_le (hpos _ huv)).mpr
  simpa only [smul_eq_mul, Real.rpow_def_of_pos (hpos u hu),
    Real.rpow_def_of_pos (hpos v hv), Real.exp_add, mul_comm] using hp

theorem concaveOn_log_integral_exp_neg {E : Type*} [AddCommGroup E] [Module ℝ E]
    {n : ℕ} {S : Set E} (hS : Convex ℝ S) (F : E × Space n → ℝ)
    (hF : ConvexOn ℝ (S ×ˢ (univ : Set (Space n))) F)
    (hmeas : ∀ u ∈ S, Measurable (fun x => Real.exp (-F (u, x))))
    (hint : ∀ u ∈ S, Integrable (fun x => Real.exp (-F (u, x)))) :
    ConcaveOn ℝ S (fun u => Real.log (∫ x, Real.exp (-F (u, x)))) := by
  apply concaveOn_log_integral hS (fun u x => Real.exp (-F (u, x)))
    (fun u hu x => (Real.exp_pos _).le) hmeas hint
  · intro u hu
    rw [integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) (hint u hu)]
    have hs : Function.support (fun x : Space n => Real.exp (-F (u, x))) = univ := by
      ext x
      simp [Function.mem_support, Real.exp_ne_zero]
    rw [hs]
    exact Measure.measure_univ_pos.mpr (NeZero.ne volume)
  · intro u hu v hv x y t ht0 ht1
    have hc := hF.2 (x := (u, x)) ⟨hu, mem_univ x⟩ (y := (v, y)) ⟨hv, mem_univ y⟩
      ht0.le (sub_pos.mpr ht1).le (by ring)
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.rpow_def_of_pos (Real.exp_pos _),
      Real.log_exp, Real.log_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    change F (t • u + (1 - t) • v, t • x + (1 - t) • y) ≤
      t * F (u, x) + (1 - t) * F (v, y) at hc
    nlinarith only [hc]

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ258_II.KLS_Spectral_BrascampLiebMoments
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace LeanBlast.KLS

section BoundedKernel

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  {h q : α → ℝ} {B : ℝ}

private theorem boundedKernel_bound (Φ : ℝ → ℝ → ℝ → ℝ)
    (hΦ : Continuous (fun p : ℝ × ℝ × ℝ => Φ p.1 p.2.1 p.2.2)) (B : ℝ) :
    ∃ C : ℝ, ∀ t ∈ Icc (-1 : ℝ) 1, ∀ a ∈ Icc (-B) B, ∀ b ∈ Icc (-B) B,
      ‖Φ t a b‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).exists_bound_of_continuousOn
    hΦ.continuousOn
  exact ⟨C, fun t ht a ha b hb => hC (t, a, b) ⟨ht, ha, hb⟩⟩

theorem boundedKernel_integrable (Φ : ℝ → ℝ → ℝ → ℝ)
    (hΦ : Continuous (fun p : ℝ × ℝ × ℝ => Φ p.1 p.2.1 p.2.2))
    (hh : Measurable h) (hq : Measurable q)
    (hhB : ∀ x, |h x| ≤ B) (hqB : ∀ x, |q x| ≤ B)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    Integrable (fun x => Φ t (h x) (q x)) μ := by
  obtain ⟨C, hC⟩ := boundedKernel_bound Φ hΦ B
  apply (integrable_const C).mono'
    (hΦ.measurable.comp (measurable_const.prodMk (hh.prodMk hq))).aestronglyMeasurable
  exact ae_of_all _ fun x => hC t ht (h x) (abs_le.mp (hhB x)) (q x) (abs_le.mp (hqB x))

theorem boundedKernel_hasDerivAt_integral (Φ Φ' : ℝ → ℝ → ℝ → ℝ)
    (hΦ : Continuous (fun p : ℝ × ℝ × ℝ => Φ p.1 p.2.1 p.2.2))
    (hΦ' : Continuous (fun p : ℝ × ℝ × ℝ => Φ' p.1 p.2.1 p.2.2))
    (hd : ∀ t a b, HasDerivAt (fun s => Φ s a b) (Φ' t a b) t)
    (hh : Measurable h) (hq : Measurable q)
    (hhB : ∀ x, |h x| ≤ B) (hqB : ∀ x, |q x| ≤ B)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun s => ∫ x, Φ s (h x) (q x) ∂μ)
      (∫ x, Φ' t (h x) (q x) ∂μ) t := by
  obtain ⟨C, hC⟩ := boundedKernel_bound Φ' hΦ' B
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun s x => Φ s (h x) (q x))
    (F' := fun s x => Φ' s (h x) (q x))
    (bound := fun _ : α => C) (Ioo_mem_nhds ht.1 ht.2) ?_
    (boundedKernel_integrable Φ hΦ hh hq hhB hqB ⟨ht.1.le, ht.2.le⟩) ?_ ?_
    (integrable_const C) ?_).2
  · exact Eventually.of_forall fun s =>
      (hΦ.measurable.comp (measurable_const.prodMk (hh.prodMk hq))).aestronglyMeasurable
  · exact (hΦ'.measurable.comp (measurable_const.prodMk (hh.prodMk hq))).aestronglyMeasurable
  · exact ae_of_all _ fun x s hs =>
      hC s ⟨hs.1.le, hs.2.le⟩ (h x) (abs_le.mp (hhB x)) (q x) (abs_le.mp (hqB x))
  · exact ae_of_all _ fun x s _ => hd s (h x) (q x)

end BoundedKernel

theorem continuous_blWeight :
    Continuous (fun p : ℝ × ℝ × ℝ => blWeight p.1 p.2.1 p.2.2) := by
  unfold blWeight
  fun_prop

theorem continuous_blWeightDeriv :
    Continuous (fun p : ℝ × ℝ × ℝ => blWeightDeriv p.1 p.2.1 p.2.2) := by
  unfold blWeightDeriv blWeight
  fun_prop

theorem continuous_blWeightSecond :
    Continuous (fun p : ℝ × ℝ × ℝ => blWeightSecond p.1 p.2.1 p.2.2) := by
  unfold blWeightSecond blWeight
  fun_prop

theorem hasDerivAt_blWeight (t a b : ℝ) :
    HasDerivAt (fun s => blWeight s a b) (blWeightDeriv t a b) t := by
  have h := ((((hasDerivAt_id' t).fun_neg.mul_const a).fun_sub
    (((hasDerivAt_id' t).fun_pow 2).div_const 2 |>.mul_const b))).exp
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [blWeight, blWeightDeriv])
  ring

theorem hasDerivAt_blWeightDeriv (t a b : ℝ) :
    HasDerivAt (fun s => blWeightDeriv s a b) (blWeightSecond t a b) t := by
  have h := ((hasDerivAt_const t (-a)).fun_sub ((hasDerivAt_id' t).mul_const b)).fun_mul
    (hasDerivAt_blWeight t a b)
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [blWeightSecond, blWeightDeriv])
  ring

section Moments

variable {n : ℕ} (μ : Measure (Space n)) [IsProbabilityMeasure μ]
  (h q : Space n → ℝ)

omit [IsProbabilityMeasure μ] in
theorem blMomentSecond_zero (hh2 : Integrable (fun x => h x ^ 2) μ) (hq : Integrable q μ) :
    blMomentSecond μ h q 0 = (∫ x, h x ^ 2 ∂μ) - ∫ x, q x ∂μ := by
  simp only [blMomentSecond, blWeightSecond, blWeight, neg_zero, zero_mul, add_zero, zero_pow (by norm_num : 2 ≠ 0),
    zero_div, sub_zero, Real.exp_zero, mul_one]
  exact integral_sub hh2 hq

variable {h q} {B : ℝ}

theorem hasDerivAt_blMoment (hh : Measurable h) (hq : Measurable q)
    (hhB : ∀ x, |h x| ≤ B) (hqB : ∀ x, |q x| ≤ B)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (blMoment μ h q) (blMomentDeriv μ h q t) t :=
  boundedKernel_hasDerivAt_integral blWeight blWeightDeriv continuous_blWeight
    continuous_blWeightDeriv hasDerivAt_blWeight hh hq hhB hqB ht

theorem hasDerivAt_blMomentDeriv (hh : Measurable h) (hq : Measurable q)
    (hhB : ∀ x, |h x| ≤ B) (hqB : ∀ x, |q x| ≤ B)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (blMomentDeriv μ h q) (blMomentSecond μ h q t) t :=
  boundedKernel_hasDerivAt_integral blWeightDeriv blWeightSecond continuous_blWeightDeriv
    continuous_blWeightSecond hasDerivAt_blWeightDeriv hh hq hhB hqB ht

theorem blMoment_pos (hh : Measurable h) (hq : Measurable q)
    (hhB : ∀ x, |h x| ≤ B) (hqB : ∀ x, |q x| ≤ B)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : 0 < blMoment μ h q t :=
  integral_exp_pos (boundedKernel_integrable blWeight continuous_blWeight hh hq hhB hqB ht)

theorem hasDerivAt_blLogMoment (hh : Measurable h) (hq : Measurable q)
    (hhB : ∀ x, |h x| ≤ B) (hqB : ∀ x, |q x| ≤ B)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (blLogMoment μ h q) (blMomentDeriv μ h q t / blMoment μ h q t) t :=
  (hasDerivAt_blMoment μ hh hq hhB hqB ht).log
    (blMoment_pos μ hh hq hhB hqB ⟨ht.1.le, ht.2.le⟩).ne'

theorem hasDerivAt_deriv_blLogMoment_zero (hh : Measurable h) (hq : Measurable q)
    (hhB : ∀ x, |h x| ≤ B) (hqB : ∀ x, |q x| ≤ B) :
    HasDerivAt (deriv (blLogMoment μ h q)) (variance μ h - ∫ x, q x ∂μ) 0 := by
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by constructor <;> norm_num
  have hhint : Integrable h μ := boundedKernel_integrable (fun _ a _ => a)
    (by fun_prop) hh hq hhB hqB (t := 0) ⟨by norm_num, by norm_num⟩
  have hh2int : Integrable (fun x => h x ^ 2) μ := boundedKernel_integrable (fun _ a _ => a ^ 2)
    (by fun_prop) hh hq hhB hqB (t := 0) ⟨by norm_num, by norm_num⟩
  have hqint : Integrable q μ := boundedKernel_integrable (fun _ _ b => b)
    (by fun_prop) hh hq hhB hqB (t := 0) ⟨by norm_num, by norm_num⟩
  have hd := (hasDerivAt_blMomentDeriv μ hh hq hhB hqB h0).div
    (hasDerivAt_blMoment μ hh hq hhB hqB h0) (by simp)
  have hratio : HasDerivAt (fun t => blMomentDeriv μ h q t / blMoment μ h q t)
      (variance μ h - ∫ x, q x ∂μ) 0 := by
    convert hd using 1
    all_goals try with_reducible_and_instances rfl
    rw [blMomentSecond_zero μ h q hh2int hqint, blMoment_zero, blMomentDeriv_zero,
      variance_eq_integral_sq_sub_sq μ hhint hh2int]
    ring
  apply hratio.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)] with t ht
  exact (hasDerivAt_blLogMoment μ hh hq hhB hqB ht).deriv

theorem variance_le_integral_of_concave_blLogMoment
    (hh : Measurable h) (hq : Measurable q)
    (hhB : ∀ x, |h x| ≤ B) (hqB : ∀ x, |q x| ≤ B)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hc : ConcaveOn ℝ (Ioo (-ε) ε) (blLogMoment μ h q)) :
    variance μ h ≤ ∫ x, q x ∂μ := by
  have hdiff : ∀ t ∈ Ioo (-ε) ε, DifferentiableAt ℝ (blLogMoment μ h q) t := by
    intro t ht
    exact (hasDerivAt_blLogMoment μ hh hq hhB hqB ⟨by linarith [ht.1], by linarith [ht.2]⟩).differentiableAt
  have hant := hc.antitoneOn_deriv hdiff
  have hnonpos := hant.derivWithin_nonpos (x := 0)
  have hd := (hasDerivAt_deriv_blLogMoment_zero μ hh hq hhB hqB).hasDerivWithinAt
    (s := Ioo (-ε) ε)
  rw [hd.derivWithin (isOpen_Ioo.uniqueDiffWithinAt ⟨by linarith, hε⟩)] at hnonpos
  linarith

end Moments

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ258_II.KLS_Convexity_HessianConvexity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set

namespace LeanBlast.KLS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem convexOn_of_second_fderiv_nonneg {f : E → ℝ} {s : Set E}
    (hf : ContDiff ℝ 2 f) (hs : Convex ℝ s)
    (hH : ∀ x ∈ s, ∀ v : E, 0 ≤ fderiv ℝ (fderiv ℝ f) x v v) :
    ConvexOn ℝ s f := by
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  let γ : ℝ → E := AffineMap.lineMap x y
  let F : ℝ → ℝ := fun t => f (γ t)
  let F' : ℝ → ℝ := fun t => fderiv ℝ f (γ t) (y - x)
  let F'' : ℝ → ℝ := fun t => fderiv ℝ (fderiv ℝ f) (γ t) (y - x) (y - x)
  have hγ (t : ℝ) : HasDerivAt γ (y - x) t := AffineMap.hasDerivAt_lineMap
  have hF (t : ℝ) : HasDerivAt F (F' t) t :=
    (hf.differentiable (by norm_num) (γ t)).hasFDerivAt.comp_hasDerivAt t (hγ t)
  have hD : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hF' (t : ℝ) : HasDerivAt F' (F'' t) t := by
    have h := ((hD (γ t)).hasFDerivAt.clm_apply
      (hasFDerivAt_const (y - x) (γ t))).comp_hasDerivAt t (hγ t)
    simpa only [F', F'', Function.comp_def, add_apply,
      ContinuousLinearMap.comp_apply, zero_apply,
      ContinuousLinearMap.flip_apply, map_zero, zero_add] using h
  have hc : ConvexOn ℝ (Icc (0 : ℝ) 1) F :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun t _ => (hF t).continuousAt.continuousWithinAt)
      (fun t _ => (hF t).hasDerivWithinAt)
      (fun t _ => (hF' t).hasDerivWithinAt)
      (fun t ht => hH (γ t) (hs.lineMap_mem hx hy (interior_subset ht)) (y - x))
  have h := hc.2 (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num) ha hb hab
  have hab' : 1 - b = a := by linarith
  simpa [F, γ, AffineMap.lineMap_apply_module, smul_eq_mul, hab'] using h

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ258_II.KLS_Spectral_BrascampLiebCurvature
attribute [-simp] _root_.OAI.LeanBlast.KLS.blMomentDeriv_zero _root_.OAI.LeanBlast.KLS.blMoment_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Matrix MeasureTheory InnerProductSpace
open scoped BigOperators ContDiff Topology Matrix.Norms.Elementwise

namespace LeanBlast.KLS

theorem bl_contDiff_gradient {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (gradient f) := by
  exact (toDual ℝ (Space n)).symm.contDiff.comp (hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

theorem bl_contDiff_hessianMatrix {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (hessianMatrix f) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact (((hf.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply
    contDiff_const).clm_apply contDiff_const

section MatrixSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {A : E → Matrix ι ι ℝ}

theorem contDiff_matrix_det (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (fun x => (A x).det) := by
  simp only [Matrix.det_apply']
  fun_prop

theorem contDiff_matrix_adjugate (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (fun x => (A x).adjugate) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simp only [Matrix.adjugate_apply]
  apply contDiff_matrix_det
  apply contDiff_pi.mpr
  intro a
  apply contDiff_pi.mpr
  intro b
  by_cases h : a = j
  · subst a
    simp only [Matrix.updateRow_self]
    exact contDiff_const
  · simp only [Matrix.updateRow_ne h]
    exact (contDiff_pi.mp (contDiff_pi.mp hA a)) b

theorem contDiff_matrix_inv (hA : ContDiff ℝ ∞ A) (hdet : ∀ x, (A x).det ≠ 0) :
    ContDiff ℝ ∞ (fun x => (A x)⁻¹) := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv]
  exact ((contDiff_matrix_det hA).inv hdet).smul (contDiff_matrix_adjugate hA)

end MatrixSmooth

theorem steinGamma_self_eq_dotProduct {n : ℕ} (V h : Space n → ℝ) (x : Space n) :
    steinGamma V h h x =
      (fun i => gradient h x i) ⬝ᵥ ((hessianMatrix V x)⁻¹ *ᵥ fun i => gradient h x i) := by
  simp [steinGamma, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem contDiff_steinGamma_self {n : ℕ} {V h : Space n → ℝ}
    (hV : ContDiff ℝ ∞ V) (hh : ContDiff ℝ ∞ h)
    (hpos : ∀ x, (hessianMatrix V x).PosDef) :
    ContDiff ℝ ∞ (steinGamma V h h) := by
  have hi : ContDiff ℝ ∞ (fun x => (hessianMatrix V x)⁻¹) :=
    contDiff_matrix_inv (bl_contDiff_hessianMatrix hV) fun x => (hpos x).det_pos.ne'
  have hg := bl_contDiff_gradient hh
  unfold steinGamma
  fun_prop

theorem hasCompactSupport_steinGamma_self {n : ℕ} (V : Space n → ℝ)
    {h : Space n → ℝ} (hh : IsTestFunction h) : HasCompactSupport (steinGamma V h h) := by
  apply HasCompactSupport.intro hh.hasCompactSupport_gradient.isCompact
  intro x hx
  have hzero : gradient h x = 0 := image_eq_zero_of_notMem_tsupport hx
  simp only [steinGamma, hzero, PiLp.zero_apply, zero_mul, Finset.sum_const_zero]

theorem sum_standardBasisVector {n : ℕ} (v : Space n) :
    (∑ i, v i • standardBasisVector i) = v := by
  simpa only [standardBasisVector, EuclideanSpace.basisFun_repr] using
    (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v

theorem second_fderiv_eq_hessianMatrix {n : ℕ} (V : Space n → ℝ) (x u v : Space n) :
    fderiv ℝ (fderiv ℝ V) x u v =
      (fun i => u i) ⬝ᵥ (hessianMatrix V x *ᵥ fun i => v i) := by
  calc
    _ = fderiv ℝ (fderiv ℝ V) x (∑ i, u i • standardBasisVector i)
      (∑ j, v j • standardBasisVector j) := by rw [sum_standardBasisVector, sum_standardBasisVector]
    _ = _ := by
      simp [map_sum, hessianMatrix, Matrix.mulVec, dotProduct, Finset.mul_sum,
        mul_comm, mul_left_comm]
      exact Finset.sum_comm

theorem fderiv_eq_gradient_dotProduct {n : ℕ} {h : Space n → ℝ} {x : Space n}
    (hh : DifferentiableAt ℝ h x) (v : Space n) :
    fderiv ℝ h x v = (fun i => gradient h x i) ⬝ᵥ (fun i => v i) := by
  rw [hh.hasGradientAt.fderiv_apply, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial, dotProduct_comm]

theorem quadratic_schur_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℝ} (hH : H.PosDef) (g v : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (s : ℝ) (hsv : s ≠ 0 ∨ v ≠ 0) :
    0 < v ⬝ᵥ H *ᵥ v + 2 * s * (g ⬝ᵥ v) +
      (g ⬝ᵥ H⁻¹ *ᵥ g + δ) * s ^ 2 := by
  have hmul : H *ᵥ (H⁻¹ *ᵥ g) = g := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'),
      Matrix.one_mulVec]
  have hsym : Hᵀ = H := hH.isHermitian.eq
  have hcross : (H⁻¹ *ᵥ g) ⬝ᵥ H *ᵥ v = g ⬝ᵥ v := by
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, hmul]
  have heq : v ⬝ᵥ H *ᵥ v + 2 * s * (g ⬝ᵥ v) +
      (g ⬝ᵥ H⁻¹ *ᵥ g + δ) * s ^ 2 =
      (v + s • (H⁻¹ *ᵥ g)) ⬝ᵥ H *ᵥ (v + s • (H⁻¹ *ᵥ g)) + δ * s ^ 2 := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hmul]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hcross]
    rw [dotProduct_comm v g, dotProduct_comm (H⁻¹ *ᵥ g) g]
    ring
  rw [heq]
  by_cases hs : s = 0
  · rcases hsv with hsv | hv
    · exact (hsv hs).elim
    · simpa [hs] using hH.dotProduct_mulVec_pos hv
  · have hnonneg := hH.posSemidef.dotProduct_mulVec_nonneg (v + s • (H⁻¹ *ᵥ g))
    have hpos : 0 < δ * s ^ 2 := mul_pos hδ (sq_pos_of_ne_zero hs)
    simpa only [star_trivial] using add_pos_of_nonneg_of_pos hnonneg hpos

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ258_II.KLS_Spectral_BrascampLiebPerturbation
attribute [-simp] _root_.OAI.LeanBlast.KLS.blMomentDeriv_zero _root_.OAI.LeanBlast.KLS.blMoment_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Matrix
open scoped BigOperators ContDiff Topology Matrix.Norms.Elementwise

namespace LeanBlast.KLS

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (V h q : E → ℝ)

variable {V h q}

theorem contDiff_blPerturbation (hV : ContDiff ℝ ∞ V) (hh : ContDiff ℝ ∞ h)
    (hq : ContDiff ℝ ∞ q) : ContDiff ℝ ∞ (blPerturbation V h q) := by
  unfold blPerturbation
  fun_prop

theorem fderiv_blPerturbation_apply (hV : ContDiff ℝ ∞ V) (hh : ContDiff ℝ ∞ h)
    (hq : ContDiff ℝ ∞ q) (p w : ℝ × E) :
    fderiv ℝ (blPerturbation V h q) p w =
      fderiv ℝ V p.2 w.2 + p.1 * fderiv ℝ h p.2 w.2 +
        p.1 ^ 2 / 2 * fderiv ℝ q p.2 w.2 + w.1 * (h p.2 + p.1 * q p.2) := by
  have ht : HasFDerivAt (fun r : ℝ × E => r.1) (ContinuousLinearMap.fst ℝ ℝ E) p :=
    hasFDerivAt_fst
  have hx : HasFDerivAt (fun r : ℝ × E => r.2) (ContinuousLinearMap.snd ℝ ℝ E) p :=
    hasFDerivAt_snd
  have hv' := (hV.differentiable (by simp) p.2).hasFDerivAt.comp p hx
  have hh' := (hh.differentiable (by simp) p.2).hasFDerivAt.comp p hx
  have hq' := (hq.differentiable (by simp) p.2).hasFDerivAt.comp p hx
  have hd := (hv'.add (ht.mul hh')).add (((ht.pow 2).mul_const (2 : ℝ)⁻¹).mul hq')
  simp only [Pi.add_def, Pi.mul_def, Function.comp_def] at hd
  change (fderiv ℝ (fun r : ℝ × E => V r.2 + r.1 * h r.2 + r.1 ^ 2 / 2 * q r.2) p) w = _
  simp only [div_eq_mul_inv]
  rw [hd.fderiv]
  simp
  ring

theorem second_fderiv_blPerturbation_apply (hV : ContDiff ℝ ∞ V) (hh : ContDiff ℝ ∞ h)
    (hq : ContDiff ℝ ∞ q) (p w : ℝ × E) :
    fderiv ℝ (fderiv ℝ (blPerturbation V h q)) p w w =
      fderiv ℝ (fderiv ℝ V) p.2 w.2 w.2 +
      p.1 * fderiv ℝ (fderiv ℝ h) p.2 w.2 w.2 +
      p.1 ^ 2 / 2 * fderiv ℝ (fderiv ℝ q) p.2 w.2 w.2 +
      2 * w.1 * (fderiv ℝ h p.2 w.2 + p.1 * fderiv ℝ q p.2 w.2) +
      w.1 ^ 2 * q p.2 := by
  have hF := contDiff_blPerturbation hV hh hq
  have heval := (((hF.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p).hasFDerivAt.clm_apply
    (hasFDerivAt_const w p)).fderiv
  have he : fderiv ℝ (fderiv ℝ (blPerturbation V h q)) p w w =
      fderiv ℝ (fun r => fderiv ℝ (blPerturbation V h q) r w) p w := by
    rw [heval]
    simp
  rw [he]
  simp_rw [fderiv_blPerturbation_apply hV hh hq]
  have ht : HasFDerivAt (fun r : ℝ × E => r.1) (ContinuousLinearMap.fst ℝ ℝ E) p :=
    hasFDerivAt_fst
  have hx : HasFDerivAt (fun r : ℝ × E => r.2) (ContinuousLinearMap.snd ℝ ℝ E) p :=
    hasFDerivAt_snd
  have hDV := ((((hV.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p.2).hasFDerivAt.clm_apply
    (hasFDerivAt_const w.2 p.2))).comp p hx
  have hDh := ((((hh.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p.2).hasFDerivAt.clm_apply
    (hasFDerivAt_const w.2 p.2))).comp p hx
  have hDq := ((((hq.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p.2).hasFDerivAt.clm_apply
    (hasFDerivAt_const w.2 p.2))).comp p hx
  have hh' := (hh.differentiable (by simp) p.2).hasFDerivAt.comp p hx
  have hq' := (hq.differentiable (by simp) p.2).hasFDerivAt.comp p hx
  have hd := (((hDV.add (ht.mul hDh)).add (((ht.pow 2).mul_const (2 : ℝ)⁻¹).mul hDq)).add
    ((hh'.add (ht.mul hq')).const_mul w.1))
  simp only [Pi.add_def, Pi.mul_def, Function.comp_def] at hd
  simp only [div_eq_mul_inv]
  rw [hd.fderiv]
  simp
  ring

end Calculus

theorem second_fderiv_blPerturbation_zero_pos {n : ℕ} {V h : Space n → ℝ}
    (hV : ContDiff ℝ ∞ V) (hh : ContDiff ℝ ∞ h)
    (hpos : ∀ x, (hessianMatrix V x).PosDef) {δ : ℝ} (hδ : 0 < δ)
    (x : Space n) (w : ℝ × Space n) (hw : w ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ (blPerturbation V h (fun y => steinGamma V h h y + δ)))
      (0, x) w w := by
  have hq : ContDiff ℝ ∞ (fun y => steinGamma V h h y + δ) :=
    (contDiff_steinGamma_self hV hh hpos).add contDiff_const
  rw [second_fderiv_blPerturbation_apply hV hh hq]
  simp only [zero_mul, zero_pow (by norm_num : 2 ≠ 0), zero_div, add_zero]
  rw [second_fderiv_eq_hessianMatrix,
    fderiv_eq_gradient_dotProduct (hh.differentiable (by simp) x), steinGamma_self_eq_dotProduct]
  have hw' : w.1 ≠ 0 ∨ (fun i => w.2 i) ≠ 0 := by
    by_cases hs : w.1 = 0
    · right
      intro hv
      apply hw
      apply Prod.ext hs
      ext i
      exact congrFun hv i
    · exact Or.inl hs
  convert quadratic_schur_positive (hpos x) (fun i => gradient h x i) (fun i => w.2 i) hδ w.1 hw' using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem exists_blPerturbation_convex {n : ℕ} {V h : Space n → ℝ}
    (hV : ContDiff ℝ ∞ V) (hh : IsTestFunction h)
    (hpos : ∀ x, (hessianMatrix V x).PosDef) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ConvexOn ℝ (Ioo (-ε) ε ×ˢ (univ : Set (Space n)))
        (blPerturbation V h (fun x => steinGamma V h h x + δ)) := by
  let q : Space n → ℝ := steinGamma V h h
  let F : ℝ × Space n → ℝ := blPerturbation V h (fun x => q x + δ)
  let S : Set (Space n) := tsupport h ∪ tsupport q
  have hq : ContDiff ℝ ∞ q := contDiff_steinGamma_self hV hh.1 hpos
  have hqc : HasCompactSupport q := hasCompactSupport_steinGamma_self V hh
  have hS : IsCompact S := hh.2.isCompact.union hqc.isCompact
  have hF : ContDiff ℝ ∞ F := contDiff_blPerturbation hV hh.1 (hq.add contDiff_const)
  have hF2 : Continuous (fderiv ℝ (fderiv ℝ F)) :=
    ((hF.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuous
  let Ψ : ℝ × (Space n × (ℝ × Space n)) → ℝ :=
    fun p => fderiv ℝ (fderiv ℝ F) (p.1, p.2.1) p.2.2 p.2.2
  have hΨ : Continuous Ψ := by
    have ha : Continuous (fun p : ℝ × (Space n × (ℝ × Space n)) => (p.1, p.2.1)) := by fun_prop
    have hb : Continuous (fun p : ℝ × (Space n × (ℝ × Space n)) => p.2.2) := by fun_prop
    exact ((hF2.comp ha).clm_apply hb).clm_apply hb
  have hopen : IsOpen {p | 0 < Ψ p} := isOpen_lt continuous_const hΨ
  have hprod : ({0} : Set ℝ) ×ˢ (S ×ˢ Metric.sphere (0 : ℝ × Space n) 1) ⊆
      {p | 0 < Ψ p} := by
    rintro ⟨t, x, w⟩ ⟨ht, _, hw⟩
    have ht0 : t = 0 := by simpa using ht
    subst t
    have hw0 : w ≠ 0 := by
      intro heq
      simp [heq] at hw
    exact second_fderiv_blPerturbation_zero_pos hV hh.1 hpos hδ x w hw0
  obtain ⟨U, W, hU, _, h0U, hKW, hUW⟩ := generalized_tube_lemma
    isCompact_singleton (hS.prod (isCompact_sphere (0 : ℝ × Space n) 1)) hopen hprod
  have hzU : (0 : ℝ) ∈ U := h0U (by simp)
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hzU)
  let ε : ℝ := min r 1
  have hε : 0 < ε := lt_min hr (by norm_num)
  refine ⟨ε, hε, min_le_right _ _, ?_⟩
  have hFtwo : ContDiff ℝ 2 F := hF.of_le (WithTop.coe_le_coe.mpr le_top)
  apply convexOn_of_second_fderiv_nonneg hFtwo
    ((convex_Ioo _ _).prod convex_univ)
  rintro ⟨t, x⟩ ⟨ht, _⟩ w
  by_cases hx : x ∈ S
  · by_cases hw : w = 0
    · simp [hw]
    · let u : ℝ × Space n := ‖w‖⁻¹ • w
      have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
      have hu : u ∈ Metric.sphere (0 : ℝ × Space n) 1 := by
        change dist (‖w‖⁻¹ • w) 0 = 1
        rw [dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
      have htU : t ∈ U := hrU (by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero]
        exact (abs_lt.mpr ht).trans_le (min_le_left r 1))
      have hp : 0 < Ψ (t, x, u) := hUW ⟨htU, hKW ⟨hx, hu⟩⟩
      change 0 < fderiv ℝ (fderiv ℝ F) (t, x) (‖w‖⁻¹ • w) (‖w‖⁻¹ • w) at hp
      simp only [map_smul, _root_.smul_apply, smul_eq_mul] at hp
      exact ((mul_pos_iff_of_pos_left (inv_pos.mpr hn)).mp
        ((mul_pos_iff_of_pos_left (inv_pos.mpr hn)).mp hp)).le
  · have hx' : x ∉ tsupport h ∧ x ∉ tsupport q := by simpa only [S, mem_union, not_or] using hx
    have hh0 : h =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx'.1
    have hq0 : q =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx'.2
    have hqc0 : (fun y => q y + δ) =ᶠ[𝓝 x] (fun _ => δ) := by
      filter_upwards [hq0] with y hy
      simp only [Pi.zero_apply] at hy
      simp only [hy, zero_add]
    have hh1 : fderiv ℝ h x = 0 := by simpa using hh0.fderiv_eq (𝕜 := ℝ)
    have hh2 : fderiv ℝ (fderiv ℝ h) x = 0 := by
      simpa using (hh0.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
    have hq1 : fderiv ℝ (fun y => q y + δ) x = 0 := by
      simpa using hqc0.fderiv_eq (𝕜 := ℝ)
    have hq2 : fderiv ℝ (fderiv ℝ (fun y => q y + δ)) x = 0 := by
      simpa using (hqc0.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
    change 0 ≤ fderiv ℝ (fderiv ℝ (blPerturbation V h (fun y => q y + δ))) (t, x) w w
    rw [second_fderiv_blPerturbation_apply hV hh.1 (hq.add contDiff_const)]
    simp only [hh1, hh2, hq1, hq2, _root_.zero_apply,
      mul_zero, add_zero, hqc0.eq_of_nhds]
    apply add_nonneg
    · rw [second_fderiv_eq_hessianMatrix]
      simpa only [star_trivial] using
        (hpos x).posSemidef.dotProduct_mulVec_nonneg (fun i => w.2 i)
    · positivity

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ258_II.KLS_Spectral_BrascampLieb
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace LeanBlast.KLS

variable {n : ℕ}

theorem exp_neg_blPerturbation (V h q : Space n → ℝ) (t : ℝ) (x : Space n) :
    Real.exp (-blPerturbation V h q (t, x)) =
      Real.exp (-V x) * blWeight t (h x) (q x) := by
  rw [blWeight, ← Real.exp_add]
  congr 1
  dsimp [blPerturbation]
  ring

theorem blMoment_potentialMeasure (V h q : Space n → ℝ) (t : ℝ) :
    blMoment (potentialMeasure V) h q t =
      (∫ x, Real.exp (-blPerturbation V h q (t, x))) / potentialPartition V := by
  rw [blMoment, integral_potentialMeasure]
  simp_rw [exp_neg_blPerturbation]

theorem concaveOn_blLogMoment_of_convex {V h q : Space n → ℝ} {B ε : ℝ}
    (hV : Measurable V) (hVint : Integrable (fun x => Real.exp (-V x)))
    (hh : Measurable h) (hq : Measurable q)
    (hhB : ∀ x, |h x| ≤ B) (hqB : ∀ x, |q x| ≤ B) (hε1 : ε ≤ 1)
    (hc : ConvexOn ℝ (Ioo (-ε) ε ×ˢ (univ : Set (Space n)))
      (blPerturbation V h q)) :
    ConcaveOn ℝ (Ioo (-ε) ε) (blLogMoment (potentialMeasure V) h q) := by
  let : IsProbabilityMeasure (potentialMeasure V) := isProbabilityMeasure_potentialMeasure hVint
  have hint : ∀ t ∈ Ioo (-ε) ε, Integrable (fun x => Real.exp (-blPerturbation V h q (t, x))) := by
    intro t ht
    have hk : Integrable (fun x => blWeight t (h x) (q x)) (potentialMeasure V) :=
      boundedKernel_integrable blWeight continuous_blWeight hh hq hhB hqB
        ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simpa only [exp_neg_blPerturbation] using (integrable_potentialMeasure_iff hVint _).mp hk
  have hm : ∀ t ∈ Ioo (-ε) ε, Measurable (fun x => Real.exp (-blPerturbation V h q (t, x))) := by
    intro t _
    dsimp [blPerturbation]
    fun_prop
  have hp := concaveOn_log_integral_exp_neg (convex_Ioo (-ε) ε) (blPerturbation V h q) hc hm hint
  refine (hp.add_const (-Real.log (potentialPartition V))).congr ?_
  intro t ht
  rw [blLogMoment, blMoment_potentialMeasure,
    Real.log_div (integral_exp_pos (hint t ht)).ne' (potentialPartition_pos hVint).ne']
  simp only [Pi.add_apply]
  ring

theorem brascamp_lieb {V h : Space n → ℝ}
    (hV : ContDiff ℝ ∞ V) (hVint : Integrable (fun x => Real.exp (-V x)))
    (hpos : ∀ x, (hessianMatrix V x).PosDef) (hh : IsTestFunction h) :
    variance (potentialMeasure V) h ≤
      ∫ x, steinGamma V h h x ∂potentialMeasure V := by
  let : IsProbabilityMeasure (potentialMeasure V) := isProbabilityMeasure_potentialMeasure hVint
  have hq := contDiff_steinGamma_self hV hh.1 hpos
  have hqc := hasCompactSupport_steinGamma_self V hh
  have hqint : Integrable (steinGamma V h h) (potentialMeasure V) :=
    hq.continuous.integrable_of_hasCompactSupport hqc
  obtain ⟨Bh, hBh⟩ := hh.2.exists_bound_of_continuous hh.continuous
  obtain ⟨Bq, hBq⟩ := hqc.exists_bound_of_continuous hq.continuous
  apply le_of_forall_pos_le_add
  intro δ hδ
  let B : ℝ := max Bh (Bq + |δ|)
  have hhB : ∀ x, |h x| ≤ B := by
    intro x
    have hb : |h x| ≤ Bh := by simpa only [Real.norm_eq_abs] using hBh x
    exact hb.trans (le_max_left _ _)
  have hqB : ∀ x, |steinGamma V h h x + δ| ≤ B := by
    intro x
    calc
      |steinGamma V h h x + δ| ≤ |steinGamma V h h x| + |δ| := abs_add_le _ _
      _ ≤ Bq + |δ| := by
        have hb : |steinGamma V h h x| ≤ Bq := by simpa only [Real.norm_eq_abs] using hBq x
        linarith
      _ ≤ B := le_max_right _ _
  obtain ⟨ε, hε, hε1, hc⟩ := exists_blPerturbation_convex hV hh hpos hδ
  have hqm : Measurable (fun x => steinGamma V h h x + δ) :=
    (hq.continuous.add continuous_const).measurable
  have hlog := concaveOn_blLogMoment_of_convex hV.continuous.measurable hVint
    hh.continuous.measurable hqm hhB hqB hε1 hc
  have hb := variance_le_integral_of_concave_blLogMoment (potentialMeasure V)
    hh.continuous.measurable hqm hhB hqB hε hε1 hlog
  calc
    variance (potentialMeasure V) h ≤
        ∫ x, (steinGamma V h h x + δ) ∂potentialMeasure V := hb
    _ = (∫ x, steinGamma V h h x ∂potentialMeasure V) + δ := by
      rw [integral_add hqint (integrable_const δ)]
      simp

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ258_II.KLS_Spectral_RegularPoincare
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators ContDiff

namespace LeanBlast.KLS

theorem quadratic_inverse_upper_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℝ} (hH : H.PosDef) {t : ℝ} (ht : 0 ≤ t)
    (hlower : ∀ v : ι → ℝ, t * (v ⬝ᵥ v) ≤ v ⬝ᵥ H *ᵥ v) (g : ι → ℝ) :
    t * (g ⬝ᵥ H⁻¹ *ᵥ g) ≤ g ⬝ᵥ g := by
  let v := H⁻¹ *ᵥ g
  have hmul : H *ᵥ v = g := by
    rw [show v = H⁻¹ *ᵥ g from rfl, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'), Matrix.one_mulVec]
  have hl : t * (v ⬝ᵥ v) ≤ g ⬝ᵥ v := by
    simpa only [hmul, dotProduct_comm v g] using hlower v
  have hsq : 0 ≤ (g - t • v) ⬝ᵥ (g - t • v) :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg ((g - t • v) i)
  have heq : (g - t • v) ⬝ᵥ (g - t • v) =
      g ⬝ᵥ g - 2 * t * (g ⬝ᵥ v) + t ^ 2 * (v ⬝ᵥ v) := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, dotProduct_comm v g]
    ring
  rw [heq] at hsq
  change t * (g ⬝ᵥ v) ≤ g ⬝ᵥ g
  nlinarith [mul_le_mul_of_nonneg_left hl ht]

theorem IsRegularPotential.hessianMatrix_posDef {n : ℕ} {V : Space n → ℝ} {t t' : ℝ}
    (hV : IsRegularPotential V t t') (x : Space n) : (hessianMatrix V x).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact (hessianMatrix_isSymm
      ((hV.contDiff.of_le (WithTop.coe_le_coe.mpr le_top) : ContDiff ℝ 2 V).contDiffAt)).eq
  · intro v hv
    let w : Space n := WithLp.toLp 2 v
    have hw : w ≠ 0 := by
      intro heq
      apply hv
      funext i
      exact congrArg (fun u : Space n => u i) heq
    simpa only [second_fderiv_eq_hessianMatrix, w, PiLp.toLp_apply, star_trivial] using
      hV.hessian_pos x hw

theorem IsRegularPotential.steinGamma_self_le {n : ℕ} {V : Space n → ℝ} {t t' : ℝ}
    (hV : IsRegularPotential V t t') (h : Space n → ℝ) (x : Space n) :
    t * steinGamma V h h x ≤ ‖gradient h x‖ ^ 2 := by
  have hlower : ∀ v : Fin n → ℝ,
      t * (v ⬝ᵥ v) ≤ v ⬝ᵥ hessianMatrix V x *ᵥ v := by
    intro v
    have hv := hV.lower_bound x (WithLp.toLp 2 v)
    rw [EuclideanSpace.real_norm_sq_eq] at hv
    simpa only [second_fderiv_eq_hessianMatrix,
      PiLp.toLp_apply, dotProduct, pow_two] using hv
  have hb := quadratic_inverse_upper_bound (hV.hessianMatrix_posDef x) hV.lower_pos.le
    hlower (fun i => gradient h x i)
  rw [steinGamma_self_eq_dotProduct, EuclideanSpace.real_norm_sq_eq]
  simpa only [dotProduct, pow_two] using hb

theorem IsRegularPotential.poincare {n : ℕ} {V f : Space n → ℝ} {t t' : ℝ}
    (hV : IsRegularPotential V t t')
    (hVint : Integrable (fun x => Real.exp (-V x))) (hf : IsTestFunction f) :
    t * variance (potentialMeasure V) f ≤ dirichletEnergy (potentialMeasure V) f := by
  let : IsProbabilityMeasure (potentialMeasure V) := isProbabilityMeasure_potentialMeasure hVint
  have hqint : Integrable (steinGamma V f f) (potentialMeasure V) :=
    (contDiff_steinGamma_self hV.contDiff hf.1 hV.hessianMatrix_posDef).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_steinGamma_self V hf)
  calc
    t * variance (potentialMeasure V) f ≤
        t * (∫ x, steinGamma V f f x ∂potentialMeasure V) :=
      mul_le_mul_of_nonneg_left
        (brascamp_lieb hV.contDiff hVint hV.hessianMatrix_posDef hf) hV.lower_pos.le
    _ = ∫ x, t * steinGamma V f f x ∂potentialMeasure V := (integral_const_mul _ _).symm
    _ ≤ ∫ x, ‖gradient f x‖ ^ 2 ∂potentialMeasure V :=
      integral_mono (hqint.const_mul t) (hf.integrable_gradient_sq _) (hV.steinGamma_self_le f)
    _ = dirichletEnergy (potentialMeasure V) f := rfl

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianQuadraticPotential
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-dimensional quadratic potential for Gaussian Poincare. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace InvariantIsing

lemma gaussianQuadraticPotential_derivative (d : ℕ) :
    fderiv ℝ (gaussianQuadraticPotential (d := d))=
      ⇑(innerSL ℝ (E := EuclideanSpace ℝ (Fin d))) := by
  funext x
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (1/2 : ℝ)).fderiv
  change fderiv ℝ (fun y : EuclideanSpace ℝ (Fin d) => (1/2 : ℝ)*‖y‖^2) x = _
  rw [h]
  ext v
  simp only [smul_apply,two_smul,add_apply,smul_eq_mul]
  ring

lemma gaussianQuadraticPotential_hessian {d : ℕ} (x v : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (fderiv ℝ (gaussianQuadraticPotential (d := d))) x v v=‖v‖^2 := by
  rw [gaussianQuadraticPotential_derivative]
  rw [((innerSL ℝ (E := EuclideanSpace ℝ (Fin d))).hasFDerivAt (x := x)).fderiv]
  exact real_inner_self_eq_norm_sq v

lemma gaussianQuadraticPotential_regular (d : ℕ) :
    LeanBlast.KLS.IsRegularPotential (gaussianQuadraticPotential (d := d)) 1 1 where
  contDiff := contDiff_const.mul (contDiff_norm_sq ℝ)
  lower_pos := zero_lt_one
  le_upper := le_rfl
  lower_bound x v := by rw [gaussianQuadraticPotential_hessian,one_mul]
  upper_bound x v := by rw [gaussianQuadraticPotential_hessian,one_mul]

lemma gaussianQuadraticPotential_integrable (d : ℕ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp (-gaussianQuadraticPotential x)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := EuclideanSpace ℝ (Fin d)) (b := (1/2 : ℂ)) (by norm_num) 0 0
  have hc : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      Complex.exp ((-(1/2 : ℝ)*‖x‖^2 : ℝ) : ℂ)) := by
    simpa only [zero_mul,add_zero,Complex.ofReal_mul,Complex.ofReal_neg,
      Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using h
  simpa only [Complex.norm_exp,Complex.ofReal_re,gaussianQuadraticPotential,neg_mul] using hc.norm

lemma gaussianQuadraticPotential_poincare_test {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : LeanBlast.KLS.IsTestFunction f) :
    LeanBlast.KLS.variance (LeanBlast.KLS.potentialMeasure gaussianQuadraticPotential) f ≤
      LeanBlast.KLS.dirichletEnergy (LeanBlast.KLS.potentialMeasure gaussianQuadraticPotential) f := by
  simpa only [one_mul] using (gaussianQuadraticPotential_regular d).poincare
    (gaussianQuadraticPotential_integrable d) hf

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianQuadraticLaw
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the normalized quadratic-potential law with stdGaussian. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace InvariantIsing

lemma gaussianQuadratic_integral_cexp {d : ℕ} (t : EuclideanSpace ℝ (Fin d)) :
    (∫ x : EuclideanSpace ℝ (Fin d), Complex.exp
      (-(gaussianQuadraticPotential x : ℂ)+Complex.I*(inner ℝ t x)))=
    (LeanBlast.KLS.potentialPartition (gaussianQuadraticPotential (d := d)) : ℂ)*
      Complex.exp (-(‖t‖ : ℂ)^2/2) := by
  have hb := GaussianFourier.integral_cexp_neg_mul_sq_norm
    (V := EuclideanSpace ℝ (Fin d)) (b := (1/2 : ℂ)) (by norm_num)
  have hbase : (LeanBlast.KLS.potentialPartition (gaussianQuadraticPotential (d := d)) : ℂ)=
      (Real.pi/(1/2 : ℂ))^(Module.finrank ℝ (EuclideanSpace ℝ (Fin d))/2 : ℂ) := by
    rw [LeanBlast.KLS.potentialPartition,← integral_complex_ofReal]
    convert hb using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext x
    rw [Complex.ofReal_exp]
    congr 1
    simp [gaussianQuadraticPotential,Complex.ofReal_mul,Complex.ofReal_pow]
  have hf := GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (V := EuclideanSpace ℝ (Fin d)) (b := (1/2 : ℂ)) (by norm_num) Complex.I t
  have he : Complex.I^2*(‖t‖ : ℂ)^2/(4*(1/2 : ℂ))=-(‖t‖ : ℂ)^2/2 := by
    rw [Complex.I_sq]
    ring
  rw [he,← hbase] at hf
  convert hf using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext x
  congr 1
  simp [gaussianQuadraticPotential,Complex.ofReal_mul,Complex.ofReal_pow]

lemma gaussianQuadratic_charFun {d : ℕ} (t : EuclideanSpace ℝ (Fin d)) :
    charFun (LeanBlast.KLS.potentialMeasure (gaussianQuadraticPotential (d := d))) t=
      Complex.exp (-(‖t‖ : ℂ)^2/2) := by
  let p := LeanBlast.KLS.potentialPartition (gaussianQuadraticPotential (d := d))
  have hp : (p : ℂ) ≠ 0 := by
    exact_mod_cast (LeanBlast.KLS.potentialPartition_pos (gaussianQuadraticPotential_integrable d)).ne'
  rw [charFun_apply,LeanBlast.KLS.potentialMeasure,integral_tilted]
  change (∫ x : EuclideanSpace ℝ (Fin d), (Real.exp (-gaussianQuadraticPotential x)/p) •
    Complex.exp ((inner ℝ x t : ℂ)*Complex.I))=_
  calc
    _ = (p : ℂ)⁻¹*(∫ x : EuclideanSpace ℝ (Fin d), Complex.exp
        (-(gaussianQuadraticPotential x : ℂ)+Complex.I*(inner ℝ t x))) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_exp,Complex.exp_add]
      rw [Complex.ofReal_neg]
      have he : (inner ℝ x t : ℂ)*Complex.I=Complex.I*(inner ℝ t x) := by
        rw [real_inner_comm x t]
        exact mul_comm _ _
      rw [he]
      ring
    _ = _ := by
      rw [gaussianQuadratic_integral_cexp,← mul_assoc,inv_mul_cancel₀ hp,one_mul]

lemma gaussianQuadratic_potentialMeasure_eq_stdGaussian (d : ℕ) :
    LeanBlast.KLS.potentialMeasure (gaussianQuadraticPotential (d := d))=
      stdGaussian (EuclideanSpace ℝ (Fin d)) := by
  let : IsProbabilityMeasure (LeanBlast.KLS.potentialMeasure (gaussianQuadraticPotential (d := d))) :=
    LeanBlast.KLS.isProbabilityMeasure_potentialMeasure (gaussianQuadraticPotential_integrable d)
  apply Measure.ext_of_charFun
  ext t
  rw [gaussianQuadratic_charFun,charFun_stdGaussian]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianTestVariance
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The proved regular-potential Poincare inequality at the standard Gaussian. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped NNReal
namespace InvariantIsing

theorem gaussian_test_variance_le {d : ℕ} {L : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (ht : LeanBlast.KLS.IsTestFunction f) (hf : LipschitzWith L f) :
    variance f (stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ (L : ℝ)^2 := by
  have hp := gaussianQuadraticPotential_poincare_test f ht
  rw [gaussianQuadratic_potentialMeasure_eq_stdGaussian] at hp
  have hv : variance f (stdGaussian (EuclideanSpace ℝ (Fin d))) =
      LeanBlast.KLS.variance (stdGaussian (EuclideanSpace ℝ (Fin d))) f := by
    rw [variance_eq_integral hf.continuous.aemeasurable]
    rfl
  rw [hv]
  apply hp.trans
  change (∫ x, ‖gradient f x‖^2 ∂stdGaussian _) ≤ _
  calc
    _ ≤ ∫ _ : EuclideanSpace ℝ (Fin d), (L : ℝ)^2 ∂stdGaussian _ := by
      apply integral_mono (ht.integrable_gradient_sq _) (integrable_const _)
      intro x
      dsimp only
      rw [LeanBlast.KLS.norm_gradient_eq_norm_fderiv]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hf) 2
    _ = _ := by simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_VarianceLimit
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing the Gaussian variance bound from finite leaf cutoffs to their limit. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace InvariantIsing

/-- Fatou's lemma for centered squares. This permits finite-leaf Gaussian
variance estimates to pass to the countable cascade prior. -/
theorem variance_le_of_ae_tendsto_of_mean_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {C : ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (ht : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (hm : Tendsto (fun n => ∫ ω, f n ω ∂μ) atTop (𝓝 (∫ ω, g ω ∂μ)))
    (hv : ∀ n, variance (f n) μ ≤ C) : variance g μ ≤ C := by
  let F := fun n ω => (f n ω - ∫ z, f n z ∂μ) ^ 2
  let G := fun ω => (g ω - ∫ z, g z ∂μ) ^ 2
  have hFi (n : ℕ) : Integrable (F n) μ :=
    ((hf n).sub (memLp_const _)).integrable_sq
  have hGi : Integrable G μ := (hg.sub (memLp_const _)).integrable_sq
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => ENNReal.ofReal (F n ω)) atTop (𝓝 (ENNReal.ofReal (G ω))) := by
    filter_upwards [ht] with ω hω
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hω.sub hm).pow 2)
  have hfatou : (∫⁻ ω, ENNReal.ofReal (G ω) ∂μ) ≤
      liminf (fun n => ∫⁻ ω, ENNReal.ofReal (F n ω) ∂μ) atTop := by
    calc
      _ = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (F n ω)) atTop ∂μ :=
        lintegral_congr_ae (hlim.mono fun _ hω => hω.liminf_eq.symm)
      _ ≤ _ := lintegral_liminf_le' (fun n => (hFi n).aemeasurable.ennreal_ofReal)
  have hpoint (n : ℕ) : (∫⁻ ω, ENNReal.ofReal (F n ω) ∂μ) ≤ ENNReal.ofReal C := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hFi n) (ae_of_all _ fun _ => sq_nonneg _)]
    change ENNReal.ofReal (∫ ω, (f n ω - ∫ z, f n z ∂μ) ^ 2 ∂μ) ≤ _
    rw [← variance_eq_integral (hf n).aemeasurable]
    exact ENNReal.ofReal_le_ofReal (hv n)
  have hb : liminf (fun n => ∫⁻ ω, ENNReal.ofReal (F n ω) ∂μ) atTop ≤ ENNReal.ofReal C := by
    refine liminf_le_of_le (by isBoundedDefault) (fun b hb => ?_)
    obtain ⟨n, hn⟩ := hb.exists
    exact hn.trans (hpoint n)
  rw [← ofReal_integral_eq_lintegral_ofReal hGi (ae_of_all _ fun _ => sq_nonneg _)] at hfatou
  change ENNReal.ofReal (∫ ω, (g ω - ∫ z, g z ∂μ) ^ 2 ∂μ) ≤ _ at hfatou
  rw [← variance_eq_integral hg.aemeasurable] at hfatou
  exact (ENNReal.ofReal_le_ofReal_iff ((variance_nonneg (f 0) μ).trans (hv 0))).mp (hfatou.trans hb)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianCompactVariance
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extending Gaussian Poincare from smooth to compact Lipschitz tests. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace InvariantIsing

lemma gaussianApproxBump_rOut_le (d n : ℕ) : (gaussianApproxBump d n).rOut ≤ 1 := by
  change 1/(n+1 : ℝ) ≤ 1
  apply (div_le_one (by positivity)).mpr
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem gaussian_compact_variance_le {d : ℕ} {L : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LipschitzWith L f)
    (hc : HasCompactSupport f) :
    variance f (stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ (L : ℝ)^2 := by
  let F := fun n => gaussianSmooth (gaussianApproxBump d n) f
  have hL n : LipschitzWith L (F n) := gaussianSmooth_lipschitz _ hf
  have hv n : variance (F n) (stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ (L : ℝ)^2 :=
    gaussian_test_variance_le (gaussianSmooth_test _ hf hc) (hL n)
  have ht (x : EuclideanSpace ℝ (Fin d)) : Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
    exact ContDiffBump.convolution_tendsto_right_of_continuous
      (show Tendsto (fun n => (gaussianApproxBump d n).rOut) atTop (𝓝 0) from
        tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) hf.continuous x
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuous hf.continuous
  have hbound n x : ‖F n x‖ ≤ B+(L : ℝ) := by
    calc
      _ ≤ ‖f x‖+dist (F n x) (f x) := by
        simpa only [add_sub_cancel, dist_eq_norm] using norm_add_le (f x) (F n x-f x)
      _ ≤ B+(L : ℝ)*(gaussianApproxBump d n).rOut :=
        add_le_add (hB x) (gaussianSmooth_dist_le _ hf x)
      _ ≤ B+(L : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_left (gaussianApproxBump_rOut_le d n) L.coe_nonneg]
  have hm : Tendsto (fun n => ∫ x, F n x ∂stdGaussian _) atTop
      (𝓝 (∫ x, f x ∂stdGaussian _)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => B+(L : ℝ))
      (fun n => (hL n).continuous.aestronglyMeasurable) (integrable_const _)
    · exact fun n => ae_of_all _ (hbound n)
    · exact ae_of_all _ ht
  exact variance_le_of_ae_tendsto_of_mean_tendsto
    (fun n => gaussian_lipschitz_memLp_two (hL n)) (gaussian_lipschitz_memLp_two hf)
    (ae_of_all _ ht) hm hv

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianConeCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact scalar cutoffs preserving the exact Lipschitz constant. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace InvariantIsing

lemma gaussianCone_nonneg {d : ℕ} (L : ℝ≥0) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ gaussianCone L R x := le_max_right _ _

lemma gaussianCone_lipschitz {d : ℕ} (L : ℝ≥0) (R : ℝ) :
    LipschitzWith L (gaussianCone (d := d) L R) := by
  have h : LipschitzWith L (fun x : EuclideanSpace ℝ (Fin d) => (L : ℝ)*(R-‖x‖)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq]
    have he : (L : ℝ)*(R-‖x‖)-(L : ℝ)*(R-‖y‖) = (L : ℝ)*(‖y‖-‖x‖) := by ring
    rw [he, abs_mul, abs_of_nonneg L.coe_nonneg]
    apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, dist_comm y x] using
      (lipschitzWith_one_norm (E := EuclideanSpace ℝ (Fin d))).dist_le_mul y x
  exact h.max_const 0

lemma gaussianConeCutoff_lipschitz {d : ℕ} {L : ℝ≥0} {R : ℝ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LipschitzWith L f) :
    LipschitzWith L (gaussianConeCutoff L R f) := by
  unfold gaussianConeCutoff
  simpa only [Pi.neg_apply, max_self] using
    (gaussianCone_lipschitz (d := d) L R).neg.max (hf.min (gaussianCone_lipschitz L R))

lemma gaussianConeCutoff_zero {d : ℕ} (L : ℝ≥0) (R : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d))
    (hx : R ≤ ‖x‖) : gaussianConeCutoff L R f x = 0 := by
  have hc : gaussianCone L R x = 0 :=
    max_eq_right (mul_nonpos_of_nonneg_of_nonpos L.coe_nonneg (sub_nonpos.mpr hx))
  simp only [gaussianConeCutoff, hc, neg_zero, max_eq_left (min_le_right _ _)]

lemma gaussianConeCutoff_compact {d : ℕ} (L : ℝ≥0) (R : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : HasCompactSupport (gaussianConeCutoff L R f) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) R)
  intro x hx
  by_contra hn
  have he : R ≤ ‖x‖ := le_of_lt (by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hn)
  exact hx (gaussianConeCutoff_zero L R f x he)

lemma gaussianConeCutoff_norm_le {d : ℕ} (L : ℝ≥0) (R : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ‖gaussianConeCutoff L R f x‖ ≤ ‖f x‖ := by
  have ha := gaussianCone_nonneg L R x
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  unfold gaussianConeCutoff
  by_cases hf : 0 ≤ f x
  · have hlo : 0 ≤ max (-gaussianCone L R x) (min (f x) (gaussianCone L R x)) :=
      (le_min hf ha).trans (le_max_right _ _)
    rw [abs_of_nonneg hlo, abs_of_nonneg hf]
    exact max_le (by linarith) (min_le_left _ _)
  · have hf' : f x ≤ 0 := (lt_of_not_ge hf).le
    rw [min_eq_left (hf'.trans ha), abs_of_nonpos (max_le (by linarith) hf'), abs_of_nonpos hf']
    exact neg_le_neg (le_max_right _ _)

lemma gaussianConeCutoff_eq {d : ℕ} {L : ℝ≥0} {R : ℝ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LipschitzWith L f) (h0 : f 0 = 0)
    (x : EuclideanSpace ℝ (Fin d)) (hx : 2*‖x‖ ≤ R) :
    gaussianConeCutoff L R f x = f x := by
  have hb : |f x| ≤ (L : ℝ)*‖x‖ := by
    simpa only [h0, dist_zero_right, Real.norm_eq_abs] using hf.dist_le_mul x 0
  have hh : (L : ℝ)*‖x‖ ≤ (L : ℝ)*(R-‖x‖) :=
    mul_le_mul_of_nonneg_left (by linarith) L.coe_nonneg
  have ha : |f x| ≤ gaussianCone L R x := hb.trans (hh.trans (le_max_left _ _))
  unfold gaussianConeCutoff
  rw [min_eq_left ((le_abs_self _).trans ha), max_eq_right]
  linarith [neg_le_abs (f x)]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianVarianceInput
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-dimensional Gaussian variance for Lipschitz functions. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace InvariantIsing

lemma gaussian_centered_lipschitz_variance_le {d : ℕ} {L : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LipschitzWith L f) (h0 : f 0 = 0) :
    variance f (stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ (L : ℝ)^2 := by
  let F := fun n : ℕ => gaussianConeCutoff L (2*(n+1 : ℝ)) f
  have hL n : LipschitzWith L (F n) := gaussianConeCutoff_lipschitz hf
  have hv n : variance (F n) (stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ (L : ℝ)^2 :=
    gaussian_compact_variance_le (hL n) (gaussianConeCutoff_compact _ _ _)
  have ht (x : EuclideanSpace ℝ (Fin d)) : Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
    have he : ∀ᶠ n : ℕ in atTop, ‖x‖ ≤ (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ‖x‖)
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with n hn
    exact (gaussianConeCutoff_eq hf h0 x (by linarith)).symm
  have hm : Tendsto (fun n => ∫ x, F n x ∂stdGaussian _) atTop
      (𝓝 (∫ x, f x ∂stdGaussian _)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
      (fun n => (hL n).continuous.aestronglyMeasurable) (gaussian_lipschitz_integrable hf).norm
    · exact fun n => ae_of_all _ (gaussianConeCutoff_norm_le _ _ _)
    · exact ae_of_all _ ht
  exact variance_le_of_ae_tendsto_of_mean_tendsto
    (fun n => gaussian_lipschitz_memLp_two (hL n)) (gaussian_lipschitz_memLp_two hf)
    (ae_of_all _ ht) hm hv

/-- The Gaussian Poincaré inequality for globally Lipschitz observables. -/
theorem gaussianLipschitzVariance_proved_oai : GaussianLipschitzVarianceInput := by
  intro d L f hf
  have hc : LipschitzWith L (fun x => f x-f 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using hf.dist_le_mul x y
  have h := gaussian_centered_lipschitz_variance_le hc (by simp)
  rwa [variance_sub_const hf.continuous.aestronglyMeasurable] at h

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.gaussianLipschitzVariance_proved_oai := @OAI.InvariantIsing.gaussianLipschitzVariance_proved_oai
