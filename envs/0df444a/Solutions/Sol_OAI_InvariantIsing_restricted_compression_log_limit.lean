-- Prove2me | solution 1 for OAI.InvariantIsing.restricted_compression_log_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:05:31.449123+00:00
-- url     : https://prove2.me/submissions/559c741b-494f-40c6-ba58-800d0ade50a2

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005

section
-- module Solutions.OAIQ258_II.Compat
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- d13f23b's `Measurable.eval_matrix` (q258). -/
lemma _root_.Measurable.eval_matrix {m n α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {i : m} {j : n} {M : β → Matrix m n α} (hM : Measurable M) : Measurable (M · i j) :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hM)
/-- d13f23b's `Matrix.measurable_apply` (q258). -/
protected lemma _root_.Matrix.measurable_apply {m n α : Type*} [MeasurableSpace α] {i : m} {j : n} :
    Measurable (fun M : Matrix m n α => M i j) := measurable_id.eval_matrix
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_PartitionPowLe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partition Pow Le. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron



lemma exp_integral_le_partition {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν] {H : X → ℝ}
    (hH : Integrable H ν) (he : Integrable (fun x => Real.exp (H x)) ν) :
    Real.exp (∫ x, H x ∂ν) ≤ ∫ x, Real.exp (H x) ∂ν := by
  exact convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall (fun _ => mem_univ _)) hH he



end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_MonomialGgAtMinimum
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

lemma logMean_bounds (μ : Measure A) [IsProbabilityMeasure μ]
    {F : A → ℝ} (hF : Measurable F) {b K : ℝ} (hb : 0 < b)
    (hbound : ∀ a, |F a| ≤ K) : |logMean b μ F| ≤ K := by
  have hi : Integrable (fun a => Real.exp (b*F a)) μ := by
    apply Integrable.of_bound ((measurable_const.mul hF).exp).aestronglyMeasurable (Real.exp (b*K))
    apply ae_of_all
    intro a
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hbound a)) hb.le)
  have hlow : Real.exp (-b*K) ≤ ∫ a, Real.exp (b*F a) ∂μ := by
    calc
      _ = ∫ _, Real.exp (-b*K) ∂μ := by simp
      _ ≤ _ := by
        apply integral_mono (integrable_const _) hi
        intro a
        apply Real.exp_le_exp.mpr
        have := (abs_le.mp (hbound a)).1
        nlinarith
  have hhigh : (∫ a, Real.exp (b*F a) ∂μ) ≤ Real.exp (b*K) := by
    calc
      _ ≤ ∫ _, Real.exp (b*K) ∂μ := integral_mono hi (integrable_const _) (fun a =>
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hbound a)) hb.le))
      _ = _ := by simp
  have hM := integral_exp_pos μ F hi
  rw [abs_le, logMean]
  constructor
  · apply (le_div_iff₀ hb).mpr
    have := Real.log_le_log (Real.exp_pos _) hlow
    rw [Real.log_exp] at this
    nlinarith
  · apply (div_le_iff₀ hb).mpr
    have := Real.log_le_log hM hhigh
    rw [Real.log_exp] at this
    nlinarith

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_JointGGClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint G G Closure. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma tendsto_nat_rpow_neg {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => (N:ℝ)^(-c)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hc).comp tendsto_natCast_atTop_atTop

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_PerturbationWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform finite perturbation sums for the manuscript's geometric weights. -/

noncomputable section

open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma perturbationScale_le_one {N : ℕ} (hN : 0 < N) : perturbationScale N ≤ 1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · exact_mod_cast (Nat.succ_le_of_lt hN)
  · norm_num

lemma perturbationScale_sq_le_one {N : ℕ} (hN : 0 < N) : perturbationScale N ^ 2 ≤ 1 := by
  have hp : 0 ≤ perturbationScale N := Real.rpow_nonneg (Nat.cast_nonneg _) _
  nlinarith [perturbationScale_le_one hN]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPerturbationRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded dimension jump changes the deterministic and Gaussian
perturbation amplitudes by a vanishing amount. -/

noncomputable section
open IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_rpow_increment_le {x t p : ℝ} (hx : 0 < x) (ht : 0 ≤ t)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    |(x + t) ^ p - x ^ p| ≤ (p * t) * x ^ (p - 1) := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp
  have hc := (Real.concaveOn_rpow hp₀ hp₁).slope_le_of_hasDerivAt hx.le
    (show 0 ≤ x + t by positivity) (show x < x + t by linarith)
    (Real.hasDerivAt_rpow_const (Or.inl hx.ne'))
  rw [slope_def_field, add_sub_cancel_left] at hc
  have hd : 0 ≤ (x + t) ^ p - x ^ p :=
    sub_nonneg.mpr (Real.rpow_le_rpow hx.le (by linarith) hp₀)
  rw [abs_of_nonneg hd]
  have h := (div_le_iff₀ ht).mp hc
  nlinarith

lemma cavity_nat_rpow_increment_tendsto (n : ℕ) {p : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p < 1) :
    Tendsto (fun N : ℕ => ((N + n : ℕ) : ℝ) ^ p - (N : ℝ) ^ p) atTop (𝓝 0) := by
  apply squeeze_zero_norm'
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    simpa only [Real.norm_eq_abs, Nat.cast_add] using
      cavity_rpow_increment_le hN' (Nat.cast_nonneg n) hp₀ hp₁.le
  · have h := (tendsto_nat_rpow_neg (sub_pos.mpr hp₁)).const_mul (p * n)
    simpa only [neg_sub, mul_zero] using h

lemma cavity_deterministic_amplitude_eq {N : ℕ} (hN : 0 < N) :
    N * perturbationScale N = (N : ℝ) ^ (15 / 16 : ℝ) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  calc
    _ = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-1 / 16 : ℝ) := by
      rw [Real.rpow_one]
      rfl
    _ = (N : ℝ) ^ ((1 : ℝ) + (-1 / 16)) := (Real.rpow_add hn _ _).symm
    _ = _ := by norm_num

lemma cavity_covariance_amplitude_eq {N : ℕ} (hN : 0 < N) :
    N * perturbationScale N ^ 2 = (N : ℝ) ^ (7 / 8 : ℝ) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  change (N : ℝ) * ((N : ℝ) ^ (-1 / 16 : ℝ)) ^ 2 = _
  rw [pow_two, ← mul_assoc]
  calc
    _ = ((N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-1 / 16 : ℝ)) *
        (N : ℝ) ^ (-1 / 16 : ℝ) := by rw [Real.rpow_one]
    _ = (N : ℝ) ^ ((1 : ℝ) + (-1 / 16) + (-1 / 16)) := by
      rw [← Real.rpow_add hn, ← Real.rpow_add hn]
    _ = _ := by norm_num

theorem cavity_deterministic_amplitude_increment_tendsto (n : ℕ) :
    Tendsto (fun N : ℕ => (N + n) * perturbationScale (N + n) - N * perturbationScale N)
      atTop (𝓝 0) := by
  apply (cavity_nat_rpow_increment_tendsto n (p := 15 / 16) (by norm_num) (by norm_num)).congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [← Nat.cast_add, cavity_deterministic_amplitude_eq (N := N + n) (by omega),
    cavity_deterministic_amplitude_eq (N := N) (by omega)]

theorem cavity_covariance_amplitude_increment_tendsto (n : ℕ) :
    Tendsto (fun N : ℕ => (N + n) * perturbationScale (N + n) ^ 2 -
      N * perturbationScale N ^ 2) atTop (𝓝 0) := by
  apply (cavity_nat_rpow_increment_tendsto n (p := 7 / 8) (by norm_num) (by norm_num)).congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [← Nat.cast_add, cavity_covariance_amplitude_eq (N := N + n) (by omega),
    cavity_covariance_amplitude_eq (N := N) (by omega)]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityActualDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The deterministic perturbation error under a fixed cavity-size
jump, stated for the actual spectral-diagonal perturbation energy. -/

noncomputable section
open IsingPerceptron Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma cavityDeterministicRate_tendsto (n m : ℕ) (C : ℝ) :
    Tendsto (cavityDeterministicRate n m C) atTop (𝓝 0) := by
  have he : Tendsto perturbationScale atTop (𝓝 (0 : ℝ)) := by
    change Tendsto (fun N : ℕ => (N : ℝ) ^ (-1 / 16 : ℝ)) atTop (𝓝 0)
    simpa only [neg_div] using tendsto_nat_rpow_neg (by norm_num : (0 : ℝ) < 1 / 16)
  have hh := ((cavity_deterministic_amplitude_increment_tendsto n).abs.add (he.const_mul C)).const_mul
    (2 * (m : ℝ))
  change Tendsto (fun N => 2 * (m : ℝ) *
    (|(N + n) * perturbationScale (N + n) - N * perturbationScale N| + C * perturbationScale N))
      atTop (𝓝 0)
  simpa only [abs_zero, mul_zero, add_zero] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBlockFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite-volume algebra for the coupled cavity comparison.  The
spectral coupling and its Gaussian limit are separate source obligations. -/

noncomputable section
open IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavityQuadratic_sub {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) (y : Fin d → ℝ) :
    cavityQuadratic (A - B) y = cavityQuadratic A y - cavityQuadratic B y := by
  simp only [cavityQuadratic, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBoundedReweighting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded positive reweighting of random probability priors.  Its
replica-test limit follows from the unreweighted extra-replica limits. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

lemma measurable_cavityWeightNormalizer {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (w : Ω × X → ℝ) (hw : Measurable w) :
    Measurable (fun ω => cavityWeightNormalizer (ν ω) (fun x => w (ω, x))) := by
  let κ : Kernel Ω X := ⟨ν, hν⟩
  let : IsMarkovKernel κ := ⟨fun ω => inferInstanceAs (IsProbabilityMeasure (ν ω))⟩
  exact (hw.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eventual nondegeneracy of the Gaussian Gram matrix used to construct
fresh orthonormal directions. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix

namespace InvariantIsing

lemma cavity_posDef_of_posSemidef_det_ne_zero {q : ℕ}
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef) (hdet : G.det ≠ 0) :
    G.PosDef := by
  apply hG.1.posDef_iff_eigenvalues_pos.mpr
  intro i
  have hprod : (∏ j, hG.1.eigenvalues j) ≠ 0 := by
    rw [hG.1.det_eq_prod_eigenvalues] at hdet
    exact hdet
  have hi : hG.1.eigenvalues i ≠ 0 := (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)
  exact lt_of_le_of_ne (hG.eigenvalues_nonneg i) hi.symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFrameAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Gaussian frame construction: normalize the column Gram
matrix by its positive square root. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_sqrt_det_isUnit {q : ℕ} (G : Matrix (Fin q) (Fin q) ℝ)
    (hG : G.PosDef) : IsUnit (CFC.sqrt G).det := by
  apply isUnit_iff_ne_zero.mpr
  have he : (CFC.sqrt G).det * (CFC.sqrt G).det = G.det := by
    rw [← Matrix.det_mul, CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg]
  intro hz
  rw [hz, zero_mul] at he
  exact hG.det_pos.ne' he.symm

theorem cavityNormalizeFrame_gram {n q : ℕ} (A : Matrix (Fin n) (Fin q) ℝ)
    (hG : (A.transpose * A).PosDef) :
    (cavityNormalizeFrame A).transpose * cavityNormalizeFrame A = 1 := by
  let G : Matrix (Fin q) (Fin q) ℝ := A.transpose * A
  let S : Matrix (Fin q) (Fin q) ℝ := CFC.sqrt G
  have hS : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg G)
  have hs : S.transpose = S :=
    Matrix.isHermitian_iff_isSymm.mp hS.isHermitian
  have hss : S * S = G := CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg
  have hu : IsUnit S.det := cavity_sqrt_det_isUnit G hG
  change (A * S⁻¹).transpose * (A * S⁻¹) = 1
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hs]
  calc
    S⁻¹ * A.transpose * (A * S⁻¹) = S⁻¹ * G * S⁻¹ := by
      simp only [G, Matrix.mul_assoc]
    _ = S⁻¹ * (S * S) * S⁻¹ := by rw [hss]
    _ = 1 := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul S hu,
        Matrix.one_mul, Matrix.mul_nonsing_inv S hu]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFrameTransitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ambient orthogonal group acts transitively on finite orthonormal
frames. This identifies the orbit on which the conditioned Gaussian frame
law will be compared with Haar measure. -/

noncomputable section
open scoped RealInnerProductSpace

namespace InvariantIsing

theorem cavity_orthonormal_transitive {n q : ℕ}
    (v w : Fin q → EuclideanSpace ℝ (Fin n))
    (hv : Orthonormal ℝ v) (hw : Orthonormal ℝ w) :
    ∃ U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ i, U (v i) = w i := by
  classical
  let bv := OrthonormalBasis.span hv Finset.univ
  let bw := OrthonormalBasis.span hw Finset.univ
  let L := (Submodule.subtypeₗᵢ _).comp
    (bv.equiv bw (Equiv.refl _)).toLinearIsometry
  let U := LinearIsometryEquiv.ofSurjective L.extend
    (LinearMap.surjective_of_injective L.extend.injective)
  refine ⟨U, fun i => ?_⟩
  have hv' : (bv ⟨i, Finset.mem_univ i⟩ : EuclideanSpace ℝ (Fin n)) = v i :=
    OrthonormalBasis.span_apply hv _ _
  have hw' : (bw ⟨i, Finset.mem_univ i⟩ : EuclideanSpace ℝ (Fin n)) = w i :=
    OrthonormalBasis.span_apply hw _ _
  change L.extend (v i) = w i
  rw [← hv', LinearIsometry.extend_apply]
  change ((bv.equiv bw (Equiv.refl _)) (bv ⟨i, Finset.mem_univ i⟩) :
    EuclideanSpace ℝ (Fin n)) = w i
  rw [OrthonormalBasis.equiv_apply_basis]
  exact hw'

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFrameOrbit
attribute [-instance] _root_.OAI.InvariantIsing.tensorLabeledLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix form of transitivity and continuity of the frame orbit action. -/

noncomputable section
open MeasureTheory
open scoped Matrix

namespace InvariantIsing

lemma cavityRotationMatrix_apply {n : ℕ} (U : Rotation n)
    (x : EuclideanSpace ℝ (Fin n)) : matrixRotation (cavityRotationMatrix U) x = U x := by
  have h := U.toLinearMap.toMatrix_mulVec_repr
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis x
  ext i
  exact congrFun h i

lemma cavity_orthonormal_of_gram {n q : ℕ} (A : Matrix (Fin n) (Fin q) ℝ)
    (hA : A.transpose * A = 1) :
    Orthonormal ℝ (fun j : Fin q =>
      (WithLp.toLp 2 (fun i : Fin n => A i j) : EuclideanSpace ℝ (Fin n))) := by
  rw [orthonormal_iff_ite]
  intro i j
  have h := congrArg (fun B : Matrix (Fin q) (Fin q) ℝ => B i j) hA
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
    PiLp.toLp_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, mul_comm] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySphereAverage
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.planeRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular averaging for the moments of fresh Haar frame coordinates. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix

namespace InvariantIsing

lemma cavity_matrixRotation_mul_apply {n : ℕ} (U V : Orthogonal n)
    (x : EuclideanSpace ℝ (Fin n)) :
    matrixRotation (U * V) x = matrixRotation U (matrixRotation V x) := by
  ext i
  change (((U : Matrix (Fin n) (Fin n) ℝ) * (V : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x.ofLp) i =
    ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ ((V : Matrix (Fin n) (Fin n) ℝ) *ᵥ x.ofLp)) i
  rw [Matrix.mulVec_mulVec]

lemma cavity_unit_vector_transitive {n : ℕ} (v w : EuclideanSpace ℝ (Fin n))
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ∃ U : Orthogonal n, matrixRotation U v = w := by
  have ho (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ = 1) :
      Orthonormal ℝ (fun _ : Fin 1 => x) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    simp [hij, hx]
  obtain ⟨U, hU⟩ := cavity_orthonormal_transitive _ _ (ho v hv) (ho w hw)
  exact ⟨cavityRotationMatrix U, (cavityRotationMatrix_apply U v).trans (hU 0)⟩

lemma continuous_cavityRotationAction (n : ℕ) :
    Continuous (fun p : Orthogonal n × EuclideanSpace ℝ (Fin n) => matrixRotation p.1 p.2) := by
  change Continuous (fun p : Orthogonal n × EuclideanSpace ℝ (Fin n) =>
    WithLp.toLp 2 ((p.1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ p.2.ofLp))
  exact (PiLp.continuous_toLp 2 _).comp
    ((continuous_subtype_val.comp continuous_fst).matrix_mulVec
      ((PiLp.continuous_ofLp 2 _).comp continuous_snd))

lemma cavity_sphere_average_independent {n : ℕ}
    (μ : Measure (Orthogonal n)) [μ.IsMulRightInvariant]
    (v u w : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (p : ℕ) :
    (∫ U, |⟪v, matrixRotation U u⟫| ^ p ∂μ) =
      ∫ U, |⟪v, matrixRotation U w⟫| ^ p ∂μ := by
  obtain ⟨V, hV⟩ := cavity_unit_vector_transitive u w hu hw
  rw [← hV]
  simp_rw [← cavity_matrixRotation_mul_apply]
  exact (integral_mul_right_eq_self (μ := μ)
    (fun U : Orthogonal n => |⟪v, matrixRotation U u⟫| ^ p) V).symm

theorem cavity_sphere_radial_average {n : ℕ}
    (μ : Measure (Orthogonal n)) [μ.IsMulRightInvariant]
    (v u x : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) (p : ℕ) :
    (∫ U, |⟪v, matrixRotation U x⟫| ^ p ∂μ) =
      ‖x‖ ^ p * ∫ U, |⟪v, matrixRotation U u⟫| ^ p ∂μ := by
  by_cases hx : x = 0
  · subst x
    by_cases hp : p = 0 <;> simp [hp]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  let w := ‖x‖⁻¹ • x
  have hw : ‖w‖ = 1 := by simp [w, norm_smul, hn]
  have hxw : x = ‖x‖ • w := by simp [w, smul_smul, hn]
  calc
    _ = ‖x‖ ^ p * ∫ U, |⟪v, matrixRotation U w⟫| ^ p ∂μ := by
      conv_lhs => rw [hxw]
      simp_rw [map_smul, real_inner_smul_right, abs_mul, abs_norm, mul_pow]
      rw [integral_const_mul]
    _ = _ := by rw [cavity_sphere_average_independent μ v w u hw hu p]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianRadialMoments
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dimension-explicit Gaussian radial moments used to bound moments of
uniform spherical projections. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

namespace InvariantIsing

lemma cavityGaussianAbsMoment_nonneg (p : ℕ) : 0 ≤ cavityGaussianAbsMoment p :=
  integral_nonneg (fun z => pow_nonneg (abs_nonneg z) p)

lemma cavityGaussianAbsMoment_two : cavityGaussianAbsMoment 2 = 1 := by
  have h := variance_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
  rw [variance_eq_integral measurable_id.aemeasurable] at h
  simpa only [cavityGaussianAbsMoment, id_eq, integral_id_gaussianReal,
    sub_zero, sq_abs, NNReal.coe_one] using h

lemma cavity_gaussian_norm_pow_integrable (n p : ℕ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ p) (stdGaussian _) := by
  simpa only [id_eq] using
    (IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ (Fin n))) p (by simp)).integrable_norm_pow'

lemma cavity_gaussian_inner_abs_moment {n : ℕ}
    (v : EuclideanSpace ℝ (Fin n)) (p : ℕ) :
    (∫ z, |⟪v, z⟫| ^ p ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
      ‖v‖ ^ p * cavityGaussianAbsMoment p := by
  let L : StrongDual ℝ (EuclideanSpace ℝ (Fin n)) := innerSL ℝ v
  have hm : (stdGaussian (EuclideanSpace ℝ (Fin n))).map L =
      (gaussianReal 0 1).map (fun x : ℝ => ‖v‖ * x) := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, gaussianReal_map_const_mul]
    simp only [L, innerSL_apply_norm, mul_zero, mul_one]
    congr 1
    exact NNReal.eq (by simp)
  calc
    _ = ∫ z : ℝ, |z| ^ p ∂(stdGaussian (EuclideanSpace ℝ (Fin n))).map L :=
      (integral_map L.continuous.aemeasurable (by fun_prop)).symm
    _ = ∫ z : ℝ, |z| ^ p ∂(gaussianReal 0 1).map (fun x : ℝ => ‖v‖ * x) := by rw [hm]
    _ = ‖v‖ ^ p * cavityGaussianAbsMoment p := by
      rw [integral_map (by fun_prop) (by fun_prop)]
      simp only [abs_mul, abs_norm, mul_pow, integral_const_mul, cavityGaussianAbsMoment]

lemma cavity_gaussian_norm_sq_integral (n : ℕ) :
    (∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ ^ 2 ∂stdGaussian _) = n := by
  have hcoord (i : Fin n) :
      (∫ z : EuclideanSpace ℝ (Fin n), z i ^ 2 ∂stdGaussian _) = 1 := by
    have h := cavity_gaussian_inner_abs_moment (EuclideanSpace.basisFun (Fin n) ℝ i) 2
    simpa only [EuclideanSpace.basisFun_inner, sq_abs,
      OrthonormalBasis.norm_eq_one, one_pow, one_mul, cavityGaussianAbsMoment_two] using h
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum]
  · simp only [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  · intro i _
    simpa only [innerSL_apply_apply, EuclideanSpace.basisFun_inner, Real.norm_eq_abs, sq_abs] using
      (IsGaussian.memLp_dual (stdGaussian (EuclideanSpace ℝ (Fin n)))
        (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)) 2 (by simp)).integrable_norm_pow'

lemma cavity_gaussian_radial_moment_lower (n k : ℕ) :
    (n : ℝ) ^ k ≤ ∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ ^ (2 * k) ∂stdGaussian _ := by
  have hi : Integrable (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ 2)
      (stdGaussian _) := cavity_gaussian_norm_pow_integrable n 2
  have hik : Integrable (fun z : EuclideanSpace ℝ (Fin n) => (‖z‖ ^ 2) ^ k)
      (stdGaussian _) := by
    simpa only [← pow_mul] using cavity_gaussian_norm_pow_integrable n (2 * k)
  have h := (convexOn_pow k (𝕜 := ℝ)).map_integral_le (by fun_prop)
    isClosed_Ici (ae_of_all _ (fun z => sq_nonneg ‖z‖)) hi hik
  simpa only [cavity_gaussian_norm_sq_integral, ← pow_mul] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySphereMoments
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.planeRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform even moments of Haar projections. Gaussian angular averaging
gives a bound with the dimension in the denominator. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace InvariantIsing

theorem cavity_gaussian_angular_moment {n : ℕ}
    (μ : Measure (Orthogonal n)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (v u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) (p : ℕ) :
    (∫ z, |⟪v, z⟫| ^ p ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
      (∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ ^ p ∂stdGaussian _) *
        ∫ U, |⟪v, matrixRotation U u⟫| ^ p ∂μ := by
  let F := fun U : Orthogonal n => fun z : EuclideanSpace ℝ (Fin n) =>
    |⟪v, matrixRotation U z⟫| ^ p
  have hF : Continuous (Function.uncurry F) :=
    (continuous_const.inner (continuous_cavityRotationAction n)).abs.pow p
  have hb (U : Orthogonal n) (z : EuclideanSpace ℝ (Fin n)) :
      |F U z| ≤ ‖v‖ ^ p * ‖z‖ ^ p := by
    dsimp [F]
    rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _), ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (by
      simpa only [(matrixRotation U).norm_map] using abs_real_inner_le_norm v (matrixRotation U z)) p
  have hi : Integrable (Function.uncurry F) (μ.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
    apply (((cavity_gaussian_norm_pow_integrable n p).const_mul (‖v‖ ^ p)).comp_snd μ).mono'
      hF.aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      change |F z.1 z.2| ≤ ‖v‖ ^ p * ‖z.2‖ ^ p
      exact hb z.1 z.2)
  have hrot (U : Orthogonal n) :
      (∫ z, F U z ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
        ∫ z, |⟪v, z⟫| ^ p ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
    calc
      _ = ∫ z, |⟪v, z⟫| ^ p
          ∂(stdGaussian (EuclideanSpace ℝ (Fin n))).map (matrixRotation U) :=
        (integral_map (matrixRotation U).continuous.aemeasurable (by fun_prop)).symm
      _ = _ := by rw [stdGaussian_map]
  calc
    _ = ∫ U, ∫ z, F U z ∂stdGaussian (EuclideanSpace ℝ (Fin n)) ∂μ := by
      simp_rw [hrot]
      simp
    _ = ∫ z, ∫ U, F U z ∂μ ∂stdGaussian (EuclideanSpace ℝ (Fin n)) :=
      integral_integral_swap hi
    _ = ∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ ^ p *
        (∫ U, |⟪v, matrixRotation U u⟫| ^ p ∂μ) ∂stdGaussian _ :=
      integral_congr_ae (ae_of_all _ (fun z => cavity_sphere_radial_average μ v u z hu p))
    _ = _ := integral_mul_const _ _

theorem cavity_sphere_even_moment_bound {n : ℕ} (hn : 0 < n)
    (μ : Measure (Orthogonal n)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (v u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) (k : ℕ) :
    (∫ U, |⟪v, matrixRotation U u⟫| ^ (2 * k) ∂μ) ≤
      cavityGaussianAbsMoment (2 * k) * ‖v‖ ^ (2 * k) / (n : ℝ) ^ k := by
  have hp : (0 : ℝ) < (n : ℝ) ^ k := pow_pos (Nat.cast_pos.mpr hn) k
  apply (le_div_iff₀ hp).mpr
  have hnon : 0 ≤ ∫ U, |⟪v, matrixRotation U u⟫| ^ (2 * k) ∂μ :=
    integral_nonneg (fun _ => pow_nonneg (abs_nonneg _) _)
  calc
    _ = (n : ℝ) ^ k * ∫ U, |⟪v, matrixRotation U u⟫| ^ (2 * k) ∂μ := mul_comm _ _
    _ ≤ (∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ ^ (2 * k) ∂stdGaussian _) *
        ∫ U, |⟪v, matrixRotation U u⟫| ^ (2 * k) ∂μ :=
      mul_le_mul_of_nonneg_right (cavity_gaussian_radial_moment_lower n k) hnon
    _ = cavityGaussianAbsMoment (2 * k) * ‖v‖ ^ (2 * k) := by
      rw [← cavity_gaussian_angular_moment μ v u hu, cavity_gaussian_inner_abs_moment, mul_comm]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLogFloor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform second moment of the negative log normalizer permits
removing the positive floor after the finite-replica limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace InvariantIsing

lemma cavity_log_floor_bound {z δ M R : ℝ} (hz : 0 < z) (hzM : z ≤ M)
    (_hM : 1 ≤ M) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hR : 1 ≤ R) :
    0 ≤ Real.log (z + δ) - Real.log z ∧
      Real.log (z + δ) - Real.log z ≤
        δ * Real.exp R + (1 + Real.log (M + 1)) * (max (-Real.log z) 0) ^ 2 / R := by
  have hzδ : 0 < z + δ := add_pos_of_pos_of_nonneg hz hδ
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hL : 0 ≤ Real.log (M + 1) := Real.log_nonneg (by linarith [_hM])
  refine ⟨sub_nonneg.mpr (Real.log_le_log hz (by linarith)), ?_⟩
  have hsec : Real.log (z + δ) - Real.log z ≤ δ / z := by
    rw [← Real.log_div hzδ.ne' hz.ne']
    apply (Real.log_le_sub_one_of_pos (div_pos hzδ hz)).trans_eq
    field_simp
    ring
  by_cases hsmall : -Real.log z ≤ R
  · have hzr : Real.exp (-R) ≤ z := by
      conv_rhs => rw [← Real.exp_log hz]
      exact Real.exp_le_exp.mpr (by linarith)
    have hd : δ / z ≤ δ * Real.exp R := by
      have hh := div_le_div_of_nonneg_left hδ (Real.exp_pos (-R)) hzr
      simpa only [div_eq_mul_inv, Real.exp_neg, inv_inv] using hh
    exact (hsec.trans hd).trans (le_add_of_nonneg_right (by positivity))
  · have hy : max (-Real.log z) 0 = -Real.log z := max_eq_left (by linarith)
    rw [hy]
    have hY : -Real.log z ≤ (-Real.log z) ^ 2 / R := by
      apply (le_div_iff₀ hR0).mpr
      nlinarith
    have h1 : 1 ≤ (-Real.log z) ^ 2 / R := (by linarith : 1 ≤ -Real.log z).trans hY
    have hu : Real.log (z + δ) - Real.log z ≤ Real.log (M + 1) + -Real.log z := by
      have hh := Real.log_le_log hzδ (show z + δ ≤ M + 1 by linarith)
      linarith
    calc
      _ ≤ Real.log (M + 1) + -Real.log z := hu
      _ ≤ Real.log (M + 1) * ((-Real.log z) ^ 2 / R) + ((-Real.log z) ^ 2 / R) :=
        add_le_add (by nlinarith) hY
      _ = (1 + Real.log (M + 1)) * (-Real.log z) ^ 2 / R := by ring
      _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hδ (Real.exp_pos R).le)

lemma cavity_log_floor_integral_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → ℝ) (hZ : Measurable Z)
    {M K δ R : ℝ} (hZ0 : ∀ ω, 0 < Z ω) (hZM : ∀ ω, Z ω ≤ M)
    (hM : 1 ≤ M) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hR : 1 ≤ R)
    (hi : Integrable (fun ω => (max (-Real.log (Z ω)) 0)^2) P)
    (hK : (∫ ω, (max (-Real.log (Z ω)) 0)^2 ∂P) ≤ K) :
    0 ≤ (∫ ω, Real.log (Z ω + δ) - Real.log (Z ω) ∂P) ∧
      (∫ ω, Real.log (Z ω + δ) - Real.log (Z ω) ∂P) ≤
        δ * Real.exp R + (1 + Real.log (M + 1)) * K / R := by
  let L := 1 + Real.log (M + 1)
  have hL : 0 ≤ L := by dsimp only [L]; have := Real.log_nonneg (show 1 ≤ M + 1 by linarith); linarith
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hbound ω := cavity_log_floor_bound (hZ0 ω) (hZM ω) hM hδ hδ1 hR
  have him : Integrable (fun ω => δ * Real.exp R + L * (max (-Real.log (Z ω)) 0)^2 / R) P :=
    (integrable_const _).add ((hi.const_mul L).div_const R)
  have hie : Integrable (fun ω => Real.log (Z ω + δ) - Real.log (Z ω)) P :=
    him.mono' ((hZ.add_const δ).log.sub hZ.log).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hbound ω).1]
        exact (hbound ω).2)
  refine ⟨integral_nonneg (fun ω => (hbound ω).1), ?_⟩
  calc
    _ ≤ ∫ ω, δ * Real.exp R + L * (max (-Real.log (Z ω)) 0)^2 / R ∂P :=
      integral_mono hie him (fun ω => (hbound ω).2)
    _ = δ * Real.exp R + L * (∫ ω, (max (-Real.log (Z ω)) 0)^2 ∂P) / R := by
      rw [integral_add (integrable_const _) ((hi.const_mul L).div_const R)]
      simp only [integral_div, integral_const_mul, integral_const, probReal_univ, one_smul]
    _ ≤ _ := add_le_add le_rfl (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hK hL) hR0.le)

lemma cavity_log_floor_uniform {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Z : (n : ℕ) → Ω n → ℝ) (hZ : ∀ n, Measurable (Z n))
    {M K : ℝ} (hZ0 : ∀ n ω, 0 < Z n ω) (hZM : ∀ n ω, Z n ω ≤ M)
    (hM : 1 ≤ M) (hK0 : 0 ≤ K)
    (hi : ∀ n, Integrable (fun ω => (max (-Real.log (Z n ω)) 0)^2) (P n))
    (hK : ∀ n, (∫ ω, (max (-Real.log (Z n ω)) 0)^2 ∂P n) ≤ K) :
    ∀ ε > 0, ∃ δ₀ > 0, ∀ δ ∈ Icc (0 : ℝ) δ₀, ∀ n,
      0 ≤ (∫ ω, Real.log (Z n ω + δ) - Real.log (Z n ω) ∂P n) ∧
        (∫ ω, Real.log (Z n ω + δ) - Real.log (Z n ω) ∂P n) < ε := by
  intro ε hε
  let L := 1 + Real.log (M + 1)
  have hL : 0 ≤ L := by dsimp only [L]; have := Real.log_nonneg (show 1 ≤ M + 1 by linarith); linarith
  let R := 1 + 4 * L * K / ε
  have hR : 1 ≤ R := le_add_of_nonneg_right (div_nonneg (by positivity) hε.le)
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hRmul : R * ε = ε + 4 * L * K := by
    dsimp only [R]
    field_simp
  have htail : L * K / R < ε / 4 := by
    apply (div_lt_iff₀ hR0).mpr
    nlinarith
  refine ⟨min 1 (ε / (4 * Real.exp R)), lt_min zero_lt_one (div_pos hε (by positivity)), ?_⟩
  intro δ hδ n
  have hδ1 : δ ≤ 1 := hδ.2.trans (min_le_left _ _)
  have hδe : δ * Real.exp R ≤ ε / 4 := by
    have hh := (le_div_iff₀ (show 0 < 4 * Real.exp R by positivity)).mp
      (hδ.2.trans (min_le_right _ _))
    nlinarith
  have hh := cavity_log_floor_integral_bound (P n) (Z n) (hZ n) (hZ0 n) (hZM n)
    hM hδ.1 hδ1 hR (hi n) (hK n)
  refine ⟨hh.1, hh.2.trans_lt ?_⟩
  change δ * Real.exp R + L * K / R < ε
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCappedLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The negative logarithm of a capped cavity weight is controlled by
the original energy moments, uniformly in the cap. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Topology

namespace InvariantIsing

lemma cavity_capped_log_negative_bound {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ) (hH : Measurable H)
    (hiH : Integrable H ν) {T : ℝ} (hT : 0 ≤ T) :
    max (-Real.log (∫ x, Real.exp (min (H x) T) ∂ν)) 0 ≤ ∫ x, |H x| ∂ν := by
  have him : Integrable (fun x => min (H x) T) ν := by
    apply (hiH.abs.add (integrable_const |T|)).mono'
      (hH.min measurable_const).aestronglyMeasurable
    exact ae_of_all _ (fun x => by
      change |min (H x) T| ≤ |H x| + |T|
      apply abs_le.mpr
      constructor
      · exact le_min (by linarith [neg_abs_le (H x), abs_nonneg T])
          (by linarith [neg_abs_le T, abs_nonneg (H x)])
      · exact (min_le_left _ _).trans (by linarith [le_abs_self (H x), abs_nonneg T]))
  have hie : Integrable (fun x => Real.exp (min (H x) T)) ν := by
    apply Integrable.of_bound ((hH.min measurable_const).exp).aestronglyMeasurable (Real.exp T)
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (min_le_right _ _)
  have hz := integral_exp_pos hie
  have hj : (∫ x, min (H x) T ∂ν) ≤ Real.log (∫ x, Real.exp (min (H x) T) ∂ν) :=
    (Real.le_log_iff_exp_le hz).mpr (exp_integral_le_partition him hie)
  have hl : -(∫ x, |H x| ∂ν) ≤ ∫ x, min (H x) T ∂ν := by
    rw [← integral_neg]
    apply integral_mono hiH.abs.neg him
    intro x
    exact le_min (neg_abs_le _) ((neg_nonpos.mpr (abs_nonneg _)).trans hT)
  exact max_le (by linarith) (integral_nonneg fun _ => abs_nonneg _)

lemma cavity_capped_log_negative_sq_bound {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H R : X → ℝ)
    (hH : Measurable H) (hiH : Integrable H ν)
    (hiH2 : Integrable (fun x => |H x| ^ 2) ν)
    (hiR4 : Integrable (fun x => R x ^ 4) ν)
    {C T : ℝ} (_hC : 0 ≤ C) (hT : 0 ≤ T) (hbound : ∀ x, |H x| ≤ C * (1 + R x ^ 2)) :
    (max (-Real.log (∫ x, Real.exp (min (H x) T) ∂ν)) 0)^2 ≤
      2 * C ^ 2 * (1 + ∫ x, R x ^ 4 ∂ν) := by
  have hl := cavity_capped_log_negative_bound ν H hH hiH hT
  have hj := (convexOn_pow 2 (𝕜 := ℝ)).map_integral_le (by fun_prop)
    isClosed_Ici (ae_of_all _ (fun x => abs_nonneg (H x))) hiH.abs hiH2
  have hp : (max (-Real.log (∫ x, Real.exp (min (H x) T) ∂ν)) 0)^2 ≤ ∫ x, |H x|^2 ∂ν := by
    exact (pow_le_pow_left₀ (le_max_right _ _) hl 2).trans hj
  have hu : (∫ x, |H x|^2 ∂ν) ≤ 2 * C ^ 2 * (1 + ∫ x, R x ^ 4 ∂ν) := by
    have hb := integral_mono hiH2 ((integrable_const 1).add hiR4 |>.const_mul (2 * C ^ 2))
      (fun x => by
        change |H x| ^ 2 ≤ 2 * C ^ 2 * (1 + R x ^ 4)
        have hs := pow_le_pow_left₀ (abs_nonneg (H x)) (hbound x) 2
        nlinarith [sq_nonneg (R x ^ 2 - 1), sq_nonneg C])
    simpa only [integral_const_mul, Pi.add_apply, integral_add (integrable_const 1) hiR4,
      integral_const, probReal_univ, one_smul] using hb
  exact hp.trans hu

theorem cavity_capped_log_negative_sq_of_growth {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H R : X → ℝ) (hH : Measurable H)
    (hiR4 : Integrable (fun x => R x ^ 4) ν)
    {C T : ℝ} (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hbound : ∀ x, |H x| ≤ C * (1 + R x ^ 2)) :
    (max (-Real.log (∫ x, Real.exp (min (H x) T) ∂ν)) 0)^2 ≤
      2 * C ^ 2 * (1 + ∫ x, R x ^ 4 ∂ν) := by
  have hs x : |H x|^2 ≤ 2 * C^2 * (1 + R x^4) := by
    have hh := pow_le_pow_left₀ (abs_nonneg (H x)) (hbound x) 2
    nlinarith [sq_nonneg (R x^2 - 1), sq_nonneg C]
  have hiH : Integrable H ν := by
    apply (((integrable_const 1).add hiR4).const_mul (2 * C)).mono' hH.aestronglyMeasurable
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      change |H x| ≤ 2 * C * (1 + R x^4)
      have hh := mul_le_mul_of_nonneg_left
        (show 1 + R x^2 ≤ 2 * (1 + R x^4) by nlinarith [sq_nonneg (R x^2 - 1)]) hC
      nlinarith [hbound x]
  have hiH2 : Integrable (fun x => |H x|^2) ν := by
    apply (((integrable_const 1).add hiR4).const_mul (2 * C^2)).mono'
      (hH.abs.pow_const 2).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hs x
  exact cavity_capped_log_negative_sq_bound ν H R hH hiH hiH2 hiR4 hC hT hbound

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFactorBound
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.spinValue_not
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quadratic growth bound for the actual cavity exponent. The bound
does not require the special-coordinate block matrices to commute. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_bilinear_abs_bound {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ)
    (x : Fin d → ℝ) (y : Fin n → ℝ) {a b : ℝ} (ha : 0 ≤ a) (_hb : 0 ≤ b)
    (hx : ∀ i, |x i| ≤ a) (hy : ∀ j, |y j| ≤ b) :
    |∑ i, ∑ j, x i * A i j * y j| ≤ cavityMatrixMass A * (a * b) := by
  calc
    _ ≤ ∑ i, |∑ j, x i * A i j * y j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |x i * A i j * y j| :=
      Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, |A i j| * (a * b) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      calc
        _ = |A i j| * (|x i| * |y j|) := by simp only [abs_mul]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul (hx i) (hy j) (abs_nonneg _) ha)
          (abs_nonneg _)
    _ = _ := by simp only [cavityMatrixMass, Finset.sum_mul]

lemma cavity_quadratic_abs_bound {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (y : EuclideanSpace ℝ (Fin d)) :
    |cavityQuadratic A y| ≤ cavityMatrixMass A * ‖y‖ ^ 2 := by
  have hy i : |y i| ≤ ‖y‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y i
  have h := cavity_bilinear_abs_bound A y y (norm_nonneg y) (norm_nonneg y) hy hy
  have hm := cavityMatrixMass_nonneg A
  rw [cavityQuadratic, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  nlinarith [sq_nonneg ‖y‖]

lemma cavity_spin_quadratic_abs_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (ε : Spin n) :
    |cavityQuadratic A (fun j => spinValue (ε j))| ≤ cavityMatrixMass A := by
  have h := cavity_bilinear_abs_bound A (fun j => spinValue (ε j)) (fun j => spinValue (ε j))
    zero_le_one zero_le_one (fun i => (abs_spinValue (ε i)).le) (fun i => (abs_spinValue (ε i)).le)
  rw [cavityQuadratic, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hm := cavityMatrixMass_nonneg A
  simp only [mul_one] at h
  linarith

theorem cavity_logFactor_growth {d n : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin d)) (ε : Spin n) :
    |cavityLogFactor K L C y ε| ≤
      (cavityMatrixMass K + cavityMatrixMass L + cavityMatrixMass C) * (1 + ‖y‖ ^ 2) := by
  have hK := cavity_quadratic_abs_bound K y
  have hC := cavity_spin_quadratic_abs_bound C ε
  have hy i : |y i| ≤ ‖y‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y i
  have hL := cavity_bilinear_abs_bound L y (fun j => spinValue (ε j))
    (norm_nonneg y) zero_le_one hy (fun j => (abs_spinValue (ε j)).le)
  have hnorm : ‖y‖ ≤ 1 + ‖y‖ ^ 2 := by nlinarith [sq_nonneg (‖y‖ - 1)]
  have hL' := mul_le_mul_of_nonneg_left hnorm (cavityMatrixMass_nonneg L)
  have hsum := (abs_add_le (cavityQuadratic K y + ∑ i, ∑ j, y i * L i j * spinValue (ε j))
    (cavityQuadratic C (fun j => spinValue (ε j)))).trans
      (add_le_add (abs_add_le _ _) le_rfl)
  change |cavityLogFactor K L C y ε| ≤ _ at hsum
  simp only [mul_one] at hL
  nlinarith [cavityMatrixMass_nonneg K, cavityMatrixMass_nonneg C,
    mul_nonneg (cavityMatrixMass_nonneg C) (sq_nonneg ‖y‖)]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFrameMeasurable
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability of the finite Gram normalization, including its
arbitrary singular-matrix values. -/

noncomputable section
open MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_matrix_inverse_measurable {q : ℕ} :
    Measurable (Inv.inv : Matrix (Fin q) (Fin q) ℝ → Matrix (Fin q) (Fin q) ℝ) := by
  have he (A : Matrix (Fin q) (Fin q) ℝ) : A⁻¹ = A.det⁻¹ • A.adjugate := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
  simp_rw [show (Inv.inv : Matrix (Fin q) (Fin q) ℝ → _) =
    (fun A => A.det⁻¹ • A.adjugate) from funext he]
  exact continuous_id.matrix_det.measurable.inv.smul continuous_id.matrix_adjugate.measurable

lemma measurable_cavityNormalizeFrame (n q : ℕ) :
    Measurable (cavityNormalizeFrame : Matrix (Fin n) (Fin q) ℝ → Matrix (Fin n) (Fin q) ℝ) := by
  have hg : Measurable (fun A : Matrix (Fin n) (Fin q) ℝ => A.transpose * A) := by
    apply Measurable.of_eval_matrix
    intro i j
    change Measurable (fun A : Matrix (Fin n) (Fin q) ℝ => ∑ k, A k i * A k j)
    exact Finset.measurable_sum _ (fun k _ =>
      (Matrix.measurable_apply (i := k) (j := i)).mul
        (Matrix.measurable_apply (i := k) (j := j)))
  have hs : Measurable (fun A : Matrix (Fin n) (Fin q) ℝ => CFC.sqrt (A.transpose * A)) :=
    CFC.measurable_sqrt.comp hg
  have hi : Measurable (fun A : Matrix (Fin n) (Fin q) ℝ =>
      (CFC.sqrt (A.transpose * A))⁻¹) := cavity_matrix_inverse_measurable.comp hs
  unfold cavityNormalizeFrame
  apply Measurable.of_eval_matrix
  intro i j
  change Measurable (fun A : Matrix (Fin n) (Fin q) ℝ =>
    ∑ k, A i k * ((CFC.sqrt (A.transpose * A))⁻¹) k j)
  exact Finset.measurable_sum _ (fun k _ =>
    (Matrix.measurable_apply (i := i) (j := k)).mul (hi.eval_matrix))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityComplement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous local choice of the special complement in the cavity
block: project a limiting frame and orthonormalize its columns. -/

noncomputable section
open Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavityRawComplement_eq {r n d : ℕ} (E : Matrix (Fin r) (Fin n) ℝ)
    (B₀ : Matrix (Fin r) (Fin d) ℝ) (hEB : E.transpose * B₀ = 0) :
    cavityRawComplement E B₀ = B₀ := by
  simp only [cavityRawComplement, Matrix.sub_mul, Matrix.one_mul,
    Matrix.mul_assoc, hEB, Matrix.mul_zero, sub_zero]

lemma cavityComplement_gram {r n d : ℕ} (E : Matrix (Fin r) (Fin n) ℝ)
    (B₀ : Matrix (Fin r) (Fin d) ℝ)
    (hG : ((cavityRawComplement E B₀).transpose * cavityRawComplement E B₀).PosDef) :
    (cavityComplement E B₀).transpose * cavityComplement E B₀ = 1 :=
  cavityNormalizeFrame_gram _ hG

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpectralStack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cavity column stack formed from square roots of spectral
compressions. Its columns are orthonormal when the compressions sum to
the identity, and it has the required deterministic limit. -/

noncomputable section
open Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavitySpectralStack_gram {m n : ℕ}
    (M : Fin m → Matrix (Fin n) (Fin n) ℝ) (hM : ∀ a, (M a).PosSemidef) :
    (cavitySpectralStack M).transpose * cavitySpectralStack M = ∑ a, M a := by
  ext i j
  change (∑ k : Fin (m * n),
      CFC.sqrt (M (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2 i *
      CFC.sqrt (M (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2 j) = _
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n))]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  have hs : (CFC.sqrt (M a)).transpose = CFC.sqrt (M a) :=
    Matrix.isHermitian_iff_isSymm.mp
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (M a))).isHermitian
  have he := CFC.sqrt_mul_sqrt_self (M a) (hM a).nonneg
  have he' : (CFC.sqrt (M a)).transpose * CFC.sqrt (M a) = M a := by
    rw [hs, he]
  have hentry := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) he'
  exact hentry

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete the limiting cavity columns by a fixed orthonormal special
frame. This is the reference frame for the continuous complement rule. -/

noncomputable section
open scoped RealInnerProductSpace Matrix

namespace InvariantIsing

theorem cavity_frame_completion {d n : ℕ}
    (E : Matrix (Fin (d + n)) (Fin n) ℝ) (hE : E.transpose * E = 1) :
    ∃ B : Matrix (Fin (d + n)) (Fin d) ℝ,
      B.transpose * B = 1 ∧ E.transpose * B = 0 := by
  let e := EuclideanSpace.basisFun (Fin (d + n)) ℝ
  have hr : Orthonormal ℝ (fun j : Fin n => e (Fin.natAdd d j)) :=
    e.orthonormal.comp _ (fun _ _ h => Fin.ext (by simpa using congrArg Fin.val h))
  obtain ⟨U, hU⟩ := cavity_orthonormal_transitive
    (fun j : Fin n => e (Fin.natAdd d j))
    (fun j : Fin n => WithLp.toLp 2 (fun i => E i j)) hr (cavity_orthonormal_of_gram E hE)
  let B : Matrix (Fin (d + n)) (Fin d) ℝ := fun i j => U (e (Fin.castAdd n j)) i
  refine ⟨B, ?_, ?_⟩
  · ext i j
    change (∑ k, U (e (Fin.castAdd n i)) k * U (e (Fin.castAdd n j)) k) =
      if i = j then 1 else 0
    have hh := U.inner_map_map (e (Fin.castAdd n i)) (e (Fin.castAdd n j))
    have he := orthonormal_iff_ite.mp e.orthonormal (Fin.castAdd n i) (Fin.castAdd n j)
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
      Fin.castAdd_inj, mul_comm] using hh.trans he
  · ext i j
    change (∑ k, E k i * U (e (Fin.castAdd n j)) k) = 0
    have hh := U.inner_map_map (e (Fin.castAdd n j)) (e (Fin.natAdd d i))
    rw [hU i] at hh
    have hne : Fin.castAdd n j ≠ Fin.natAdd d i := by
      intro h
      have hval := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
      omega
    have he := orthonormal_iff_ite.mp e.orthonormal (Fin.castAdd n j) (Fin.natAdd d i)
    rw [ite_eq_right hne] at he
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
      PiLp.toLp_apply] using hh.trans he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityMeasurableComplement
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A global measurable completion of the cavity columns. The rule first
tries the prescribed limiting frame and otherwise uses a fixed dense
sequence. Near the limit it agrees with the continuous local rule. -/

noncomputable section
open MeasureTheory Filter TopologicalSpace
open scoped Matrix Topology MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma continuous_cavityRawComplement {r d n : ℕ}
    (B : Matrix (Fin r) (Fin d) ℝ) :
    Continuous (fun E : Matrix (Fin r) (Fin n) ℝ => cavityRawComplement E B) :=
  (continuous_const.sub (continuous_id.matrix_mul continuous_id.matrix_transpose)).matrix_mul
    continuous_const

lemma measurableSet_cavityGoodCandidate {d n : ℕ}
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ) (k : ℕ) :
    MeasurableSet {E | cavityGoodCandidate B₀ E k} := by
  have h := continuous_cavityRawComplement (n := n) (cavityComplementCandidate B₀ k)
  exact isOpen_lt continuous_const ((h.matrix_transpose.matrix_mul h).matrix_det) |>.measurableSet

lemma cavityGoodCandidate_exists {d n : ℕ}
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ)
    (E : Matrix (Fin (d + n)) (Fin n) ℝ) (hE : E.transpose * E = 1) :
    ∃ k, cavityGoodCandidate B₀ E k := by
  obtain ⟨B, hB, hEB⟩ := cavity_frame_completion E hE
  let s : Set (Matrix (Fin (d + n)) (Fin d) ℝ) :=
    {A | 0 < ((cavityRawComplement E A).transpose * cavityRawComplement E A).det}
  have hraw : Continuous (fun A : Matrix (Fin (d + n)) (Fin d) ℝ => cavityRawComplement E A) :=
    continuous_const.matrix_mul continuous_id
  have hs : IsOpen s := isOpen_lt continuous_const ((hraw.matrix_transpose.matrix_mul hraw).matrix_det)
  have hBmem : B ∈ s := by
    change 0 < ((cavityRawComplement E B).transpose * cavityRawComplement E B).det
    rw [cavityRawComplement_eq E B hEB, hB, Matrix.det_one]
    norm_num
  obtain ⟨k, hk⟩ := (denseRange_denseSeq (Fin (d + n) → Fin d → ℝ)).exists_mem_open hs ⟨B, hBmem⟩
  exact ⟨k + 1, hk⟩

lemma measurable_cavitySelectedComplement {d n : ℕ}
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ) : Measurable (cavitySelectedComplement B₀) := by
  classical
  refine Measurable.find (p := fun k E => cavityComplementChoicePredicate B₀ E k)
    (f := fun k E => cavityComplement E (cavityComplementCandidate B₀ (k - 1)))
    ?_ ?_ (cavityComplementChoice_exists B₀)
  · intro k
    exact (measurable_cavityNormalizeFrame _ _).comp
      (continuous_cavityRawComplement (cavityComplementCandidate B₀ (k - 1))).measurable
  · intro k
    by_cases hk : k = 0
    · subst k
      have he : {E | cavityComplementChoicePredicate B₀ E 0} =
          (⋃ j, {E | cavityGoodCandidate B₀ E j})ᶜ := by
        ext E
        simp [cavityComplementChoicePredicate]
      rw [he]
      exact (MeasurableSet.iUnion (fun j => measurableSet_cavityGoodCandidate B₀ j)).compl
    · simpa only [cavityComplementChoicePredicate, ite_eq_right hk] using
        measurableSet_cavityGoodCandidate B₀ (k - 1)

lemma cavitySelectedComplement_gram {d n : ℕ}
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ)
    (E : Matrix (Fin (d + n)) (Fin n) ℝ) (hE : E.transpose * E = 1) :
    (cavitySelectedComplement B₀ E).transpose * cavitySelectedComplement B₀ E = 1 := by
  classical
  have he := cavityGoodCandidate_exists B₀ E hE
  have hs := Nat.find_spec (cavityComplementChoice_exists B₀ E)
  have hn : Nat.find (cavityComplementChoice_exists B₀ E) ≠ 0 := by
    intro h
    simp only [cavityComplementChoicePredicate, h, ite_true, if_true] at hs
    exact hs he
  have hg : cavityGoodCandidate B₀ E (Nat.find (cavityComplementChoice_exists B₀ E) - 1) := by
    simpa only [cavityComplementChoicePredicate, ite_eq_right hn] using hs
  apply cavityComplement_gram
  apply cavity_posDef_of_posSemidef_det_ne_zero
  · simpa using Matrix.posSemidef_conjTranspose_mul_self
      (cavityRawComplement E (cavityComplementCandidate B₀
        (Nat.find (cavityComplementChoice_exists B₀ E) - 1)))
  · exact hg.ne'

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpectralImages
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The separate spectral images of the cavity columns. These are the
concrete inputs to the normalized-frame coupling construction. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavitySpectralImage_gram {r m n : ℕ} (g : Fin r → Fin m)
    (A : Matrix (Fin r) (Fin n) ℝ) (a : Fin m) :
    (cavitySpectralImage g A a).transpose * cavitySpectralImage g A a =
      A.transpose * Matrix.diagonal (fun i => if g i = a then (1 : ℝ) else 0) * A := by
  ext i j
  change (∑ k : Fin r, (if g k = a then A k i else 0) *
    (if g k = a then A k j else 0)) =
    ∑ k : Fin r, (∑ t : Fin r,
      A t i * (if t = k then (if g t = a then (1 : ℝ) else 0) else 0)) * A k j
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp_all

lemma measurable_cavitySpectralImage {r m n : ℕ} (g : Fin r → Fin m) (a : Fin m) :
    Measurable (fun A : Matrix (Fin r) (Fin n) ℝ => cavitySpectralImage g A a) := by
  apply Measurable.of_eval_matrix
  intro i j
  by_cases h : g i = a
  · simpa only [cavitySpectralImage, h, ite_true, if_true] using
      (Matrix.measurable_apply (i := i) (j := j))
  · simpa only [cavitySpectralImage, h, ite_false, if_false] using
      (measurable_const : Measurable (fun _ : Matrix (Fin r) (Fin n) ℝ => (0 : ℝ)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRetainedFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete the cavity directions inside each spectral group. The added
columns are retained eigenvectors supported in the same group. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavitySpectralProjectors_sum {r m : ℕ} (g : Fin r → Fin m) :
    (∑ a, Matrix.diagonal (fun i : Fin r => if g i = a then (1 : ℝ) else 0)) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.sum_apply, Matrix.diagonal_apply_eq, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, if_true, Matrix.one_apply_eq]
  · simp only [Matrix.sum_apply, Matrix.diagonal_apply_ne _ hij,
      Finset.sum_const_zero, Matrix.one_apply_ne hij]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPhysicalBase
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable base interaction built from the actual cavity columns. -/

noncomputable section
open MeasureTheory
open scoped Matrix

namespace InvariantIsing

lemma measurable_cavityColumns (N n : ℕ) :
    Measurable (cavityColumns : Orthogonal (N + n) → Matrix (Fin (N + n)) (Fin n) ℝ) := by
  apply Measurable.of_eval_matrix
  intro i j
  exact (Matrix.measurable_apply (i := i) (j := Fin.natAdd N j)).comp measurable_subtype_coe

lemma measurable_cavityCompressionGrams {N n m : ℕ} (g : Fin (N + n) → Fin m) :
    Measurable (cavityCompressionGrams g) := by
  apply measurable_pi_iff.mpr
  intro a
  have hX := (measurable_cavitySpectralImage g a).comp (measurable_cavityColumns N n)
  exact ((continuous_id.matrix_transpose.matrix_mul continuous_id).measurable).comp hX

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityTruncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform covariance bounds for the monomials omitted when the
perturbation cutoff changes by a fixed cavity size. -/

noncomputable section
open IsingPerceptron Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem cavity_covariance_cutoff_error_tendsto (n : ℕ) :
    Tendsto (fun N : ℕ => (N + n) * perturbationScale (N + n) ^ 2 * (1 / 2 : ℝ) ^ N)
      atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ => ((N : ℝ) + n) * (1 / 2 : ℝ) ^ N) atTop (𝓝 0) := by
    simp only [add_mul]
    simpa only [mul_zero, add_zero] using
      (tendsto_self_mul_const_pow_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (n : ℝ))
  apply squeeze_zero' _ _ ht
  · exact Eventually.of_forall (fun N => by positivity)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hp := perturbationScale_sq_le_one (N := N + n) (by omega)
    have hh := mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ N + n by positivity)
    exact (mul_le_mul_of_nonneg_right (by simpa only [mul_one] using hh)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) N))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityComparisonRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dimension-dependent errors in the finite cavity comparison.
The geometric cutoff is retained with its full Gaussian amplitude. -/

noncomputable section
open IsingPerceptron Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma cavityCovarianceRate_nonneg (n : ℕ) {C : ℝ} (hC : 0 ≤ C) (N : ℕ) :
    0 ≤ cavityCovarianceRate n C N := by
  unfold cavityCovarianceRate
  positivity

lemma cavityCovarianceRate_tendsto (n : ℕ) (C : ℝ) :
    Tendsto (cavityCovarianceRate n C) atTop (𝓝 0) := by
  have he : Tendsto perturbationScale atTop (𝓝 (0 : ℝ)) := by
    change Tendsto (fun N : ℕ => (N : ℝ) ^ (-1 / 16 : ℝ)) atTop (𝓝 0)
    simpa only [neg_div] using tendsto_nat_rpow_neg (by norm_num : (0 : ℝ) < 1 / 16)
  have hs := (cavity_covariance_amplitude_increment_tendsto n).abs.const_mul 4
  have hm := (he.pow 2).const_mul (4 * C)
  have ht := (cavity_covariance_cutoff_error_tendsto n).const_mul 4
  have heq : cavityCovarianceRate n C = (fun N : ℕ =>
      4 * |(N + n) * perturbationScale (N + n) ^ 2 - N * perturbationScale N ^ 2| +
        (4 * C) * perturbationScale N ^ 2 +
        4 * ((N + n) * perturbationScale (N + n) ^ 2 * (1 / 2 : ℝ) ^ N)) := rfl
  rw [heq]
  simpa only [abs_zero, mul_zero, zero_pow (by omega : 2 ≠ 0), add_zero] using (hs.add hm).add ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectionControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Deterministic control of the special coordinates by the unnormalized
spectral images. Only the inverse square-root norms on the good event enter. -/

noncomputable section
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_frame_transpose_contraction {r d : ℕ}
    (B : Matrix (Fin r) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (z : EuclideanSpace ℝ (Fin r)) :
    ‖(WithLp.toLp 2 (B.transpose *ᵥ z.ofLp) : EuclideanSpace ℝ (Fin d))‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  have ho : Orthonormal ℝ (fun i : Fin d =>
      (WithLp.toLp 2 (fun j : Fin r => B j i) : EuclideanSpace ℝ (Fin r))) := by
    rw [orthonormal_iff_ite]
    intro i j
    have h := congrArg (fun A : Matrix (Fin d) (Fin d) ℝ => A i j) hB
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
      PiLp.toLp_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      mul_comm] using h
  have hb := ho.sum_inner_products_le (s := Finset.univ) z
  simpa only [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, star_trivial, PiLp.toLp_apply, Matrix.mulVec, Matrix.transpose_apply,
    Real.norm_eq_abs, sq_abs, mul_comm] using hb

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCompressionBlocks
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint Haar compression limits for the actual measurable cavity block
construction. Only continuity at the prescribed limiting stack is used;
the completion rule need not be continuous on every frame. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator
  BoundedContinuousFunction

namespace InvariantIsing

lemma measurable_cavityReindexedStack {m n d : ℕ} (e : Fin (m * n) ≃ Fin (d + n)) :
    Measurable (cavityReindexedStack e) := by
  apply Measurable.of_eval_matrix
  intro i j
  change Measurable (fun M : Fin m → Matrix (Fin n) (Fin n) ℝ =>
    CFC.sqrt (M (finProdFinEquiv.symm (e.symm i)).1)
      (finProdFinEquiv.symm (e.symm i)).2 j)
  exact (CFC.measurable_sqrt.comp
    (measurable_pi_apply (finProdFinEquiv.symm (e.symm i)).1)).eval_matrix

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCompressionRank
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full rank of the actual spectral compressions, with the eigenvalue
groups arranged in their given consecutive coordinate windows. -/

noncomputable section
open MeasureTheory
open scoped Matrix BigOperators

namespace InvariantIsing

lemma cavityColumns_gram {N n : ℕ} (U : Orthogonal (N + n)) :
    (cavityColumns U).transpose * cavityColumns U = 1 := by
  have hU := (Matrix.mem_orthogonalGroup_iff' (Fin (N + n)) ℝ).mp U.property
  ext i j
  have h := congrArg (fun M : Matrix (Fin (N + n)) (Fin (N + n)) ℝ =>
    M (Fin.natAdd N i) (Fin.natAdd N j)) hU
  change (∑ k : Fin (N + n), (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)
    k (Fin.natAdd N i) * (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)
      k (Fin.natAdd N j)) = if i = j then 1 else 0
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.natAdd_inj] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityConcreteComplement
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The measurable special frame used in the actual base interaction.
Its Gram and cavity-orthogonality identities hold for every input frame. -/

noncomputable section
open MeasureTheory
open scoped Matrix BigOperators

namespace InvariantIsing

lemma cavityCompressionGrams_sum {N n m : ℕ} (g : Fin (N + n) → Fin m)
    (U : Orthogonal (N + n)) : ∑ a, cavityCompressionGrams g U a = 1 := by
  unfold cavityCompressionGrams
  simp_rw [cavitySpectralImage_gram]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, cavitySpectralProjectors_sum, Matrix.mul_one]
  exact cavityColumns_gram U

lemma measurable_cavityConcreteComplement {m n d : ℕ}
    (e : Fin (m * n) ≃ Fin (d + n)) (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ) :
    Measurable (cavityConcreteComplement e B₀) := by
  have h := (measurable_cavitySelectedComplement B₀).comp (measurable_cavityReindexedStack e)
  apply Measurable.of_eval_matrix
  intro i j
  exact h.eval_matrix

lemma cavityReindexedStack_compression_gram {N n m d : ℕ}
    (g : Fin (N + n) → Fin m) (e : Fin (m * n) ≃ Fin (d + n))
    (U : Orthogonal (N + n)) :
    (cavityReindexedStack e (cavityCompressionGrams g U)).transpose *
      cavityReindexedStack e (cavityCompressionGrams g U) = 1 := by
  have hM : ∀ a, (cavityCompressionGrams g U a).PosSemidef := by
    intro a
    simpa only [cavityCompressionGrams, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self (cavitySpectralImage g (cavityColumns U) a)
  have hs := cavitySpectralStack_gram (cavityCompressionGrams g U) hM
  rw [cavityCompressionGrams_sum g U] at hs
  ext i j
  change (∑ k : Fin (d + n),
    cavitySpectralStack (cavityCompressionGrams g U) (e.symm k) i *
      cavitySpectralStack (cavityCompressionGrams g U) (e.symm k) j) =
    (1 : Matrix (Fin n) (Fin n) ℝ) i j
  exact (Equiv.sum_comp e.symm (fun k =>
    cavitySpectralStack (cavityCompressionGrams g U) k i *
      cavitySpectralStack (cavityCompressionGrams g U) k j)).trans
        (congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) hs)

lemma cavityConcreteComplement_gram {N n m d : ℕ}
    (g : Fin (N + n) → Fin m) (e : Fin (m * n) ≃ Fin (d + n))
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ) (U : Orthogonal (N + n)) :
    (cavityConcreteComplement e B₀ (cavityCompressionGrams g U)).transpose *
      cavityConcreteComplement e B₀ (cavityCompressionGrams g U) = 1 := by
  have h := cavitySelectedComplement_gram B₀ _ (cavityReindexedStack_compression_gram g e U)
  ext i j
  change (∑ k : Fin (m * n),
    cavitySelectedComplement B₀ (cavityReindexedStack e (cavityCompressionGrams g U)) (e k) i *
      cavitySelectedComplement B₀ (cavityReindexedStack e (cavityCompressionGrams g U)) (e k) j) = _
  exact (Equiv.sum_comp e (fun k =>
    cavitySelectedComplement B₀ (cavityReindexedStack e (cavityCompressionGrams g U)) k i *
      cavitySelectedComplement B₀ (cavityReindexedStack e (cavityCompressionGrams g U)) k j)).trans
        (congrArg (fun A : Matrix (Fin d) (Fin d) ℝ => A i j) h)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpectralStabilizer
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability
attribute [-simp] _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.planeRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent rotations inside the base spectral groups preserve the
base interaction and rotate its selected frames. -/

noncomputable section
open scoped Matrix BigOperators

namespace InvariantIsing

lemma cavityGroupRotation_frame {N m : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (U : (a : Fin m) → Orthogonal (k a)) (a : Fin m) :
    (cavityGroupRotation k e U : Matrix (Fin N) (Fin N) ℝ) * cavityGroupFrame k e a =
      cavityGroupFrame k e a * (U a : Matrix (Fin (k a)) (Fin (k a)) ℝ) := by
  ext i j
  obtain ⟨⟨b, l⟩, rfl⟩ := e.surjective i
  by_cases hba : b = a
  · subst b
    simp [Matrix.mul_apply, cavityGroupFrame, cavityGroupRotation,
      Matrix.submatrix_apply, e.injective.eq_iff, Matrix.blockDiagonal'_apply_eq]
  · have hne : ∀ t : Fin (k a), e ⟨b, l⟩ ≠ e ⟨a, t⟩ := by
      intro t ht
      exact hba (congrArg Sigma.fst (e.injective ht))
    simp [Matrix.mul_apply, cavityGroupFrame, cavityGroupRotation,
      Matrix.submatrix_apply, hne]
    exact Matrix.blockDiagonal'_apply_ne
      (fun c : Fin m => (U c : Matrix (Fin (k c)) (Fin (k c)) ℝ)) l j hba

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCoefficientError
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative replacement of the finite cavity blocks by their limits.
The energy cap keeps the exponential Lipschitz constant independent of the
Gaussian marks; only their second moments enter the remaining error. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_exp_sub_le {u v B : ℝ} (hu : u ≤ B) (hv : v ≤ B) :
    |Real.exp u - Real.exp v| ≤ Real.exp B * |u - v| := by
  have hone {a b : ℝ} (hab : b ≤ a) (ha : a ≤ B) :
      Real.exp a - Real.exp b ≤ Real.exp B * (a - b) := by
    have ht := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (b - a))
      (Real.exp_pos a).le
    have he : Real.exp a * Real.exp (b - a) = Real.exp b := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he] at ht
    have hm := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ha) (sub_nonneg.mpr hab)
    nlinarith
  rcases le_total v u with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact hone h hu
  · rw [abs_sub_comm (Real.exp u), abs_sub_comm u,
      abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact hone h hv

lemma cavity_capped_exp_sub_le (u v T : ℝ) :
    |Real.exp (min u T) - Real.exp (min v T)| ≤ Real.exp T * |u - v| := by
  apply (cavity_exp_sub_le (min_le_right _ _) (min_le_right _ _)).trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos T).le
  simpa only [sub_self, abs_zero, max_eq_left (abs_nonneg (u - v))] using
    abs_min_sub_min_le_max u T v T

lemma cavityLogFactor_sub {d k : ℕ}
    (K K' : Matrix (Fin d) (Fin d) ℝ) (L L' : Matrix (Fin d) (Fin k) ℝ)
    (C C' : Matrix (Fin k) (Fin k) ℝ) (y : Fin d → ℝ) (ε : Spin k) :
    cavityLogFactor K L C y ε - cavityLogFactor K' L' C' y ε =
      cavityLogFactor (K - K') (L - L') (C - C') y ε := by
  simp only [cavityLogFactor, cavityQuadratic_sub, Matrix.sub_apply,
    mul_sub, sub_mul, Finset.sum_sub_distrib]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCompressionFactors
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual cavity factor coefficients as functions of the compression
grams, with their limit at the deterministic scalar compression. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma measurable_cavitySpectralStack (m n : ℕ) :
    Measurable (cavitySpectralStack :
      (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin n) ℝ) := by
  apply Measurable.of_eval_matrix
  intro i j
  change Measurable (fun M : Fin m → Matrix (Fin n) (Fin n) ℝ =>
    CFC.sqrt (M (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2 j)
  exact (CFC.measurable_sqrt.comp
    (measurable_pi_apply (finProdFinEquiv.symm i).1)).eval_matrix

lemma measurable_cavityCompressionFactorBlocks {m d n : ℕ}
    (e : Fin (m*n) ≃ Fin (d+n)) (lam : Fin m → ℝ) (lam₀ : Fin d → ℝ)
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) :
    Measurable (cavityCompressionFactorBlocks e lam lam₀ B₀) := by
  have hB := measurable_cavityConcreteComplement e B₀
  have hT := measurable_cavitySpectralStack m n
  unfold cavityCompressionFactorBlocks cavitySmallFactorBlocks
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  all_goals
    apply Measurable.of_eval_matrix
    intro i j
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply]
    fun_prop

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGroupedCoordinates
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selected columns in spectral groups and their exact spin coordinates.
These are the vectors to which the fresh-frame Gaussian limit applies. -/

noncomputable section
open MeasureTheory
open scoped Matrix BigOperators

namespace InvariantIsing

lemma cavityGroupedSelectedFrame_rotation {N m q d : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (f : Fin d → Fin m × Fin q)
    (A : (a : Fin m) → Matrix (Fin (k a)) (Fin q) ℝ)
    (W : (a : Fin m) → Orthogonal (k a)) :
    (cavityGroupRotation k e W : Matrix (Fin N) (Fin N) ℝ)*
      cavityGroupedSelectedFrame k e f A =
    cavityGroupedSelectedFrame k e f (cavityGroupHaarFrames A W) := by
  ext i j
  change ((cavityGroupRotation k e W : Matrix (Fin N) (Fin N) ℝ)*
    (cavityGroupFrame k e (f j).1*A (f j).1)) i (f j).2 = _
  rw [← Matrix.mul_assoc, cavityGroupRotation_frame, Matrix.mul_assoc]
  rfl

lemma cavityGroupFrame_transpose_mulVec {N m : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (a : Fin m)
    (x : Fin N → ℝ) (j : Fin (k a)) :
    ((cavityGroupFrame k e a).transpose *ᵥ x) j = x (e ⟨a,j⟩) := by
  simp [Matrix.mulVec, dotProduct, cavityGroupFrame]

lemma cavityGroupedSelectedFrame_transpose_mulVec {N m q d : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (f : Fin d → Fin m × Fin q)
    (A : (a : Fin m) → Matrix (Fin (k a)) (Fin q) ℝ) (x : Fin N → ℝ)
    (j : Fin d) :
    ((cavityGroupedSelectedFrame k e f A).transpose *ᵥ x) j =
      ∑ l, x (e ⟨(f j).1,l⟩)*A (f j).1 l (f j).2 := by
  change (((cavityGroupFrame k e (f j).1*A (f j).1).transpose) *ᵥ x) (f j).2 = _
  rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec]
  change (∑ l, A (f j).1 l (f j).2 *
    ((cavityGroupFrame k e (f j).1).transpose *ᵥ x) l) = _
  simp only [cavityGroupFrame_transpose_mulVec]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

lemma cavityGroupedSelectedFrame_coordinates {N m q d : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (f : Fin d → Fin m × Fin q)
    (A : (a : Fin m) → Matrix (Fin (k a)) (Fin q) ℝ)
    (V : Orthogonal N) (σ : Spin N) :
    cavityFrameCoordinates ((V : Matrix (Fin N) (Fin N) ℝ)*
      cavityGroupedSelectedFrame k e f A) σ =
    cavitySelectedSiteProjection f (cavityGroupSpinCoordinates k e V) A σ := by
  ext j
  change (((V : Matrix (Fin N) (Fin N) ℝ)*
    cavityGroupedSelectedFrame k e f A).transpose *ᵥ (fun i => spinValue (σ i))) j = _
  rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec,
    cavityGroupedSelectedFrame_transpose_mulVec]
  rfl

lemma cavityGroupedSelectedFrame_rotated_coordinates {N m q d : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (f : Fin d → Fin m × Fin q)
    (A : (a : Fin m) → Matrix (Fin (k a)) (Fin q) ℝ)
    (V : Orthogonal N) (W : (a : Fin m) → Orthogonal (k a)) (σ : Spin N) :
    cavityFrameCoordinates ((V : Matrix (Fin N) (Fin N) ℝ)*
      ((cavityGroupRotation k e W : Matrix (Fin N) (Fin N) ℝ)*
        cavityGroupedSelectedFrame k e f A)) σ =
    cavitySelectedSiteProjection f (cavityGroupSpinCoordinates k e V)
      (cavityGroupHaarFrames A W) σ := by
  rw [cavityGroupedSelectedFrame_rotation, cavityGroupedSelectedFrame_coordinates]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCanonicalGroupAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual canonical cavity frame admits the fresh-group Gibbs
representation. No new independent-frame assumption is required. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

lemma cavityCanonicalGroupFrame_gram {N m d : ℕ} (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N) (g : Fin d → Fin m)
    (hk : ∀ a, d ≤ k a) (a : Fin m) :
    (cavityCanonicalGroupFrame k e g hk a).transpose*cavityCanonicalGroupFrame k e g hk a=1 :=
  (Classical.choose_spec (cavity_canonical_group_frames k e g hk)).1 a

lemma cavityCanonicalGroupFrame_special {N m d : ℕ} (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N) (g : Fin d → Fin m)
    (hk : ∀ a, d ≤ k a) :
    cavityGroupedSelectedFrame (cavityBaseGroupDimension k g) (cavityBaseGroupEquiv k e g)
      (fun j => (g j,j)) (cavityCanonicalGroupFrame k e g hk)=cavityCanonicalSpecial e :=
  (Classical.choose_spec (cavity_canonical_group_frames k e g hk)).2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityUnflooredLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing the positive floor after the bounded finite-replica passage.
Only the second moment of the negative logarithm is used. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

lemma cavity_log_integrable_of_negative_sq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → ℝ) (hZ : Measurable Z)
    {M : ℝ} (hZ0 : ∀ ω, 0 < Z ω) (hZM : ∀ ω, Z ω ≤ M)
    (hi : Integrable (fun ω => (max (-Real.log (Z ω)) 0)^2) P) :
    Integrable (fun ω => Real.log (Z ω)) P := by
  apply ((integrable_const (1 + |Real.log M|)).add hi).mono' hZ.log.aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    change |Real.log (Z ω)| ≤ 1 + |Real.log M| + (max (-Real.log (Z ω)) 0)^2
    have hy := le_max_left (-Real.log (Z ω)) 0
    have hs := sq_nonneg (max (-Real.log (Z ω)) 0 - 1)
    have hu := Real.log_le_log (hZ0 ω) (hZM ω)
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (max (-Real.log (Z ω)) 0), abs_nonneg (Real.log M),
      le_abs_self (Real.log M)]

lemma cavity_floored_log_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → ℝ) (hZ : Measurable Z)
    {M δ : ℝ} (hZ0 : ∀ ω, 0 < Z ω) (hZM : ∀ ω, Z ω ≤ M) (hδ : 0 < δ) :
    Integrable (fun ω => Real.log (Z ω + δ)) P := by
  apply integrable_of_measurable_abs_le ((hZ.add_const δ).log)
    (c := |Real.log δ| + |Real.log (M + δ)|)
  intro ω
  have hl := Real.log_le_log hδ (show δ ≤ Z ω + δ by linarith [hZ0 ω])
  have hu := Real.log_le_log (show 0 < Z ω + δ by linarith [hZ0 ω])
    (show Z ω + δ ≤ M + δ by linarith [hZM ω])
  apply abs_le.mpr
  constructor <;> linarith [neg_abs_le (Real.log δ), le_abs_self (Real.log (M + δ)),
    abs_nonneg (Real.log δ), abs_nonneg (Real.log (M + δ))]

lemma cavity_log_floor_mean_difference {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → ℝ) (hZ : Measurable Z)
    {M δ : ℝ} (hZ0 : ∀ ω, 0 < Z ω) (hZM : ∀ ω, Z ω ≤ M) (hδ : 0 < δ)
    (hi : Integrable (fun ω => (max (-Real.log (Z ω)) 0)^2) P) :
    |(∫ ω, Real.log (Z ω + δ) ∂P) - ∫ ω, Real.log (Z ω) ∂P| =
      ∫ ω, Real.log (Z ω + δ) - Real.log (Z ω) ∂P := by
  rw [← integral_sub (cavity_floored_log_integrable P Z hZ hZ0 hZM hδ)
    (cavity_log_integrable_of_negative_sq P Z hZ hZ0 hZM hi)]
  exact abs_of_nonneg (integral_nonneg (fun ω => sub_nonneg.mpr
    (Real.log_le_log (hZ0 ω) (by linarith))))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCappedLogLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic finite-replica passage with its floor removed.
Fourth moments of the original marks control the negative logarithm. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_capped_negative_log_mean_bound {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H R : Ω × X → ℝ) (hH : Measurable H)
    (hi : ∀ ω, Integrable (fun x => R (ω, x)^4) (ν ω))
    (hmi : Integrable (fun ω => ∫ x, R (ω, x)^4 ∂ν ω) P)
    {D M T : ℝ} (hD : 0 ≤ D) (hT : 0 ≤ T)
    (hg : ∀ ω x, |H (ω, x)| ≤ D * (1 + R (ω, x)^2))
    (hM : (∫ ω, ∫ x, R (ω, x)^4 ∂ν ω ∂P) ≤ M) :
    Integrable (fun ω => (max (-Real.log
      (∫ x, Real.exp (min (H (ω, x)) T) ∂ν ω)) 0)^2) P ∧
    (∫ ω, (max (-Real.log (∫ x, Real.exp (min (H (ω, x)) T) ∂ν ω)) 0)^2 ∂P) ≤
      2 * D^2 * (1 + M) := by
  have hb ω := cavity_capped_log_negative_sq_of_growth (ν ω) (fun x => H (ω, x))
    (fun x => R (ω, x)) (hH.comp measurable_prodMk_left) (hi ω) hD hT (hg ω)
  have hZ : Measurable (fun ω => ∫ x, Real.exp (min (H (ω, x)) T) ∂ν ω) :=
    measurable_cavityWeightNormalizer ν hν _ ((hH.min measurable_const).exp)
  have he := ((integrable_const 1).add hmi).const_mul (2 * D^2)
  have hN : Integrable (fun ω => (max (-Real.log
      (∫ x, Real.exp (min (H (ω, x)) T) ∂ν ω)) 0)^2) P := by
    apply he.mono' ((hZ.log.neg.max measurable_const).pow_const 2).aestronglyMeasurable
    exact ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hb ω
  refine ⟨hN, ?_⟩
  have hh := integral_mono hN he hb
  simp only [Pi.add_apply, integral_const_mul, integral_add (integrable_const 1) hmi,
    integral_const, probReal_univ, one_smul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl (1 : ℝ)) hM) (by positivity))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityMovingLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Floor removal when both random normalizers vary. This is the form
needed for the finite system and its refining cascade approximation. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

theorem cavity_moving_unfloored_log
    {Ω Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (Ξ n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : (n : ℕ) → Measure (Ξ n)) [∀ n, IsProbabilityMeasure (Q n)]
    (Z : (n : ℕ) → Ω n → ℝ) (W : (n : ℕ) → Ξ n → ℝ)
    (hZ : ∀ n, Measurable (Z n)) (hW : ∀ n, Measurable (W n))
    {M K : ℝ} (hM : 1 ≤ M) (hK0 : 0 ≤ K)
    (hZ0 : ∀ n ω, 0 < Z n ω) (hW0 : ∀ n ω, 0 < W n ω)
    (hZM : ∀ n ω, Z n ω ≤ M) (hWM : ∀ n ω, W n ω ≤ M)
    (hiZ : ∀ n, Integrable (fun ω => (max (-Real.log (Z n ω)) 0)^2) (P n))
    (hiW : ∀ n, Integrable (fun ω => (max (-Real.log (W n ω)) 0)^2) (Q n))
    (hKZ : ∀ n, (∫ ω, (max (-Real.log (Z n ω)) 0)^2 ∂P n) ≤ K)
    (hKW : ∀ n, (∫ ω, (max (-Real.log (W n ω)) 0)^2 ∂Q n) ≤ K)
    (hfloors : ∀ δ > 0, Tendsto (fun n =>
      (∫ ω, Real.log (Z n ω + δ) ∂P n) - ∫ ω, Real.log (W n ω + δ) ∂Q n)
        atTop (𝓝 0)) :
    Tendsto (fun n => (∫ ω, Real.log (Z n ω) ∂P n) -
      ∫ ω, Real.log (W n ω) ∂Q n) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ₁, hδ₁, he₁⟩ := cavity_log_floor_uniform P Z hZ hZ0 hZM hM hK0 hiZ hKZ
    (ε / 3) (by positivity)
  obtain ⟨δ₂, hδ₂, he₂⟩ := cavity_log_floor_uniform Q W hW hW0 hWM hM hK0 hiW hKW
    (ε / 3) (by positivity)
  let δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have hclose := (hfloors δ hδ).eventually
    (Metric.ball_mem_nhds 0 (show 0 < ε / 3 by positivity))
  filter_upwards [hclose] with n hn
  rw [Real.dist_eq, sub_zero] at hn
  rw [Real.dist_eq, sub_zero]
  have h₁ := (he₁ δ ⟨hδ.le, min_le_left _ _⟩ n).2
  have h₂ := (he₂ δ ⟨hδ.le, min_le_right _ _⟩ n).2
  rw [← cavity_log_floor_mean_difference (P n) (Z n) (hZ n) (hZ0 n) (hZM n) hδ (hiZ n),
    abs_sub_comm] at h₁
  rw [← cavity_log_floor_mean_difference (Q n) (W n) (hW n) (hW0 n) (hWM n) hδ (hiW n)] at h₂
  have htri := abs_sub_le (∫ ω, Real.log (Z n ω) ∂P n)
    (∫ ω, Real.log (Z n ω + δ) ∂P n) (∫ ω, Real.log (W n ω) ∂Q n)
  have htri' := abs_sub_le (∫ ω, Real.log (Z n ω + δ) ∂P n)
    (∫ ω, Real.log (W n ω + δ) ∂Q n) (∫ ω, Real.log (W n ω) ∂Q n)
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLogL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing a small change in a capped normalizer.  A uniform second
moment of its negative logarithm makes convergence in mean sufficient. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_log_floor_lipschitz {z w δ : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hδ : 0 < δ) :
    |Real.log (z + δ) - Real.log (w + δ)| ≤ |z - w| / δ := by
  have hone {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) :
      Real.log (a + δ) - Real.log (b + δ) ≤ (a - b) / δ := by
    have hbδ : 0 < b + δ := by positivity
    have haδ : 0 < a + δ := by linarith
    calc
      _ ≤ (a - b) / (b + δ) := by
        rw [← Real.log_div haδ.ne' hbδ.ne']
        apply (Real.log_le_sub_one_of_pos (div_pos haδ hbδ)).trans_eq
        field_simp
        ring
      _ ≤ _ := div_le_div_of_nonneg_left (sub_nonneg.mpr hab) hδ (by linarith)
  rcases le_total w z with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (by positivity)
        (by linarith : w + δ ≤ z + δ))), abs_of_nonneg (sub_nonneg.mpr h)]
    exact hone hw h
  · rw [abs_sub_comm (Real.log _), abs_sub_comm z,
        abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (by positivity)
          (by linarith : z + δ ≤ w + δ))), abs_of_nonneg (sub_nonneg.mpr h)]
    exact hone hz h

theorem cavity_log_of_mean_distance
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Z W : (n : ℕ) → Ω n → ℝ)
    (hZ : ∀ n, Measurable (Z n)) (hW : ∀ n, Measurable (W n))
    {M K : ℝ} (hM : 1 ≤ M) (hK : 0 ≤ K)
    (hZ0 : ∀ n ω, 0 < Z n ω) (hW0 : ∀ n ω, 0 < W n ω)
    (hZM : ∀ n ω, Z n ω ≤ M) (hWM : ∀ n ω, W n ω ≤ M)
    (hiZ : ∀ n, Integrable (fun ω => (max (-Real.log (Z n ω)) 0)^2) (P n))
    (hiW : ∀ n, Integrable (fun ω => (max (-Real.log (W n ω)) 0)^2) (P n))
    (hKZ : ∀ n, (∫ ω, (max (-Real.log (Z n ω)) 0)^2 ∂P n) ≤ K)
    (hKW : ∀ n, (∫ ω, (max (-Real.log (W n ω)) 0)^2 ∂P n) ≤ K)
    (hdist : Tendsto (fun n => ∫ ω, |Z n ω - W n ω| ∂P n) atTop (𝓝 0)) :
    Tendsto (fun n => (∫ ω, Real.log (Z n ω) ∂P n) -
      ∫ ω, Real.log (W n ω) ∂P n) atTop (𝓝 0) := by
  apply cavity_moving_unfloored_log P P Z W hZ hW hM hK
    hZ0 hW0 hZM hWM hiZ hiW hKZ hKW
  intro δ hδ
  have hi n : Integrable (fun ω => |Z n ω - W n ω|) (P n) := by
    apply integrable_of_measurable_abs_le ((hZ n).sub (hW n)).abs (c := 2*M)
    intro ω
    rw [abs_abs]
    exact (abs_sub (Z n ω) (W n ω)).trans (by
      rw [abs_of_pos (hZ0 n ω), abs_of_pos (hW0 n ω)]
      linarith [hZM n ω, hWM n ω])
  apply squeeze_zero_norm (fun n => ?_) (by simpa using hdist.div_const δ)
  rw [Real.norm_eq_abs, ← integral_sub
    (cavity_floored_log_integrable (P n) (Z n) (hZ n) (hZ0 n) (hZM n) hδ)
    (cavity_floored_log_integrable (P n) (W n) (hW n) (hW0 n) (hWM n) hδ)]
  calc
    _ ≤ ∫ ω, |Real.log (Z n ω + δ) - Real.log (W n ω + δ)| ∂P n :=
      abs_integral_le_integral_abs
    _ ≤ ∫ ω, |Z n ω - W n ω| / δ ∂P n :=
      integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) ((hi n).div_const δ)
        (ae_of_all _ fun ω => cavity_log_floor_lipschitz (hZ0 n ω).le (hW0 n ω).le hδ)
    _ = _ := by rw [integral_div]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityVanishingPenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quadratic error in the geometric cavity increment disappears
after taking the expected logarithm of a capped partition function. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_abs_min_cap {h T : ℝ} (hT : 0 ≤ T) : |min h T| ≤ |h| := by
  by_cases hh : h ≤ T
  · rw [min_eq_left hh]
  · rw [min_eq_right (le_of_not_ge hh), abs_of_nonneg hT,
      abs_of_nonneg (hT.trans (le_of_not_ge hh))]
    exact le_of_not_ge hh

lemma cavity_penalized_exp_bound (h r T δ : ℝ) (hδ : 0 ≤ δ) :
    |Real.exp (min h T) - Real.exp (min h T - δ * (1 + r^2))| ≤
      2 * Real.exp T * δ * (1 + r^4) := by
  have hw : 0 ≤ δ * (1 + r^2) := by positivity
  have hh := cavity_exp_sub_le (min_le_right h T)
    (show min h T - δ * (1 + r^2) ≤ T by linarith [min_le_right h T])
  have he : |min h T - (min h T - δ * (1 + r^2))| = δ * (1 + r^2) := by
    rw [show min h T - (min h T - δ * (1 + r^2)) = δ * (1 + r^2) by ring,
      abs_of_nonneg hw]
  rw [he] at hh
  apply hh.trans
  have hrad : 1 + r^2 ≤ 2 * (1 + r^4) := by nlinarith [sq_nonneg (r^2 - 1)]
  nlinarith [mul_le_mul_of_nonneg_left hrad (mul_nonneg (Real.exp_pos T).le hδ)]

theorem cavity_vanishing_quadratic_penalty
    {Ω X : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (X n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (ν : (n : ℕ) → Ω n → Measure (X n)) (hν : ∀ n, Measurable (ν n))
    [∀ n ω, IsProbabilityMeasure (ν n ω)]
    (H R : (n : ℕ) → Ω n × X n → ℝ)
    (hH : ∀ n, Measurable (H n)) (hR : ∀ n, Measurable (R n))
    (hi : ∀ n ω, Integrable (fun x => R n (ω,x)^4) (ν n ω))
    (hmi : ∀ n, Integrable (fun ω => ∫ x, R n (ω,x)^4 ∂ν n ω) (P n))
    {D M T : ℝ} (hD : 0 ≤ D) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hg : ∀ n ω x, |H n (ω,x)| ≤ D * (1 + R n (ω,x)^2))
    (hMR : ∀ n, (∫ ω, ∫ x, R n (ω,x)^4 ∂ν n ω ∂P n) ≤ M)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) (hδ1 : ∀ n, δ n ≤ 1)
    (hδlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n =>
      (∫ ω, Real.log (∫ x, Real.exp (min (H n (ω,x)) T) ∂ν n ω) ∂P n) -
      ∫ ω, Real.log (∫ x, Real.exp (min (H n (ω,x)) T -
        δ n * (1 + R n (ω,x)^2)) ∂ν n ω) ∂P n) atTop (𝓝 0) := by
  let G n p := min (H n p) T - δ n * (1 + R n p ^ 2)
  have hG n : Measurable (G n) :=
    ((hH n).min measurable_const).sub
      (measurable_const.mul (measurable_const.add ((hR n).pow_const 2)))
  have hGcap n ω x : min (G n (ω,x)) T = G n (ω,x) := by
    apply min_eq_left
    dsimp only [G]
    have := min_le_right (H n (ω,x)) T
    have : 0 ≤ δ n * (1 + R n (ω,x)^2) := mul_nonneg (hδ n) (by positivity)
    linarith
  have hGgrowth n ω x : |G n (ω,x)| ≤ (D+1) * (1 + R n (ω,x)^2) := by
    dsimp only [G]
    calc
      _ ≤ |min (H n (ω,x)) T| + |δ n * (1 + R n (ω,x)^2)| := abs_sub _ _
      _ ≤ D * (1 + R n (ω,x)^2) + (1 + R n (ω,x)^2) := by
        apply add_le_add ((cavity_abs_min_cap hT).trans (hg n ω x))
        rw [abs_of_nonneg (mul_nonneg (hδ n) (by positivity : 0 ≤ 1 + R n (ω,x)^2))]
        exact mul_le_of_le_one_left (by positivity) (hδ1 n)
      _ = _ := by ring
  have hHgrowth n ω x : |H n (ω,x)| ≤ (D+1) * (1 + R n (ω,x)^2) :=
    (hg n ω x).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  let Z n ω := ∫ x, Real.exp (min (H n (ω,x)) T) ∂ν n ω
  let W n ω := ∫ x, Real.exp (min (G n (ω,x)) T) ∂ν n ω
  have hZ n : Measurable (Z n) :=
    measurable_cavityWeightNormalizer (ν n) (hν n) _ (((hH n).min measurable_const).exp)
  have hW n : Measurable (W n) :=
    measurable_cavityWeightNormalizer (ν n) (hν n) _ (((hG n).min measurable_const).exp)
  have hZi n ω : Integrable (fun x => Real.exp (min (H n (ω,x)) T)) (ν n ω) :=
    integrable_of_measurable_abs_le ((((hH n).min measurable_const).exp).comp
      measurable_prodMk_left) (fun x => by
        rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (min_le_right _ _))
  have hWi n ω : Integrable (fun x => Real.exp (min (G n (ω,x)) T)) (ν n ω) :=
    integrable_of_measurable_abs_le ((((hG n).min measurable_const).exp).comp
      measurable_prodMk_left) (fun x => by
        rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (min_le_right _ _))
  have hZ0 n ω : 0 < Z n ω := integral_exp_pos (hZi n ω)
  have hW0 n ω : 0 < W n ω := integral_exp_pos (hWi n ω)
  have hZb n ω : Z n ω ≤ Real.exp T := by
    exact (integral_mono (hZi n ω) (integrable_const _) (fun x =>
      Real.exp_le_exp.mpr (min_le_right _ _))).trans_eq (by simp)
  have hWb n ω : W n ω ≤ Real.exp T := by
    exact (integral_mono (hWi n ω) (integrable_const _) (fun x =>
      Real.exp_le_exp.mpr (min_le_right _ _))).trans_eq (by simp)
  have hZd n := cavity_capped_negative_log_mean_bound (P n) (ν n) (hν n)
    (H n) (R n) (hH n) (hi n) (hmi n) (by positivity : 0 ≤ D+1) hT
    (hHgrowth n) (hMR n)
  have hWd n := cavity_capped_negative_log_mean_bound (P n) (ν n) (hν n)
    (G n) (R n) (hG n) (hi n) (hmi n) (by positivity : 0 ≤ D+1) hT
    (hGgrowth n) (hMR n)
  have hdist : Tendsto (fun n => ∫ ω, |Z n ω - W n ω| ∂P n) atTop (𝓝 0) := by
    have hpoint n ω : |Z n ω - W n ω| ≤
        2 * Real.exp T * δ n * (1 + ∫ x, R n (ω,x)^4 ∂ν n ω) := by
      dsimp only [Z, W]
      rw [← integral_sub (hZi n ω) (hWi n ω)]
      calc
        _ ≤ ∫ x, |Real.exp (min (H n (ω,x)) T) -
            Real.exp (min (G n (ω,x)) T)| ∂ν n ω := abs_integral_le_integral_abs
        _ ≤ ∫ x, 2 * Real.exp T * δ n * (1 + R n (ω,x)^4) ∂ν n ω := by
          apply integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
            (((integrable_const 1).add (hi n ω)).const_mul _)
          exact ae_of_all _ fun x => by
            change |Real.exp (min (H n (ω,x)) T) - Real.exp (min (G n (ω,x)) T)| ≤
              2 * Real.exp T * δ n * (1 + R n (ω,x)^4)
            rw [hGcap]
            exact cavity_penalized_exp_bound _ _ _ _ (hδ n)
        _ = _ := by
          rw [integral_const_mul, integral_add (integrable_const 1) (hi n ω)]
          simp only [integral_const, probReal_univ, one_smul]
    have hb n : (∫ ω, |Z n ω - W n ω| ∂P n) ≤ 2 * Real.exp T * (1+M) * δ n := by
      calc
        _ ≤ ∫ ω, 2 * Real.exp T * δ n * (1 + ∫ x, R n (ω,x)^4 ∂ν n ω) ∂P n :=
          integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
            (((integrable_const 1).add (hmi n)).const_mul _) (ae_of_all _ (hpoint n))
        _ = 2 * Real.exp T * δ n * (1 + ∫ ω, ∫ x, R n (ω,x)^4 ∂ν n ω ∂P n) := by
          rw [integral_const_mul, integral_add (integrable_const 1) (hmi n)]
          simp only [integral_const, probReal_univ, one_smul]
        _ ≤ 2 * Real.exp T * (1+M) * δ n := by
          calc
            _ ≤ 2 * Real.exp T * δ n * (1+M) :=
              mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) (hMR n))
                (mul_nonneg (by positivity) (hδ n))
            _ = _ := by ring
    exact squeeze_zero (fun n => integral_nonneg fun _ => abs_nonneg _) hb
      (by simpa using hδlim.const_mul (2 * Real.exp T * (1+M)))
  have hout := cavity_log_of_mean_distance P Z W hZ hW (Real.one_le_exp hT)
    (by positivity : 0 ≤ 2 * (D+1)^2 * (1+M)) hZ0 hW0 hZb hWb
    (fun n => (hZd n).1) (fun n => (hWd n).1)
    (fun n => (hZd n).2) (fun n => (hWd n).2) hdist
  simpa only [Z, W, hGcap, G] using hout

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFrameLogBound
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-volume bounds for the capped logarithm on the canonical
orthonormal frame.  These bounds are only used for Haar integrability. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

lemma cavityCanonicalSpecial_gram {N d : ℕ} {ι : Type*}
    (e : (ι ⊕ Fin d) ≃ Fin N) :
    (cavityCanonicalSpecial e).transpose * cavityCanonicalSpecial e = 1 := by
  ext i j
  simp [Matrix.mul_apply, Matrix.transpose_apply, cavityCanonicalSpecial, Matrix.one_apply, eq_comm]

lemma cavity_orthogonal_frame_gram {N d : ℕ} (V : Orthogonal N)
    (S : Matrix (Fin N) (Fin d) ℝ) (hS : S.transpose*S=1) :
    ((V : Matrix (Fin N) (Fin N) ℝ)*S).transpose *
      ((V : Matrix (Fin N) (Fin N) ℝ)*S)=1 := by
  have hV := (Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mp V.property
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc
    (V : Matrix (Fin N) (Fin N) ℝ).transpose, hV, Matrix.one_mul, hS]

lemma cavity_frame_coordinates_norm_le {N d : ℕ} (S : Matrix (Fin N) (Fin d) ℝ)
    (hS : S.transpose*S=1) (σ : Spin N) : ‖cavityFrameCoordinates S σ‖^2 ≤ N := by
  have h := cavity_frame_transpose_contraction S hS (spinVector σ)
  rw [spinVector_norm_sq] at h
  exact h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySelectedHaarMoment
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform ordinary fourth moments for the actual selected Haar axes.
These are the physical-side moments used to remove the normalizer floor. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators RealInnerProductSpace

namespace InvariantIsing

lemma cavity_sphere_fourth_moment_of_norm {n : ℕ} (hn : 0 < n)
    (μ : Measure (Orthogonal n)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (v u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1)
    {C : ℝ} (hv : ‖v‖^2 ≤ C * n) :
    (∫ U, |⟪v, matrixRotation U u⟫|^4 ∂μ) ≤ cavityGaussianAbsMoment 4 * C^2 := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hr : ‖v‖^2 / (n : ℝ) ≤ C := (div_le_iff₀ hn').mpr hv
  have h := cavity_sphere_even_moment_bound hn μ v u hu 2
  norm_num only [Nat.reduceMul] at h
  calc
    _ ≤ cavityGaussianAbsMoment 4 * ‖v‖^4 / (n : ℝ)^2 := h
    _ = cavityGaussianAbsMoment 4 * (‖v‖^2 / (n : ℝ))^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (div_nonneg (sq_nonneg _) hn'.le) hr 2)
      (cavityGaussianAbsMoment_nonneg 4)

lemma cavity_selected_site_inner {m q d : ℕ} {N : Fin m → ℕ}
    (e : Fin d → Fin m × Fin q) (v : (a : Fin m) → Fin (N a) → ℝ)
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (U : (a : Fin m) → Orthogonal (N a)) (j : Fin d) :
    cavitySelectedSiteProjection e (fun a (_ : Unit) => v a) (cavityGroupHaarFrames A₀ U) () j =
      ⟪(WithLp.toLp 2 (v (e j).1) : EuclideanSpace ℝ (Fin (N (e j).1))),
        matrixRotation (U (e j).1) (WithLp.toLp 2 (fun l => A₀ (e j).1 l (e j).2))⟫ := by
  simp only [cavitySelectedSiteProjection, PiLp.toLp_apply, cavityGroupHaarFrames,
    Matrix.mul_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
    matrixRotation_apply]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem cavity_selected_haar_fourth_moment {m q d : ℕ} {N : Fin m → ℕ}
    (hN : ∀ a, 0 < N a)
    (μ : (a : Fin m) → Measure (Orthogonal (N a)))
    [∀ a, IsProbabilityMeasure (μ a)] [∀ a, (μ a).IsMulRightInvariant]
    (e : Fin d → Fin m × Fin q) (v : (a : Fin m) → Fin (N a) → ℝ)
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (hA₀ : ∀ a, (A₀ a).transpose * A₀ a = 1) {C : ℝ}
    (hv : ∀ a, ‖(WithLp.toLp 2 (v a) : EuclideanSpace ℝ (Fin (N a)))‖^2 ≤ C * N a) :
    (∫ U, ‖cavitySelectedSiteProjection e (fun a (_ : Unit) => v a)
      (cavityGroupHaarFrames A₀ U) ()‖^4 ∂Measure.pi μ) ≤
      (d : ℝ)^2 * cavityGaussianAbsMoment 4 * C^2 := by
  let Y := fun U : (a : Fin m) → Orthogonal (N a) =>
    cavitySelectedSiteProjection e (fun a (_ : Unit) => v a) (cavityGroupHaarFrames A₀ U) ()
  have hu (j : Fin d) : ‖(WithLp.toLp 2 (fun l => A₀ (e j).1 l (e j).2) :
      EuclideanSpace ℝ (Fin (N (e j).1)))‖ = 1 :=
    (cavity_orthonormal_of_gram (A₀ (e j).1) (hA₀ (e j).1)).norm_eq_one (e j).2
  have hcoord (U) (j : Fin d) : |Y U j| ≤ ‖(WithLp.toLp 2 (v (e j).1) :
      EuclideanSpace ℝ (Fin (N (e j).1)))‖ := by
    dsimp only [Y]
    rw [cavity_selected_site_inner]
    simpa only [(matrixRotation _).norm_map, hu j, mul_one] using
      abs_real_inner_le_norm (WithLp.toLp 2 (v (e j).1))
        (matrixRotation (U (e j).1) (WithLp.toLp 2 (fun l => A₀ (e j).1 l (e j).2)))
  have hm (j : Fin d) : Measurable (fun U : Orthogonal (N (e j).1) =>
      |⟪(WithLp.toLp 2 (v (e j).1) : EuclideanSpace ℝ (Fin (N (e j).1))),
        matrixRotation U (WithLp.toLp 2 (fun l => A₀ (e j).1 l (e j).2))⟫|^4) := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
      matrixRotation_apply]
    apply Measurable.pow_const
    apply Measurable.abs
    apply Finset.measurable_sum
    intro i _
    apply Measurable.mul_const
    apply Finset.measurable_sum
    intro l _
    exact (((measurable_pi_apply l).comp ((measurable_pi_apply i).comp
      measurable_subtype_coe)).mul_const _)
  have hcm (j : Fin d) : Measurable (fun U => |Y U j|^4) := by
    simpa only [Y, cavity_selected_site_inner, Function.comp_def] using
      (hm j).comp (measurable_pi_apply (e j).1)
  have hci (j : Fin d) : Integrable (fun U => |Y U j|^4) (Measure.pi μ) := by
    apply Integrable.of_bound (hcm j).aestronglyMeasurable
      (‖(WithLp.toLp 2 (v (e j).1) : EuclideanSpace ℝ (Fin (N (e j).1)))‖^4)
    apply ae_of_all
    intro U
    change ‖|Y U j|^4‖ ≤ _
    simpa only [Real.norm_eq_abs, abs_pow, abs_abs] using
      pow_le_pow_left₀ (abs_nonneg _) (hcoord U j) 4
  have hb (j : Fin d) : (∫ U, |Y U j|^4 ∂Measure.pi μ) ≤ cavityGaussianAbsMoment 4 * C^2 := by
    have h := cavity_sphere_fourth_moment_of_norm (hN (e j).1) (μ (e j).1)
      (WithLp.toLp 2 (v (e j).1)) (WithLp.toLp 2 (fun l => A₀ (e j).1 l (e j).2)) (hu j) (hv (e j).1)
    have he := (measurePreserving_eval μ (e j).1).hasLaw.integral_comp (hm j).aestronglyMeasurable
    simpa only [Y, cavity_selected_site_inner, Function.comp_def, Function.eval] using he.le.trans h
  have hpoint (U) : ‖Y U‖^4 ≤ (d : ℝ) * ∑ j, |Y U j|^4 := by
    have h := pow_sum_le_card_mul_sum_pow (s := Finset.univ)
      (f := fun j : Fin d => (Y U j)^2) (fun _ _ => sq_nonneg _) 1
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, EuclideanSpace.real_norm_sq_eq]
    simpa only [Nat.reduceAdd, pow_one, Finset.card_univ, Fintype.card_fin, pow_mul,
      sq_abs] using h
  calc
    _ ≤ ∫ U, (d : ℝ) * ∑ j, |Y U j|^4 ∂Measure.pi μ :=
      integral_mono_of_nonneg (ae_of_all _ (fun U => pow_nonneg (norm_nonneg _) _))
        ((integrable_finsetSum _ fun j _ => hci j).const_mul d) (ae_of_all _ hpoint)
    _ = (d : ℝ) * ∑ j, ∫ U, |Y U j|^4 ∂Measure.pi μ := by
      rw [integral_const_mul, integral_finsetSum _ fun j _ => hci j]
    _ ≤ (d : ℝ) * ∑ _j : Fin d, cavityGaussianAbsMoment 4 * C^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hb j) (Nat.cast_nonneg d)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] <;> ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarPriorMoment
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary fourth moment bound after averaging over the original
Gibbs prior and the independent fresh Haar frames. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_selected_site_fourth_bound {m q d : ℕ} {N : Fin m → ℕ}
    (e : Fin d → Fin m × Fin q) (v : (a : Fin m) → Fin (N a) → ℝ)
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (hA₀ : ∀ a, (A₀ a).transpose * A₀ a = 1) {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ a, ‖(WithLp.toLp 2 (v a) : EuclideanSpace ℝ (Fin (N a)))‖^2 ≤ C * N a)
    (U : (a : Fin m) → Orthogonal (N a)) :
    ‖cavitySelectedSiteProjection e (fun a (_ : Unit) => v a)
      (cavityGroupHaarFrames A₀ U) ()‖^4 ≤ ((d : ℝ) * (C * ∑ a, (N a : ℝ)))^2 := by
  let Y := cavitySelectedSiteProjection e (fun a (_ : Unit) => v a) (cavityGroupHaarFrames A₀ U) ()
  have hb (j : Fin d) : (Y j)^2 ≤ C * ∑ a, (N a : ℝ) := by
    have hu := (cavity_orthonormal_of_gram (A₀ (e j).1) (hA₀ (e j).1)).norm_eq_one (e j).2
    have hi := abs_real_inner_le_norm (WithLp.toLp 2 (v (e j).1))
      (matrixRotation (U (e j).1) (WithLp.toLp 2 (fun l => A₀ (e j).1 l (e j).2)))
    rw [(matrixRotation _).norm_map, hu, mul_one] at hi
    have hsq : (Y j)^2 ≤ ‖(WithLp.toLp 2 (v (e j).1) :
        EuclideanSpace ℝ (Fin (N (e j).1)))‖^2 := by
      simpa only [Y, cavity_selected_site_inner, sq_abs] using
        pow_le_pow_left₀ (abs_nonneg _) hi 2
    exact (hsq.trans (hv _)).trans (mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun a _ => Nat.cast_nonneg (N a)) (Finset.mem_univ (e j).1)) hC)
  have hs : ‖Y‖^2 ≤ (d : ℝ) * (C * ∑ a, (N a : ℝ)) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun j _ => hb j)
  simpa only [← pow_mul, Nat.reduceMul, Y] using pow_le_pow_left₀ (sq_nonneg ‖Y‖) hs 2

lemma measurable_cavitySelectedSiteProjection {m q d : ℕ} {N : Fin m → ℕ}
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (e : Fin d → Fin m × Fin q)
    (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (hv : ∀ x, Measurable (fun ω a => v ω a x))
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ) :
    Measurable (fun p : (Ω × ((a : Fin m) → Orthogonal (N a))) × X =>
      cavitySelectedSiteProjection e (v p.1.1) (cavityGroupHaarFrames A₀ p.1.2) p.2) := by
  apply measurable_from_prod_countable_left
  intro x
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  apply Measurable.of_eval
  intro j
  dsimp only [cavitySelectedSiteProjection]
  apply Finset.measurable_sum
  intro l _
  exact (((measurable_pi_apply l).comp ((measurable_pi_apply (e j).1).comp
    ((hv x).comp measurable_fst))).mul
      (((measurable_pi_apply (e j).2).comp ((measurable_pi_apply l).comp
        ((measurable_pi_apply (e j).1).comp
          ((measurable_cavityGroupHaarFrames A₀).comp measurable_snd))))))

theorem cavity_haar_prior_fourth_moment {m q d k : ℕ} {N : Fin m → ℕ}
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (hN : ∀ a, 0 < N a)
    (μ : (a : Fin m) → Measure (Orthogonal (N a)))
    [∀ a, IsProbabilityMeasure (μ a)] [∀ a, (μ a).IsMulRightInvariant]
    (e : Fin d → Fin m × Fin q)
    (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (hvM : ∀ x, Measurable (fun ω a => v ω a x))
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (hA₀ : ∀ a, (A₀ a).transpose * A₀ a = 1) {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ ω x a, ‖(WithLp.toLp 2 (v ω a x) : EuclideanSpace ℝ (Fin (N a)))‖^2 ≤ C * N a)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    let R := fun (p : Ω × ((a : Fin m) → Orthogonal (N a))) (x : X × Spin k) =>
      ‖cavitySelectedSiteProjection e (v p.1) (cavityGroupHaarFrames A₀ p.2) x.1‖^4
    (∀ p, Integrable (R p) ((ν p.1).prod π)) ∧
    Integrable (fun p => ∫ x, R p x ∂(ν p.1).prod π) (P.prod (Measure.pi μ)) ∧
    (∫ p, ∫ x, R p x ∂(ν p.1).prod π ∂P.prod (Measure.pi μ)) ≤
      (d : ℝ)^2 * cavityGaussianAbsMoment 4 * C^2 := by
  intro R
  let D := ((d : ℝ) * (C * ∑ a, (N a : ℝ)))^2
  have hbound p x : ‖R p x‖ ≤ D := by
    simp only [R, norm_pow, norm_norm]
    exact cavity_selected_site_fourth_bound e (fun a => v p.1 a x.1) A₀ hA₀ hC (hv p.1 x.1) p.2
  have hR : Measurable (Function.uncurry R) :=
    ((measurable_cavitySelectedSiteProjection e v hvM A₀).comp
      (measurable_fst.prodMk measurable_snd.fst)).norm.pow_const 4
  have hi p : Integrable (R p) ((ν p.1).prod π) :=
    Integrable.of_bound ((hR.comp measurable_prodMk_left).aestronglyMeasurable) D
      (ae_of_all _ (hbound p))
  let νK : Kernel Ω X := Kernel.mk ν hν
  let : IsMarkovKernel νK := ⟨fun ω => inferInstanceAs (IsProbabilityMeasure (ν ω))⟩
  let κ : Kernel (Ω × ((a : Fin m) → Orthogonal (N a))) (X × Spin k) :=
    (Kernel.comap νK Prod.fst measurable_fst).prod (Kernel.const _ π)
  have hm : Measurable (fun p => ∫ x, R p x ∂(ν p.1).prod π) := by
    simpa only [κ, Kernel.prod_apply, Kernel.comap_apply, Kernel.const_apply,
      νK, Kernel.coe_mk, Function.uncurry_apply_pair] using
      (hR.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable
  have hmi : Integrable (fun p => ∫ x, R p x ∂(ν p.1).prod π) (P.prod (Measure.pi μ)) :=
    Integrable.of_bound hm.aestronglyMeasurable D (ae_of_all _ fun p =>
      by simpa only [probReal_univ, mul_one] using
        norm_integral_le_of_norm_le_const (μ := (ν p.1).prod π) (ae_of_all _ (hbound p)))
  refine ⟨hi, hmi, ?_⟩
  rw [integral_prod _ hmi]
  have hn p : 0 ≤ ∫ x, R p x ∂(ν p.1).prod π :=
    integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _)
  have hpω (ω : Ω) : (∫ U, ∫ x, R (ω,U) x ∂(ν ω).prod π ∂Measure.pi μ) ≤
      (d : ℝ)^2 * cavityGaussianAbsMoment 4 * C^2 := by
    have hiω : Integrable (fun p : ((a : Fin m) → Orthogonal (N a)) × (X × Spin k) =>
        R (ω, p.1) p.2) ((Measure.pi μ).prod ((ν ω).prod π)) :=
      Integrable.of_bound ((hR.comp ((measurable_const.prodMk measurable_fst).prodMk
          measurable_snd)).aestronglyMeasurable) D
        (ae_of_all _ fun p => hbound (ω,p.1) p.2)
    rw [integral_integral_swap hiω]
    have hb x : (∫ U, R (ω,U) x ∂Measure.pi μ) ≤
        (d : ℝ)^2 * cavityGaussianAbsMoment 4 * C^2 :=
      cavity_selected_haar_fourth_moment hN μ e (fun a => v ω a x.1) A₀ hA₀ (hv ω x.1)
    have hi := integral_mono_of_nonneg (μ := (ν ω).prod π)
      (ae_of_all _ fun x => integral_nonneg (fun U => pow_nonneg (norm_nonneg _) 4))
      (integrable_const ((d : ℝ)^2 * cavityGaussianAbsMoment 4 * C^2)) (ae_of_all _ hb)
    simpa only [integral_const, probReal_univ, one_smul] using hi
  have ht := integral_mono_of_nonneg (μ := P)
    (ae_of_all _ fun ω => integral_nonneg (fun U => hn (ω,U)))
    (integrable_const ((d : ℝ)^2 * cavityGaussianAbsMoment 4 * C^2)) (ae_of_all _ hpω)
  simpa only [integral_const, probReal_univ, one_smul] using ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPhysicalGram
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fresh-frame covariance is the physical projected overlap divided
by the finite spectral-group mass. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma cavityPhysicalReplicaVectors_gram {N m r : ℕ} (hN : 0 < N)
    (U : Rotation N) (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ)
    (e : (a : Fin m) → Fin (d a) ≃ ↥(I a)) (σ : Fin r → Spin N)
    (a : Fin m) (i j : Fin r) :
    cavityGroupReplicaGram (cavityPhysicalReplicaVectors U I d e σ) a i j =
      projectedOverlap U (I a) (σ i) (σ j) / ((d a : ℝ) / N) := by
  have hs : (∑ k, U (spinVector (σ i)) (e a k) * U (spinVector (σ j)) (e a k)) =
      ∑ k ∈ I a, U (spinVector (σ i)) k * U (spinVector (σ j)) k := by
    exact ((e a).sum_comp (fun k : ↥(I a) =>
      U (spinVector (σ i)) k * U (spinVector (σ j)) k)).trans
        ((I a).sum_coe_sort (fun k : Fin N => U (spinVector (σ i)) k * U (spinVector (σ j)) k))
  simp only [cavityGroupReplicaGram, cavityPhysicalReplicaVectors, hs, projectedOverlap]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  by_cases hd : d a = 0
  · simp [hd]
  · have hd' : (d a : ℝ) ≠ 0 := by exact_mod_cast hd
    field_simp

lemma cavityPhysicalReplicaVectors_gram_bound {N m r : ℕ} (hN : 0 < N)
    (U : Rotation N) (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ)
    (e : (a : Fin m) → Fin (d a) ≃ ↥(I a)) (σ : Fin r → Spin N)
    (c : ℝ) (hc : 0 < c) (hd : ∀ a, c ≤ (d a : ℝ) / N) :
    ∀ a i j, |cavityGroupReplicaGram (cavityPhysicalReplicaVectors U I d e σ) a i j| ≤ 1 / c := by
  intro a i j
  rw [cavityPhysicalReplicaVectors_gram hN, abs_div,
    abs_of_pos (lt_of_lt_of_le hc (hd a))]
  exact div_le_div₀ (by positivity) (projectedOverlap_abs_le_one U (I a) (σ i) (σ j))
    hc (hd a)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGroupedGram
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The vectors used by the fresh group frames have exactly the
physical projected-overlap covariance divided by the group density. -/

noncomputable section
open IsingPerceptron
open scoped Matrix

namespace InvariantIsing

lemma cavityGroupSetEquiv_apply {N m : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (a : Fin m) (j : Fin (k a)) :
    ((cavityGroupSetEquiv k e a) j : Fin N)=e ⟨a,j⟩ := rfl

lemma cavityGroupSpinCoordinates_physical {N m r : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (V : Orthogonal N) (σ : Fin r → Spin N) :
    (fun a i => cavityGroupSpinCoordinates k e V a (σ i)) =
    cavityPhysicalReplicaVectors (matrixRotation V⁻¹)
      (cavitySpectralGroup (fun i => (e.symm i).1)) k (cavityGroupSetEquiv k e) σ := by
  funext a i j
  rw [cavityPhysicalReplicaVectors, cavityGroupSetEquiv_apply]
  rfl

lemma cavityGroupSpinCoordinates_gram_bound {N m r : ℕ} (hN : 0 < N)
    (k : Fin m → ℕ) (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (V : Orthogonal N) (σ : Fin r → Spin N) {c : ℝ} (hc : 0 < c)
    (hk : ∀ a, c ≤ (k a : ℝ)/N) :
    ∀ a i j, |cavityGroupReplicaGram (fun a i => cavityGroupSpinCoordinates k e V a (σ i)) a i j|
      ≤ 1/c := by
  rw [cavityGroupSpinCoordinates_physical]
  exact cavityPhysicalReplicaVectors_gram_bound hN _ _ _ _ _ c hc hk

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRotationVectors
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable physical group vectors and their covariance in the actual
base Gibbs disorder space. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma measurable_cavityRotationVectors {N m depth : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (x : Spin N × LabeledLeaf depth) :
    Measurable (fun p a => cavityRotationVectors k e p a x) := by
  apply Measurable.of_eval
  intro a
  apply Measurable.of_eval
  intro j
  exact (measurable_cavityRotation_eval (spinVector x.1) (e ⟨a,j⟩)).comp measurable_fst.fst

lemma cavityRotationVectors_gram_bound {N m depth r : ℕ} (hN : 0 < N)
    (k : Fin m → ℕ) (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (p : (((Orthogonal N × LabeledTree depth) × (ℕ → ℝ)) ×
      (ℕ → Spin N × LabeledLeaf depth)))
    {c : ℝ} (hc : 0 < c) (hk : ∀ a, c ≤ (k a : ℝ)/N) :
    ∀ a i j, |cavityGroupReplicaGram
      (fun a (i : Fin r) => cavityRotationVectors k e p.1 a (p.2 i)) a i j| ≤ 1/c :=
  cavityGroupSpinCoordinates_gram_bound hN k e p.1.1.1
    (fun i => (p.2 i).1) hc hk

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarLogObservable
attribute [-instance] _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The capped logarithmic observable in the actual fresh-Haar Gibbs
model, with its measurable original prior and quadratic penalty. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_capped_factor_growth_bound {d n : ℕ} (B : CavityFactorBlocks d n)
    {D R : ℝ} (hD : cavityFactorSize B.1 B.2.1 B.2.2 ≤ D)
    (y : EuclideanSpace ℝ (Fin d)) (hy : ‖y‖^2 ≤ R) (ε : Spin n)
    (t cap δ : ℝ) (hcap : 0 ≤ cap) :
    |min (t*cavityLogFactor B.1 B.2.1 B.2.2 y ε) cap - δ*(1+‖y‖^2)| ≤
      (|t| *D+|δ|)*(1+R) := by
  have hd := (cavityFactorSize_nonneg B.1 B.2.1 B.2.2).trans hD
  have hg : |cavityLogFactor B.1 B.2.1 B.2.2 y ε| ≤ D*(1+R) :=
    (cavity_logFactor_growth B.1 B.2.1 B.2.2 y ε).trans
      (mul_le_mul hD (add_le_add (le_refl 1) hy) (by positivity) hd)
  calc
    _ ≤ |min (t*cavityLogFactor B.1 B.2.1 B.2.2 y ε) cap|+|δ*(1+‖y‖^2)| := abs_sub _ _
    _ ≤ |t| *(D*(1+R))+|δ| *(1+R) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1+‖y‖^2)]
      exact add_le_add ((cavity_abs_min_cap hcap).trans
        (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hg (abs_nonneg t)))
        (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hy) (abs_nonneg δ))
    _ = _ := by ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCanonicalHaarLog
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual canonical fresh-group logarithmic observable and its
finite-volume measurability and boundedness. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

lemma cavity_canonical_group_projection_bound {N m d : ℕ}
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (hk : ∀ a, d ≤ k a) (V : Orthogonal N)
    (W : (a : Fin m) → Orthogonal (cavityBaseGroupDimension k a₀ a)) (σ : Spin N) :
    ‖cavitySelectedSiteProjection (fun j => (a₀ j,j))
      (cavityGroupSpinCoordinates (cavityBaseGroupDimension k a₀) (cavityBaseGroupEquiv k e a₀) V)
      (cavityGroupHaarFrames (cavityCanonicalGroupFrame k e a₀ hk) W) σ‖^2 ≤ N := by
  rw [← cavityGroupedSelectedFrame_rotated_coordinates]
  apply cavity_frame_coordinates_norm_le
  apply cavity_orthogonal_frame_gram
  apply cavity_orthogonal_frame_gram
  rw [cavityCanonicalGroupFrame_special, cavityCanonicalSpecial_gram]


end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityNormalizerProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convergence in probability of a quadratic coefficient error controls
capped normalizers in mean, using the actual prior fourth moment. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

theorem cavity_capped_normalizer_probability_limit
    {Ω X : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (X n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (ν : (n : ℕ) → Ω n → Measure (X n)) [∀ n ω, IsProbabilityMeasure (ν n ω)]
    (H G R : (n : ℕ) → Ω n × X n → ℝ)
    (hH : ∀ n, Measurable (H n)) (hG : ∀ n, Measurable (G n))
    (hi : ∀ n ω, Integrable (fun x => R n (ω,x)^4) (ν n ω))
    (hmi : ∀ n, Integrable (fun ω => ∫ x, R n (ω,x)^4 ∂ν n ω) (P n))
    {M : ℝ} (hM : 0 ≤ M) (hMR : ∀ n, (∫ ω, ∫ x, R n (ω,x)^4 ∂ν n ω ∂P n) ≤ M)
    (a : (n : ℕ) → Ω n → ℝ) (ha : ∀ n, Measurable (a n))
    (hchange : ∀ n ω x, |H n (ω,x)-G n (ω,x)| ≤ a n ω*(1+R n (ω,x)^2))
    (hprob : ∀ δ > 0, Tendsto (fun n => (P n).real {ω | δ < a n ω}) atTop (𝓝 0))
    (T : ℝ) :
    Tendsto (fun n => ∫ ω,
      |(∫ x, Real.exp (min (H n (ω,x)) T) ∂ν n ω) -
        ∫ x, Real.exp (min (G n (ω,x)) T) ∂ν n ω| ∂P n) atTop (𝓝 0) := by
  let Z n ω := ∫ x, Real.exp (min (H n (ω,x)) T) ∂ν n ω
  let W n ω := ∫ x, Real.exp (min (G n (ω,x)) T) ∂ν n ω
  have hexp n ω (F : Ω n × X n → ℝ) (hF : Measurable F) :
      Integrable (fun x => Real.exp (min (F (ω,x)) T)) (ν n ω) :=
    integrable_of_measurable_abs_le (((hF.min measurable_const).exp).comp measurable_prodMk_left)
      (fun x => by rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr (min_le_right _ _))
  have hbound n ω : |Z n ω-W n ω| ≤ 2*Real.exp T := by
    have hz : 0 ≤ Z n ω := integral_nonneg (fun _ => (Real.exp_pos _).le)
    have hw : 0 ≤ W n ω := integral_nonneg (fun _ => (Real.exp_pos _).le)
    have hz' : Z n ω ≤ Real.exp T :=
      (integral_mono (hexp n ω (H n) (hH n)) (integrable_const _)
        (fun _ => Real.exp_le_exp.mpr (min_le_right _ _))).trans_eq (by simp)
    have hw' : W n ω ≤ Real.exp T :=
      (integral_mono (hexp n ω (G n) (hG n)) (integrable_const _)
        (fun _ => Real.exp_le_exp.mpr (min_le_right _ _))).trans_eq (by simp)
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg hz, abs_of_nonneg hw]; linarith)
  have hmean (δ : ℝ) (hδ : 0 ≤ δ) (n : ℕ) :
      (∫ ω, |Z n ω-W n ω| ∂P n) ≤
        2*Real.exp T*δ*(1+M)+2*Real.exp T*(P n).real {ω | δ < a n ω} := by
    let bad := {ω : Ω n | δ < a n ω}
    have hbad : MeasurableSet bad := measurableSet_lt measurable_const (ha n)
    have hp ω : |Z n ω-W n ω| ≤
        2*Real.exp T*δ*(1+∫ x, R n (ω,x)^4 ∂ν n ω) +
          2*Real.exp T*bad.indicator (fun _ => (1:ℝ)) ω := by
      by_cases hω : ω ∈ bad
      · rw [indicator_of_mem hω, mul_one]
        exact (hbound n ω).trans (le_add_of_nonneg_left (mul_nonneg (by positivity)
          (by positivity : 0 ≤ 1+∫ x, R n (ω,x)^4 ∂ν n ω)))
      · rw [indicator_of_notMem hω, mul_zero, add_zero]
        dsimp only [Z,W]
        rw [← integral_sub (hexp n ω (H n) (hH n)) (hexp n ω (G n) (hG n))]
        calc
          _ ≤ ∫ x, |Real.exp (min (H n (ω,x)) T)-Real.exp (min (G n (ω,x)) T)| ∂ν n ω :=
            abs_integral_le_integral_abs
          _ ≤ ∫ x, 2*Real.exp T*δ*(1+R n (ω,x)^4) ∂ν n ω := by
            apply integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
              (((integrable_const 1).add (hi n ω)).const_mul _)
            exact ae_of_all _ fun x => by
              change |Real.exp (min (H n (ω,x)) T)-Real.exp (min (G n (ω,x)) T)| ≤
                2*Real.exp T*δ*(1+R n (ω,x)^4)
              have hc := (cavity_capped_exp_sub_le (H n (ω,x)) (G n (ω,x)) T).trans
                (mul_le_mul_of_nonneg_left (hchange n ω x) (Real.exp_pos T).le)
              have hsmall : a n ω ≤ δ := le_of_not_gt hω
              have hrad : 1+R n (ω,x)^2 ≤ 2*(1+R n (ω,x)^4) :=
                by nlinarith [sq_nonneg (R n (ω,x)^2-1)]
              have hb := mul_le_mul_of_nonneg_right hsmall (by positivity : 0 ≤ 1+R n (ω,x)^2)
              have hb' := mul_le_mul_of_nonneg_left hrad hδ
              have hc' := mul_le_mul_of_nonneg_left (hb.trans hb') (Real.exp_pos T).le
              exact hc.trans (hc'.trans_eq (by ring))
          _ = _ := by
            rw [integral_const_mul, integral_add (integrable_const 1) (hi n ω)]
            simp only [integral_const, probReal_univ, one_smul]
    have hiB := (((integrable_const 1).add (hmi n)).const_mul (2*Real.exp T*δ)).add
      (((integrable_const (1:ℝ)).indicator hbad).const_mul (2*Real.exp T))
    calc
      _ ≤ ∫ ω, 2*Real.exp T*δ*(1+∫ x, R n (ω,x)^4 ∂ν n ω) +
          2*Real.exp T*bad.indicator (fun _ => (1:ℝ)) ω ∂P n :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) hiB (ae_of_all _ hp)
      _ = 2*Real.exp T*δ*(1+∫ ω, ∫ x, R n (ω,x)^4 ∂ν n ω ∂P n) +
          2*Real.exp T*(P n).real bad := by
        rw [integral_add, integral_const_mul, integral_add (integrable_const 1) (hmi n),
          integral_const_mul, integral_indicator hbad]
        · simp only [integral_const, smul_eq_mul, mul_one,
            Measure.restrict_apply_univ, measureReal_def, measure_univ, ENNReal.toReal_one]
        · exact ((integrable_const 1).add (hmi n)).const_mul _
        · exact ((integrable_const (1:ℝ)).indicator hbad).const_mul _
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) (hMR n)) (by positivity)) le_rfl
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε/(8*Real.exp T*(1+M))
  have hδ : 0 < δ := by dsimp only [δ] <;> positivity
  have hδeq : 8*Real.exp T*(1+M)*δ = ε := by dsimp only [δ]; field_simp
  have ht : Tendsto (fun n => 2*Real.exp T*(P n).real {ω | δ < a n ω}) atTop (𝓝 0) := by
    simpa only [mul_zero] using (hprob δ hδ).const_mul (2*Real.exp T)
  have htail := ht.eventually
    (gt_mem_nhds (show (0:ℝ) < ε/2 by positivity))
  filter_upwards [htail] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
  have hb := hmean δ hδ.le n
  change 2*Real.exp T*(P n).real {ω | δ < a n ω} < ε/2 at hn
  nlinarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLogProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concentrating quadratic coefficient error may be removed from
the expected capped logarithm without an inverse-normalizer assumption. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

theorem cavity_capped_log_probability_limit
    {Ω X : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (X n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (ν : (n : ℕ) → Ω n → Measure (X n)) (hν : ∀ n, Measurable (ν n))
    [∀ n ω, IsProbabilityMeasure (ν n ω)]
    (H G R : (n : ℕ) → Ω n × X n → ℝ)
    (hH : ∀ n, Measurable (H n)) (hG : ∀ n, Measurable (G n))
    (hi : ∀ n ω, Integrable (fun x => R n (ω,x)^4) (ν n ω))
    (hmi : ∀ n, Integrable (fun ω => ∫ x, R n (ω,x)^4 ∂ν n ω) (P n))
    {D M T : ℝ} (hD : 0 ≤ D) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hgH : ∀ n ω x, |H n (ω,x)| ≤ D*(1+R n (ω,x)^2))
    (hgG : ∀ n ω x, |G n (ω,x)| ≤ D*(1+R n (ω,x)^2))
    (hMR : ∀ n, (∫ ω, ∫ x, R n (ω,x)^4 ∂ν n ω ∂P n) ≤ M)
    (a : (n : ℕ) → Ω n → ℝ) (ha : ∀ n, Measurable (a n))
    (hchange : ∀ n ω x, |H n (ω,x)-G n (ω,x)| ≤ a n ω*(1+R n (ω,x)^2))
    (hprob : ∀ δ > 0, Tendsto (fun n => (P n).real {ω | δ < a n ω}) atTop (𝓝 0)) :
    Tendsto (fun n =>
      (∫ ω, Real.log (∫ x, Real.exp (min (H n (ω,x)) T) ∂ν n ω) ∂P n) -
      ∫ ω, Real.log (∫ x, Real.exp (min (G n (ω,x)) T) ∂ν n ω) ∂P n) atTop (𝓝 0) := by
  let Z n ω := ∫ x, Real.exp (min (H n (ω,x)) T) ∂ν n ω
  let W n ω := ∫ x, Real.exp (min (G n (ω,x)) T) ∂ν n ω
  have hZi n := cavity_capped_negative_log_mean_bound (P n) (ν n) (hν n) (H n) (R n)
    (hH n) (hi n) (hmi n) hD hT (hgH n) (hMR n)
  have hWi n := cavity_capped_negative_log_mean_bound (P n) (ν n) (hν n) (G n) (R n)
    (hG n) (hi n) (hmi n) hD hT (hgG n) (hMR n)
  have hexp n ω (F : Ω n × X n → ℝ) (hF : Measurable F) :
      Integrable (fun x => Real.exp (min (F (ω,x)) T)) (ν n ω) :=
    integrable_of_measurable_abs_le (((hF.min measurable_const).exp).comp measurable_prodMk_left)
      (fun x => by rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr (min_le_right _ _))
  have hb n ω (F : Ω n × X n → ℝ) (hF : Measurable F) :
      (∫ x, Real.exp (min (F (ω,x)) T) ∂ν n ω) ≤ Real.exp T :=
    (integral_mono (hexp n ω F hF) (integrable_const _)
      (fun _ => Real.exp_le_exp.mpr (min_le_right _ _))).trans_eq (by simp)
  exact cavity_log_of_mean_distance P Z W
    (fun n => measurable_cavityWeightNormalizer (ν n) (hν n) _ (((hH n).min measurable_const).exp))
    (fun n => measurable_cavityWeightNormalizer (ν n) (hν n) _ (((hG n).min measurable_const).exp))
    (Real.one_le_exp hT) (by positivity : 0 ≤ 2*D^2*(1+M))
    (fun n ω => integral_exp_pos (hexp n ω (H n) (hH n)))
    (fun n ω => integral_exp_pos (hexp n ω (G n) (hG n)))
    (fun n ω => hb n ω (H n) (hH n)) (fun n ω => hb n ω (G n) (hG n))
    (fun n => (hZi n).1) (fun n => (hWi n).1) (fun n => (hZi n).2) (fun n => (hWi n).2)
    (cavity_capped_normalizer_probability_limit P ν H G R hH hG hi hmi hM hMR
      a ha hchange hprob T)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCappedBlockLog
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replacement of random cavity blocks inside the capped expected
logarithm.  The hypotheses are the proved coefficient and prior bounds. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

theorem cavity_capped_block_log_limit {d k : ℕ}
    {Ω X : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (X n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (ν : (n : ℕ) → Ω n → Measure (X n)) (hν : ∀ n, Measurable (ν n))
    [∀ n ω, IsProbabilityMeasure (ν n ω)]
    (A : (n : ℕ) → Ω n → CavityFactorBlocks d k) (hA : ∀ n, Measurable (A n))
    (A₀ : CavityFactorBlocks d k)
    (Y : (n : ℕ) → Ω n × X n → EuclideanSpace ℝ (Fin d))
    (hY : ∀ n, Measurable (Y n))
    (ε : (n : ℕ) → Ω n × X n → Spin k) (hε : ∀ n, Measurable (ε n))
    (hi : ∀ n ω, Integrable (fun x => ‖Y n (ω,x)‖^4) (ν n ω))
    (hmi : ∀ n, Integrable (fun ω => ∫ x, ‖Y n (ω,x)‖^4 ∂ν n ω) (P n))
    {D M T : ℝ} (hD : 0 ≤ D) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hAb : ∀ n ω, cavityFactorSize (A n ω).1 (A n ω).2.1 (A n ω).2.2 ≤ D)
    (hA₀b : cavityFactorSize A₀.1 A₀.2.1 A₀.2.2 ≤ D)
    (hMR : ∀ n, (∫ ω, ∫ x, ‖Y n (ω,x)‖^4 ∂ν n ω ∂P n) ≤ M)
    (hprob : ∀ δ > 0, Tendsto (fun n => (P n).real
      {ω | δ < cavityFactorDeviation (A n ω) A₀}) atTop (𝓝 0)) :
    Tendsto (fun n =>
      (∫ ω, Real.log (∫ x, Real.exp (min
        (cavityLogFactor (A n ω).1 (A n ω).2.1 (A n ω).2.2 (Y n (ω,x)) (ε n (ω,x))) T)
        ∂ν n ω) ∂P n) -
      ∫ ω, Real.log (∫ x, Real.exp (min
        (cavityLogFactor A₀.1 A₀.2.1 A₀.2.2 (Y n (ω,x)) (ε n (ω,x))) T)
        ∂ν n ω) ∂P n) atTop (𝓝 0) := by
  let : OpensMeasurableSpace (CavityFactorBlocks d k) := inferInstanceAs
    (OpensMeasurableSpace ((Fin d → Fin d → ℝ) ×
      ((Fin d → Fin k → ℝ) × (Fin k → Fin k → ℝ))))
  let H n p := cavityLogFactor (A n p.1).1 (A n p.1).2.1 (A n p.1).2.2 (Y n p) (ε n p)
  let G n p := cavityLogFactor A₀.1 A₀.2.1 A₀.2.2 (Y n p) (ε n p)
  have hm n (B : Ω n → CavityFactorBlocks d k) (hB : Measurable B) :
      Measurable (fun p : Ω n × X n =>
        cavityLogFactor (B p.1).1 (B p.1).2.1 (B p.1).2.2 (Y n p) (ε n p)) := by
    unfold cavityLogFactor cavityQuadratic
    fun_prop
  refine cavity_capped_log_probability_limit P ν hν H G (fun n p => ‖Y n p‖)
    (fun n => hm n (A n) (hA n)) (fun n => hm n (fun _ => A₀) measurable_const)
    hi hmi hD hM hT ?_ ?_ hMR (fun n ω => cavityFactorDeviation (A n ω) A₀)
    (fun n => (continuous_cavityFactorDeviation A₀).measurable.comp (hA n)) ?_ hprob
  · intro n ω x
    exact (cavity_logFactor_growth _ _ _ _ _).trans
      (mul_le_mul_of_nonneg_right (hAb n ω) (by positivity))
  · intro n ω x
    exact (cavity_logFactor_growth _ _ _ _ _).trans
      (mul_le_mul_of_nonneg_right hA₀b (by positivity))
  · intro n ω x
    change |cavityLogFactor _ _ _ _ _-cavityLogFactor _ _ _ _ _| ≤ _
    rw [cavityLogFactor_sub]
    exact cavity_logFactor_growth _ _ _ _ _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCoefficientSampling
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sampling Gibbs replicas retains the distribution of the disorder.
Consequently the coefficient concentration estimate is unchanged when
replica coordinates are added. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_factor_deviation_pullback {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {d n : ℕ} (P : Measure Ω) (Q : Measure Ξ) (f : Ω → Ξ)
    (hf : MeasurePreserving f P Q) (A : Ξ → CavityFactorBlocks d n)
    (hA : Measurable A) (A₀ : CavityFactorBlocks d n) (δ : ℝ) :
    P.real {ω | δ < cavityFactorDeviation (A (f ω)) A₀} =
      Q.real {x | δ < cavityFactorDeviation (A x) A₀} := by
  let : OpensMeasurableSpace (CavityFactorBlocks d n) := inferInstanceAs
    (OpensMeasurableSpace ((Fin d → Fin d → ℝ) ×
      ((Fin d → Fin n → ℝ) × (Fin n → Fin n → ℝ))))
  have hs : MeasurableSet {x | δ < cavityFactorDeviation (A x) A₀} :=
    measurableSet_lt measurable_const ((continuous_cavityFactorDeviation A₀).measurable.comp hA)
  have h := congrArg (fun μ : Measure Ξ => μ {x | δ < cavityFactorDeviation (A x) A₀}) hf.map_eq
  rw [Measure.map_apply hf.measurable hs] at h
  exact congrArg ENNReal.toReal h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCompressionFactorBound
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform bound for the actual random cavity coefficients.  It
depends only on the fixed cavity dimensions and spectral values. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavity_frame_entry_bound {s d : ℕ} (B : Matrix (Fin s) (Fin d) ℝ)
    (hB : B.transpose * B = 1) (i : Fin s) (j : Fin d) : |B i j| ≤ 1 := by
  have hn := (cavity_orthonormal_of_gram B hB).norm_eq_one j
  have hi := PiLp.norm_apply_le (WithLp.toLp 2 (fun i : Fin s => B i j) :
    EuclideanSpace ℝ (Fin s)) i
  simpa only [PiLp.toLp_apply, Real.norm_eq_abs, hn] using hi

lemma cavity_frame_block_mass_bound {s d n : ℕ} (D : Matrix (Fin s) (Fin s) ℝ)
    (B : Matrix (Fin s) (Fin d) ℝ) (T : Matrix (Fin s) (Fin n) ℝ)
    (hB : B.transpose * B = 1) (hT : T.transpose * T = 1) :
    cavityMatrixMass (B.transpose * D * T) ≤ (d : ℝ)*n*cavityMatrixMass D := by
  have hb (i : Fin d) (j : Fin n) : |(B.transpose * D * T) i j| ≤ cavityMatrixMass D := by
    have hh := cavity_bilinear_abs_bound D (fun l => B l i) (fun l => T l j)
      zero_le_one zero_le_one (fun l => cavity_frame_entry_bound B hB l i)
      (fun l => cavity_frame_entry_bound T hT l j)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    simpa only [one_mul, mul_one] using hh
  change (∑ i, ∑ j, |(B.transpose * D * T) i j|) ≤ (d : ℝ)*n*cavityMatrixMass D
  calc
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin n, cavityMatrixMass D :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hb i j))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] <;> ring

lemma cavity_matrix_mass_sub_le {d n : ℕ} (A B : Matrix (Fin d) (Fin n) ℝ) :
    cavityMatrixMass (A-B) ≤ cavityMatrixMass A+cavityMatrixMass B := by
  unfold cavityMatrixMass
  simp only [Matrix.sub_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => abs_sub _ _))

theorem cavity_small_factor_size_bound {s d n : ℕ} (D : Matrix (Fin s) (Fin s) ℝ)
    (A₀ : Matrix (Fin d) (Fin d) ℝ)
    (B : Matrix (Fin s) (Fin d) ℝ) (T : Matrix (Fin s) (Fin n) ℝ)
    (hB : B.transpose * B = 1) (hT : T.transpose * T = 1) :
    let A := cavitySmallFactorBlocks D A₀ B T
    cavityFactorSize A.1 A.2.1 A.2.2 ≤
      ((d : ℝ)*d+d*n+n*n)*cavityMatrixMass D+cavityMatrixMass A₀ := by
  intro A
  have hK : cavityMatrixMass (B.transpose * D * B-A₀) ≤
      (d : ℝ)*d*cavityMatrixMass D+cavityMatrixMass A₀ :=
    (cavity_matrix_mass_sub_le (B.transpose * D * B) A₀).trans
      (add_le_add (cavity_frame_block_mass_bound D B B hB hB) le_rfl)
  have hL := cavity_frame_block_mass_bound D B T hB hT
  have hC := cavity_frame_block_mass_bound D T T hT hT
  dsimp only [A, cavitySmallFactorBlocks, cavityFactorSize]
  nlinarith

theorem cavity_compression_factor_size_bound {N m d n : ℕ}
    (g : Fin (N+n) → Fin m) (e : Fin (m*n) ≃ Fin (d+n))
    (lam : Fin m → ℝ) (lam₀ : Fin d → ℝ) (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ)
    (U : Orthogonal (N+n)) :
    let A := cavityCompressionFactorBlocks e lam lam₀ B₀ (cavityCompressionGrams g U)
    cavityFactorSize A.1 A.2.1 A.2.2 ≤
      ((d : ℝ)*d+d*n+n*n)*cavityMatrixMass (cavityRepeatedSpectrum (n := n) lam)+
        cavityMatrixMass (Matrix.diagonal lam₀) := by
  intro A
  apply cavity_small_factor_size_bound
  · exact cavityConcreteComplement_gram g e B₀ U
  · rw [cavitySpectralStack_gram, cavityCompressionGrams_sum]
    intro a
    simpa only [cavityCompressionGrams, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self (cavitySpectralImage g (cavityColumns U) a)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityExtraLogAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two finite-volume Fubini steps needed to retain an independent
compression variable in the logarithmic cavity limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_bounded_extra_product_integral {Z A B : Type*}
    [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure Z) [IsProbabilityMeasure P] (Q : Measure A) [IsProbabilityMeasure Q]
    (R : Measure B) [IsProbabilityMeasure R]
    (f : (Z × A) × B → ℝ) (hf : Measurable f) {M : ℝ} (hb : ∀ p, |f p| ≤ M) :
    (∫ p, f p ∂(P.prod Q).prod R) =
      ∫ z, ∫ p, f ((z,p.1),p.2) ∂Q.prod R ∂P := by
  have hi : Integrable f ((P.prod Q).prod R) :=
    integrable_of_measurable_abs_le hf hb
  rw [integral_prod _ hi, integral_prod _ hi.integral_prod_left]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  have hm : Measurable (fun p : A × B => f ((z,p.1),p.2)) :=
    hf.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  exact (integral_prod _ (integrable_of_measurable_abs_le hm (fun p => hb ((z,p.1),p.2)))).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarLogCoefficients
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Capped logarithmic coefficient replacement in the actual fresh-Haar
model, with all ordinary spatial moment assumptions discharged. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

theorem cavity_haar_capped_coefficient_limit {m q d k : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ n a, 0 < N n a)
    (μ : (n : ℕ) → (a : Fin m) → Measure (Orthogonal (N n a)))
    [∀ n a, IsProbabilityMeasure (μ n a)] [∀ n a, (μ n a).IsMulRightInvariant]
    (Ω X : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (X n)]
    [∀ n, Countable (X n)] [∀ n, MeasurableSingletonClass (X n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (ν : (n : ℕ) → Ω n → Measure (X n)) (hν : ∀ n, Measurable (ν n))
    [∀ n ω, IsProbabilityMeasure (ν n ω)]
    (e : Fin d → Fin m × Fin q)
    (v : (n : ℕ) → Ω n → (a : Fin m) → X n → Fin (N n a) → ℝ)
    (hvM : ∀ n x, Measurable (fun ω a => v n ω a x))
    (A₀ : (n : ℕ) → (a : Fin m) → Matrix (Fin (N n a)) (Fin q) ℝ)
    (hA₀ : ∀ n a, (A₀ n a).transpose * A₀ n a = 1)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hv : ∀ n ω x a, ‖(WithLp.toLp 2 (v n ω a x) :
      EuclideanSpace ℝ (Fin (N n a)))‖^2 ≤ C₀ * N n a)
    (A : (n : ℕ) → Ω n → CavityFactorBlocks d k) (hA : ∀ n, Measurable (A n))
    (A₁ : CavityFactorBlocks d k) {D : ℝ} (hD : 0 ≤ D)
    (hAb : ∀ n ω, cavityFactorSize (A n ω).1 (A n ω).2.1 (A n ω).2.2 ≤ D)
    (hA₁ : cavityFactorSize A₁.1 A₁.2.1 A₁.2.2 ≤ D)
    (hprob : ∀ δ > 0, Tendsto (fun n => (P n).real
      {ω | δ < cavityFactorDeviation (A n ω) A₁}) atTop (𝓝 0))
    (π : Measure (Spin k)) [IsProbabilityMeasure π] (T : ℝ) (hT : 0 ≤ T) :
    let Y := fun n (p : (Ω n × ((a : Fin m) → Orthogonal (N n a))) × (X n × Spin k)) =>
      cavitySelectedSiteProjection e (v n p.1.1) (cavityGroupHaarFrames (A₀ n) p.1.2) p.2.1
    Tendsto (fun n =>
      (∫ ω, Real.log (∫ x, Real.exp (min
        (cavityLogFactor (A n ω.1).1 (A n ω.1).2.1 (A n ω.1).2.2 (Y n (ω,x)) x.2) T)
        ∂(ν n ω.1).prod π) ∂(P n).prod (Measure.pi (μ n))) -
      ∫ ω, Real.log (∫ x, Real.exp (min
        (cavityLogFactor A₁.1 A₁.2.1 A₁.2.2 (Y n (ω,x)) x.2) T)
        ∂(ν n ω.1).prod π) ∂(P n).prod (Measure.pi (μ n))) atTop (𝓝 0) := by
  intro Y
  let η n := cavityHaarSpinPriorKernel (U := (a : Fin m) → Orthogonal (N n a))
    (ν n) (hν n) π
  let M := (d : ℝ)^2 * cavityGaussianAbsMoment 4 * C₀^2
  have hm n := cavity_haar_prior_fourth_moment (P n) (ν n) (hν n) (hN n) (μ n)
    e (v n) (hvM n) (A₀ n) (hA₀ n) hC₀ (hv n) π
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg (sq_nonneg _) (cavityGaussianAbsMoment_nonneg 4)) (sq_nonneg C₀)
  have hp n : MeasurePreserving Prod.fst ((P n).prod (Measure.pi (μ n))) (P n) :=
    measurePreserving_fst
  have hprob' : ∀ δ > 0, Tendsto (fun n => ((P n).prod (Measure.pi (μ n))).real
      {ω | δ < cavityFactorDeviation (A n ω.1) A₁}) atTop (𝓝 0) := by
    intro δ hδ
    apply (hprob δ hδ).congr'
    filter_upwards [] with n
    exact (cavity_factor_deviation_pullback _ _ Prod.fst (hp n) (A n) (hA n) A₁ δ).symm
  have hout := cavity_capped_block_log_limit (fun n => (P n).prod (Measure.pi (μ n)))
    (fun n => η n) (fun n => (η n).measurable)
    (fun n ω => A n ω.1) (fun n => (hA n).comp measurable_fst) A₁ Y
    (fun n => (measurable_cavitySelectedSiteProjection e (v n) (hvM n) (A₀ n)).comp
      (measurable_fst.prodMk measurable_snd.fst))
    (fun _ p => p.2.2) (fun _ => measurable_snd.snd)
    (fun n => by simpa only [η, cavityHaarSpinPriorKernel_apply, Y] using (hm n).1)
    (fun n => by simpa only [η, cavityHaarSpinPriorKernel_apply, Y] using (hm n).2.1)
    hD hM hT (fun n ω => hAb n ω.1) hA₁
    (fun n => by simpa only [η, cavityHaarSpinPriorKernel_apply, Y, M] using (hm n).2.2) hprob'
  simpa only [η, cavityHaarSpinPriorKernel_apply] using hout

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarVariablePenalty
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removal of the geometric penalty before replacing the random
compression blocks.  The Haar fourth moment is uniform in those blocks. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

theorem cavity_haar_variable_quadratic_penalty {m q d k : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ n a, 0 < N n a)
    (μ : (n : ℕ) → (a : Fin m) → Measure (Orthogonal (N n a)))
    [∀ n a, IsProbabilityMeasure (μ n a)] [∀ n a, (μ n a).IsMulRightInvariant]
    (Ω X : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (X n)]
    [∀ n, Countable (X n)] [∀ n, MeasurableSingletonClass (X n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (ν : (n : ℕ) → Ω n → Measure (X n)) (hν : ∀ n, Measurable (ν n))
    [∀ n ω, IsProbabilityMeasure (ν n ω)]
    (e : Fin d → Fin m × Fin q)
    (v : (n : ℕ) → Ω n → (a : Fin m) → X n → Fin (N n a) → ℝ)
    (hvM : ∀ n x, Measurable (fun ω a => v n ω a x))
    (A₀ : (n : ℕ) → (a : Fin m) → Matrix (Fin (N n a)) (Fin q) ℝ)
    (hA₀ : ∀ n a, (A₀ n a).transpose * A₀ n a = 1)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hv : ∀ n ω x a, ‖(WithLp.toLp 2 (v n ω a x) :
      EuclideanSpace ℝ (Fin (N n a)))‖^2 ≤ C₀ * N n a)
    (A : (n : ℕ) → Ω n → CavityFactorBlocks d k) (hA : ∀ n, Measurable (A n))
    {D : ℝ} (hD : 0 ≤ D)
    (hAb : ∀ n ω, cavityFactorSize (A n ω).1 (A n ω).2.1 (A n ω).2.2 ≤ D)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] (T : ℝ) (hT : 0 ≤ T)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) (hδlim : Tendsto δ atTop (𝓝 0)) :
    let Y := fun n (p : (Ω n × ((a : Fin m) → Orthogonal (N n a))) × (X n × Spin k)) =>
      cavitySelectedSiteProjection e (v n p.1.1) (cavityGroupHaarFrames (A₀ n) p.1.2) p.2.1
    let H := fun n (p : (Ω n × ((a : Fin m) → Orthogonal (N n a))) × (X n × Spin k)) =>
      cavityLogFactor (A n p.1.1).1 (A n p.1.1).2.1 (A n p.1.1).2.2 (Y n p) p.2.2
    Tendsto (fun n =>
      (∫ ω, Real.log (∫ x, Real.exp (min (H n (ω,x)) T) ∂(ν n ω.1).prod π)
        ∂(P n).prod (Measure.pi (μ n))) -
      ∫ ω, Real.log (∫ x, Real.exp (min (H n (ω,x)) T - δ n*(1+‖Y n (ω,x)‖^2))
        ∂(ν n ω.1).prod π) ∂(P n).prod (Measure.pi (μ n))) atTop (𝓝 0) := by
  intro Y H
  let η n := cavityHaarSpinPriorKernel (U := (a : Fin m) → Orthogonal (N n a))
    (ν n) (hν n) π
  let M := (d : ℝ)^2 * cavityGaussianAbsMoment 4 * C₀^2
  have hm n := cavity_haar_prior_fourth_moment (P n) (ν n) (hν n) (hN n) (μ n)
    e (v n) (hvM n) (A₀ n) (hA₀ n) hC₀ (hv n) π
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg (sq_nonneg _) (cavityGaussianAbsMoment_nonneg 4)) (sq_nonneg C₀)
  have hY n : Measurable (Y n) :=
    (measurable_cavitySelectedSiteProjection e (v n) (hvM n) (A₀ n)).comp
      (measurable_fst.prodMk measurable_snd.fst)
  have hH n : Measurable (H n) := by
    have hA' : Measurable (fun p : (Ω n × ((a : Fin m) → Orthogonal (N n a))) × (X n × Spin k) =>
        A n p.1.1) := (hA n).comp measurable_fst.fst
    have hε : Measurable (fun p : (Ω n × ((a : Fin m) → Orthogonal (N n a))) × (X n × Spin k) =>
        p.2.2) := measurable_snd.snd
    dsimp only [H]
    unfold cavityLogFactor cavityQuadratic
    fun_prop
  let δ' n := min (δ n) 1
  have hδ' : Tendsto δ' atTop (𝓝 0) := by
    simpa only [min_eq_left zero_le_one] using hδlim.min (tendsto_const_nhds (x := (1:ℝ)))
  have hout := cavity_vanishing_quadratic_penalty (fun n => (P n).prod (Measure.pi (μ n)))
    (fun n => η n) (fun n => (η n).measurable) H (fun n p => ‖Y n p‖) hH
    (fun n => (hY n).norm)
    (fun n => by simpa only [η, cavityHaarSpinPriorKernel_apply, Y] using (hm n).1)
    (fun n => by simpa only [η, cavityHaarSpinPriorKernel_apply, Y] using (hm n).2.1)
    hD hM hT
    (fun n ω x => (cavity_logFactor_growth _ _ _ _ _).trans
      (mul_le_mul_of_nonneg_right (hAb n ω.1) (by positivity)))
    (fun n => by simpa only [η, cavityHaarSpinPriorKernel_apply, Y, M] using (hm n).2.2)
    δ' (fun n => le_min (hδ n) zero_le_one) (fun n => min_le_right _ _) hδ'
  apply hout.congr'
  filter_upwards [hδlim.eventually (eventually_lt_nhds zero_lt_one)] with n hn
  simp only [η, cavityHaarSpinPriorKernel_apply, δ', min_eq_left hn.le]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarPenalizedLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.planeRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual capped cavity logarithm with its geometric penalty has
its deterministic-block limit after fresh-Haar averaging. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

theorem cavity_haar_penalized_coefficient_limit {m q d k : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ n a, 0 < N n a)
    (μ : (n : ℕ) → (a : Fin m) → Measure (Orthogonal (N n a)))
    [∀ n a, IsProbabilityMeasure (μ n a)] [∀ n a, (μ n a).IsMulRightInvariant]
    (Ω X : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (X n)]
    [∀ n, Countable (X n)] [∀ n, MeasurableSingletonClass (X n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (ν : (n : ℕ) → Ω n → Measure (X n)) (hν : ∀ n, Measurable (ν n))
    [∀ n ω, IsProbabilityMeasure (ν n ω)]
    (e : Fin d → Fin m × Fin q)
    (v : (n : ℕ) → Ω n → (a : Fin m) → X n → Fin (N n a) → ℝ)
    (hvM : ∀ n x, Measurable (fun ω a => v n ω a x))
    (A₀ : (n : ℕ) → (a : Fin m) → Matrix (Fin (N n a)) (Fin q) ℝ)
    (hA₀ : ∀ n a, (A₀ n a).transpose * A₀ n a = 1)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hv : ∀ n ω x a, ‖(WithLp.toLp 2 (v n ω a x) :
      EuclideanSpace ℝ (Fin (N n a)))‖^2 ≤ C₀ * N n a)
    (A : (n : ℕ) → Ω n → CavityFactorBlocks d k) (hA : ∀ n, Measurable (A n))
    (A₁ : CavityFactorBlocks d k) {D : ℝ} (hD : 0 ≤ D)
    (hAb : ∀ n ω, cavityFactorSize (A n ω).1 (A n ω).2.1 (A n ω).2.2 ≤ D)
    (hA₁ : cavityFactorSize A₁.1 A₁.2.1 A₁.2.2 ≤ D)
    (hprob : ∀ δ > 0, Tendsto (fun n => (P n).real
      {ω | δ < cavityFactorDeviation (A n ω) A₁}) atTop (𝓝 0))
    (π : Measure (Spin k)) [IsProbabilityMeasure π] (T : ℝ) (hT : 0 ≤ T)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) (hδlim : Tendsto δ atTop (𝓝 0)) :
    let Y := fun n (p : (Ω n × ((a : Fin m) → Orthogonal (N n a))) × (X n × Spin k)) =>
      cavitySelectedSiteProjection e (v n p.1.1) (cavityGroupHaarFrames (A₀ n) p.1.2) p.2.1
    Tendsto (fun n =>
      (∫ ω, Real.log (∫ x, Real.exp (min
        (cavityLogFactor (A n ω.1).1 (A n ω.1).2.1 (A n ω.1).2.2 (Y n (ω,x)) x.2) T -
          δ n*(1+‖Y n (ω,x)‖^2))
        ∂(ν n ω.1).prod π) ∂(P n).prod (Measure.pi (μ n))) -
      ∫ ω, Real.log (∫ x, Real.exp (min
        (cavityLogFactor A₁.1 A₁.2.1 A₁.2.2 (Y n (ω,x)) x.2) T)
        ∂(ν n ω.1).prod π) ∂(P n).prod (Measure.pi (μ n))) atTop (𝓝 0) := by
  intro Y
  have hc := cavity_haar_capped_coefficient_limit N hN μ Ω X P ν hν e v hvM A₀ hA₀ hC₀ hv
    A hA A₁ hD hAb hA₁ hprob π T hT
  have hp := cavity_haar_variable_quadratic_penalty N hN μ Ω X P ν hν e v hvM A₀ hA₀ hC₀ hv
    A hA hD hAb π T hT δ hδ hδlim
  have ht := hc.sub hp
  convert (config := {transparency := .instances, preTransparency := .instances}) ht using 1
  · funext n
    dsimp only [Y]
    ring
  · simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarSpinNumerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product-disorder integration for physical Haar spin numerators. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma cavity_group_gram_diagonal_norm {m : ℕ} {N : Fin m → ℕ}
    (hN : ∀ a, 0 < N a) (v : (a : Fin m) → Fin (N a) → ℝ) {C : ℝ}
    (hv : ∀ a, |cavityGroupReplicaGram (fun a (_ : Fin 1) => v a) a 0 0| ≤ C) :
    ∀ a, ‖(WithLp.toLp 2 (v a) : EuclideanSpace ℝ (Fin (N a)))‖^2 ≤ C * N a := by
  intro a
  have hn : 0 < (N a : ℝ) := Nat.cast_pos.mpr (hN a)
  have h := (le_abs_self _).trans (hv a)
  have he : cavityGroupReplicaGram (fun a (_ : Fin 1) => v a) a 0 0 =
      ‖(WithLp.toLp 2 (v a) : EuclideanSpace ℝ (Fin (N a)))‖^2 / (N a : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [cavityGroupReplicaGram, pow_two]
  rw [he] at h
  exact (div_le_iff₀ hn).mp h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRotationVectorNorm
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual base-model group vectors satisfy the size bound required
by logarithmic coefficient replacement. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_rotation_vectors_norm_bound {N m depth : ℕ} (hN : 0<N)
    (dims : Fin m → ℕ) (hgroups : ∀ a, 0<dims a)
    (E : ((a : Fin m) × Fin (dims a)) ≃ Fin N)
    {c : ℝ} (hc : 0 < c) (hfrac : ∀ a, c ≤ (dims a : ℝ)/N)
    (p : (Orthogonal N × LabeledTree depth) × (ℕ → ℝ))
    (x : Spin N × LabeledLeaf depth) :
    ∀ a, ‖(WithLp.toLp 2 (cavityRotationVectors dims E p a x) :
      EuclideanSpace ℝ (Fin (dims a)))‖^2 ≤ (1/c)*dims a := by
  have h := cavityRotationVectors_gram_bound (r := 1) hN dims E
    (p,fun _ => x) hc hfrac
  exact cavity_group_gram_diagonal_norm hgroups
    (fun a => cavityRotationVectors dims E p a x) (fun a => h a 0 0)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedHaarLogObservable
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityFactorDeviation_self _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.planeRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fresh-frame capped logarithm with its actual constrained cavity prior. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma measurable_restrictedHaarLogObservable {m q d n : ℕ} {dims : Fin m → ℕ} {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (C : Finset (Spin n)) (hC : C.Nonempty) (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (e : Fin d → Fin m × Fin q) (v : Ω → (a : Fin m) → X → Fin (dims a) → ℝ)
    (hv : ∀ x, Measurable (fun ω a => v ω a x))
    (A₀ : (a : Fin m) → Matrix (Fin (dims a)) (Fin q) ℝ)
    (B : Ω → CavityFactorBlocks d n) (hB : Measurable B) (t cap δ : ℝ) :
    Measurable (restrictedHaarLogObservable C hC ν e v A₀ B t cap δ) := by
  let U := (a : Fin m) → Orthogonal (dims a)
  let κ := cavityHaarSpinPriorKernel (U := U) ν hν (restrictedSpinPrior C hC : Measure (Spin n))
  let Y := fun p : (Ω × U) × (X × Spin n) =>
    cavitySelectedSiteProjection e (v p.1.1) (cavityGroupHaarFrames A₀ p.1.2) p.2.1
  have hY : Measurable Y := (measurable_cavitySelectedSiteProjection e v hv A₀).comp
    (measurable_fst.prodMk measurable_snd.fst)
  let H := fun p : (Ω × U) × (X × Spin n) =>
    min (t*cavityLogFactor (B p.1.1).1 (B p.1.1).2.1 (B p.1.1).2.2 (Y p) p.2.2) cap -
      δ*(1+‖Y p‖^2)
  have hH : Measurable H := by
    have hB' : Measurable (fun p : (Ω × U) × (X × Spin n) => B p.1.1) :=
      hB.comp measurable_fst.fst
    dsimp only [H]
    unfold cavityLogFactor cavityQuadratic
    fun_prop
  have hh := (measurable_random_referencePartition (ν := fun p => κ p) κ.measurable hH).log
  change Measurable (fun p => restrictedHaarLogObservable C hC ν e v A₀ B t cap δ p)
  simpa only [κ, cavityHaarSpinPriorKernel_apply, H, Y, restrictedHaarLogObservable,
    referencePartition] using hh

lemma restrictedHaarLogObservable_bound {m q d n : ℕ} {dims : Fin m → ℕ} {Ω X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (C : Finset (Spin n)) (hC : C.Nonempty) (ν : Ω → Measure X) [∀ ω, IsProbabilityMeasure (ν ω)]
    (e : Fin d → Fin m × Fin q) (v : Ω → (a : Fin m) → X → Fin (dims a) → ℝ)
    (A₀ : (a : Fin m) → Matrix (Fin (dims a)) (Fin q) ℝ)
    (B : Ω → CavityFactorBlocks d n) (t cap δ : ℝ) (hcap : 0 ≤ cap)
    {D R : ℝ} (hD : ∀ ω, cavityFactorSize (B ω).1 (B ω).2.1 (B ω).2.2 ≤ D)
    (hy : ∀ ω W x, ‖cavitySelectedSiteProjection e (v ω) (cavityGroupHaarFrames A₀ W) x‖^2 ≤ R)
    (p : Ω × ((a : Fin m) → Orthogonal (dims a))) :
    |restrictedHaarLogObservable C hC ν e v A₀ B t cap δ p| ≤ (|t| *D+|δ|)*(1+R) := by
  simpa only [logMean, one_mul, div_one, restrictedHaarLogObservable] using
    logMean_bounds ((ν p.1).prod (restrictedSpinPrior C hC : Measure (Spin n)))
      (measurable_of_countable _) (by norm_num : (0:ℝ)<1)
      (fun x => cavity_capped_factor_growth_bound (B p.1) (hD p.1) _ (hy p.1 p.2 x.1) x.2
        t cap δ hcap)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedCanonicalHaarLog
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constrained base Gibbs law and independent fresh group frames
in the actual canonical capped logarithm. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

lemma restrictedCanonicalHaarLog_bound {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty)
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (hk : ∀ a, d ≤ k a) (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (t cap δ : ℝ) (hcap : 0 ≤ cap) (B : CavityFactorBlocks d n)
    (p : (((Orthogonal N × LabeledTree depth) × (ℕ → ℝ)) ×
      ((a : Fin m) → Orthogonal (cavityBaseGroupDimension k a₀ a)))) :
    |restrictedCanonicalHaarLog S hS C hC k e a₀ hk lam v u t cap δ B p| ≤
      (|t| *cavityFactorSize B.1 B.2.1 B.2.2+|δ|)*(1+N) := by
  let E := cavityBaseGroupEquiv k e a₀
  let dims := cavityBaseGroupDimension k a₀
  let Ω := (Orthogonal N × LabeledTree depth) × (ℕ → ℝ)
  let eig := diagonalPerturbedEigenvalues (fun i => lam (E.symm i).1)
    (cavitySpectralGroup (fun i => (E.symm i).1)) v t
  let ν : Ω → Measure (Spin N × LabeledLeaf depth) :=
    restrictedRotationProbability S hS eig (cavitySpectralGroup (fun i => (E.symm i).1)) u
  let vectors := cavityRotationVectors (depth := depth) dims E
  let frames := cavityCanonicalGroupFrame k e a₀ hk
  have hy (ω : Ω) (W : (a : Fin m) → Orthogonal (dims a)) (x : Spin N × LabeledLeaf depth) :
      ‖cavitySelectedSiteProjection (fun j => (a₀ j,j)) (vectors ω)
        (cavityGroupHaarFrames frames W) x‖^2 ≤ (N : ℝ) := by
    change ‖cavitySelectedSiteProjection (fun j => (a₀ j,j))
      (cavityGroupSpinCoordinates dims E ω.1.1) (cavityGroupHaarFrames frames W) x.1‖^2 ≤ N
    exact cavity_canonical_group_projection_bound k e a₀ hk ω.1.1 W x.1
  exact restrictedHaarLogObservable_bound C hC ν (fun j => (a₀ j,j)) vectors frames (fun _ => B)
    t cap δ hcap (fun _ => le_rfl) hy p

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedRandomHaarLog
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The canonical logarithm with independent random compression
coefficients. The original base disorder stays in its own coordinates. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma measurable_restrictedRandomHaarLog {Z : Type*} [MeasurableSpace Z] {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty)
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (hk : ∀ a, d ≤ k a) (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (t cap δ : ℝ) (A : Z → CavityFactorBlocks d n) (hA : Measurable A) :
    Measurable (restrictedRandomHaarLog (depth := depth) S hS C hC k e a₀ hk lam v u t cap δ A) := by
  let E := cavityBaseGroupEquiv k e a₀
  let dims := cavityBaseGroupDimension k a₀
  let Ω := Z × ((Orthogonal N × LabeledTree depth) × (ℕ → ℝ))
  let eig := diagonalPerturbedEigenvalues (fun i => lam (E.symm i).1)
    (cavitySpectralGroup (fun i => (E.symm i).1)) v t
  let ν : Ω → Measure (Spin N × LabeledLeaf depth) := fun z =>
    restrictedRotationProbability S hS eig (cavitySpectralGroup (fun i => (E.symm i).1)) u z.2
  let vectors := fun z : Ω => cavityRotationVectors (depth := depth) dims E z.2
  have hmν : Measurable ν := (measurable_restrictedRotationProbability S hS _ _ _).comp measurable_snd
  have hmv x : Measurable (fun z a => vectors z a x) :=
    (measurable_cavityRotationVectors dims E x).comp measurable_snd
  exact measurable_restrictedHaarLogObservable C hC ν hmν (fun j => (a₀ j,j)) vectors hmv
    (cavityCanonicalGroupFrame k e a₀ hk) (fun z => A z.1) (hA.comp measurable_fst) t cap δ

lemma restrictedRandomHaarLog_bound {Z : Type*} {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty)
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (hk : ∀ a, d ≤ k a) (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (t cap δ : ℝ) (hcap : 0 ≤ cap) (A : Z → CavityFactorBlocks d n) {D : ℝ}
    (hA : ∀ z, cavityFactorSize (A z).1 (A z).2.1 (A z).2.2 ≤ D)
    (p : (Z × ((Orthogonal N × LabeledTree depth) × (ℕ → ℝ))) ×
      ((a : Fin m) → Orthogonal (cavityBaseGroupDimension k a₀ a))) :
    |restrictedRandomHaarLog S hS C hC k e a₀ hk lam v u t cap δ A p| ≤ (|t| *D+|δ|)*(1+N) := by
  have h := restrictedCanonicalHaarLog_bound S hS C hC k e a₀ hk lam v u t cap δ hcap (A p.1.1) (p.1.2,p.2)
  apply h.trans
  exact mul_le_mul_of_nonneg_right
    (add_le_add (mul_le_mul_of_nonneg_left (hA p.1.1) (abs_nonneg t)) (le_refl |δ|)) (by positivity)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedConstantHaarLog
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An independent compression coordinate disappears once its coefficient
has been replaced by the deterministic limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma restricted_constant_haar_log_average {Z : Type*} [MeasurableSpace Z]
    {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty) (P : Measure Z) [IsProbabilityMeasure P]
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (hk : ∀ a, d ≤ k a)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ]
    (θ : Measure (LabeledTree depth)) [IsProbabilityMeasure θ]
    (η : Measure ((a : Fin m) → Orthogonal (cavityBaseGroupDimension k a₀ a)))
    [IsProbabilityMeasure η] (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (t cap δ : ℝ) (hcap : 0 ≤ cap) (A : CavityFactorBlocks d n) :
    (∫ p, restrictedRandomHaarLog S hS C hC k e a₀ hk lam v u t cap δ (fun _ : Z => A) p
      ∂(P.prod ((μ.prod θ).prod gaussianCoordinates)).prod η) =
    ∫ p, restrictedCanonicalHaarLog S hS C hC k e a₀ hk lam v u t cap δ A p
      ∂((μ.prod θ).prod gaussianCoordinates).prod η := by
  let F := restrictedRandomHaarLog (depth := depth) S hS C hC k e a₀ hk lam v u t cap δ (fun _ : Z => A)
  have hF : Measurable F :=
    measurable_restrictedRandomHaarLog S hS C hC k e a₀ hk lam v u t cap δ _ measurable_const
  have hb p : |F p| ≤ (|t| * cavityFactorSize A.1 A.2.1 A.2.2+|δ|)*(1+N) :=
    restrictedRandomHaarLog_bound S hS C hC k e a₀ hk lam v u t cap δ hcap _ (fun _ => le_rfl) p
  rw [cavity_bounded_extra_product_integral P ((μ.prod θ).prod gaussianCoordinates) η F hF hb]
  change (∫ _ : Z, (∫ p, restrictedCanonicalHaarLog S hS C hC k e a₀ hk lam v u t cap δ A p
    ∂((μ.prod θ).prod gaussianCoordinates).prod η) ∂P) = _
  simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedPhysicalLogCoefficients
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logarithmic coefficient replacement specialized to the actual
base-system Gibbs probability and its physical spectral-group vectors. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

theorem restricted_physical_penalized_log_coefficients {m q d n : ℕ}
    (N depth : ℕ → ℕ)
    (S : (r : ℕ) → Finset (Spin (N r))) (hS : ∀ r, (S r).Nonempty)
    (C : Finset (Spin n)) (hC : C.Nonempty) (hN : ∀ r, 0<N r)
    (dims : ℕ → Fin m → ℕ) (hgroups : ∀ r a, 0<dims r a)
    (E : (r : ℕ) → ((a : Fin m) × Fin (dims r a)) ≃ Fin (N r))
    (μ : (r : ℕ) → Measure (Orthogonal (N r))) [∀ r, IsProbabilityMeasure (μ r)]
    (θ : (r : ℕ) → Measure (LabeledTree (depth r))) [∀ r, IsProbabilityMeasure (θ r)]
    (μG : (r : ℕ) → (a : Fin m) → Measure (Orthogonal (dims r a)))
    [∀ r a, IsProbabilityMeasure (μG r a)] [∀ r a, (μG r a).IsMulRightInvariant]
    (A₀ : (r : ℕ) → (a : Fin m) → Matrix (Fin (dims r a)) (Fin q) ℝ)
    (hA₀ : ∀ r a, (A₀ r a).transpose*A₀ r a=1)
    (eig : (r : ℕ) → Fin (N r) → ℝ) (u : ℕ → ℕ → ℝ)
    {c : ℝ} (hc : 0 < c) (hfrac : ∀ r a, c ≤ (dims r a : ℝ)/N r)
    (Z : ℕ → Type*) [∀ r, MeasurableSpace (Z r)]
    (P : (r : ℕ) → Measure (Z r)) [∀ r, IsProbabilityMeasure (P r)]
    (A : (r : ℕ) → Z r → CavityFactorBlocks d n) (hA : ∀ r, Measurable (A r))
    (A₁ : CavityFactorBlocks d n) {D : ℝ} (hD : 0≤D)
    (hAb : ∀ r z, cavityFactorSize (A r z).1 (A r z).2.1 (A r z).2.2 ≤ D)
    (hA₁ : cavityFactorSize A₁.1 A₁.2.1 A₁.2.2 ≤ D)
    (hprob : ∀ ε>0, Tendsto (fun r => (P r).real
      {z | ε < cavityFactorDeviation (A r z) A₁}) atTop (𝓝 0))
    (f : Fin d → Fin m × Fin q) (cap : ℝ) (hcap : 0 ≤ cap)
    (δ : ℕ → ℝ) (hδ : ∀ r, 0≤δ r) (hδlim : Tendsto δ atTop (𝓝 0)) :
    let ν := fun r => restrictedRotationProbability (depth := depth r) (S r) (hS r) (eig r)
      (cavitySpectralGroup (fun i => ((E r).symm i).1)) (u r)
    let vectors := fun r => cavityRotationVectors (depth := depth r) (dims r) (E r)
    let Q := fun r => ((P r).prod (((μ r).prod (θ r)).prod gaussianCoordinates)).prod
      (Measure.pi (μG r))
    Tendsto (fun r =>
      (∫ ω, restrictedHaarLogObservable C hC (fun z => ν r z.2) f (fun z => vectors r z.2)
        (A₀ r) (fun z => A r z.1) 1 cap (δ r) ω ∂Q r) -
      ∫ ω, restrictedHaarLogObservable C hC (fun z => ν r z.2) f (fun z => vectors r z.2)
        (A₀ r) (fun _ => A₁) 1 cap 0 ω ∂Q r) atTop (𝓝 0) := by
  intro ν vectors Q
  let Ω := fun r => Z r × ((Orthogonal (N r) × LabeledTree (depth r)) × (ℕ → ℝ))
  let X := fun r => Spin (N r) × LabeledLeaf (depth r)
  let P₀ := fun r => (P r).prod (((μ r).prod (θ r)).prod gaussianCoordinates)
  let ν₀ := fun r (ω : Ω r) => ν r ω.2
  let v₀ := fun r (ω : Ω r) => vectors r ω.2
  let A₂ := fun r (ω : Ω r) => A r ω.1
  have hmν r : Measurable (ν₀ r) :=
    (measurable_restrictedRotationProbability (S r) (hS r) _ _ _).comp measurable_snd
  have hmv r x : Measurable (fun ω a => v₀ r ω a x) :=
    (measurable_cavityRotationVectors (dims r) (E r) x).comp measurable_snd
  have hnorm r (ω : Ω r) x a :
      ‖(WithLp.toLp 2 (v₀ r ω a x) : EuclideanSpace ℝ (Fin (dims r a)))‖^2 ≤
        (1/c)*dims r a :=
    cavity_rotation_vectors_norm_bound (hN r) (dims r) (hgroups r) (E r) hc (hfrac r) ω.2 x a
  have hmA r : Measurable (A₂ r) := (hA r).comp measurable_fst
  have hp : ∀ ε>0, Tendsto (fun r => (P₀ r).real
      {ω | ε < cavityFactorDeviation (A₂ r ω) A₁}) atTop (𝓝 0) := by
    intro ε hε
    apply (hprob ε hε).congr
    intro r
    exact (cavity_factor_deviation_pullback (P₀ r) (P r) Prod.fst
      measurePreserving_fst (A r) (hA r) A₁ ε).symm
  have h := cavity_haar_penalized_coefficient_limit dims hgroups μG Ω X P₀ ν₀ hmν
    f v₀ hmv A₀ hA₀ (div_nonneg zero_le_one hc.le) hnorm A₂ hmA A₁ hD
    (fun r ω => hAb r ω.1) hA₁ hp (restrictedSpinPrior C hC) cap hcap δ hδ hδlim
  simpa only [restrictedHaarLogObservable, ν₀, v₀, A₂, P₀, Q, one_mul, zero_mul, sub_zero] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedCanonicalLogCoefficients
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Random coefficient replacement on the canonical physical cavity
space, with the independent compression coordinate integrated out. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

theorem restricted_canonical_log_coefficients {m d n : ℕ}
    (N depth : ℕ → ℕ)
    (S : (r : ℕ) → Finset (Spin (N r))) (hS : ∀ r, (S r).Nonempty)
    (C : Finset (Spin n)) (hC : C.Nonempty) (hN : ∀ r, 0<N r) (k : ℕ → Fin m → ℕ)
    (e : (r : ℕ) → (((a : Fin m) × Fin (k r a)) ⊕ Fin d) ≃ Fin (N r))
    (a₀ : Fin d → Fin m) (hk : ∀ r a, d ≤ k r a)
    (hgroups : ∀ r a, 0 < cavityBaseGroupDimension (k r) a₀ a)
    (μ : (r : ℕ) → Measure (Orthogonal (N r))) [∀ r, IsProbabilityMeasure (μ r)]
    (θ : (r : ℕ) → Measure (LabeledTree (depth r))) [∀ r, IsProbabilityMeasure (θ r)]
    (μG : (r : ℕ) → (a : Fin m) → Measure (Orthogonal (cavityBaseGroupDimension (k r) a₀ a)))
    [∀ r a, IsProbabilityMeasure (μG r a)] [∀ r a, (μG r a).IsMulRightInvariant]
    (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ) (u : ℕ → ℕ → ℝ)
    {c : ℝ} (hc : 0 < c)
    (hfrac : ∀ r a, c ≤ (cavityBaseGroupDimension (k r) a₀ a : ℝ)/N r)
    (Z : ℕ → Type*) [∀ r, MeasurableSpace (Z r)]
    (P : (r : ℕ) → Measure (Z r)) [∀ r, IsProbabilityMeasure (P r)]
    (A : (r : ℕ) → Z r → CavityFactorBlocks d n) (hA : ∀ r, Measurable (A r))
    (A₁ : CavityFactorBlocks d n) {D : ℝ} (hD : 0≤D)
    (hAb : ∀ r z, cavityFactorSize (A r z).1 (A r z).2.1 (A r z).2.2 ≤ D)
    (hA₁ : cavityFactorSize A₁.1 A₁.2.1 A₁.2.2 ≤ D)
    (hprob : ∀ ε>0, Tendsto (fun r => (P r).real
      {z | ε < cavityFactorDeviation (A r z) A₁}) atTop (𝓝 0))
    (cap : ℝ) (hcap : 0 ≤ cap) (δ : ℕ → ℝ) (hδ : ∀ r, 0≤δ r)
    (hδlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun r =>
      (∫ p, restrictedRandomHaarLog (S r) (hS r) C hC (k r) (e r) a₀ (hk r) lam (v r) (u r) 1 cap (δ r) (A r) p
        ∂((P r).prod (((μ r).prod (θ r)).prod gaussianCoordinates)).prod (Measure.pi (μG r))) -
      ∫ p, restrictedCanonicalHaarLog (S r) (hS r) C hC (k r) (e r) a₀ (hk r) lam (v r) (u r) 1 cap 0 A₁ p
        ∂(((μ r).prod (θ r)).prod gaussianCoordinates).prod (Measure.pi (μG r))) atTop (𝓝 0) := by
  let dims := fun r => cavityBaseGroupDimension (k r) a₀
  let E := fun r => cavityBaseGroupEquiv (k r) (e r) a₀
  let frames := fun r => cavityCanonicalGroupFrame (k r) (e r) a₀ (hk r)
  let eig := fun r => diagonalPerturbedEigenvalues (fun i => lam ((E r).symm i).1)
    (cavitySpectralGroup (fun i => ((E r).symm i).1)) (v r) 1
  have h := restricted_physical_penalized_log_coefficients N depth S hS C hC hN dims hgroups E μ θ μG
    frames (fun r a => cavityCanonicalGroupFrame_gram (k r) (e r) a₀ (hk r) a)
    eig u hc hfrac Z P A hA A₁ hD hAb hA₁ hprob (fun j => (a₀ j,j)) cap hcap δ hδ hδlim
  change Tendsto (fun r =>
    (∫ p, restrictedRandomHaarLog (S r) (hS r) C hC (k r) (e r) a₀ (hk r) lam (v r) (u r) 1 cap (δ r) (A r) p
      ∂((P r).prod (((μ r).prod (θ r)).prod gaussianCoordinates)).prod (Measure.pi (μG r))) -
    ∫ p, restrictedRandomHaarLog (S r) (hS r) C hC (k r) (e r) a₀ (hk r) lam (v r) (u r) 1 cap 0 (fun _ => A₁) p
      ∂((P r).prod (((μ r).prod (θ r)).prod gaussianCoordinates)).prod (Measure.pi (μG r)))
      atTop (𝓝 0) at h
  have he r := restricted_constant_haar_log_average (S r) (hS r) C hC (P r) (k r) (e r) a₀ (hk r)
    (μ r) (θ r) (Measure.pi (μG r)) lam (v r) (u r) 1 cap 0 hcap A₁
  exact h.congr (fun r => by rw [he r])

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedCompressionLogLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual random compression and its explicit geometric error give
the canonical logarithm with fixed coefficients in the large-system limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

theorem restricted_compression_log_limit_oai {m d n : ℕ}
    (N depth : ℕ → ℕ)
    (S : (r : ℕ) → Finset (Spin (N r))) (hS : ∀ r, (S r).Nonempty)
    (C : Finset (Spin n)) (hC : C.Nonempty) (hN : ∀ r, 0<N r) (hNlim : Tendsto N atTop atTop)
    (g : (r : ℕ) → Fin (N r+n) → Fin m) (k : ℕ → Fin m → ℕ)
    (e : (r : ℕ) → (((a : Fin m) × Fin (k r a)) ⊕ Fin d) ≃ Fin (N r))
    (es : Fin (m*n) ≃ Fin (d+n)) (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ)
    (a₀ : Fin d → Fin m) (hk : ∀ r a, d ≤ k r a)
    (hgroups : ∀ r a, 0 < cavityBaseGroupDimension (k r) a₀ a)
    (μ : (r : ℕ) → Measure (Orthogonal (N r+n)))
    [∀ r, IsProbabilityMeasure (μ r)]
    (ν : (r : ℕ) → Measure (Orthogonal (N r))) [∀ r, IsProbabilityMeasure (ν r)]
    (θ : (r : ℕ) → Measure (LabeledTree (depth r))) [∀ r, IsProbabilityMeasure (θ r)]
    (μG : (r : ℕ) → (a : Fin m) → Measure (Orthogonal (cavityBaseGroupDimension (k r) a₀ a)))
    [∀ r a, IsProbabilityMeasure (μG r a)] [∀ r a, (μG r a).IsMulRightInvariant]
    (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ) (u : ℕ → ℕ → ℝ)
    {c : ℝ} (hc : 0 < c)
    (hfrac : ∀ r a, c ≤ (cavityBaseGroupDimension (k r) a₀ a : ℝ)/N r)
    (A₁ : CavityFactorBlocks d n)
    (hprob : ∀ ε>0, Tendsto (fun r => (μ r).real {U | ε < cavityFactorDeviation
      (cavityCompressionFactorBlocks es lam (fun j => lam (a₀ j)) B₀
        (cavityCompressionGrams (g r) U)) A₁}) atTop (𝓝 0))
    (cap : ℝ) (hcap : 0 ≤ cap) :
    let A := fun r U => cavityCompressionFactorBlocks es lam (fun j => lam (a₀ j)) B₀
      (cavityCompressionGrams (g r) U)
    let δ := fun r => cavityDeterministicRate n m (2*(2*n+1)) (N r)+
      2*cavityCovarianceRate n (2*n+1) (N r)
    Tendsto (fun r =>
      (∫ p, restrictedRandomHaarLog (S r) (hS r) C hC (k r) (e r) a₀ (hk r) lam (v r) (u r) 1 cap (δ r) (A r) p
        ∂((μ r).prod (((ν r).prod (θ r)).prod gaussianCoordinates)).prod (Measure.pi (μG r))) -
      ∫ p, restrictedCanonicalHaarLog (S r) (hS r) C hC (k r) (e r) a₀ (hk r) lam (v r) (u r) 1 cap 0 A₁ p
        ∂(((ν r).prod (θ r)).prod gaussianCoordinates).prod (Measure.pi (μG r))) atTop (𝓝 0) := by
  intro A δ
  let D₀ := ((d : ℝ)*d+d*n+n*n)*cavityMatrixMass (cavityRepeatedSpectrum (n := n) lam)+
    cavityMatrixMass (Matrix.diagonal (fun j => lam (a₀ j)))
  let D := max D₀ (cavityFactorSize A₁.1 A₁.2.1 A₁.2.2)
  have hD : 0≤D := (cavityFactorSize_nonneg A₁.1 A₁.2.1 A₁.2.2).trans (le_max_right _ _)
  have hA r : Measurable (A r) :=
    (measurable_cavityCompressionFactorBlocks es lam (fun j => lam (a₀ j)) B₀).comp
      (measurable_cavityCompressionGrams (g r))
  have hAb r U : cavityFactorSize (A r U).1 (A r U).2.1 (A r U).2.2 ≤ D :=
    (cavity_compression_factor_size_bound (g r) es lam (fun j => lam (a₀ j)) B₀ U).trans
      (le_max_left _ _)
  have hδ r : 0≤δ r := by
    dsimp only [δ]
    have hd : 0 ≤ cavityDeterministicRate n m (2*(2*n+1)) (N r) := by
      unfold cavityDeterministicRate perturbationScale
      positivity
    exact add_nonneg hd (mul_nonneg (by norm_num)
      (cavityCovarianceRate_nonneg n (by positivity) (N r)))
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    have ht := ((cavityDeterministicRate_tendsto n m (2*(2*n+1))).comp hNlim).add
      (((cavityCovarianceRate_tendsto n (2*n+1)).comp hNlim).const_mul 2)
    simpa only [δ, Function.comp_def, mul_zero, add_zero] using ht
  exact restricted_canonical_log_coefficients N depth S hS C hC hN k e a₀ hk hgroups ν θ μG lam v u
    hc hfrac (fun r => Orthogonal (N r+n)) μ A hA A₁ hD hAb (le_max_right _ _)
    hprob cap hcap δ hδ hδlim

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.restricted_compression_log_limit_oai := @OAI.InvariantIsing.restricted_compression_log_limit_oai
