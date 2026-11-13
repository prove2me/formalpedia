-- Prove2me | solution 1 for OAI.InvariantIsing.restricted_haar_cutoff_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:05:58.573129+00:00
-- url     : https://prove2.me/submissions/09f0d251-cac6-4b99-9501-221cbbb19667

import Mathlib
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Topology.Order.Compact
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_restricted_physical_cutoff_comparison
import Theorems.Thm_OAI_InvariantIsing_restricted_projector_coefficient_error

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
-- module Solutions.OAIQ258_II.IsingPerceptron_CountableMonomialGG
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable Monomial G G. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma reference_replica_partition {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SigmaFinite ν] (H : X → ℝ) (r : ℕ) :
    (∫ σ : Fin r → X, Real.exp (∑ i, H (σ i)) ∂Measure.pi (fun _ => ν)) =
      (referencePartition ν H)^r := by
  simp_rw [Real.exp_sum]
  simpa only [Fintype.card_fin,referencePartition] using
    (integral_fintype_prod_eq_pow (ι := Fin r) (μ := ν) (fun x => Real.exp (H x)))

lemma measurable_referenceReplicaMean {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] {r : ℕ} {H : Ω × X → ℝ}
    {D : Ω × (Fin r → X) → ℝ} (hmH : Measurable H) (hmD : Measurable D) :
    Measurable (fun ω => referenceReplicaMean ν (fun x => H (ω,x)) (fun σ => D (ω,σ))) := by
  have hrep : Measurable (fun z : Ω × (Fin r → X) => ∑ i, H (z.1,z.2 i)) := by
    apply Finset.measurable_sum
    intro i _
    exact hmH.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  exact (hrep.exp.mul hmD).stronglyMeasurable.integral_prod_right'.measurable.div
    (hmH.exp.stronglyMeasurable.integral_prod_right'.measurable.pow_const r)

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ConvexDerivativeFluctuation
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convex Derivative Fluctuation. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma replica_tilted_pi {X : Type*} [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν) (r : ℕ) :
    (Measure.pi (fun _ : Fin r => ν)).tilted (fun σ => ∑ i, H (σ i)) =
      Measure.pi (fun _ : Fin r => ν.tilted H) := by
  have : IsProbabilityMeasure (ν.tilted H) := isProbabilityMeasure_tilted he
  have hz : 0 < referencePartition ν H := _root_.MeasureTheory.integral_exp_pos he
  apply Measure.ext_of_singleton
  intro σ
  rw [tilted_singleton,Measure.pi_singleton,Measure.pi_singleton]
  simp_rw [tilted_singleton]
  rw [show referencePartition (Measure.pi (fun _ : Fin r => ν)) (fun σ => ∑ i, H (σ i)) =
    (referencePartition ν H)^r from reference_replica_partition ν H r]
  rw [Real.exp_sum,ENNReal.ofReal_div_of_pos (pow_pos hz r),
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),ENNReal.ofReal_pow hz.le]
  simp_rw [ENNReal.ofReal_div_of_pos hz]
  rw [Finset.prod_mul_distrib,ENNReal.prod_div_distrib_of_ne_top (fun _ _ => ENNReal.ofReal_ne_top)]
  simp

lemma referenceReplicaMean_eq_tilted {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν) {r : ℕ} (D : (Fin r → X) → ℝ) :
    referenceReplicaMean ν H D = ∫ σ, D σ ∂Measure.pi (fun _ : Fin r => ν.tilted H) := by
  rw [← replica_tilted_pi ν H he r,integral_tilted]
  simp only [smul_eq_mul,div_mul_eq_mul_div,integral_div]
  rw [reference_replica_partition]; rfl

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianRows
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian rows used to generate the finite fresh frames. Their empirical
Gram matrices converge almost surely to the identity at fixed frame width. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

namespace InvariantIsing

lemma cavityGaussianRow_eval_law {q : ℕ} (i : Fin q) :
    HasLaw (fun x : Fin q → ℝ => x i) (gaussianReal 0 1) (cavityGaussianRow q) :=
  ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval (fun _ : Fin q => gaussianReal 0 1) i).map_eq⟩

lemma cavityGaussianRows_eval_law (q n : ℕ) :
    HasLaw (fun x : ℕ → Fin q → ℝ => x n) (cavityGaussianRow q) (cavityGaussianRows q) := by
  refine ⟨(measurable_pi_apply n).aemeasurable, ?_⟩
  exact Measure.infinitePi_map_eval (fun _ : ℕ => cavityGaussianRow q) n

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

lemma cavityEmpiricalGram_posSemidef {q : ℕ} (x : ℕ → Fin q → ℝ) (n : ℕ) :
    (cavityEmpiricalGram x n).PosSemidef := by
  have he : cavityEmpiricalGram x n =
      (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, Matrix.vecMulVec (x k) (x k) := by
    ext i j
    simp only [cavityEmpiricalGram, Matrix.smul_apply, Matrix.sum_apply,
      Matrix.vecMulVec_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [he]
  apply (Matrix.posSemidef_sum (Finset.range n) (fun k _ => ?_)).smul
    (inv_nonneg.mpr (Nat.cast_nonneg n))
  simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (x k)

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

lemma cavityGaussianMatrix_gram {q : ℕ} (x : ℕ → Fin q → ℝ) (n : ℕ) :
    (cavityGaussianMatrix x n).transpose * cavityGaussianMatrix x n =
      cavityEmpiricalGram x n := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, cavityGaussianMatrix]
  simp_rw [div_mul_div_comm, Real.mul_self_sqrt (Nat.cast_nonneg n)]
  rw [← Finset.sum_div]
  change (∑ k : Fin n, x k i * x k j) / (n : ℝ) =
    (∑ k ∈ Finset.range n, x k i * x k j) / (n : ℝ)
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun k => x k i * x k j) n

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFrameRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonal equivariance of the Gaussian frame normalization. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

lemma cavityGram_left_orthogonal {n q : ℕ} (A : Matrix (Fin n) (Fin q) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U.transpose * U = 1) :
    (U * A).transpose * (U * A) = A.transpose * A := by
  rw [Matrix.transpose_mul]
  calc
    A.transpose * U.transpose * (U * A) = A.transpose * (U.transpose * U) * A := by
      simp only [Matrix.mul_assoc]
    _ = A.transpose * A := by rw [hU, Matrix.mul_one]

lemma cavityNormalizeFrame_left_orthogonal {n q : ℕ} (A : Matrix (Fin n) (Fin q) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U.transpose * U = 1) :
    cavityNormalizeFrame (U * A) = U * cavityNormalizeFrame A := by
  simp only [cavityNormalizeFrame, cavityGram_left_orthogonal A U hU, Matrix.mul_assoc]


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

lemma cavityRawComplement_orthogonal {r n d : ℕ} (E : Matrix (Fin r) (Fin n) ℝ)
    (B₀ : Matrix (Fin r) (Fin d) ℝ) (hE : E.transpose * E = 1) :
    E.transpose * cavityRawComplement E B₀ = 0 := by
  simp only [cavityRawComplement, Matrix.sub_mul, Matrix.one_mul,
    Matrix.mul_sub, ← Matrix.mul_assoc, hE, Matrix.one_mul, sub_self]

lemma cavityComplement_orthogonal {r n d : ℕ} (E : Matrix (Fin r) (Fin n) ℝ)
    (B₀ : Matrix (Fin r) (Fin d) ℝ) (hE : E.transpose * E = 1) :
    E.transpose * cavityComplement E B₀ = 0 := by
  rw [cavityComplement, cavityNormalizeFrame, ← Matrix.mul_assoc,
    cavityRawComplement_orthogonal E B₀ hE, Matrix.zero_mul]

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
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability
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

theorem cavityFrame_transitive {n q : ℕ} (A B : Matrix (Fin n) (Fin q) ℝ)
    (hA : A.transpose * A = 1) (hB : B.transpose * B = 1) :
    ∃ U : Orthogonal n, (U : Matrix (Fin n) (Fin n) ℝ) * A = B := by
  obtain ⟨U, hU⟩ := cavity_orthonormal_transitive _ _
    (cavity_orthonormal_of_gram A hA) (cavity_orthonormal_of_gram B hB)
  refine ⟨cavityRotationMatrix U, ?_⟩
  ext i j
  have h := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x i) (hU j)
  rw [← cavityRotationMatrix_apply U] at h
  exact h

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

lemma cavitySelectedComplement_orthogonal {d n : ℕ}
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ)
    (E : Matrix (Fin (d + n)) (Fin n) ℝ) (hE : E.transpose * E = 1) :
    E.transpose * cavitySelectedComplement B₀ E = 0 :=
  cavityComplement_orthogonal E _ hE

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteGaussian
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite-dimensional laws of the independent Gaussian array used
in the fresh-frame construction. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InvariantIsing

lemma cavityGaussianRows_coordinate_law {q : ℕ} (k : ℕ) (i : Fin q) :
    HasLaw (fun x : ℕ → Fin q → ℝ => x k i) (gaussianReal 0 1)
      (cavityGaussianRows q) :=
  (cavityGaussianRow_eval_law i).fun_comp (cavityGaussianRows_eval_law q k)

lemma cavityGaussianRows_coordinates_independent (q : ℕ) :
    iIndepFun (fun p : ℕ × Fin q => fun x : ℕ → Fin q → ℝ => x p.1 p.2)
      (cavityGaussianRows q) := by
  simpa only [cavityGaussianRows, cavityGaussianRow, Measure.infinitePi_eq_pi] using
    iIndepFun_uncurry_infinitePi' (fun (_ : ℕ) (_ : Fin q) => gaussianReal 0 1)
      (X := fun _ _ x => x) (fun _ _ => measurable_id)

lemma cavityGaussianRows_finite_array_law (n q : ℕ) :
    HasLaw (fun x : ℕ → Fin q → ℝ => fun p : Fin n × Fin q => x p.1 p.2)
      (Measure.pi (fun _ : Fin n × Fin q => gaussianReal 0 1))
      (cavityGaussianRows q) := by
  have hinj : Function.Injective (fun p : Fin n × Fin q => ((p.1 : ℕ), p.2)) := by
    intro p r h
    exact Prod.ext (Fin.ext (congrArg (fun z : ℕ × Fin q => z.1) h))
      (congrArg (fun z : ℕ × Fin q => z.2) h)
  have hind : iIndepFun
      (fun p : Fin n × Fin q => fun x : ℕ → Fin q → ℝ => x p.1 p.2)
      (cavityGaussianRows q) := (cavityGaussianRows_coordinates_independent q).precomp hinj
  refine ⟨(measurable_pi_iff.mpr (fun p =>
    (measurable_pi_apply p.2).comp (measurable_pi_apply (p.1 : ℕ)))).aemeasurable, ?_⟩
  have hm := hind.map_fun_eq_pi_map (fun (p : Fin n × Fin q) =>
    (cavityGaussianRows_coordinate_law (p.1 : ℕ) p.2).aemeasurable)
  simpa only [(cavityGaussianRows_coordinate_law _ _).map_eq] using hm

theorem cavityGaussianRows_finite_standard_law (n q : ℕ) :
    HasLaw (fun x : ℕ → Fin q → ℝ =>
      (WithLp.toLp 2 (fun p : Fin n × Fin q => x p.1 p.2) :
        EuclideanSpace ℝ (Fin n × Fin q)))
      (stdGaussian (EuclideanSpace ℝ (Fin n × Fin q))) (cavityGaussianRows q) := by
  have ht : HasLaw (WithLp.toLp 2 : (Fin n × Fin q → ℝ) →
      EuclideanSpace ℝ (Fin n × Fin q))
      (stdGaussian (EuclideanSpace ℝ (Fin n × Fin q)))
      (Measure.pi (fun _ : Fin n × Fin q => gaussianReal 0 1)) :=
    ⟨(by fun_prop), map_pi_eq_stdGaussian⟩
  exact ht.fun_comp (cavityGaussianRows_finite_array_law n q)

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCouplingAlgebra
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The orthogonal spectral directions in the finite cavity coupling.
Each spectral image of the cavity columns is normalized separately.
The resulting frame carries the small square-root stack isometrically
back to the original cavity columns. -/

noncomputable section
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavityNormalizeFrame_mul_sqrt {r n : ℕ}
    (X : Matrix (Fin r) (Fin n) ℝ) (hX : (X.transpose * X).PosDef) :
    cavityNormalizeFrame X * CFC.sqrt (X.transpose * X) = X := by
  rw [cavityNormalizeFrame, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (cavity_sqrt_det_isUnit _ hX), Matrix.mul_one]

lemma cavityNormalizeFrame_crossGram {r n : ℕ}
    (X Y : Matrix (Fin r) (Fin n) ℝ) (hXY : X.transpose * Y = 0) :
    (cavityNormalizeFrame X).transpose * cavityNormalizeFrame Y = 0 := by
  simp only [cavityNormalizeFrame, Matrix.transpose_mul]
  calc
    _ = ((CFC.sqrt (X.transpose * X))⁻¹).transpose *
        (X.transpose * Y) * (CFC.sqrt (Y.transpose * Y))⁻¹ := by
      simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hXY, Matrix.mul_zero, Matrix.zero_mul]

theorem cavityEigenspaceFrame_gram {r m n : ℕ}
    (X : Fin m → Matrix (Fin r) (Fin n) ℝ)
    (hX : ∀ a, ((X a).transpose * X a).PosDef)
    (hXY : ∀ a b, a ≠ b → (X a).transpose * X b = 0) :
    (cavityEigenspaceFrame X).transpose * cavityEigenspaceFrame X = 1 := by
  classical
  ext i j
  let a := (finProdFinEquiv.symm i).1
  let b := (finProdFinEquiv.symm j).1
  let s := (finProdFinEquiv.symm i).2
  let t := (finProdFinEquiv.symm j).2
  change ((cavityNormalizeFrame (X a)).transpose * cavityNormalizeFrame (X b)) s t =
    if i = j then 1 else 0
  by_cases hab : a = b
  · rw [← hab, cavityNormalizeFrame_gram _ (hX a), Matrix.one_apply]
    have hij : i = j ↔ s = t := by
      constructor
      · intro h; subst j; rfl
      · intro h
        apply (finProdFinEquiv.symm : Fin (m * n) ≃ Fin m × Fin n).injective
        exact Prod.ext hab h
    simp only [hij]
  · rw [cavityNormalizeFrame_crossGram _ _ (hXY a b hab), Matrix.zero_apply]
    have hij : i ≠ j := by
      intro h; subst j; exact hab rfl
    simp only [hij, ite_false, if_false]

theorem cavityEigenspaceFrame_stack {r m n : ℕ}
    (X : Fin m → Matrix (Fin r) (Fin n) ℝ)
    (hX : ∀ a, ((X a).transpose * X a).PosDef) :
    cavityEigenspaceFrame X * cavitySpectralStack (fun a => (X a).transpose * X a) =
      ∑ a, X a := by
  ext i j
  change (∑ k : Fin (m * n), cavityNormalizeFrame (X (finProdFinEquiv.symm k).1)
    i (finProdFinEquiv.symm k).2 *
    CFC.sqrt ((X (finProdFinEquiv.symm k).1).transpose * X (finProdFinEquiv.symm k).1)
      (finProdFinEquiv.symm k).2 j) = _
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n))]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg (fun A : Matrix (Fin r) (Fin n) ℝ => A i j)
    (cavityNormalizeFrame_mul_sqrt (X a) (hX a))

lemma cavityNormalizeFrame_eigen {r n : ℕ}
    (D : Matrix (Fin r) (Fin r) ℝ) (X : Matrix (Fin r) (Fin n) ℝ)
    (lam : ℝ) (hDX : D * X = lam • X) :
    D * cavityNormalizeFrame X = lam • cavityNormalizeFrame X := by
  simp only [cavityNormalizeFrame, ← Matrix.mul_assoc, hDX, Matrix.smul_mul]

theorem cavityEigenspaceFrame_eigen {r m n : ℕ}
    (D : Matrix (Fin r) (Fin r) ℝ)
    (X : Fin m → Matrix (Fin r) (Fin n) ℝ) (lam : Fin m → ℝ)
    (hDX : ∀ a, D * X a = lam a • X a) :
    D * cavityEigenspaceFrame X =
      cavityEigenspaceFrame X * cavityRepeatedSpectrum (n := n) lam := by
  ext i j
  have h := congrArg (fun A : Matrix (Fin r) (Fin n) ℝ =>
    A i (finProdFinEquiv.symm j).2)
      (cavityNormalizeFrame_eigen D (X (finProdFinEquiv.symm j).1)
        (lam (finProdFinEquiv.symm j).1) (hDX _))
  change (∑ k, D i k * cavityNormalizeFrame (X (finProdFinEquiv.symm j).1)
    k (finProdFinEquiv.symm j).2) = _ at h
  rw [cavityRepeatedSpectrum, Matrix.mul_diagonal]
  simpa only [Matrix.mul_apply, cavityEigenspaceFrame, Matrix.smul_apply, smul_eq_mul,
    mul_comm] using h

lemma measurable_cavityEigenspaceFrame (r m n : ℕ) :
    Measurable (cavityEigenspaceFrame :
      (Fin m → Matrix (Fin r) (Fin n) ℝ) → Matrix (Fin r) (Fin (m * n)) ℝ) := by
  apply Measurable.of_eval_matrix
  intro i j
  exact ((measurable_cavityNormalizeFrame r n).comp
    (measurable_pi_apply (finProdFinEquiv.symm j).1)).eval_matrix

lemma cavityEigenspaceFrame_left_orthogonal {r m n : ℕ}
    (X : Fin m → Matrix (Fin r) (Fin n) ℝ)
    (U : Matrix (Fin r) (Fin r) ℝ) (hU : U.transpose * U = 1) :
    cavityEigenspaceFrame (fun a => U * X a) = U * cavityEigenspaceFrame X := by
  ext i j
  change cavityNormalizeFrame (U * X (finProdFinEquiv.symm j).1)
    i (finProdFinEquiv.symm j).2 = _
  rw [cavityNormalizeFrame_left_orthogonal _ U hU]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityConditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conditioning on the nondegenerate Gram event does not change the
limit of bounded observables. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_conditioning_map {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (f : Ω → Ω') (hf : Measurable f)
    (s : Set Ω') (hs : MeasurableSet s) :
    (cond μ (f ⁻¹' s)).map f = cond (μ.map f) s := by
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond,
    Measure.map_smul, Measure.map_apply hf hs,
    Measure.restrict_map hf hs]

lemma cavity_conditioning_invariant {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → Ω) (hT : Measurable T) (hμ : μ.map T = μ)
    (s : Set Ω) (hs : MeasurableSet s) (hinv : T ⁻¹' s = s) :
    (cond μ s).map T = cond μ s := by
  have hr : (μ.restrict s).map T = μ.restrict s := by
    calc
      (μ.restrict s).map T = (μ.restrict (T ⁻¹' s)).map T := by rw [hinv]
      _ = (μ.map T).restrict s := (Measure.restrict_map hT hs).symm
      _ = μ.restrict s := by rw [hμ]
  rw [ProbabilityTheory.cond, Measure.map_smul, hr]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianRotation
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonal invariance of the finite Gaussian array, expressed as a
simultaneous rotation of all its columns. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InvariantIsing

lemma cavityColumnRotation_apply {n q : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n × Fin q)) (k : Fin n) (j : Fin q) :
    cavityColumnRotation q U x (k, j) =
      U (WithLp.toLp 2 (fun i : Fin n => x (i, j))) k := rfl

theorem cavityColumnRotation_gaussian {n q : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (stdGaussian (EuclideanSpace ℝ (Fin n × Fin q))).map (cavityColumnRotation q U) =
      stdGaussian (EuclideanSpace ℝ (Fin n × Fin q)) :=
  stdGaussian_map (cavityColumnRotation q U)

lemma cavityArrayMatrix_rotation {n q : ℕ} (U : Orthogonal n)
    (z : EuclideanSpace ℝ (Fin n × Fin q)) :
    cavityArrayMatrix n q (cavityColumnRotation q (matrixRotation U) z) =
      (U : Matrix (Fin n) (Fin n) ℝ) * cavityArrayMatrix n q z := by
  ext k j
  simp only [cavityArrayMatrix, cavityColumnRotation_apply, matrixRotation_apply,
    Matrix.mul_apply, Finset.sum_div, mul_div_assoc]

lemma cavityArrayFrame_rotation {n q : ℕ} (U : Orthogonal n)
    (z : EuclideanSpace ℝ (Fin n × Fin q)) :
    cavityNormalizeFrame (cavityArrayMatrix n q (cavityColumnRotation q (matrixRotation U) z)) =
      (U : Matrix (Fin n) (Fin n) ℝ) * cavityNormalizeFrame (cavityArrayMatrix n q z) := by
  rw [cavityArrayMatrix_rotation]
  exact cavityNormalizeFrame_left_orthogonal _ _
    ((Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp U.property)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityConditionedFrame
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite conditioned Gaussian construction is an orthonormal frame
and has an exactly orthogonally invariant law. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace InvariantIsing

lemma measurable_cavityArrayMatrix (n q : ℕ) :
    Measurable (cavityArrayMatrix n q) := by
  unfold cavityArrayMatrix
  fun_prop

lemma measurableSet_cavityArrayGood (n q : ℕ) : MeasurableSet (cavityArrayGood n q) := by
  have hc : Continuous (fun z : EuclideanSpace ℝ (Fin n × Fin q) =>
      (cavityArrayMatrix n q z).transpose * cavityArrayMatrix n q z) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, cavityArrayMatrix]
    fun_prop
  exact measurableSet_lt measurable_const hc.matrix_det.measurable

lemma cavityArrayGood_rotation {n q : ℕ} (U : Orthogonal n) :
    (cavityColumnRotation q (matrixRotation U)) ⁻¹' cavityArrayGood n q =
      cavityArrayGood n q := by
  ext z
  simp only [Set.mem_preimage, cavityArrayGood, Set.mem_ofPred_eq, cavityArrayMatrix_rotation,
    cavityGram_left_orthogonal _ _
      ((Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp U.property)]

lemma cavityArrayGood_probability (n q : ℕ) :
    stdGaussian (EuclideanSpace ℝ (Fin n × Fin q)) (cavityArrayGood n q) =
      cavityGaussianRows q (cavityGoodGram q n) := by
  rw [← (cavityGaussianRows_finite_standard_law n q).map_eq,
    Measure.map_apply_of_aemeasurable (cavityGaussianRows_finite_standard_law n q).aemeasurable
      (measurableSet_cavityArrayGood n q)]
  congr 1
  ext x
  change 0 < ((cavityGaussianMatrix x n).transpose * cavityGaussianMatrix x n).det ↔ _
  rw [cavityGaussianMatrix_gram]
  rfl

lemma cavityConditionedFrameLaw_of_rows (n q : ℕ) :
    (cond (cavityGaussianRows q) (cavityGoodGram q n)).map
      (fun x => cavityNormalizeFrame (cavityGaussianMatrix x n)) =
        cavityConditionedFrameLaw n q := by
  let f := fun x : ℕ → Fin q → ℝ => (WithLp.toLp 2
    (fun p : Fin n × Fin q => x p.1 p.2) : EuclideanSpace ℝ (Fin n × Fin q))
  have hf : Measurable f := (PiLp.continuous_toLp 2 _).measurable.comp
    (measurable_pi_iff.mpr (fun p =>
      (measurable_pi_apply p.2).comp (measurable_pi_apply (p.1 : ℕ))))
  have hpre : f ⁻¹' cavityArrayGood n q = cavityGoodGram q n := by
    ext x
    change 0 < ((cavityGaussianMatrix x n).transpose * cavityGaussianMatrix x n).det ↔ _
    rw [cavityGaussianMatrix_gram]
    rfl
  have hmap := cavity_conditioning_map (cavityGaussianRows q) f hf
    (cavityArrayGood n q) (measurableSet_cavityArrayGood n q)
  rw [hpre, (cavityGaussianRows_finite_standard_law n q).map_eq] at hmap
  rw [cavityConditionedFrameLaw, ← hmap]
  rw [Measure.map_map (show Measurable (fun z : EuclideanSpace ℝ (Fin n × Fin q) =>
    cavityNormalizeFrame (cavityArrayMatrix n q z)) from
      (measurable_cavityNormalizeFrame n q).comp (measurable_cavityArrayMatrix n q)) hf]
  rfl

lemma cavityConditionedFrameLaw_probability {n q : ℕ}
    (hp : stdGaussian (EuclideanSpace ℝ (Fin n × Fin q)) (cavityArrayGood n q) ≠ 0) :
    IsProbabilityMeasure (cavityConditionedFrameLaw n q) := by
  let := cond_isProbabilityMeasure hp
  unfold cavityConditionedFrameLaw
  first | exact Measure.isProbabilityMeasure_map ((measurable_cavityNormalizeFrame n q).comp (measurable_cavityArrayMatrix n q)).aemeasurable | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem cavityConditionedFrameLaw_rotation {n q : ℕ} (U : Orthogonal n) :
    (cavityConditionedFrameLaw n q).map (fun A => (U : Matrix (Fin n) (Fin n) ℝ) * A) =
      cavityConditionedFrameLaw n q := by
  let f := fun z : EuclideanSpace ℝ (Fin n × Fin q) =>
    cavityNormalizeFrame (cavityArrayMatrix n q z)
  let act := fun A : Matrix (Fin n) (Fin q) ℝ => (U : Matrix (Fin n) (Fin n) ℝ) * A
  let R := cavityColumnRotation q (matrixRotation U)
  have hf : Measurable f := (measurable_cavityNormalizeFrame n q).comp
    (measurable_cavityArrayMatrix n q)
  have ha : Measurable act :=
    ((continuous_cavityFrameAction n q).comp (continuous_const.prodMk continuous_id)).measurable
  have hR : Measurable R := R.continuous.measurable
  have he : act ∘ f = f ∘ R := funext (fun z => (cavityArrayFrame_rotation U z).symm)
  have hinv := cavity_conditioning_invariant (stdGaussian _) R hR
    (cavityColumnRotation_gaussian (matrixRotation U)) (cavityArrayGood n q)
    (measurableSet_cavityArrayGood n q) (cavityArrayGood_rotation U)
  change ((cond (stdGaussian _) (cavityArrayGood n q)).map f).map act =
    (cond (stdGaussian _) (cavityArrayGood n q)).map f
  rw [Measure.map_map ha hf, he, ← Measure.map_map hf hR, hinv]

theorem cavityConditionedFrameLaw_orthonormal (n q : ℕ) :
    ∀ᵐ A ∂cavityConditionedFrameLaw n q, A.transpose * A = 1 := by
  have hf : Measurable (fun z => cavityNormalizeFrame (cavityArrayMatrix n q z)) :=
    (measurable_cavityNormalizeFrame n q).comp (measurable_cavityArrayMatrix n q)
  have hs : MeasurableSet {A : Matrix (Fin n) (Fin q) ℝ | A.transpose * A = 1} :=
    (isClosed_eq (continuous_id.matrix_transpose.matrix_mul continuous_id)
      continuous_const).measurableSet
  rw [cavityConditionedFrameLaw, ae_map_iff hf.aemeasurable hs]
  apply ae_cond_of_forall_mem (measurableSet_cavityArrayGood n q)
  intro z hz
  apply cavityNormalizeFrame_gram
  apply cavity_posDef_of_posSemidef_det_ne_zero
  · simpa using Matrix.posSemidef_conjTranspose_mul_self (cavityArrayMatrix n q z)
  · exact ne_of_gt hz

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFrameHaar
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.planeRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniqueness of the invariant frame law, proved by averaging bounded
continuous tests over the compact orthogonal group. -/

noncomputable section
open MeasureTheory
open scoped Matrix BoundedContinuousFunction

namespace InvariantIsing

theorem cavityFrame_eq_haar_orbit {n q : ℕ}
    (μ : Measure (Orthogonal n)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (ν : Measure (Matrix (Fin n) (Fin q) ℝ)) [IsProbabilityMeasure ν]
    (hinv : ∀ U : Orthogonal n,
      ν.map (fun A => (U : Matrix (Fin n) (Fin n) ℝ) * A) = ν)
    (hframe : ∀ᵐ A ∂ν, A.transpose * A = 1)
    (A₀ : Matrix (Fin n) (Fin q) ℝ) (hA₀ : A₀.transpose * A₀ = 1) :
    ν = μ.map (fun U : Orthogonal n => (U : Matrix (Fin n) (Fin n) ℝ) * A₀) := by
  let : HasOuterApproxClosed (Matrix (Fin n) (Fin q) ℝ) :=
    inferInstanceAs (HasOuterApproxClosed (Fin n → Fin q → ℝ))
  let : SecondCountableTopology (Matrix (Fin n) (Fin q) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin q → ℝ))
  have hact := continuous_cavityFrameAction n q
  have hfix (U : Orthogonal n) :
      Continuous (fun A : Matrix (Fin n) (Fin q) ℝ => (U : Matrix (Fin n) (Fin n) ℝ) * A) :=
    hact.comp (continuous_const.prodMk continuous_id)
  have horbit : Continuous (fun U : Orthogonal n => (U : Matrix (Fin n) (Fin n) ℝ) * A₀) :=
    hact.comp (continuous_id.prodMk continuous_const)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  have hi : Integrable (fun p : Orthogonal n × Matrix (Fin n) (Fin q) ℝ =>
      F ((p.1 : Matrix (Fin n) (Fin n) ℝ) * p.2)) (μ.prod ν) :=
    Integrable.of_bound (F.continuous.comp hact).aestronglyMeasurable ‖F‖
      (ae_of_all _ (fun p => F.norm_coe_le_norm _))
  have hrow (U : Orthogonal n) :
      (∫ A, F ((U : Matrix (Fin n) (Fin n) ℝ) * A) ∂ν) = ∫ A, F A ∂ν := by
    rw [← integral_map (hfix U).aemeasurable F.continuous.aestronglyMeasurable, hinv U]
  have hcol : ∀ᵐ A ∂ν,
      (∫ U, F ((U : Matrix (Fin n) (Fin n) ℝ) * A) ∂μ) =
        ∫ U, F ((U : Matrix (Fin n) (Fin n) ℝ) * A₀) ∂μ := by
    filter_upwards [hframe] with A hA
    obtain ⟨V, hV⟩ := cavityFrame_transitive A₀ A hA₀ hA
    rw [← hV]
    simp only [← Matrix.mul_assoc]
    change (∫ U, F (((U * V : Orthogonal n) : Matrix (Fin n) (Fin n) ℝ) * A₀) ∂μ) = _
    exact integral_mul_right_eq_self (μ := μ)
      (fun U : Orthogonal n => F ((U : Matrix (Fin n) (Fin n) ℝ) * A₀)) V
  calc
    (∫ A, F A ∂ν) = ∫ U, ∫ A, F ((U : Matrix (Fin n) (Fin n) ℝ) * A) ∂ν ∂μ := by
      simp only [hrow]
      simp
    _ = ∫ A, ∫ U, F ((U : Matrix (Fin n) (Fin n) ℝ) * A) ∂μ ∂ν :=
      integral_integral_swap hi
    _ = ∫ U, F ((U : Matrix (Fin n) (Fin n) ℝ) * A₀) ∂μ := by
      rw [integral_congr_ae hcol]
      simp
    _ = ∫ A, F A ∂μ.map (fun U : Orthogonal n => (U : Matrix (Fin n) (Fin n) ℝ) * A₀) :=
      (integral_map horbit.aemeasurable F.continuous.aestronglyMeasurable).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityWindowGram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian Gram matrices compressed to a growing spectral coordinate
window. Prefix differences avoid introducing a second Gaussian array. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix

namespace InvariantIsing

lemma continuous_cavityPrefixGram (N q l : ℕ) :
    Continuous (fun A : Matrix (Fin N) (Fin q) ℝ => cavityPrefixGram A l) :=
  (continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_id

lemma cavityPrefixGram_apply {N q : ℕ} (A : Matrix (Fin N) (Fin q) ℝ)
    (l : ℕ) (i j : Fin q) :
    cavityPrefixGram A l i j = ∑ k : Fin N, if k.val < l then A k i * A k j else 0 := by
  change (∑ k : Fin N, (∑ t : Fin N,
    A t i * (if t = k then (if t.val < l then (1 : ℝ) else 0) else 0)) * A k j) = _
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp_all

lemma cavityPrefixGram_mul {N q : ℕ} (A : Matrix (Fin N) (Fin q) ℝ)
    (C : Matrix (Fin q) (Fin q) ℝ) (l : ℕ) :
    cavityPrefixGram (A * C) l = C.transpose * cavityPrefixGram A l * C := by
  simp only [cavityPrefixGram, Matrix.transpose_mul, Matrix.mul_assoc]

lemma continuous_cavityWindowGram (N q l u : ℕ) :
    Continuous (fun A : Matrix (Fin N) (Fin q) ℝ => cavityWindowGram A l u) :=
  (continuous_cavityPrefixGram N q u).sub (continuous_cavityPrefixGram N q l)

lemma cavityWindowGram_posSemidef {N q : ℕ}
    (A : Matrix (Fin N) (Fin q) ℝ) (l u : ℕ) (hlu : l ≤ u) :
    (cavityWindowGram A l u).PosSemidef := by
  let D : Matrix (Fin N) (Fin N) ℝ := Matrix.diagonal
    (fun i : Fin N => if l ≤ i.val ∧ i.val < u then (1 : ℝ) else 0)
  have he : cavityWindowGram A l u = A.transpose * D * A := by
    have hd : Matrix.diagonal (fun i : Fin N => if i.val < u then (1 : ℝ) else 0) -
        Matrix.diagonal (fun i : Fin N => if i.val < l then (1 : ℝ) else 0) = D := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp only [D, Matrix.sub_apply, Matrix.diagonal_apply_eq]
        split_ifs <;> norm_num at * <;> omega
      · simp [D, Matrix.sub_apply, Matrix.diagonal_apply_ne _ hij]
    rw [cavityWindowGram, cavityPrefixGram, cavityPrefixGram,
      ← Matrix.sub_mul, ← Matrix.mul_sub, hd]
  rw [he]
  have hd : D.PosSemidef := Matrix.posSemidef_diagonal_iff.mpr (fun i => by
    split_ifs <;> norm_num)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hd.conjTranspose_mul_mul_same A

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

lemma cavitySpectralImage_sum {r m n : ℕ} (g : Fin r → Fin m)
    (A : Matrix (Fin r) (Fin n) ℝ) : ∑ a, cavitySpectralImage g A a = A := by
  ext i j
  simp only [Matrix.sum_apply, cavitySpectralImage, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, if_true]

lemma cavitySpectralImage_crossGram {r m n : ℕ} (g : Fin r → Fin m)
    (A : Matrix (Fin r) (Fin n) ℝ) (a b : Fin m) (hab : a ≠ b) :
    (cavitySpectralImage g A a).transpose * cavitySpectralImage g A b = 0 := by
  ext i j
  change (∑ k : Fin r, (if g k = a then A k i else 0) *
    (if g k = b then A k j else 0)) = 0
  apply Finset.sum_eq_zero
  intro k _
  by_cases ha : g k = a
  · simp only [ha, hab, ite_true, if_true, ite_false, if_false, mul_zero]
  · simp only [ha, ite_false, if_false, zero_mul]

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

lemma cavitySpectralImage_eigen {r m n : ℕ} (g : Fin r → Fin m)
    (A : Matrix (Fin r) (Fin n) ℝ) (lam : Fin m → ℝ) (a : Fin m) :
    Matrix.diagonal (fun i => lam (g i)) * cavitySpectralImage g A a =
      lam a • cavitySpectralImage g A a := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.smul_apply]
  change lam (g i) * (if g i = a then A i j else 0) =
    lam a * (if g i = a then A i j else 0)
  split_ifs with h
  · rw [h]
  · rw [mul_zero, mul_zero]

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

lemma cavityGroupLift_support {r m q t : ℕ} (g : Fin r → Fin m) (a : Fin m)
    (e : {i : Fin r // g i = a} ≃ Fin q) (B : Matrix (Fin q) (Fin t) ℝ)
    (i : Fin r) (hi : g i ≠ a) (j : Fin t) : cavityGroupLift g a e B i j = 0 := by
  simp only [cavityGroupLift, hi, dite_false]

lemma cavityGroupLift_gram {r m q s t : ℕ} (g : Fin r → Fin m) (a : Fin m)
    (e : {i : Fin r // g i = a} ≃ Fin q)
    (B : Matrix (Fin q) (Fin s) ℝ) (C : Matrix (Fin q) (Fin t) ℝ) :
    (cavityGroupLift g a e B).transpose * cavityGroupLift g a e C = B.transpose * C := by
  classical
  ext i j
  change (∑ k : Fin r, cavityGroupLift g a e B k i * cavityGroupLift g a e C k j) =
    ∑ k : Fin q, B k i * C k j
  calc
    _ = ∑ k : {k : Fin r // g k = a}, B (e k) i * C (e k) j := by
      apply Finset.sum_congr_set {k : Fin r | g k = a}
      · intro k hk
        change g k = a at hk
        simp only [cavityGroupLift, hk, dite_true]
      · intro k hk
        change g k ≠ a at hk
        simp only [cavityGroupLift, hk, dite_false, zero_mul]
    _ = _ := Equiv.sum_comp e (fun k : Fin q => B k i * C k j)

lemma cavityGroupLift_restrict {r m q t : ℕ} (g : Fin r → Fin m) (a : Fin m)
    (e : {i : Fin r // g i = a} ≃ Fin q) (W : Matrix (Fin r) (Fin t) ℝ)
    (hW : ∀ i, g i ≠ a → ∀ j, W i j = 0) :
    cavityGroupLift g a e (fun i j => W (e.symm i) j) = W := by
  ext i j
  by_cases hi : g i = a
  · simp only [cavityGroupLift, hi, dite_true, Equiv.symm_apply_apply]
  · simp only [cavityGroupLift, hi, dite_false, hW i hi j]

lemma cavityNormalizeFrame_spectral_support {r m n : ℕ}
    (g : Fin r → Fin m) (A : Matrix (Fin r) (Fin n) ℝ) (a : Fin m)
    (i : Fin r) (hi : g i ≠ a) (j : Fin n) :
    cavityNormalizeFrame (cavitySpectralImage g A a) i j = 0 := by
  change (∑ k : Fin n, cavitySpectralImage g A a i k * _) = 0
  apply Finset.sum_eq_zero
  intro k _
  simp only [cavitySpectralImage, hi, ite_false, if_false, zero_mul]

lemma cavity_complement_projection {k n : ℕ}
    (B : Matrix (Fin (k + n)) (Fin k) ℝ) (Y : Matrix (Fin (k + n)) (Fin n) ℝ)
    (hB : B.transpose * B = 1) (hY : Y.transpose * Y = 1)
    (hYB : Y.transpose * B = 0) :
    B * B.transpose + Y * Y.transpose = 1 := by
  have hBY : B.transpose * Y = 0 := by
    have h := congrArg Matrix.transpose hYB
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h
  have hQ : (Matrix.fromCols B Y).transpose * Matrix.fromCols B Y = 1 := by
    rw [Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols, hB, hBY, hYB, hY,
      Matrix.fromBlocks_one]
  have h := (Matrix.mul_eq_one_comm_of_equiv
    (finSumFinEquiv : Fin k ⊕ Fin n ≃ Fin (k + n))).mp hQ
  simpa only [Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows] using h

lemma cavityGroupLift_projection {r m q s t : ℕ} (g : Fin r → Fin m) (a : Fin m)
    (e : {i : Fin r // g i = a} ≃ Fin q)
    (B : Matrix (Fin q) (Fin s) ℝ) (C : Matrix (Fin q) (Fin t) ℝ)
    (hBC : B * B.transpose + C * C.transpose = 1) :
    cavityGroupLift g a e B * (cavityGroupLift g a e B).transpose +
      cavityGroupLift g a e C * (cavityGroupLift g a e C).transpose =
        Matrix.diagonal (fun i => if g i = a then (1 : ℝ) else 0) := by
  classical
  ext i j
  by_cases hi : g i = a <;> by_cases hj : g j = a
  · have h := congrArg (fun M : Matrix (Fin q) (Fin q) ℝ =>
      M (e ⟨i, hi⟩) (e ⟨j, hj⟩)) hBC
    simpa only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      cavityGroupLift, hi, hj, dite_true, Matrix.one_apply, Equiv.apply_eq_iff_eq,
      Subtype.mk.injEq, Matrix.diagonal_apply, ite_true, if_true] using h
  · have hij : i ≠ j := fun h => hj (h ▸ hi)
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      cavityGroupLift, hi, hj, dite_true, dite_false, mul_zero, Finset.sum_const_zero,
      add_zero, Matrix.diagonal_apply_ne _ hij]
  · have hij : i ≠ j := fun h => hi (h.symm ▸ hj)
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      cavityGroupLift, hi, hj, dite_true, dite_false, zero_mul, Finset.sum_const_zero,
      add_zero, Matrix.diagonal_apply_ne _ hij]
  · simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      cavityGroupLift, hi, hj, dite_false, zero_mul, Finset.sum_const_zero, add_zero]
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, hi, ite_false, if_false]
    · rw [Matrix.diagonal_apply_ne _ hij]

theorem cavityRetainedFrame_exists {r m n k : ℕ}
    (g : Fin r → Fin m) (A : Matrix (Fin r) (Fin n) ℝ) (a : Fin m)
    (e : {i : Fin r // g i = a} ≃ Fin (k + n))
    (hA : ((cavitySpectralImage g A a).transpose * cavitySpectralImage g A a).PosDef) :
    ∃ R : Matrix (Fin r) (Fin k) ℝ,
      R.transpose * R = 1 ∧
      (cavityNormalizeFrame (cavitySpectralImage g A a)).transpose * R = 0 ∧
      (∀ i, g i ≠ a → ∀ j, R i j = 0) ∧
      R * R.transpose + cavityNormalizeFrame (cavitySpectralImage g A a) *
        (cavityNormalizeFrame (cavitySpectralImage g A a)).transpose =
          Matrix.diagonal (fun i => if g i = a then (1 : ℝ) else 0) := by
  let W := cavityNormalizeFrame (cavitySpectralImage g A a)
  let Y : Matrix (Fin (k + n)) (Fin n) ℝ := fun i j => W (e.symm i) j
  have hW : cavityGroupLift g a e Y = W :=
    cavityGroupLift_restrict g a e W (cavityNormalizeFrame_spectral_support g A a)
  have hY : Y.transpose * Y = 1 := by
    rw [← cavityGroupLift_gram g a e Y Y, hW]
    exact cavityNormalizeFrame_gram _ hA
  obtain ⟨B, hB, hYB⟩ := cavity_frame_completion Y hY
  refine ⟨cavityGroupLift g a e B, ?_, ?_, ?_, ?_⟩
  · rw [cavityGroupLift_gram, hB]
  · change W.transpose * cavityGroupLift g a e B = 0
    rw [← hW, cavityGroupLift_gram, hYB]
  · exact cavityGroupLift_support g a e B
  · change _ + W * W.transpose = _
    rw [← hW]
    exact cavityGroupLift_projection g a e B Y (cavity_complement_projection B Y hB hY hYB)

lemma cavitySpectralSupport_crossGram {r m s t : ℕ}
    (g : Fin r → Fin m) (a b : Fin m) (hab : a ≠ b)
    (V : Matrix (Fin r) (Fin s) ℝ) (W : Matrix (Fin r) (Fin t) ℝ)
    (hV : ∀ i, g i ≠ a → ∀ j, V i j = 0)
    (hW : ∀ i, g i ≠ b → ∀ j, W i j = 0) : V.transpose * W = 0 := by
  ext i j
  change (∑ k, V k i * W k j) = 0
  apply Finset.sum_eq_zero
  intro k _
  by_cases ha : g k = a
  · have hb : g k ≠ b := fun h => hab (ha.symm.trans h)
    rw [hW k hb j, mul_zero]
  · rw [hV k ha i, zero_mul]

lemma cavitySpectralSupport_eigen {r m t : ℕ}
    (g : Fin r → Fin m) (a : Fin m) (lam : Fin m → ℝ)
    (V : Matrix (Fin r) (Fin t) ℝ)
    (hV : ∀ i, g i ≠ a → ∀ j, V i j = 0) :
    Matrix.diagonal (fun i => lam (g i)) * V = lam a • V := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.smul_apply]
  by_cases hi : g i = a
  · rw [hi]; rfl
  · rw [hV i hi j, mul_zero, smul_zero]

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRetainedStack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble the retained group frames without imposing equal group
sizes. The separate group projector identities give completeness. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

theorem cavityRetainedStack_gram {r m : ℕ} (k : Fin m → ℕ)
    (R : (a : Fin m) → Matrix (Fin r) (Fin (k a)) ℝ)
    (hR : ∀ a, (R a).transpose * R a = 1)
    (hcross : ∀ a b, a ≠ b → (R a).transpose * R b = 0) :
    (cavityRetainedStack k R).transpose * cavityRetainedStack k R = 1 := by
  classical
  ext ⟨a, i⟩ ⟨b, j⟩
  change ((R a).transpose * R b) i j = if (⟨a, i⟩ : Sigma fun a => Fin (k a)) = ⟨b, j⟩ then 1 else 0
  by_cases hab : a = b
  · subst b
    rw [hR, Matrix.one_apply]
    simp
  · rw [hcross a b hab, Matrix.zero_apply]
    have hij : (⟨a, i⟩ : Sigma fun a => Fin (k a)) ≠ ⟨b, j⟩ := fun h => hab (congrArg Sigma.fst h)
    simp only [hij, ite_false, if_false]

theorem cavityRetainedStack_outer {r m : ℕ} (k : Fin m → ℕ)
    (R : (a : Fin m) → Matrix (Fin r) (Fin (k a)) ℝ) :
    cavityRetainedStack k R * (cavityRetainedStack k R).transpose =
      ∑ a, R a * (R a).transpose := by
  ext i j
  change (∑ a : Sigma fun a => Fin (k a), R a.1 i a.2 * R a.1 j a.2) = _
  simp only [Fintype.sum_sigma, Matrix.sum_apply, Matrix.mul_apply, Matrix.transpose_apply]

theorem cavityEigenspaceFrame_outer {r m n : ℕ}
    (X : Fin m → Matrix (Fin r) (Fin n) ℝ) :
    cavityEigenspaceFrame X * (cavityEigenspaceFrame X).transpose =
      ∑ a, cavityNormalizeFrame (X a) * (cavityNormalizeFrame (X a)).transpose := by
  ext i j
  change (∑ k : Fin (m * n), cavityNormalizeFrame (X (finProdFinEquiv.symm k).1)
    i (finProdFinEquiv.symm k).2 * cavityNormalizeFrame (X (finProdFinEquiv.symm k).1)
      j (finProdFinEquiv.symm k).2) = _
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n))]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type,
    Matrix.sum_apply, Matrix.mul_apply, Matrix.transpose_apply]

theorem cavityRetainedStack_complete {r m n : ℕ} (g : Fin r → Fin m)
    (A : Matrix (Fin r) (Fin n) ℝ) (k : Fin m → ℕ)
    (R : (a : Fin m) → Matrix (Fin r) (Fin (k a)) ℝ)
    (hR : ∀ a, R a * (R a).transpose +
      cavityNormalizeFrame (cavitySpectralImage g A a) *
        (cavityNormalizeFrame (cavitySpectralImage g A a)).transpose =
          Matrix.diagonal (fun i => if g i = a then (1 : ℝ) else 0)) :
    cavityRetainedStack k R * (cavityRetainedStack k R).transpose +
      cavityEigenspaceFrame (cavitySpectralImage g A) *
        (cavityEigenspaceFrame (cavitySpectralImage g A)).transpose = 1 := by
  rw [cavityRetainedStack_outer, cavityEigenspaceFrame_outer, ← Finset.sum_add_distrib]
  simp only [hR]
  exact cavitySpectralProjectors_sum g

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBaseEigenspaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The replaced interaction preserves retained eigenvectors, gives the
special axes their assigned eigenvalues, and annihilates the cavity. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

lemma cavityBaseReplacement_conjugate {r s d : ℕ}
    (J U : Matrix (Fin r) (Fin r) ℝ) (W : Matrix (Fin r) (Fin s) ℝ)
    (D : Matrix (Fin s) (Fin s) ℝ) (B : Matrix (Fin s) (Fin d) ℝ)
    (A₀ : Matrix (Fin d) (Fin d) ℝ) :
    cavityBaseReplacement (U * J * U.transpose) (U * W) D B A₀ =
      U * cavityBaseReplacement J W D B A₀ * U.transpose := by
  simp only [cavityBaseReplacement, Matrix.transpose_mul, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBaseSpectralSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The base interaction has an explicit spectral decomposition. Its
retained multiplicities and the assigned special multiplicities add to
the required base counts. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavityBaseReplacement_spectral_sum {r s d : ℕ} {ι : Type*} [Fintype ι]
    (J : Matrix (Fin r) (Fin r) ℝ) (W : Matrix (Fin r) (Fin s) ℝ)
    (D : Matrix (Fin s) (Fin s) ℝ) (B : Matrix (Fin s) (Fin d) ℝ)
    (A₀ : Matrix (Fin d) (Fin d) ℝ) (R : Matrix (Fin r) ι ℝ) (L : Matrix ι ι ℝ)
    (hJR : J * R = R * L) (hJW : J * W = W * D)
    (hcomplete : R * R.transpose + W * W.transpose = 1) :
    cavityBaseReplacement J W D B A₀ =
      R * L * R.transpose + (W * B) * A₀ * (W * B).transpose := by
  have hJ : J = R * L * R.transpose + W * D * W.transpose := by
    calc
      J = J * (R * R.transpose + W * W.transpose) := by rw [hcomplete, Matrix.mul_one]
      _ = _ := by rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJR, hJW]
  unfold cavityBaseReplacement
  rw [hJ]
  abel

lemma cavityRetainedStack_perp {r m n : ℕ} (k : Fin m → ℕ)
    (R : (a : Fin m) → Matrix (Fin r) (Fin (k a)) ℝ)
    (X : Fin m → Matrix (Fin r) (Fin n) ℝ)
    (hRX : ∀ a b, (R a).transpose * cavityNormalizeFrame (X b) = 0) :
    (cavityRetainedStack k R).transpose * cavityEigenspaceFrame X = 0 := by
  ext ⟨a, i⟩ j
  exact congrArg (fun M : Matrix (Fin (k a)) (Fin n) ℝ =>
    M i (finProdFinEquiv.symm j).2) (hRX a (finProdFinEquiv.symm j).1)

lemma cavityRetainedStack_eigen {r m : ℕ} (g : Fin r → Fin m) (lam : Fin m → ℝ)
    (k : Fin m → ℕ) (R : (a : Fin m) → Matrix (Fin r) (Fin (k a)) ℝ)
    (hR : ∀ a i, g i ≠ a → ∀ j, R a i j = 0) :
    Matrix.diagonal (fun i => lam (g i)) * cavityRetainedStack k R =
      cavityRetainedStack k R * Matrix.diagonal (fun j : Sigma (fun a : Fin m => Fin (k a)) => lam j.1) := by
  ext i ⟨a, j⟩
  have h := congrArg (fun M : Matrix (Fin r) (Fin (k a)) ℝ => M i j)
    (cavitySpectralSupport_eigen g a lam (R a) (hR a))
  rw [Matrix.mul_diagonal]
  simpa only [Matrix.diagonal_mul, cavityRetainedStack, Matrix.smul_apply,
    smul_eq_mul, mul_comm] using h

theorem cavityBase_spectral_decomposition {r m n d : ℕ}
    (g : Fin r → Fin m) (A : Matrix (Fin r) (Fin n) ℝ) (lam : Fin m → ℝ)
    (k : Fin m → ℕ) (R : (a : Fin m) → Matrix (Fin r) (Fin (k a)) ℝ)
    (hR : ∀ a i, g i ≠ a → ∀ j, R a i j = 0)
    (hproj : ∀ a, R a * (R a).transpose +
      cavityNormalizeFrame (cavitySpectralImage g A a) *
        (cavityNormalizeFrame (cavitySpectralImage g A a)).transpose =
          Matrix.diagonal (fun i => if g i = a then (1 : ℝ) else 0))
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (A₀ : Matrix (Fin d) (Fin d) ℝ) :
    cavityBaseReplacement (Matrix.diagonal (fun i => lam (g i)))
      (cavityEigenspaceFrame (cavitySpectralImage g A)) (cavityRepeatedSpectrum (n := n) lam) B A₀ =
        cavityRetainedStack k R * Matrix.diagonal (fun j : Sigma (fun a : Fin m => Fin (k a)) => lam j.1) *
          (cavityRetainedStack k R).transpose +
        (cavityEigenspaceFrame (cavitySpectralImage g A) * B) * A₀ *
          (cavityEigenspaceFrame (cavitySpectralImage g A) * B).transpose := by
  apply cavityBaseReplacement_spectral_sum
  · exact cavityRetainedStack_eigen g lam k R hR
  · exact cavityEigenspaceFrame_eigen _ _ lam (cavitySpectralImage_eigen g A lam)
  · exact cavityRetainedStack_complete g A k R hproj

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityReservoirFrame
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An orthonormal base frame perpendicular to the physical cavity
coordinates gives an orthogonal eigenbasis of the reservoir. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavityBaseFrame_gram {r s d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Matrix (Fin r) ι ℝ) (W : Matrix (Fin r) (Fin s) ℝ)
    (B : Matrix (Fin s) (Fin d) ℝ)
    (hR : R.transpose * R = 1) (hW : W.transpose * W = 1)
    (hRW : R.transpose * W = 0) (hB : B.transpose * B = 1) :
    (Matrix.fromCols R (W * B)).transpose * Matrix.fromCols R (W * B) = 1 := by
  have hRV : R.transpose * (W * B) = 0 := by rw [← Matrix.mul_assoc, hRW, Matrix.zero_mul]
  have hVR : (W * B).transpose * R = 0 := by
    have h := congrArg Matrix.transpose hRV
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h
  have hVV : (W * B).transpose * (W * B) = 1 := by
    rw [Matrix.transpose_mul]
    calc
      _ = B.transpose * (W.transpose * W) * B := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hW, Matrix.mul_one, hB]
  rw [Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols, hR, hRV, hVR, hVV,
    Matrix.fromBlocks_one]

lemma cavityBaseFrame_cavity_perp {r s d n : ℕ} {ι : Type*} [Fintype ι]
    (R : Matrix (Fin r) ι ℝ) (W : Matrix (Fin r) (Fin s) ℝ)
    (B : Matrix (Fin s) (Fin d) ℝ) (E : Matrix (Fin s) (Fin n) ℝ)
    (hW : W.transpose * W = 1) (hRW : R.transpose * W = 0)
    (hBE : B.transpose * E = 0) :
    (W * E).transpose * Matrix.fromCols R (W * B) = 0 := by
  have hWR : W.transpose * R = 0 := by
    have h := congrArg Matrix.transpose hRW
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h
  have hEB : E.transpose * B = 0 := by
    have h := congrArg Matrix.transpose hBE
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h
  have hER : (W * E).transpose * R = 0 := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, hWR, Matrix.mul_zero]
  have hEV : (W * E).transpose * (W * B) = 0 := by
    rw [Matrix.transpose_mul]
    calc
      _ = E.transpose * (W.transpose * W) * B := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hW, Matrix.mul_one, hEB]
  rw [Matrix.mul_fromCols, hER, hEV, Matrix.fromCols_zero]

lemma cavityBaseFrame_spectral_sum {r d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Matrix (Fin r) ι ℝ) (V : Matrix (Fin r) (Fin d) ℝ)
    (lam : ι → ℝ) (lam₀ : Fin d → ℝ) :
    Matrix.fromCols R V * Matrix.diagonal (Sum.elim lam lam₀) *
      (Matrix.fromCols R V).transpose =
        R * Matrix.diagonal lam * R.transpose + V * Matrix.diagonal lam₀ * V.transpose := by
  rw [← Matrix.fromBlocks_diagonal, Matrix.fromCols_mul_fromBlocks, Matrix.transpose_fromCols]
  simp only [Matrix.mul_zero, add_zero, zero_add,
    Matrix.fromCols_mul_fromRows]

lemma cavityReservoirRows_conjugate {N n : ℕ} {ι : Type*} [Fintype ι]
    (F : Matrix (Fin (N + n)) ι ℝ) (L : Matrix ι ι ℝ) :
    (F * L * F.transpose).submatrix (Fin.castAdd n) (Fin.castAdd n) =
      cavityReservoirRows F * L * (cavityReservoirRows F).transpose := by
  ext i j
  rfl

lemma cavityReservoirRows_gram {N n : ℕ} {ι : Type*} [Fintype ι]
    (F : Matrix (Fin (N + n)) ι ℝ)
    (hF : ∀ i : Fin n, ∀ j, F (Fin.natAdd N i) j = 0) :
    (cavityReservoirRows F).transpose * cavityReservoirRows F = F.transpose * F := by
  ext i j
  change (∑ k : Fin N, F (k.castAdd n) i * F (k.castAdd n) j) =
    ∑ k : Fin (N + n), F k i * F k j
  rw [Fin.sum_univ_add]
  simp only [hF, zero_mul, Finset.sum_const_zero, add_zero]

lemma cavityReservoirRows_orthogonal {N n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ Fin N) (F : Matrix (Fin (N + n)) ι ℝ)
    (hG : F.transpose * F = 1)
    (hF : ∀ i : Fin n, ∀ j, F (Fin.natAdd N i) j = 0) :
    ∃ U : Orthogonal N, ∀ i j, (U : Matrix (Fin N) (Fin N) ℝ) i j =
      cavityReservoirRows F i (e.symm j) := by
  let A : Matrix (Fin N) (Fin N) ℝ := fun i j => cavityReservoirRows F i (e.symm j)
  have hA : A.transpose * A = 1 := by
    ext i j
    have hh := congrArg (fun M : Matrix ι ι ℝ => M (e.symm i) (e.symm j))
      ((cavityReservoirRows_gram F hF).trans hG)
    change (∑ k : Fin N, cavityReservoirRows F k (e.symm i) *
      cavityReservoirRows F k (e.symm j)) = if i = j then 1 else 0
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Equiv.apply_eq_iff_eq] using hh
  exact ⟨⟨A, (Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mpr hA⟩, fun _ _ => rfl⟩

lemma cavityPhysicalFrame_lastRows {N n : ℕ} {ι : Type*} [Fintype ι]
    (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)
    (F : Matrix (Fin (N + n)) ι ℝ)
    (hF : (show Matrix (Fin (N + n)) (Fin n) ℝ from
      fun i j => U i (Fin.natAdd N j)).transpose * F = 0) :
    ∀ i : Fin n, ∀ j, (U.transpose * F) (Fin.natAdd N i) j = 0 := by
  intro i j
  exact congrArg (fun M : Matrix (Fin n) ι ℝ => M i j) hF

lemma cavityPhysicalFrame_gram {r : ℕ} {ι : Type*} [Fintype ι]
    (U : Orthogonal r) (F : Matrix (Fin r) ι ℝ) :
    ((U : Matrix (Fin r) (Fin r) ℝ).transpose * F).transpose *
      ((U : Matrix (Fin r) (Fin r) ℝ).transpose * F) = F.transpose * F := by
  have hU : (U : Matrix (Fin r) (Fin r) ℝ) *
      (U : Matrix (Fin r) (Fin r) ℝ).transpose = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin r) ℝ).mp U.property
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    _ = F.transpose * ((U : Matrix (Fin r) (Fin r) ℝ) *
        (U : Matrix (Fin r) (Fin r) ℝ).transpose) * F := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, Matrix.mul_one]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityReservoirRotation
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability
attribute [-simp] _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.planeRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reservoir rotations fix the physical cavity columns exactly. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavityReservoirRotation_last {N n : ℕ} (V : Orthogonal N)
    (i : Fin (N + n)) (j : Fin n) :
    (cavityReservoirRotation (n := n) V : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)
      i (Fin.natAdd N j) = if i = Fin.natAdd N j then 1 else 0 := by
  obtain ⟨a, rfl⟩ := (finSumFinEquiv : Fin N ⊕ Fin n ≃ Fin (N + n)).surjective i
  cases a with
  | inl i =>
    have hij : i.castAdd n ≠ Fin.natAdd N j := by
      intro h
      have hh := congrArg (finSumFinEquiv.symm : Fin (N + n) → Fin N ⊕ Fin n) h
      simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd] at hh
      cases hh
    simp [cavityReservoirRotation, Matrix.submatrix_apply, Matrix.fromBlocks, hij]
  | inr i =>
    simp [cavityReservoirRotation, Matrix.submatrix_apply, Matrix.fromBlocks, Matrix.one_apply]

lemma cavityReservoirRotation_first {N n : ℕ} (V : Orthogonal N)
    (i j : Fin N) :
    (cavityReservoirRotation (n := n) V : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)
      (i.castAdd n) (j.castAdd n) = (V : Matrix (Fin N) (Fin N) ℝ) i j := by
  simp [cavityReservoirRotation, Matrix.submatrix_apply, Matrix.fromBlocks]

lemma cavityReservoirRotation_lowerLeft {N n : ℕ} (V : Orthogonal N)
    (i : Fin n) (j : Fin N) :
    (cavityReservoirRotation (n := n) V : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)
      (Fin.natAdd N i) (j.castAdd n) = 0 := by
  simp [cavityReservoirRotation, Matrix.submatrix_apply, Matrix.fromBlocks]

lemma cavityReservoirRotation_conjugate {N n : ℕ} (V : Orthogonal N)
    (J : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) :
    ((cavityReservoirRotation (n := n) V : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose *
      J * (cavityReservoirRotation (n := n) V : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)).submatrix
        (Fin.castAdd n) (Fin.castAdd n) =
      (V : Matrix (Fin N) (Fin N) ℝ).transpose *
        J.submatrix (Fin.castAdd n) (Fin.castAdd n) * (V : Matrix (Fin N) (Fin N) ℝ) := by
  ext i j
  change (∑ k : Fin (N + n), (∑ l : Fin (N + n),
    (cavityReservoirRotation (n := n) V : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)
      l (i.castAdd n) * J l k) *
    (cavityReservoirRotation (n := n) V : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)
      k (j.castAdd n)) =
    ∑ k : Fin N, (∑ l : Fin N, (V : Matrix (Fin N) (Fin N) ℝ) l i *
      J (l.castAdd n) (k.castAdd n)) * (V : Matrix (Fin N) (Fin N) ℝ) k j
  simp only [Fin.sum_univ_add, cavityReservoirRotation_first,
    cavityReservoirRotation_lowerLeft, zero_mul, mul_zero, Finset.sum_const_zero, add_zero]

lemma cavityReservoirRotation_cavityColumns {N n : ℕ}
    (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) (V : Orthogonal N) :
    (fun (i : Fin (N + n)) (j : Fin n) => (U *
      (cavityReservoirRotation (n := n) V : Matrix (Fin (N + n)) (Fin (N + n)) ℝ))
        i (Fin.natAdd N j)) =
      fun i j => U i (Fin.natAdd N j) := by
  ext i j
  simp only [Matrix.mul_apply, cavityReservoirRotation_last, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]

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

lemma measurable_cavityPhysicalBase {N n m d : ℕ} (g : Fin (N + n) → Fin m)
    (lam : Fin m → ℝ)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (hB : Measurable B) (A₀ : Matrix (Fin d) (Fin d) ℝ) :
    Measurable (cavityPhysicalBase g lam B A₀) := by
  let : OpensMeasurableSpace (Matrix (Fin (N + n)) (Fin (m * n)) ℝ ×
      Matrix (Fin (m * n)) (Fin d) ℝ) := inferInstanceAs
    (OpensMeasurableSpace ((Fin (N + n) → Fin (m * n) → ℝ) × (Fin (m * n) → Fin d → ℝ)))
  let : OpensMeasurableSpace (Orthogonal (N + n) ×
      Matrix (Fin (N + n)) (Fin (N + n)) ℝ) := inferInstanceAs
    (OpensMeasurableSpace (Orthogonal (N + n) × (Fin (N + n) → Fin (N + n) → ℝ)))
  have hX : Measurable (fun U : Orthogonal (N + n) =>
      cavitySpectralImage g (cavityColumns U)) := measurable_pi_iff.mpr
    (fun a => (measurable_cavitySpectralImage g a).comp (measurable_cavityColumns N n))
  have hW := (measurable_cavityEigenspaceFrame (N + n) m n).comp hX
  have hBU := hB.comp (measurable_cavityCompressionGrams g)
  have hrep : Continuous (fun p : Matrix (Fin (N + n)) (Fin (m * n)) ℝ ×
      Matrix (Fin (m * n)) (Fin d) ℝ =>
      cavityBaseReplacement (Matrix.diagonal (fun i => lam (g i))) p.1
        (cavityRepeatedSpectrum (n := n) lam) p.2 A₀) := by
    unfold cavityBaseReplacement
    exact (continuous_const.sub ((continuous_fst.matrix_mul continuous_const).matrix_mul
      continuous_fst.matrix_transpose)).add
        (((continuous_fst.matrix_mul continuous_snd).matrix_mul continuous_const).matrix_mul
          (continuous_fst.matrix_mul continuous_snd).matrix_transpose)
  have hJ := hrep.measurable.comp (hW.prodMk hBU)
  have hconj : Continuous (fun p : Orthogonal (N + n) ×
      Matrix (Fin (N + n)) (Fin (N + n)) ℝ =>
      (p.1 : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose * p.2 *
        (p.1 : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)) :=
    (((continuous_subtype_val.comp continuous_fst).matrix_transpose.matrix_mul
      continuous_snd).matrix_mul (continuous_subtype_val.comp continuous_fst))
  have h := hconj.measurable.comp (measurable_id.prodMk hJ)
  apply Measurable.of_eval_matrix
  intro i j
  exact h.eval_matrix

lemma cavityCompressionGrams_reservoir {N n m : ℕ} (g : Fin (N + n) → Fin m)
    (U : Orthogonal (N + n)) (V : Orthogonal N) :
    cavityCompressionGrams g (U * cavityReservoirRotation (n := n) V) =
      cavityCompressionGrams g U := by
  unfold cavityCompressionGrams
  have hc : cavityColumns (U * cavityReservoirRotation (n := n) V) = cavityColumns U :=
    cavityReservoirRotation_cavityColumns _ V
  rw [hc]

lemma cavityPhysicalBase_reservoir {N n m d : ℕ} (g : Fin (N + n) → Fin m)
    (lam : Fin m → ℝ)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (A₀ : Matrix (Fin d) (Fin d) ℝ)
    (U : Orthogonal (N + n)) (V : Orthogonal N) :
    cavityPhysicalBase g lam B A₀ (U * cavityReservoirRotation (n := n) V) =
      (V : Matrix (Fin N) (Fin N) ℝ).transpose * cavityPhysicalBase g lam B A₀ U *
        (V : Matrix (Fin N) (Fin N) ℝ) := by
  have hc : cavityColumns (U * cavityReservoirRotation (n := n) V) = cavityColumns U :=
    cavityReservoirRotation_cavityColumns _ V
  unfold cavityPhysicalBase
  rw [hc, cavityCompressionGrams_reservoir]
  let J := cavityBaseReplacement (Matrix.diagonal (fun i => lam (g i)))
    (cavityEigenspaceFrame (cavitySpectralImage g (cavityColumns U)))
    (cavityRepeatedSpectrum (n := n) lam) (B (cavityCompressionGrams g U)) A₀
  change (((U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) *
    (cavityReservoirRotation (n := n) V : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)).transpose *
    J * ((U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) *
    (cavityReservoirRotation (n := n) V : Matrix (Fin (N + n)) (Fin (N + n)) ℝ))).submatrix
      (Fin.castAdd n) (Fin.castAdd n) =
    (V : Matrix (Fin N) (Fin N) ℝ).transpose *
      ((U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose * J *
        (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)).submatrix
          (Fin.castAdd n) (Fin.castAdd n) * (V : Matrix (Fin N) (Fin N) ℝ)
  rw [Matrix.transpose_mul]
  simpa only [Matrix.mul_assoc] using cavityReservoirRotation_conjugate V
    ((U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose * J *
      (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBaseHaarFactorization
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact independence, in bounded-test form, of the Haar base spectral
orbit and the small compression data in the concrete cavity coupling. -/

noncomputable section
open MeasureTheory
open scoped Matrix

namespace InvariantIsing

lemma continuous_cavityConjugate (N : ℕ) :
    Continuous (Function.uncurry (cavityConjugate (N := N))) :=
  ((continuous_subtype_val.comp continuous_fst).matrix_mul continuous_snd).matrix_mul
    (continuous_subtype_val.comp continuous_fst).matrix_transpose

lemma cavityConjugate_mul {N : ℕ} (U V : Orthogonal N)
    (J : Matrix (Fin N) (Fin N) ℝ) :
    cavityConjugate (U * V) J = cavityConjugate U (cavityConjugate V J) := by
  change ((U : Matrix (Fin N) (Fin N) ℝ) * (V : Matrix (Fin N) (Fin N) ℝ)) * J *
    ((U : Matrix (Fin N) (Fin N) ℝ) * (V : Matrix (Fin N) (Fin N) ℝ)).transpose = _
  simp only [cavityConjugate, Matrix.transpose_mul, Matrix.mul_assoc]

lemma cavityPhysicalBase_reservoir_inv {N n m d : ℕ} (g : Fin (N + n) → Fin m)
    (lam : Fin m → ℝ)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (A₀ : Matrix (Fin d) (Fin d) ℝ)
    (U : Orthogonal (N + n)) (V : Orthogonal N) :
    cavityPhysicalBase g lam B A₀ (U * cavityReservoirRotation (n := n) V⁻¹) =
      cavityConjugate V (cavityPhysicalBase g lam B A₀ U) := by
  rw [cavityPhysicalBase_reservoir]
  have hV : (V⁻¹ : Orthogonal N).val = (V : Matrix (Fin N) (Fin N) ℝ).transpose := by
    ext i j
    rfl
  simp only [hV, Matrix.transpose_transpose, cavityConjugate]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCoefficientValueLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded normalized cavity observables are stable under coefficient
concentration when their cutoff energy has a uniform secant bound. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

theorem cavity_coefficient_values_tendsto {Ω : ℕ → Type*}
    [∀ k, MeasurableSpace (Ω k)] {d n : ℕ}
    (P : (k : ℕ) → Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (A : (k : ℕ) → Ω k → CavityFactorBlocks d n) (hA : ∀ k, Measurable (A k))
    (A₀ : CavityFactorBlocks d n)
    (f g : (k : ℕ) → Ω k → ℝ) (hf : ∀ k, Measurable (f k)) (hg : ∀ k, Measurable (g k))
    {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hfb : ∀ k ω, |f k ω| ≤ M) (hgb : ∀ k ω, |g k ω| ≤ M)
    (hlocal : ∀ k ω s, 0 < s → |f k ω-g k ω| ≤
      K*cavityFactorDeviation (A k ω) A₀/s+M^2*s/2)
    (hprob : ∀ δ > 0, Tendsto (fun k => (P k).real
      {ω | δ < cavityFactorDeviation (A k ω) A₀}) atTop (𝓝 0)) :
    Tendsto (fun k => (∫ ω, f k ω ∂P k) - ∫ ω, g k ω ∂P k) atTop (𝓝 0) := by
  let : OpensMeasurableSpace (CavityFactorBlocks d n) := inferInstanceAs
    (OpensMeasurableSpace ((Fin d → Fin d → ℝ) ×
      ((Fin d → Fin n → ℝ) × (Fin n → Fin n → ℝ))))
  have hmean k (δ s : ℝ) (hδ : 0 ≤ δ) (hs : 0 < s) :
      |(∫ ω, f k ω ∂P k) - ∫ ω, g k ω ∂P k| ≤
        K*δ/s+M^2*s/2+2*M*(P k).real {ω | δ < cavityFactorDeviation (A k ω) A₀} := by
    let bad := {ω : Ω k | δ < cavityFactorDeviation (A k ω) A₀}
    have hbad : MeasurableSet bad := measurableSet_lt measurable_const
      ((continuous_cavityFactorDeviation A₀).measurable.comp (hA k))
    have hfi : Integrable (f k) (P k) := integrable_of_measurable_abs_le (hf k) (hfb k)
    have hgi : Integrable (g k) (P k) := integrable_of_measurable_abs_le (hg k) (hgb k)
    have hb ω : |f k ω-g k ω| ≤ K*δ/s+M^2*s/2+
        2*M*bad.indicator (fun _ => (1 : ℝ)) ω := by
      by_cases hω : ω ∈ bad
      · rw [indicator_of_mem hω, mul_one]
        have ht : |f k ω-g k ω| ≤ 2*M := (abs_sub _ _).trans (by linarith [hfb k ω,hgb k ω])
        exact ht.trans (le_add_of_nonneg_left (by positivity))
      · rw [indicator_of_notMem hω, mul_zero, add_zero]
        have hd : cavityFactorDeviation (A k ω) A₀ ≤ δ := le_of_not_gt hω
        exact (hlocal k ω s hs).trans (add_le_add
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd hK) hs.le) le_rfl)
    have hbi : Integrable (fun ω => K*δ/s+M^2*s/2+
        2*M*bad.indicator (fun _ => (1 : ℝ)) ω) (P k) :=
      (integrable_const _).add (((integrable_const (1 : ℝ)).indicator hbad).const_mul _)
    rw [← integral_sub hfi hgi]
    calc
      _ ≤ ∫ ω, |f k ω-g k ω| ∂P k := abs_integral_le_integral_abs
      _ ≤ ∫ ω, K*δ/s+M^2*s/2+2*M*bad.indicator (fun _ => (1 : ℝ)) ω ∂P k :=
        integral_mono (hfi.sub hgi).abs hbi hb
      _ = _ := by
        rw [integral_add (integrable_const _)
          (((integrable_const (1 : ℝ)).indicator hbad).const_mul _), integral_const_mul,
          integral_indicator hbad, integral_const, integral_const]
        simp only [smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ,
          measure_univ, ENNReal.toReal_one, one_mul, bad]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let s := ε/(4*(M^2+1))
  have hs : 0 < s := by dsimp only [s] <;> positivity
  have hse : 4*(M^2+1)*s = ε := by
    dsimp only [s]
    field_simp
  let δ := ε*s/(4*(K+1))
  have hδ : 0 < δ := by dsimp only [δ] <;> positivity
  have hδe : 4*(K+1)*δ = ε*s := by
    dsimp only [δ]
    field_simp
  have hsmall : K*δ/s+M^2*s/2 < ε/2 := by
    have hd : K*δ/s < ε/4 := (div_lt_iff₀ hs).mpr (by nlinarith)
    have ht : M^2*s/2 < ε/4 := by nlinarith
    linarith
  have hden : 0 < 4*(2*M+1) := by positivity
  have hevent := (hprob δ hδ).eventually (gt_mem_nhds (show (0 : ℝ) < ε/(4*(2*M+1)) by positivity))
  filter_upwards [hevent] with k hk
  have htail : 2*M*(P k).real {ω | δ < cavityFactorDeviation (A k ω) A₀} < ε/4 := by
    have hh := (lt_div_iff₀ hden).mp hk
    nlinarith [measureReal_nonneg (μ := P k) (s := {ω | δ < cavityFactorDeviation (A k ω) A₀})]
  rw [Real.dist_eq, sub_zero]
  exact (hmean k δ s hδ.le hs).trans_lt (by linarith)

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarCompression
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Haar cavity compressions converge to their spectral proportions.
The proof transfers the almost sure Gaussian Gram limit through the
exact conditioned frame law. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator
  BoundedContinuousFunction

namespace InvariantIsing

lemma measurable_cavityGaussianNormalizedFrame (q N : ℕ) :
    Measurable (fun x : ℕ → Fin q → ℝ =>
      cavityNormalizeFrame (cavityGaussianMatrix x N)) := by
  apply (measurable_cavityNormalizeFrame N q).comp
  apply Measurable.of_eval_matrix
  intro i j
  exact ((measurable_pi_apply j).comp (measurable_pi_apply (i : ℕ))).div_const _

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianRank
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Almost-sure nonsingularity of the fixed-width iid Gaussian block. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

namespace InvariantIsing

private lemma gaussian_pi_extract_law {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (f : J → I) (hf : Function.Injective f) :
    (Measure.pi (fun _ : I => gaussianReal 0 1)).map
      (fun x j => x (f j)) = Measure.pi (fun _ : J => gaussianReal 0 1) := by
  have hi : iIndepFun (fun i : I => fun x : I → ℝ => x i)
      (Measure.pi (fun _ : I => gaussianReal 0 1)) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  have he := (hi.precomp hf).map_fun_eq_pi_map (fun j =>
    (measurable_pi_apply (f j)).aemeasurable)
  simpa only [(measurePreserving_eval (fun _ : I => gaussianReal 0 1) _).map_eq] using he

/-- Replacing one coordinate by a fresh standard Gaussian preserves the
finite iid Gaussian law. The unused old coordinate causes no problem. -/
private lemma gaussian_pi_update_law {I : Type*} [Fintype I] [DecidableEq I] (i : I) :
    ((Measure.pi (fun _ : I => gaussianReal 0 1)).prod (gaussianReal 0 1)).map
      (fun p : (I → ℝ) × ℝ => Function.update p.1 i p.2) =
        Measure.pi (fun _ : I => gaussianReal 0 1) := by
  have hm : Measurable (fun p : (I → ℝ) × ℝ => Function.update p.1 i p.2) :=
    measurable_update'
  symm
  apply Measure.pi_eq
  intro s hs
  have hpre : (fun p : (I → ℝ) × ℝ => Function.update p.1 i p.2) ⁻¹' Set.univ.pi s =
      (Set.univ.pi (Function.update s i Set.univ)) ×ˢ s i := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_prod]
    constructor
    · intro hp
      refine ⟨?_, ?_⟩
      · intro j
        by_cases hji : j = i
        · subst j; simp
        · simpa only [Function.update_of_ne hji] using hp j
      · simpa only [Function.update_self] using hp i
    · rintro ⟨hp, hi⟩ j
      by_cases hji : j = i
      · subst j; simpa only [Function.update_self] using hi
      · simpa only [Function.update_of_ne hji] using hp j
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs), hpre, Measure.prod_prod,
    Measure.pi_pi]
  have he : (fun j => (gaussianReal 0 1) (Function.update s i Set.univ j)) =
      Function.update (fun j => (gaussianReal 0 1) (s j)) i 1 := by
    funext j
    by_cases hji : j = i
    · subst j; simp
    · simp only [Function.update_of_ne hji]
  rw [he, Finset.prod_update_of_mem (Finset.mem_univ i), one_mul]
  simpa only [Finset.sdiff_singleton_eq_erase] using
    (Finset.prod_erase_mul (s := Finset.univ)
      (f := fun j => (gaussianReal 0 1) (s j)) (Finset.mem_univ i))

private lemma determinant_update_corner_affine (n : ℕ)
    (x : Fin (n + 1) × Fin (n + 1) → ℝ) :
    ∃ c : ℝ, ∀ t : ℝ,
      Matrix.det (fun i j => Function.update x (0, 0) t (i, j)) =
        t * Matrix.det (fun i j : Fin n => x (i.succ, j.succ)) + c := by
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun i j => x (i, j)
  refine ⟨∑ j : Fin n, (-1 : ℝ) ^ (j.succ : ℕ) * A 0 j.succ *
    Matrix.det (A.submatrix Fin.succ j.succ.succAbove), ?_⟩
  intro t
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    fun i j => Function.update x (0, 0) t (i, j)
  have hb (j : Fin (n + 1)) : B.submatrix Fin.succ j.succAbove =
      A.submatrix Fin.succ j.succAbove := by
    ext a b
    change Function.update x (0, 0) t (a.succ, j.succAbove b) = x (a.succ, j.succAbove b)
    exact Function.update_of_ne
      (show (a.succ, j.succAbove b) ≠ (0, 0) from
        fun h => Fin.succ_ne_zero a (congrArg Prod.fst h)) t x
  change B.det = _
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp_rw [hb]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
  have h00 : B 0 0 = t := by simp [B]
  have h0j (j : Fin n) : B 0 j.succ = A 0 j.succ := by simp [B, A]
  rw [h00]
  simp_rw [h0j]
  rfl

private lemma gaussian_affine_ne_zero (a c : ℝ) (ha : a ≠ 0) :
    ∀ᵐ t ∂gaussianReal 0 1, t * a + c ≠ 0 := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hn : ∀ᵐ t ∂gaussianReal 0 1, t ≠ -c / a := by
    exact compl_mem_ae_iff.mpr (measure_singleton (-c / a))
  filter_upwards [hn] with t ht
  intro he
  apply ht
  apply (eq_div_iff ha).mpr
  linarith

/-- A square matrix with independent standard Gaussian entries is
nonsingular almost surely, including the empty-matrix convention. -/
theorem cavityGaussianSquare_det_ne_zero (n : ℕ) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 1),
      Matrix.det (fun i j => x (i, j)) ≠ 0 := by
  induction n with
  | zero =>
    apply ae_of_all
    intro x
    have h : Matrix.det (show Matrix (Fin 0) (Fin 0) ℝ from fun i j => x (i, j)) = 1 :=
      Matrix.det_isEmpty
    exact h.trans_ne one_ne_zero
  | succ n ih =>
    let μ := Measure.pi (fun _ : Fin (n + 1) × Fin (n + 1) => gaussianReal 0 1)
    let corner : Fin (n + 1) × Fin (n + 1) := (0, 0)
    let f : Fin n × Fin n → Fin (n + 1) × Fin (n + 1) := fun p => (p.1.succ, p.2.succ)
    have hf : Function.Injective f := by
      intro p q h
      exact Prod.ext (Fin.succ_inj.mp (congrArg Prod.fst h))
        (Fin.succ_inj.mp (congrArg Prod.snd h))
    have hminor : ∀ᵐ x ∂μ, Matrix.det (fun i j : Fin n => x (i.succ, j.succ)) ≠ 0 := by
      have hh : ∀ᵐ y ∂μ.map (fun x j => x (f j)),
          Matrix.det (fun i j : Fin n => y (i, j)) ≠ 0 := by
        rw [gaussian_pi_extract_law f hf]
        exact ih
      exact ae_of_ae_map
        (show AEMeasurable (fun x j => x (f j)) μ from (by fun_prop : Measurable _).aemeasurable) hh
    have hpair : ∀ᵐ p ∂μ.prod (gaussianReal 0 1),
        Matrix.det (fun i j => Function.update p.1 corner p.2 (i, j)) ≠ 0 := by
      have hm : Measurable (fun p : (Fin (n + 1) × Fin (n + 1) → ℝ) × ℝ =>
          Matrix.det (fun i j => Function.update p.1 corner p.2 (i, j))) := by
        unfold corner
        fun_prop
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hm measurable_const).compl).mpr
      filter_upwards [hminor] with x hx
      obtain ⟨c, hc⟩ := determinant_update_corner_affine n x
      filter_upwards [gaussian_affine_ne_zero _ c hx] with t ht
      simpa only [corner, hc] using ht
    rw [← gaussian_pi_update_law corner]
    apply (ae_map_iff (by fun_prop)
      (measurableSet_eq_fun (by fun_prop) measurable_const).compl).mpr
    exact hpair

/-- The concrete first `q` iid Gaussian rows used by the frame construction
are full rank almost surely. -/
theorem cavityGaussianRows_square_det_ne_zero (q : ℕ) :
    ∀ᵐ x ∂cavityGaussianRows q,
      Matrix.det (fun i j : Fin q => x i j) ≠ 0 := by
  have hh : ∀ᵐ y ∂(cavityGaussianRows q).map
      (fun x : ℕ → Fin q → ℝ => fun p : Fin q × Fin q => x p.1 p.2),
      Matrix.det (fun i j : Fin q => y (i, j)) ≠ 0 := by
    rw [(cavityGaussianRows_finite_array_law q q).map_eq]
    exact cavityGaussianSquare_det_ne_zero q
  exact ae_of_ae_map (cavityGaussianRows_finite_array_law q q).aemeasurable hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianRankGram
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive definiteness of finite Gaussian and normalized-frame windows. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator NNReal

namespace InvariantIsing

/-- Any consecutive square block of the iid Gaussian row sequence is
nonsingular almost surely. -/
theorem cavityGaussianRows_window_det_ne_zero (q l : ℕ) :
    ∀ᵐ x ∂cavityGaussianRows q,
      Matrix.det (fun i j : Fin q => x (l + i) j) ≠ 0 := by
  let f : Fin q × Fin q → ℕ × Fin q := fun p => (l + p.1, p.2)
  have hf : Function.Injective f := by
    intro p r h
    apply Prod.ext
    · apply Fin.ext
      exact Nat.add_left_cancel (congrArg Prod.fst h)
    · exact congrArg (fun z : ℕ × Fin q => z.2) h
  have hi := (cavityGaussianRows_coordinates_independent q).precomp hf
  have hm := hi.map_fun_eq_pi_map (fun p : Fin q × Fin q =>
    (cavityGaussianRows_coordinate_law (l + p.1) p.2).aemeasurable)
  have hmap : (cavityGaussianRows q).map
      (fun x => fun p : Fin q × Fin q => x (l + p.1) p.2) =
        Measure.pi (fun _ : Fin q × Fin q => gaussianReal 0 1) := by
    simpa only [(cavityGaussianRows_coordinate_law _ _).map_eq] using hm
  have hh : ∀ᵐ y ∂(cavityGaussianRows q).map
      (fun x => fun p : Fin q × Fin q => x (l + p.1) p.2),
      Matrix.det (fun i j : Fin q => y (i, j)) ≠ 0 := by
    rw [hmap]
    exact cavityGaussianSquare_det_ne_zero q
  have hm : Measurable
      (fun x : ℕ → Fin q → ℝ => fun p : Fin q × Fin q => x (l + p.1) p.2) := by
    fun_prop
  have he : ∀ᵐ x ∂cavityGaussianRows q,
      Matrix.det (fun i j : Fin q => x (l + i) j) ≠ 0 :=
    ae_of_ae_map hm.aemeasurable hh
  exact he

lemma cavity_gram_posDef_of_minor {N q : ℕ} (A : Matrix (Fin N) (Fin q) ℝ)
    (f : Fin q → Fin N) (hdet : (A.submatrix f id).det ≠ 0) :
    (A.transpose * A).PosDef := by
  have hB : Function.Injective (A.submatrix f id).mulVec :=
    Matrix.mulVec_injective_iff.mpr
      ((Matrix.nonsingular_iff_det_ne_zero.mpr hdet).linearIndependent_col)
  have hA : Function.Injective A.mulVec := by
    intro x y hxy
    apply hB
    funext i
    simpa only [Matrix.mulVec, Matrix.submatrix_apply, id_eq, dotProduct] using
      congrFun hxy (f i)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.PosDef.conjTranspose_mul_self A hA

lemma cavityWindowGram_mul {N q : ℕ} (A : Matrix (Fin N) (Fin q) ℝ)
    (C : Matrix (Fin q) (Fin q) ℝ) (l u : ℕ) :
    cavityWindowGram (A * C) l u = C.transpose * cavityWindowGram A l u * C := by
  simp only [cavityWindowGram, cavityPrefixGram_mul]
  noncomm_ring

lemma cavityWindowGram_eq_mask_gram {N q : ℕ} (A : Matrix (Fin N) (Fin q) ℝ)
    (l u : ℕ) (hlu : l ≤ u) :
    cavityWindowGram A l u =
      (cavityMaskedRows A l u).transpose * cavityMaskedRows A l u := by
  ext i j
  simp only [cavityWindowGram, Matrix.sub_apply, cavityPrefixGram_apply,
    ← Finset.sum_sub_distrib, Matrix.mul_apply, Matrix.transpose_apply, cavityMaskedRows]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hkl : k.val < l
  · have hku : k.val < u := lt_of_lt_of_le hkl hlu
    simp [hkl, hku, Nat.not_le_of_lt hkl]
  · by_cases hku : k.val < u
    · simp [hkl, hku, Nat.le_of_not_gt hkl]
    · simp [hkl, hku]

lemma cavityWindowGram_posDef_of_minor {N q : ℕ} (A : Matrix (Fin N) (Fin q) ℝ)
    (l u : ℕ) (hlu : l ≤ u) (f : Fin q → Fin N)
    (hf : ∀ i, l ≤ (f i).val ∧ (f i).val < u)
    (hdet : (A.submatrix f id).det ≠ 0) :
    (cavityWindowGram A l u).PosDef := by
  rw [cavityWindowGram_eq_mask_gram A l u hlu]
  apply cavity_gram_posDef_of_minor _ f
  convert hdet using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext i j
  simp [Matrix.submatrix_apply, cavityMaskedRows, hf i]

/-- Positive definiteness holds at every admissible finite row count. -/
theorem cavityGaussianRows_gram_posDef (N q : ℕ) (hqN : q ≤ N) :
    ∀ᵐ x ∂cavityGaussianRows q, (cavityEmpiricalGram x N).PosDef := by
  by_cases hq : q = 0
  · subst q
    apply ae_of_all
    intro x
    exact cavity_posDef_of_posSemidef_det_ne_zero
      (cavityEmpiricalGram_posSemidef x N)
      (by
        have h : (cavityEmpiricalGram x N).det = 1 := Matrix.det_isEmpty
        exact h.trans_ne one_ne_zero)
  have hN : 0 < N := by omega
  have hsqrt : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (Nat.cast_pos.mpr hN))
  filter_upwards [cavityGaussianRows_square_det_ne_zero q] with x hx
  let A := cavityGaussianMatrix x N
  let f : Fin q → Fin N := Fin.castLE hqN
  let B : Matrix (Fin q) (Fin q) ℝ := fun i j => x i j
  have he : A.submatrix f id = (Real.sqrt (N : ℝ))⁻¹ • B := by
    ext i j
    change x i j / Real.sqrt (N : ℝ) = (Real.sqrt (N : ℝ))⁻¹ * x i j
    ring
  have hdet : (A.submatrix f id).det ≠ 0 := by
    rw [he, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hsqrt)) hx
  rw [← cavityGaussianMatrix_gram]
  exact cavity_gram_posDef_of_minor A f hdet

lemma cavityGoodGram_probability_one (N q : ℕ) (hqN : q ≤ N) :
    cavityGaussianRows q (cavityGoodGram q N) = 1 := by
  have hae : cavityGoodGram q N =ᵐ[cavityGaussianRows q] Set.univ := by
    filter_upwards [cavityGaussianRows_gram_posDef N q hqN] with x hx
    change (0 < (cavityEmpiricalGram x N).det) = True
    exact propext (iff_true_intro hx.det_pos)
  rw [measure_congr hae, measure_univ]

/-- Every window containing at least `q` rows is positive definite at
finite volume, before and after the common Gram normalization. -/
theorem cavityGaussianRows_normalized_window_posDef (N q l u : ℕ)
    (hlq : l + q ≤ u) (huN : u ≤ N) :
    ∀ᵐ x ∂cavityGaussianRows q,
      (cavityWindowGram (cavityNormalizeFrame (cavityGaussianMatrix x N)) l u).PosDef := by
  have hlu : l ≤ u := by omega
  by_cases hq : q = 0
  · subst q
    apply ae_of_all
    intro x
    exact cavity_posDef_of_posSemidef_det_ne_zero
      (cavityWindowGram_posSemidef _ l u hlu) (by
        have h : (cavityWindowGram
          (cavityNormalizeFrame (cavityGaussianMatrix x N)) l u).det = 1 := Matrix.det_isEmpty
        exact h.trans_ne one_ne_zero)
  have hN : 0 < N := by omega
  have hsqrt : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (Nat.cast_pos.mpr hN))
  filter_upwards [cavityGaussianRows_window_det_ne_zero q l] with x hx
  let A := cavityGaussianMatrix x N
  let f : Fin q → Fin N := fun i => ⟨l + i.val, by omega⟩
  have hf : ∀ i, l ≤ (f i).val ∧ (f i).val < u := by
    intro i
    dsimp [f]
    constructor <;> omega
  let B : Matrix (Fin q) (Fin q) ℝ := fun i j => x (l + i) j
  have he : A.submatrix f id = (Real.sqrt (N : ℝ))⁻¹ • B := by
    ext i j
    change x (l + i) j / Real.sqrt (N : ℝ) = (Real.sqrt (N : ℝ))⁻¹ * x (l + i) j
    ring
  have hdet : (A.submatrix f id).det ≠ 0 := by
    rw [he, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hsqrt)) hx
  have hG := cavity_gram_posDef_of_minor A f hdet
  have hW := cavityWindowGram_posDef_of_minor A l u hlu f hf hdet
  have hS := cavity_sqrt_det_isUnit (A.transpose * A) hG
  let C := (CFC.sqrt (A.transpose * A))⁻¹
  have hC : Function.Injective C.mulVec := by
    apply Matrix.mulVec_injective_iff.mpr
    apply Matrix.Nonsingular.linearIndependent_col
    apply Matrix.nonsingular_iff_det_ne_zero.mpr
    exact (Matrix.isUnit_nonsing_inv_det (CFC.sqrt (A.transpose * A)) hS).ne_zero
  change (cavityWindowGram (A * C) l u).PosDef
  rw [cavityWindowGram_mul]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hW.conjTranspose_mul_mul_same hC

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarRank
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Almost-sure positive definiteness of finite Haar spectral compressions. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

/-- A Haar-rotated orthonormal `q`-frame has positive-definite compression
to every fixed coordinate window containing at least `q` rows. -/
theorem cavityHaarWindowGram_posDef {N q : ℕ} (l u : ℕ)
    (hlq : l + q ≤ u) (huN : u ≤ N)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (A₀ : Matrix (Fin N) (Fin q) ℝ) (hA₀ : A₀.transpose * A₀ = 1) :
    ∀ᵐ (U : Orthogonal N) ∂μ, (cavityWindowGram ((U : Matrix (Fin N) (Fin N) ℝ) * A₀) l u).PosDef := by
  have hqN : q ≤ N := by omega
  have hlu : l ≤ u := by omega
  have hp : stdGaussian (EuclideanSpace ℝ (Fin N × Fin q)) (cavityArrayGood N q) ≠ 0 := by
    rw [cavityArrayGood_probability, cavityGoodGram_probability_one N q hqN]
    exact one_ne_zero
  have : IsProbabilityMeasure (cavityConditionedFrameLaw N q) :=
    cavityConditionedFrameLaw_probability hp
  have hdet : Measurable (fun A : Matrix (Fin N) (Fin q) ℝ =>
      (cavityWindowGram A l u).det) :=
    (continuous_cavityWindowGram N q l u).matrix_det.measurable
  have hs : MeasurableSet {A : Matrix (Fin N) (Fin q) ℝ |
      0 < (cavityWindowGram A l u).det} := measurableSet_lt measurable_const hdet
  have hraw : ∀ᵐ x ∂cond (cavityGaussianRows q) (cavityGoodGram q N),
      0 < (cavityWindowGram (cavityNormalizeFrame (cavityGaussianMatrix x N)) l u).det := by
    exact cond_absolutelyContinuous.ae_le
      ((cavityGaussianRows_normalized_window_posDef N q l u hlq huN).mono
        (fun _ hx => hx.det_pos))
  have hframe : ∀ᵐ A ∂cavityConditionedFrameLaw N q,
      0 < (cavityWindowGram A l u).det := by
    rw [← cavityConditionedFrameLaw_of_rows N q]
    exact (ae_map_iff (measurable_cavityGaussianNormalizedFrame q N).aemeasurable hs).mpr hraw
  rw [cavityFrame_eq_haar_orbit μ (cavityConditionedFrameLaw N q)
    cavityConditionedFrameLaw_rotation (cavityConditionedFrameLaw_orthonormal N q) A₀ hA₀] at hframe
  have hm : Measurable (fun U : Orthogonal N =>
      (U : Matrix (Fin N) (Fin N) ℝ) * A₀) :=
    ((continuous_cavityFrameAction N q).comp
      (continuous_id.prodMk continuous_const)).measurable
  have he : ∀ᵐ (U : Orthogonal N) ∂μ,
      0 < (cavityWindowGram ((U : Matrix (Fin N) (Fin N) ℝ) * A₀) l u).det :=
    ae_of_ae_map hm.aemeasurable hframe
  filter_upwards [he] with U hU
  exact cavity_posDef_of_posSemidef_det_ne_zero
    (cavityWindowGram_posSemidef _ l u hlu) hU.ne'

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCompressionRank
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.planeRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
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

lemma cavityColumns_eq_mul {N n : ℕ} (U : Orthogonal (N + n)) :
    cavityColumns U = (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) *
      cavityColumns (1 : Orthogonal (N + n)) := by
  ext i j
  change (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) i (Fin.natAdd N j) =
    ∑ k : Fin (N + n), (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) i k *
      (if k = Fin.natAdd N j then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]

lemma cavityCompressionGrams_eq_window {N n m : ℕ} (g : Fin (N + n) → Fin m)
    (a : Fin m) (l u : ℕ) (hlu : l ≤ u)
    (hg : ∀ i, g i = a ↔ l ≤ i.val ∧ i.val < u) (U : Orthogonal (N + n)) :
    cavityCompressionGrams g U a = cavityWindowGram (cavityColumns U) l u := by
  ext i j
  change (∑ k : Fin (N + n), (if g k = a then cavityColumns U k i else 0) *
    (if g k = a then cavityColumns U k j else 0)) = _
  rw [cavityWindowGram, Matrix.sub_apply, cavityPrefixGram_apply, cavityPrefixGram_apply,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [hg k]
  split_ifs <;> simp_all <;> omega

theorem cavityCompressionGrams_posDef_ae {N n m : ℕ}
    (g : Fin (N + n) → Fin m) (l u : Fin m → ℕ)
    (hg : ∀ a i, g i = a ↔ l a ≤ i.val ∧ i.val < u a)
    (hln : ∀ a, l a + n ≤ u a) (hu : ∀ a, u a ≤ N + n)
    (μ : Measure (Orthogonal (N + n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant] :
    ∀ᵐ U ∂μ, ∀ a, (cavityCompressionGrams g U a).PosDef := by
  apply ae_all_iff.mpr
  intro a
  have h := cavityHaarWindowGram_posDef (l a) (u a) (hln a) (hu a) μ
    (cavityColumns (1 : Orthogonal (N + n))) (cavityColumns_gram _)
  filter_upwards [h] with U hU
  rw [cavityCompressionGrams_eq_window g a (l a) (u a) (by have := hln a; omega) (hg a) U,
    cavityColumns_eq_mul]
  exact hU

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

lemma cavityConcreteComplement_perp {N n m d : ℕ}
    (g : Fin (N + n) → Fin m) (e : Fin (m * n) ≃ Fin (d + n))
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ) (U : Orthogonal (N + n)) :
    (cavityConcreteComplement e B₀ (cavityCompressionGrams g U)).transpose *
      cavitySpectralStack (cavityCompressionGrams g U) = 0 := by
  have h := congrArg Matrix.transpose (cavitySelectedComplement_orthogonal B₀ _
    (cavityReindexedStack_compression_gram g e U))
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] at h
  ext i j
  have he := Equiv.sum_comp e (fun k =>
    cavitySelectedComplement B₀ (cavityReindexedStack e (cavityCompressionGrams g U)) k i *
      cavityReindexedStack e (cavityCompressionGrams g U) k j)
  simpa only [cavityConcreteComplement, cavityReindexedStack, Equiv.symm_apply_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply] using
      he.trans (congrArg (fun A : Matrix (Fin d) (Fin n) ℝ => A i j) h)

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPhysicalFrameOrbit
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single reservoir rotation represents both the base interaction
and its selected special axes, as needed for the fresh-frame law. -/

noncomputable section
open scoped Matrix BigOperators

namespace InvariantIsing

lemma cavityReservoir_spectral_eq {N n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ Fin N) (F : Matrix (Fin (N + n)) ι ℝ) (lam : ι → ℝ)
    (V : Orthogonal N)
    (hV : ∀ i j, (V : Matrix (Fin N) (Fin N) ℝ) i j = cavityReservoirRows F i (e.symm j)) :
    cavityReservoirRows F * Matrix.diagonal lam * (cavityReservoirRows F).transpose =
      (V : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal (fun j => lam (e.symm j)) *
        (V : Matrix (Fin N) (Fin N) ℝ).transpose := by
  ext i j
  change (∑ k : ι, (∑ t : ι, cavityReservoirRows F i t *
      (if t = k then lam t else 0)) * cavityReservoirRows F j k) =
    ∑ k : Fin N, (∑ t : Fin N, (V : Matrix (Fin N) (Fin N) ℝ) i t *
      (if t = k then lam (e.symm t) else 0)) * (V : Matrix (Fin N) (Fin N) ℝ) j k
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true, hV]
  exact (Equiv.sum_comp e.symm (fun k : ι =>
    cavityReservoirRows F i k * lam k * cavityReservoirRows F j k)).symm

lemma cavityCanonicalSpecial_mul {N d : ℕ} {ι : Type*} (e : (ι ⊕ Fin d) ≃ Fin N)
    (V : Matrix (Fin N) (Fin N) ℝ) (i : Fin N) (j : Fin d) :
    (V * cavityCanonicalSpecial e) i j = V i (e (Sum.inr j)) := by
  simp only [Matrix.mul_apply, cavityCanonicalSpecial, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityConcreteFrameOrbit
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual base interaction and special axes belong jointly to a
single prescribed Haar orbit, not merely to separate marginal orbits. -/

noncomputable section
open MeasureTheory
open scoped Matrix BigOperators

namespace InvariantIsing

lemma cavityReservoirRotation_leftRows {N n d : ℕ} (V : Orthogonal N)
    (F : Matrix (Fin (N + n)) (Fin d) ℝ) :
    cavityReservoirRows
      ((cavityReservoirRotation (n := n) V : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose * F) =
      (V : Matrix (Fin N) (Fin N) ℝ).transpose * cavityReservoirRows F := by
  ext i j
  change (∑ k : Fin (N + n),
    (cavityReservoirRotation (n := n) V : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)
      k (i.castAdd n) * F k j) =
    ∑ k : Fin N, (V : Matrix (Fin N) (Fin N) ℝ) k i * F (k.castAdd n) j
  simp only [Fin.sum_univ_add, cavityReservoirRotation_first,
    cavityReservoirRotation_lowerLeft, zero_mul, Finset.sum_const_zero, add_zero]

lemma measurable_cavityPhysicalSpecial {N n m d : ℕ} (g : Fin (N + n) → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (hB : Measurable B) : Measurable (cavityPhysicalSpecial g B) := by
  let : OpensMeasurableSpace (Matrix (Fin (N + n)) (Fin (m * n)) ℝ ×
      Matrix (Fin (m * n)) (Fin d) ℝ) := inferInstanceAs
    (OpensMeasurableSpace ((Fin (N + n) → Fin (m * n) → ℝ) × (Fin (m * n) → Fin d → ℝ)))
  let : OpensMeasurableSpace (Orthogonal (N + n) × Matrix (Fin (N + n)) (Fin d) ℝ) :=
    inferInstanceAs (OpensMeasurableSpace (Orthogonal (N + n) × (Fin (N + n) → Fin d → ℝ)))
  have hX : Measurable (fun U : Orthogonal (N + n) =>
      cavitySpectralImage g (cavityColumns U)) := measurable_pi_iff.mpr
    (fun a => (measurable_cavitySpectralImage g a).comp (measurable_cavityColumns N n))
  have hW := (measurable_cavityEigenspaceFrame (N + n) m n).comp hX
  have hBU := hB.comp (measurable_cavityCompressionGrams g)
  have hmul : Continuous (fun p : Matrix (Fin (N + n)) (Fin (m * n)) ℝ ×
      Matrix (Fin (m * n)) (Fin d) ℝ => p.1 * p.2) :=
    continuous_fst.matrix_mul continuous_snd
  have hWB := hmul.measurable.comp (hW.prodMk hBU)
  have hleft : Continuous (fun p : Orthogonal (N + n) × Matrix (Fin (N + n)) (Fin d) ℝ =>
      (p.1 : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose * p.2) :=
    (continuous_subtype_val.comp continuous_fst).matrix_transpose.matrix_mul continuous_snd
  have h := hleft.measurable.comp (measurable_id.prodMk hWB)
  apply Measurable.of_eval_matrix
  intro i j
  exact h.eval_matrix

lemma cavityPhysicalSpecial_reservoir {N n m d : ℕ} (g : Fin (N + n) → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (U : Orthogonal (N + n)) (V : Orthogonal N) :
    cavityPhysicalSpecial g B (U * cavityReservoirRotation (n := n) V) =
      (V : Matrix (Fin N) (Fin N) ℝ).transpose * cavityPhysicalSpecial g B U := by
  have hc : cavityColumns (U * cavityReservoirRotation (n := n) V) = cavityColumns U :=
    cavityReservoirRotation_cavityColumns _ V
  unfold cavityPhysicalSpecial
  rw [hc, cavityCompressionGrams_reservoir]
  change cavityReservoirRows
    ((((U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) *
      (cavityReservoirRotation (n := n) V : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)).transpose) * _) = _
  rw [Matrix.transpose_mul, Matrix.mul_assoc, cavityReservoirRotation_leftRows]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFullSymmetry
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full finite Ising model with its actual spectral/tree tensor
perturbation has signed site-permutation symmetry after Haar averaging. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma measurable_cavityPerturbationField {N m depth : ℕ}
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (x : Spin N × LabeledLeaf depth) :
    Measurable (fun p : SpecialOrthogonal N × (ℕ → ℝ) =>
      cylinderField (cavityPerturbationCoefficients (specialRotation p.1) I u depth x) p.2) := by
  simp only [cavityPerturbationCoefficients, tensorLeafCoefficients, cylinderField_feature]
  apply Finset.measurable_sum
  intro i _
  exact (((measurable_spinTensorFeature I _ _ x.1 i.2).comp measurable_fst).const_mul _).mul
    ((measurable_pi_apply (treeFeatureTag depth x.2 i)).comp measurable_snd)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityReplicaCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit normalization of a cutoff in a bounded two-replica test.
The ratio convention also covers an empty cutoff. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Classical

namespace InvariantIsing

lemma measurable_cavityCutoffReplicaMean {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (H : Ω × X → ℝ) (hH : Measurable H) (s : Ω → Set X)
    (hs : MeasurableSet {p : Ω × X | p.2 ∈ s p.1})
    (F : Ω × (Fin 2 → X) → ℝ) (hF : Measurable F) :
    Measurable (fun ω => cavityCutoffReplicaMean ν (fun x => H (ω, x)) (s ω)
      (fun σ => F (ω, σ))) := by
  have hS : MeasurableSet {p : Ω × (Fin 2 → X) | ∀ i, p.2 i ∈ s p.1} := by
    have he : {p : Ω × (Fin 2 → X) | ∀ i, p.2 i ∈ s p.1} =
        ⋂ i, {p : Ω × (Fin 2 → X) | p.2 i ∈ s p.1} := by ext p; simp
    rw [he]
    exact MeasurableSet.iInter (fun i => hs.preimage
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  exact (measurable_referenceReplicaMean ν (H := H) hH
    (Measurable.ite hS hF measurable_const)).div
      (measurable_referenceReplicaMean ν (H := H) hH
        (Measurable.ite hS measurable_const measurable_const))

lemma cavity_cutoff_replica_eq_cond {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (hH : Integrable (fun x => Real.exp (H x)) ν)
    (s : Set X) (hs : MeasurableSet s) (F : (Fin 2 → X) → ℝ) :
    cavityCutoffReplicaMean ν H s F =
      ∫ σ, F σ ∂cond (Measure.pi (fun _ : Fin 2 => ν.tilted H))
        (univ.pi (fun _ => s)) := by
  let P := Measure.pi (fun _ : Fin 2 => ν.tilted H)
  let S := univ.pi (fun _ : Fin 2 => s)
  have hS : MeasurableSet S := MeasurableSet.univ_pi (fun _ => hs)
  have hnum : (fun σ : Fin 2 → X => if ∀ i, σ i ∈ s then F σ else 0) = S.indicator F := by
    funext σ
    simp only [S, mem_univ_pi, indicator_apply]
  have hden : (fun σ : Fin 2 → X => if ∀ i, σ i ∈ s then (1 : ℝ) else 0) =
      S.indicator (fun _ => (1 : ℝ)) := by
    funext σ
    simp only [S, mem_univ_pi, indicator_apply]
  rw [cavityCutoffReplicaMean, referenceReplicaMean_eq_tilted ν H hH,
    referenceReplicaMean_eq_tilted ν H hH, hnum, hden]
  change (∫ σ, S.indicator F σ ∂P) / (∫ σ, S.indicator (fun _ => (1 : ℝ)) σ ∂P) = _
  rw [integral_indicator hS, integral_indicator hS, integral_const]
  rw [ProbabilityTheory.cond, integral_smul_measure]
  simp only [smul_eq_mul, ENNReal.toReal_inv, Measure.real, Measure.restrict_apply_univ, mul_one, div_eq_inv_mul]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRandomCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A random cutoff changes bounded replica tests by its discarded
one-replica probability, after averaging over the common disorder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Classical

namespace InvariantIsing

lemma cavity_cutoff_replica_abs_le {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (hH : Integrable (fun x => Real.exp (H x)) ν)
    (s : Set X) (hs : MeasurableSet s) (F : (Fin 2 → X) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ σ, |F σ| ≤ M) :
    |cavityCutoffReplicaMean ν H s F| ≤ M := by
  rw [cavity_cutoff_replica_eq_cond ν H hH s hs F]
  have h := norm_integral_le_of_norm_le_const
    (μ := cond (Measure.pi (fun _ : Fin 2 => ν.tilted H)) (univ.pi (fun _ => s)))
    (f := F) (C := M) (ae_of_all _ (fun σ => by
      simpa only [Real.norm_eq_abs] using hF σ))
  rw [Real.norm_eq_abs] at h
  exact h.trans (mul_le_of_le_one_right hM measureReal_le_one)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCutoffTotalBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized cutoff is bounded also when its partition integral
is undefined: the existing zero convention then gives zero. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_cutoff_replica_abs_le_all {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (s : Set X) (F : (Fin 2 → X) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ σ, |F σ| ≤ M) :
    |cavityCutoffReplicaMean ν H s F| ≤ M := by
  by_cases hi : Integrable (fun x => Real.exp (H x)) ν
  · exact cavity_cutoff_replica_abs_le ν H hi s (Set.to_countable s).measurableSet F hM hF
  · have hz : referencePartition ν H = 0 := integral_undef hi
    simp only [cavityCutoffReplicaMean, referenceReplicaMean, hz, zero_pow (by decide : 2 ≠ 0),
      div_zero, abs_zero]
    exact hM

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGeometricTail
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full-model cutoff estimate for the actual normalized spectral
image construction, with no inverse-Gram estimate on the bad event. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma measurable_cavityFullSpecialCoordinates {N n m d : ℕ}
    (g : Fin (N + n) → Fin m)
    (B : SpecialOrthogonal (N + n) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (hB : Measurable B) (σ : Spin (N + n)) :
    Measurable (fun U => cavityFullSpecialCoordinates g (B U) U σ) := by
  have hO : Measurable (cavitySpecialOrthogonal (N := N + n)) :=
    measurable_subtype_coe.subtype_mk
  have hA : Measurable (fun U : SpecialOrthogonal (N + n) =>
      cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U))) :=
    measurable_pi_iff.mpr fun a => ((measurable_cavitySpectralImage g a).comp
      (measurable_cavityColumns N n)).comp hO
  have hW := (measurable_cavityEigenspaceFrame (N + n) m n).comp hA
  have hmul : Continuous (fun p : Matrix (Fin (N + n)) (Fin (m * n)) ℝ ×
      Matrix (Fin (m * n)) (Fin d) ℝ => p.1 * p.2) :=
    continuous_fst.matrix_mul continuous_snd
  have hV := hmul.measurable.comp (hW.prodMk hB)
  have hz : Measurable (fun U : SpecialOrthogonal (N + n) =>
      ((cavityEigenspaceFrame (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U))) *
        B U).transpose *ᵥ (specialRotation U (spinVector σ)).ofLp)) := by
    apply measurable_pi_iff.mpr
    intro j
    change Measurable (fun U : SpecialOrthogonal (N + n) => ∑ i : Fin (N + n),
      (cavityEigenspaceFrame (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U))) *
        B U) i j * specialRotation U (spinVector σ) i)
    apply Finset.measurable_sum
    intro i _
    exact hV.eval_matrix.mul (measurable_specialRotation_eval (spinVector σ) i)
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.continuous.measurable).comp hz

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFullCutoff
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded cutoff tests for the actual perturbed Ising law, with the
same Haar and Gaussian disorder in the full and restricted models. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Classical

namespace InvariantIsing

lemma measurable_cavityFullHamiltonian {N m depth : ℕ} (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    Measurable (Function.uncurry (cavityFullHamiltonian (depth := depth) eig I u)) := by
  apply measurable_from_prod_countable_left
  intro x
  have hr : Measurable (fun U : SpecialOrthogonal N => rotatedEnergy eig (specialRotation U) x.1) := by
    unfold rotatedEnergy
    exact (Finset.measurable_sum _ fun i _ =>
      ((measurable_specialRotation_eval (spinVector x.1) i).pow_const 2).const_mul (eig i)).const_mul _
  exact (hr.comp measurable_fst).add (measurable_cavityPerturbationField I u x)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySimultaneousFrame
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single physical eigenframe represents every assignment of the
spectral values. In particular it retains the labeled spectral
projectors even when two physical eigenvalues coincide. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

theorem cavityBaseFrame_simultaneous_orbit {N n s d : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (e : (ι ⊕ Fin d) ≃ Fin N)
    (U : Orthogonal (N+n)) (R : Matrix (Fin (N+n)) ι ℝ)
    (W : Matrix (Fin (N+n)) (Fin s) ℝ) (B : Matrix (Fin s) (Fin d) ℝ)
    (T : Matrix (Fin s) (Fin n) ℝ)
    (hR : R.transpose * R = 1) (hW : W.transpose * W = 1)
    (hRW : R.transpose * W = 0) (hB : B.transpose * B = 1)
    (hBT : B.transpose * T = 0)
    (hWT : W*T = fun i j => (U : Matrix (Fin (N+n)) (Fin (N+n)) ℝ) i (Fin.natAdd N j)) :
    ∃ V : Orthogonal N,
      (∀ lam : ι ⊕ Fin d → ℝ,
        ((U : Matrix (Fin (N+n)) (Fin (N+n)) ℝ).transpose *
          (Matrix.fromCols R (W*B) * Matrix.diagonal lam * (Matrix.fromCols R (W*B)).transpose) *
          (U : Matrix (Fin (N+n)) (Fin (N+n)) ℝ)).submatrix (Fin.castAdd n) (Fin.castAdd n) =
          cavityConjugate V (Matrix.diagonal (fun j => lam (e.symm j)))) ∧
      cavityReservoirRows ((U : Matrix (Fin (N+n)) (Fin (N+n)) ℝ).transpose * (W*B)) =
        (V : Matrix (Fin N) (Fin N) ℝ) * cavityCanonicalSpecial e := by
  let F := Matrix.fromCols R (W*B)
  let P := (U : Matrix (Fin (N+n)) (Fin (N+n)) ℝ).transpose * F
  have hFG : F.transpose * F = 1 := cavityBaseFrame_gram R W B hR hW hRW hB
  have hPG : P.transpose * P = 1 := (cavityPhysicalFrame_gram U F).trans hFG
  have hPF : ∀ i : Fin n, ∀ j, P (Fin.natAdd N i) j = 0 := by
    apply cavityPhysicalFrame_lastRows _ F
    rw [← hWT]
    exact cavityBaseFrame_cavity_perp R W B T hW hRW hBT
  obtain ⟨V,hV⟩ := cavityReservoirRows_orthogonal e P hPG hPF
  refine ⟨V, ?_, ?_⟩
  · intro lam
    have hp : (U : Matrix (Fin (N+n)) (Fin (N+n)) ℝ).transpose *
        (F * Matrix.diagonal lam * F.transpose) * (U : Matrix (Fin (N+n)) (Fin (N+n)) ℝ) =
        P * Matrix.diagonal lam * P.transpose := by
      simp only [P, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [hp, cavityReservoirRows_conjugate]
    exact cavityReservoir_spectral_eq e P lam V hV
  · ext i j
    rw [cavityCanonicalSpecial_mul, hV]
    simp only [Equiv.symm_apply_apply]
    rfl

theorem cavityPhysicalBaseSpecial_simultaneous {N n m d : ℕ}
    (g : Fin (N+n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N+n) // g i = a} ≃ Fin (k a+n))
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (U : Orthogonal (N+n))
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (hB : (B (cavityCompressionGrams g U)).transpose * B (cavityCompressionGrams g U) = 1)
    (hBT : (B (cavityCompressionGrams g U)).transpose *
      cavitySpectralStack (cavityCompressionGrams g U) = 0)
    (hA : ∀ a, (cavityCompressionGrams g U a).PosDef) :
    ∃ V : Orthogonal N,
      (∀ (lam : Fin m → ℝ) (lam₀ : Fin d → ℝ),
        cavityPhysicalBase g lam B (Matrix.diagonal lam₀) U =
          cavityConjugate V (Matrix.diagonal
            (fun j => Sum.elim (fun w => lam w.1) lam₀ (e.symm j)))) ∧
      cavityPhysicalSpecial g B U =
        (V : Matrix (Fin N) (Fin N) ℝ) * cavityCanonicalSpecial e := by
  classical
  let A := cavityColumns U
  let X := cavitySpectralImage g A
  choose R hRG hRX hRS hRP using fun a => cavityRetainedFrame_exists g A a (ek a) (hA a)
  have hcross : ∀ a b, a ≠ b → (R a).transpose * R b = 0 := by
    intro a b hab
    exact cavitySpectralSupport_crossGram g a b hab (R a) (R b) (hRS a) (hRS b)
  have hperp : ∀ a b, (R a).transpose * cavityNormalizeFrame (X b) = 0 := by
    intro a b
    by_cases hab : a = b
    · subst b
      have h := congrArg Matrix.transpose (hRX a)
      simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h
    · exact cavitySpectralSupport_crossGram g a b hab (R a) _ (hRS a)
        (cavityNormalizeFrame_spectral_support g A b)
  have hWT : cavityEigenspaceFrame X * cavitySpectralStack (cavityCompressionGrams g U) = A := by
    change cavityEigenspaceFrame X * cavitySpectralStack (fun a => (X a).transpose * X a) = A
    rw [cavityEigenspaceFrame_stack X hA]
    exact cavitySpectralImage_sum g A
  obtain ⟨V, hV, hVS⟩ := cavityBaseFrame_simultaneous_orbit e U
    (cavityRetainedStack k R) (cavityEigenspaceFrame X) (B (cavityCompressionGrams g U))
    (cavitySpectralStack (cavityCompressionGrams g U))
    (cavityRetainedStack_gram k R hRG hcross)
    (cavityEigenspaceFrame_gram X hA (cavitySpectralImage_crossGram g A))
    (cavityRetainedStack_perp k R X hperp) hB hBT hWT
  refine ⟨V, ?_, hVS⟩
  intro lam lam₀
  have hJ := cavityBase_spectral_decomposition g A lam k R hRS hRP
    (B (cavityCompressionGrams g U)) (Matrix.diagonal lam₀)
  rw [← cavityBaseFrame_spectral_sum] at hJ
  change ((_ * cavityBaseReplacement _ _ _ _ _ * _).submatrix _ _) = _
  rw [hJ]
  exact hV (Sum.elim (fun w => lam w.1) lam₀)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLabeledProjectors
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint labeled spectral projectors and special axes of the physical
base model. Labels are retained even for repeated spectral values. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Matrix

namespace InvariantIsing

lemma continuous_cavityLabeledProjectorAction (N m d : ℕ) :
    Continuous (Function.uncurry (cavityLabeledProjectorAction (N := N) (m := m) (d := d))) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro a
    exact (continuous_cavityConjugate N).comp (continuous_fst.prodMk
      ((continuous_apply a).comp (continuous_fst.comp continuous_snd)))
  · exact (continuous_subtype_val.comp continuous_fst).matrix_mul
      (continuous_snd.comp continuous_snd)

lemma cavityLabeledProjectorAction_mul {N m d : ℕ} (U V : Orthogonal N)
    (p : CavityProjectorFrame N m d) :
    cavityLabeledProjectorAction (U*V) p =
      cavityLabeledProjectorAction U (cavityLabeledProjectorAction V p) := by
  apply Prod.ext
  · funext a
    exact cavityConjugate_mul U V (p.1 a)
  · exact Matrix.mul_assoc _ _ _

lemma measurable_cavityPhysicalLabeledProjectors {N n m d : ℕ}
    (g : Fin (N+n) → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (hB : Measurable B) (a₀ : Fin d → Fin m) :
    Measurable (cavityPhysicalLabeledProjectors g B a₀) := by
  unfold cavityPhysicalLabeledProjectors
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro a
    exact measurable_cavityPhysicalBase g (fun b => if b=a then 1 else 0) B hB
      (Matrix.diagonal (fun j => if a₀ j=a then 1 else 0))
  · exact measurable_cavityPhysicalSpecial g B hB

lemma cavityPhysicalLabeledProjectors_reservoir {N n m d : ℕ}
    (g : Fin (N+n) → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (a₀ : Fin d → Fin m) (U : Orthogonal (N+n)) (V : Orthogonal N) :
    cavityPhysicalLabeledProjectors g B a₀ (U*cavityReservoirRotation (n := n) V⁻¹) =
      cavityLabeledProjectorAction V (cavityPhysicalLabeledProjectors g B a₀ U) := by
  apply Prod.ext
  · funext a
    exact cavityPhysicalBase_reservoir_inv g (fun b => if b=a then 1 else 0) B
      (Matrix.diagonal (fun j => if a₀ j=a then 1 else 0)) U V
  · have h := cavityPhysicalSpecial_reservoir g B U V⁻¹
    have hV : (V⁻¹ : Orthogonal N).val = (V : Matrix (Fin N) (Fin N) ℝ).transpose := by
      ext i j
      rfl
    simpa only [hV, Matrix.transpose_transpose, cavityPhysicalLabeledProjectors,
      cavityLabeledProjectorAction] using h

theorem cavityPhysicalLabeledProjectors_mem_orbit {N n m d : ℕ}
    (g : Fin (N+n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N+n) // g i = a} ≃ Fin (k a+n))
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (U : Orthogonal (N+n))
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (hB : (B (cavityCompressionGrams g U)).transpose * B (cavityCompressionGrams g U) = 1)
    (hBT : (B (cavityCompressionGrams g U)).transpose *
      cavitySpectralStack (cavityCompressionGrams g U) = 0)
    (hA : ∀ a, (cavityCompressionGrams g U a).PosDef) :
    ∃ V : Orthogonal N, cavityPhysicalLabeledProjectors g B a₀ U =
      cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀) := by
  obtain ⟨V,hV,hS⟩ := cavityPhysicalBaseSpecial_simultaneous g k ek e U B hB hBT hA
  refine ⟨V, Prod.ext ?_ hS⟩
  funext a
  exact hV (fun b => if b=a then 1 else 0) (fun j => if a₀ j=a then 1 else 0)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOrbitJointAE
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.planeRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint bounded tests in the orbit factorization retain the random
compression parameter inside the test. -/

noncomputable section
open MeasureTheory

namespace InvariantIsing

theorem cavity_orbit_joint_right_ae {N M : ℕ} {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure (Orthogonal M)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]
    (e : Orthogonal N → Orthogonal M)
    (F : Orthogonal M → X) (T : Orthogonal M → Y)
    (hF : Measurable F) (hT : Measurable T)
    (act : Orthogonal N → X → X) (hact : Measurable (Function.uncurry act))
    (hmul : ∀ U V x, act (U*V) x = act U (act V x))
    (heF : ∀ V, ∀ᵐ U ∂μ, F (U*e V) = act V (F U))
    (heT : ∀ V, ∀ᵐ U ∂μ, T (U*e V) = T U)
    (x₀ : X) (horbit : ∀ᵐ U ∂μ, ∃ V, F U = act V x₀)
    (f : Y × X → ℝ) (hf : Measurable f)
    (C : ℝ) (hb : ∀ p, ‖f p‖ ≤ C) :
    (∫ U, f (T U,F U) ∂μ) = ∫ U, ∫ V, f (T U,act V x₀) ∂ν ∂μ := by
  let B := fun p : Orthogonal N × Orthogonal M => f (T p.2,act p.1 (F p.2))
  have hm : Measurable B := hf.comp ((hT.comp measurable_snd).prodMk
    (hact.comp (measurable_fst.prodMk (hF.comp measurable_snd))))
  have hi : Integrable B (ν.prod μ) :=
    Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ fun p => hb _)
  have hrow V : (∫ U, B (V,U) ∂μ) = ∫ U, f (T U,F U) ∂μ := by
    calc
      _ = ∫ U, f (T (U*e V),F (U*e V)) ∂μ := by
        apply integral_congr_ae
        filter_upwards [heF V,heT V] with U hFU hTU
        simp only [B,hTU,hFU]
      _ = _ := integral_mul_right_eq_self (fun U => f (T U,F U)) (e V)
  have hcol : ∀ᵐ U ∂μ, (∫ V, B (V,U) ∂ν) = ∫ V, f (T U,act V x₀) ∂ν := by
    filter_upwards [horbit] with U hU
    obtain ⟨W,hW⟩ := hU
    change (∫ V, f (T U,act V (F U)) ∂ν) = _
    rw [hW]
    simp_rw [← hmul]
    exact integral_mul_right_eq_self (fun V => f (T U,act V x₀)) W
  calc
    _ = ∫ V, ∫ U, B (V,U) ∂μ ∂ν := by simp only [hrow] <;> simp
    _ = ∫ U, ∫ V, B (V,U) ∂ν ∂μ := integral_integral_swap hi
    _ = _ := integral_congr_ae hcol

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOrientation
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Correcting a spectral row sign sends an orthogonal matrix to SO
without changing its spectral compression blocks. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavityOrientationLift_compression {N n m : ℕ} (hN : 0 < N + n)
    (g : Fin (N + n) → Fin m) (U : Orthogonal (N + n)) :
    cavityCompressionGrams g (cavitySpecialOrthogonal (cavityOrientationLift hN U)) =
      cavityCompressionGrams g U := by
  funext a
  ext i j
  change (∑ k : Fin (N + n),
    (if g k = a then (cavityOrientationSign hN U * (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)) k (Fin.natAdd N i) else 0) *
      (if g k = a then (cavityOrientationSign hN U * (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)) k (Fin.natAdd N j) else 0)) =
    ∑ k : Fin (N + n), (if g k = a then (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) k (Fin.natAdd N i) else 0) *
      (if g k = a then (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) k (Fin.natAdd N j) else 0)
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : g k = a
  · simp only [hk, ite_true, if_true, cavityOrientationSign, Matrix.diagonal_mul]
    split_ifs
    · rcases orthogonal_det_eq_one_or_neg_one U with h | h <;> rw [h] <;> ring
    · ring
  · simp only [hk, ite_false, if_false, mul_zero]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOrientedProjectors
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The SO orientation correction preserves the full physical labeled
projector/frame data, as well as the compression matrices. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

lemma cavityOrientationSign_gram {N : ℕ} (hN : 0 < N) (U : Orthogonal N) :
    (cavityOrientationSign hN U).transpose * cavityOrientationSign hN U = 1 := by
  simpa only [cavityOrientationSign, Matrix.diagonal_transpose] using
    cavityOrientationSign_square hN U

lemma cavityOrientationSign_diagonal {N : ℕ} (hN : 0 < N) (U : Orthogonal N)
    (lam : Fin N → ℝ) :
    cavityOrientationSign hN U * Matrix.diagonal lam * (cavityOrientationSign hN U).transpose =
      Matrix.diagonal lam := by
  have hc : cavityOrientationSign hN U * Matrix.diagonal lam =
      Matrix.diagonal lam * cavityOrientationSign hN U := by
    simp only [cavityOrientationSign, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    ring
  rw [hc, Matrix.mul_assoc, cavityOrientationSign_square, Matrix.mul_one]

lemma cavityOrientationLift_eigenspace {N n m : ℕ} (hN : 0 < N+n)
    (g : Fin (N+n) → Fin m) (U : Orthogonal (N+n)) :
    cavityEigenspaceFrame (cavitySpectralImage g
      (cavityColumns (cavitySpecialOrthogonal (cavityOrientationLift hN U)))) =
    cavityOrientationSign hN U * cavityEigenspaceFrame (cavitySpectralImage g (cavityColumns U)) := by
  have hx : cavitySpectralImage g
      (cavityColumns (cavitySpecialOrthogonal (cavityOrientationLift hN U))) =
      fun a => cavityOrientationSign hN U * cavitySpectralImage g (cavityColumns U) a := by
    funext a
    ext i j
    simp only [cavitySpectralImage, cavityColumns, cavitySpecialOrthogonal,
      cavityOrientationLift, cavityOrientationSign, Matrix.diagonal_mul]
    split_ifs <;> ring
  rw [hx, cavityEigenspaceFrame_left_orthogonal _ _ (cavityOrientationSign_gram hN U)]

lemma cavityOrientationLift_physicalBase {N n m d : ℕ} (hN : 0 < N+n)
    (g : Fin (N+n) → Fin m) (U : Orthogonal (N+n)) (lam : Fin m → ℝ)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (A₀ : Matrix (Fin d) (Fin d) ℝ) :
    cavityPhysicalBase g lam B A₀ (cavitySpecialOrthogonal (cavityOrientationLift hN U)) =
      cavityPhysicalBase g lam B A₀ U := by
  let D := cavityOrientationSign hN U
  let O : Matrix (Fin (N+n)) (Fin (N+n)) ℝ := U
  let W := cavityEigenspaceFrame (cavitySpectralImage g (cavityColumns U))
  let J := Matrix.diagonal (fun i => lam (g i))
  have hD : D.transpose * D = 1 := cavityOrientationSign_gram hN U
  have hj : D * J * D.transpose = J := cavityOrientationSign_diagonal hN U _
  have hr := cavityBaseReplacement_conjugate J D W (cavityRepeatedSpectrum (n := n) lam)
    (B (cavityCompressionGrams g U)) A₀
  rw [hj] at hr
  unfold cavityPhysicalBase
  rw [cavityOrientationLift_compression, cavityOrientationLift_eigenspace]
  change ((D*O).transpose * cavityBaseReplacement J (D*W)
    (cavityRepeatedSpectrum (n := n) lam) (B (cavityCompressionGrams g U)) A₀ * (D*O)).submatrix
      (Fin.castAdd n) (Fin.castAdd n) = _
  rw [hr, Matrix.transpose_mul]
  have he (R : Matrix (Fin (N+n)) (Fin (N+n)) ℝ) :
      (U : Matrix (Fin (N+n)) (Fin (N+n)) ℝ).transpose * D.transpose *
        (D*R*D.transpose) * (D*(U : Matrix (Fin (N+n)) (Fin (N+n)) ℝ)) =
      (U : Matrix (Fin (N+n)) (Fin (N+n)) ℝ).transpose * R *
        (U : Matrix (Fin (N+n)) (Fin (N+n)) ℝ) := by
    calc
      _ = (U : Matrix (Fin (N+n)) (Fin (N+n)) ℝ).transpose * (D.transpose*D) * R *
          (D.transpose*D) * (U : Matrix (Fin (N+n)) (Fin (N+n)) ℝ) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hD]; simp
  rw [he]

lemma cavityOrientationLift_physicalSpecial {N n m d : ℕ} (hN : 0 < N+n)
    (g : Fin (N+n) → Fin m) (U : Orthogonal (N+n))
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ) :
    cavityPhysicalSpecial g B (cavitySpecialOrthogonal (cavityOrientationLift hN U)) =
      cavityPhysicalSpecial g B U := by
  unfold cavityPhysicalSpecial
  rw [cavityOrientationLift_compression, cavityOrientationLift_eigenspace]
  change cavityReservoirRows (((cavityOrientationSign hN U *
    (U : Matrix (Fin (N+n)) (Fin (N+n)) ℝ)).transpose) *
      ((cavityOrientationSign hN U * _) * _)) = _
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (cavityOrientationSign hN U).transpose
    (cavityOrientationSign hN U), cavityOrientationSign_gram, Matrix.one_mul]

lemma cavityOrientationLift_projectors {N n m d : ℕ} (hN : 0 < N+n)
    (g : Fin (N+n) → Fin m) (U : Orthogonal (N+n))
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (a₀ : Fin d → Fin m) :
    cavityPhysicalLabeledProjectors g B a₀ (cavitySpecialOrthogonal (cavityOrientationLift hN U)) =
      cavityPhysicalLabeledProjectors g B a₀ U := by
  refine Prod.ext ?_ (cavityOrientationLift_physicalSpecial hN g U B)
  funext a
  exact cavityOrientationLift_physicalBase (N := N) (n := n) (m := m) (d := d)
    hN g U (fun b => if b=a then 1 else 0) B
    (Matrix.diagonal (fun j => if a₀ j=a then 1 else 0))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectorMeasurability
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable, bounded Gibbs observables expressed in the joint
projector and special-frame data. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

lemma measurable_cavityProjectorSpinCoordinate {N : ℕ} (σ : Spin N) (i : Fin N) :
    Measurable (fun Q : Matrix (Fin N) (Fin N) ℝ => cavityProjectorSpinCoordinate Q σ i) := by
  unfold cavityProjectorSpinCoordinate Matrix.mulVec dotProduct
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro j _
  exact ((measurable_pi_apply j).comp (measurable_pi_apply i)).mul_const _

lemma measurable_cavityProjectorMonomial {N m : ℕ} (degree : Fin m → ℕ)
    (σ : Spin N) (w : SpectralTensorIndex
      (fun _ : Fin m => (Finset.univ : Finset (Fin N))) degree) :
    Measurable (fun Q : Fin m → Matrix (Fin N) (Fin N) ℝ =>
      cavityProjectorMonomial Q degree σ w) := by
  unfold cavityProjectorMonomial tensorFeature
  apply Finset.measurable_prod
  intro a _
  apply Finset.measurable_prod
  intro j _
  exact (measurable_cavityProjectorSpinCoordinate σ (w a j)).comp (measurable_pi_apply a)

lemma measurable_cavityProjectorSpinFeature {N m : ℕ} (degree : Fin N → Fin m → ℕ)
    (amp : Fin N → ℝ) (σ : Spin N) (j : CavityProjectorTensorIndex N m degree) :
    Measurable (fun Q : Fin m → Matrix (Fin N) (Fin N) ℝ =>
      cavityProjectorSpinFeature Q degree amp σ j) := by
  cases j with
  | inl j => exact measurable_const
  | inr w => exact (measurable_cavityProjectorMonomial (degree w.1) σ w.2).const_mul _

lemma measurable_cavityProjectorField {N m depth : ℕ}
    (u : ℕ → ℝ) (x : Spin N × LabeledLeaf depth) :
    Measurable (fun p : (Fin m → Matrix (Fin N) (Fin N) ℝ) × (ℕ → ℝ) =>
      cylinderField (cavityProjectorPerturbation p.1 u x) p.2) := by
  simp only [cavityProjectorPerturbation, cylinderField_feature]
  apply Finset.measurable_sum
  intro i _
  exact (((measurable_cavityProjectorSpinFeature _ _ x.1 i.2).comp measurable_fst).const_mul _).mul
    ((measurable_pi_apply (treeFeatureTag depth x.2 i)).comp measurable_snd)

lemma measurable_cavityProjectorHamiltonian {N m depth : ℕ}
    (c : Fin m → ℝ) (u : ℕ → ℝ) :
    Measurable (fun p : ((Fin m → Matrix (Fin N) (Fin N) ℝ) × (ℕ → ℝ)) ×
      (Spin N × LabeledLeaf depth) => cavityProjectorHamiltonian p.1.1 c u p.1.2 p.2) := by
  apply measurable_from_prod_countable_left
  intro x
  have he : Measurable (fun Q : Fin m → Matrix (Fin N) (Fin N) ℝ =>
      cavityProjectorEnergy Q c x.1) := by
    unfold cavityProjectorEnergy Matrix.mulVec dotProduct
    fun_prop
  exact (he.comp measurable_fst).add (measurable_cavityProjectorField u x)

lemma measurable_cavityProjectorHamiltonian_pullback {Ω : Type*} [MeasurableSpace Ω]
    {N m depth : ℕ} (f : Ω → Fin m → Matrix (Fin N) (Fin N) ℝ) (hf : Measurable f)
    (c : Fin m → ℝ) (u : ℕ → ℝ) :
    Measurable (fun p : (Ω × (ℕ → ℝ)) × (Spin N × LabeledLeaf depth) =>
      cavityProjectorHamiltonian (f p.1.1) c u p.1.2 p.2) := by
  let π : (Ω × (ℕ → ℝ)) × (Spin N × LabeledLeaf depth) →
      ((Fin m → Matrix (Fin N) (Fin N) ℝ) × (ℕ → ℝ)) × (Spin N × LabeledLeaf depth) :=
    fun p => ((f p.1.1,p.1.2),p.2)
  have hπ : Measurable π :=
    ((hf.comp measurable_fst.fst).prodMk measurable_fst.snd).prodMk measurable_snd
  have hbase := measurable_cavityProjectorHamiltonian (N := N) (m := m) (depth := depth) c u
  have hcomp := hbase.comp hπ
  exact hcomp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectorCavity
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized cavity observable as a measurable function of the
physical labeled projectors, selected frame and small coefficient blocks. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

lemma continuous_cavityFrameCoordinates {N d : ℕ} (σ : Spin N) :
    Continuous (fun S : Matrix (Fin N) (Fin d) ℝ => cavityFrameCoordinates S σ) := by
  unfold cavityFrameCoordinates
  fun_prop

lemma measurable_cavityBlockPotential {Ω : Type*} [MeasurableSpace Ω] {N n d : ℕ}
    (A : Ω → CavityFactorBlocks d n) (hA : Measurable A)
    (S : Ω → Matrix (Fin N) (Fin d) ℝ) (hS : Measurable S)
    (σ : Spin N) (ε : Spin n) :
    Measurable (fun ω => cavityLogFactor (A ω).1 (A ω).2.1 (A ω).2.2
      (cavityFrameCoordinates (S ω) σ) ε) := by
  have hy := (continuous_cavityFrameCoordinates σ).measurable.comp hS
  unfold cavityLogFactor cavityQuadratic
  fun_prop

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectorJointHaar
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint factorization allows the replica test to depend on the actual
compression coefficients, not only through a separate scalar factor. -/

noncomputable section
open MeasureTheory
open scoped Matrix

namespace InvariantIsing

theorem cavity_labeled_projector_joint_haar {N n m d : ℕ}
    (g : Fin (N+n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N+n) // g i = a} ≃ Fin (k a+n))
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (l u : Fin m → ℕ)
    (hg : ∀ a i, g i=a ↔ l a ≤ i.val ∧ i.val < u a)
    (hln : ∀ a, l a+n ≤ u a) (hu : ∀ a, u a ≤ N+n)
    (μ : Measure (Orthogonal (N+n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]
    (f : (Fin m → Matrix (Fin n) (Fin n) ℝ) × CavityProjectorFrame N m d → ℝ)
    (hf : Measurable f) (C : ℝ) (hfb : ∀ p, ‖f p‖ ≤ C) :
    (∫ U, f (cavityCompressionGrams g U,
      cavityPhysicalLabeledProjectors g (cavityConcreteComplement es B₀) a₀ U) ∂μ) =
    ∫ U, ∫ V, f (cavityCompressionGrams g U,
      cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)) ∂ν ∂μ := by
  let : BorelSpace (CavityProjectorFrame N m d) := inferInstanceAs
    (BorelSpace ((Fin m → Fin N → Fin N → ℝ) × (Fin N → Fin d → ℝ)))
  let : OpensMeasurableSpace (Orthogonal N × CavityProjectorFrame N m d) := inferInstanceAs
    (OpensMeasurableSpace (Orthogonal N × ((Fin m → Fin N → Fin N → ℝ) × (Fin N → Fin d → ℝ))))
  let B := cavityConcreteComplement es B₀
  have hBm : Measurable B := measurable_cavityConcreteComplement es B₀
  apply cavity_orbit_joint_right_ae μ ν
    (fun V => cavityReservoirRotation (n := n) V⁻¹)
    (cavityPhysicalLabeledProjectors g B a₀) (cavityCompressionGrams g)
    (measurable_cavityPhysicalLabeledProjectors g B hBm a₀)
    (measurable_cavityCompressionGrams g) cavityLabeledProjectorAction
    (continuous_cavityLabeledProjectorAction N m d).measurable cavityLabeledProjectorAction_mul
    _ _ (cavityCanonicalProjectorFrame k e a₀) _ f hf C hfb
  · intro V
    exact ae_of_all _ (fun U => cavityPhysicalLabeledProjectors_reservoir g B a₀ U V)
  · intro V
    exact ae_of_all _ (fun U => cavityCompressionGrams_reservoir g U V⁻¹)
  · filter_upwards [cavityCompressionGrams_posDef_ae g l u hg hln hu μ] with U hU
    exact cavityPhysicalLabeledProjectors_mem_orbit g k ek e a₀ U B
      (cavityConcreteComplement_gram g es B₀ U)
      (cavityConcreteComplement_perp g es B₀ U) hU

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectorGibbsHaar
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint averaging of the actual projector-based Gibbs law and its
compression-dependent bounded replica tests. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

lemma cavityCanonicalProjectorFrame_action_fst {N m d : ℕ} (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (V : Orthogonal N) :
    (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)).1 =
      fun a => cavitySpectralProjector V
        (cavitySpectralGroup (fun j => Sum.elim (fun w => w.1) a₀ (e.symm j)) a) := by
  funext a
  have hd : (fun j : Fin N => Sum.elim (fun w => if w.1=a then (1:ℝ) else 0)
      (fun j => if a₀ j=a then 1 else 0) (e.symm j)) =
      (fun j => if j ∈ cavitySpectralGroup
        (fun j => Sum.elim (fun w => w.1) a₀ (e.symm j)) a then 1 else 0) := by
    funext j
    simp only [cavitySpectralGroup, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases h : e.symm j with w | j₀ <;> rfl
  exact congrArg (fun f : Fin N → ℝ => cavityConjugate V (Matrix.diagonal f)) hd

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectorHaarMean
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized coefficient replacement for the actual independent
compression and base-Haar factors. The chosen spectral axes remain in
the same base Gibbs law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology Matrix

namespace InvariantIsing

lemma measurable_cavityCanonicalProjectorAction {N m d : ℕ}
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) :
    Measurable (fun V : Orthogonal N =>
      cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)) := by
  let : BorelSpace (CavityProjectorFrame N m d) := inferInstanceAs
    (BorelSpace ((Fin m → Fin N → Fin N → ℝ) × (Fin N → Fin d → ℝ)))
  let : OpensMeasurableSpace (Orthogonal N × CavityProjectorFrame N m d) :=
    inferInstanceAs (OpensMeasurableSpace
      (Orthogonal N × ((Fin m → Fin N → Fin N → ℝ) × (Fin N → Fin d → ℝ))))
  have hmap : Continuous (fun V : Orthogonal N =>
      (V, cavityCanonicalProjectorFrame k e a₀)) := continuous_id.prodMk continuous_const
  exact ((continuous_cavityLabeledProjectorAction N m d).comp hmap).measurable

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityTestLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vanishing covariance and deterministic errors imply convergence of
bounded cavity replica tests, even when the configuration space varies
with the system size. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_secant_error_tendsto {f δ : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hbound : ∀ s : ℝ, 0 < s → ∀ᶠ N in atTop, |f N| ≤ δ N / s + C * s) :
    Tendsto f atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let s := ε / (2 * (C + 1))
  have hs : 0 < s := div_pos hε (by positivity)
  have hCs : C * s < ε / 2 := by
    have he : (C + 1) * s = ε / 2 := by
      dsimp [s]
      field_simp
    nlinarith
  have hd := hδ.eventually (gt_mem_nhds (show (0 : ℝ) < ε * s / 2 by positivity))
  filter_upwards [hd, hbound s hs] with N hN hb
  have hd' : δ N / s < ε / 2 := by
    apply (div_lt_iff₀ hs).mpr
    nlinarith
  simpa only [Real.dist_eq, sub_zero] using lt_of_le_of_lt hb (by linarith)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedGeometricMean
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual original-spin geometric cutoff as a measurable bounded
function of its orthogonal disorder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

lemma measurable_restrictedOriginalGeometricMean {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (Cset : Finset (Spin n)) (hCset : Cset.Nonempty)
    (g : Fin (N+n) → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (hB : Measurable B) (T : LabeledTree depth) (eig : Fin (N+n) → ℝ)
    (u : ℕ → ℝ) (D : ℝ)
    (F : (Fin 2 → (Spin N × Spin n) × LabeledLeaf depth) → ℝ) :
    Measurable (restrictedOriginalGeometricMean S hS Cset hCset g B T eig u D F) := by
  let X := Spin (N+n) × LabeledLeaf depth
  let I := cavitySpectralGroup g
  have hO : Measurable (cavitySpecialOrthogonal (N := N+n)) :=
    measurable_subtype_coe.subtype_mk
  have hBc := hB.comp ((measurable_cavityCompressionGrams g).comp hO)
  have hs : MeasurableSet {q : (SpecialOrthogonal (N+n) × (ℕ → ℝ)) × X |
      cavityGeometricWeight g (B (cavityCompressionGrams g (cavitySpecialOrthogonal q.1.1)))
        q.1.1 (cavitySpinSplit N n q.2.1) ≤ D} := by
    apply measurableSet_le _ measurable_const
    apply measurable_from_prod_countable_left
    intro x
    exact ((measurable_cavityFullSpecialCoordinates g _ hBc
      (cavityJoinedSpin (cavitySpinSplit N n x.1))).norm.pow_const 2).const_add 1 |>.comp
        measurable_fst
  have hH := measurable_cavityFullHamiltonian (N := N+n) (m := m) (depth := depth) eig I u
  have hF : Measurable (fun q : (SpecialOrthogonal (N+n) × (ℕ → ℝ)) × (Fin 2 → X) =>
      F (fun i => (cavitySpinSplit N n (q.2 i).1,(q.2 i).2))) := by
    have hf : Measurable (fun σ : Fin 2 → X =>
        F (fun i => (cavitySpinSplit N n (σ i).1,(σ i).2))) := measurable_of_countable _
    exact hf.comp measurable_snd
  have hc := measurable_cavityCutoffReplicaMean
    (labeledSpinReference depth (restrictedSpinPrior (cavityProductSlice S Cset) (cavityProductSlice_nonempty S hS Cset hCset) : Measure (Spin (N+n))) T)
    (Function.uncurry (cavityFullHamiltonian (depth := depth) eig I u)) hH
    (fun q => {x | cavityGeometricWeight g
      (B (cavityCompressionGrams g (cavitySpecialOrthogonal q.1))) q.1
        (cavitySpinSplit N n x.1) ≤ D}) hs _ hF
  exact hc.stronglyMeasurable.integral_prod_right'.measurable

lemma restrictedOriginalGeometricMean_bound {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (Cset : Finset (Spin n)) (hCset : Cset.Nonempty)
    (g : Fin (N+n) → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (T : LabeledTree depth) (eig : Fin (N+n) → ℝ) (u : ℕ → ℝ) (D : ℝ)
    (F : (Fin 2 → (Spin N × Spin n) × LabeledLeaf depth) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ σ, |F σ| ≤ M) (U : SpecialOrthogonal (N+n)) :
    ‖restrictedOriginalGeometricMean S hS Cset hCset g B T eig u D F U‖ ≤ M := by
  have hb := fun z => cavity_cutoff_replica_abs_le_all
    (labeledSpinReference depth (restrictedSpinPrior (cavityProductSlice S Cset) (cavityProductSlice_nonempty S hS Cset hCset) : Measure (Spin (N+n))) T)
    (cavityRotationHamiltonian (specialRotation U) eig (cavitySpectralGroup g) u z)
    {x | cavityGeometricWeight g (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))) U
      (cavitySpinSplit N n x.1) ≤ D}
    (fun σ => F (fun i => (cavitySpinSplit N n (σ i).1,(σ i).2))) hM (fun σ => hF _)
  have ht := norm_integral_le_of_norm_le_const (μ := gaussianCoordinates)
    (f := fun z => cavityCutoffReplicaMean
      (labeledSpinReference depth (restrictedSpinPrior (cavityProductSlice S Cset) (cavityProductSlice_nonempty S hS Cset hCset) : Measure (Spin (N+n))) T)
      (cavityRotationHamiltonian (specialRotation U) eig (cavitySpectralGroup g) u z)
      {x | cavityGeometricWeight g (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))) U
        (cavitySpinSplit N n x.1) ≤ D}
      (fun σ => F (fun i => (cavitySpinSplit N n (σ i).1,(σ i).2))))
    (C := M) (ae_of_all gaussianCoordinates (fun z => by
      simpa only [Real.norm_eq_abs] using hb z))
  simpa only [restrictedOriginalGeometricMean, probReal_univ, mul_one] using ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedProjectorCavity
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized cavity observable as a measurable function of the
physical labeled projectors, selected frame and small coefficient blocks. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

lemma restrictedProjectorCavityMean_bound {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (Cset : Finset (Spin n)) (hCset : Cset.Nonempty) (T : LabeledTree depth)
    (c : Fin m → ℝ) (u : ℕ → ℝ) (t D : ℝ) (A : CavityFactorBlocks d n)
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hF : ∀ σ, |F σ| ≤ C)
    (p : CavityProjectorFrame N m d) :
    ‖restrictedProjectorCavityMean S hS Cset hCset T c u t D A F p‖ ≤ C := by
  have hb : ∀ᵐ z ∂gaussianCoordinates, ‖cavityCutoffReplicaMean
      ((labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T).prod
        (restrictedSpinPrior Cset hCset))
      (fun x => cavityProjectorHamiltonian p.1 c u z x.1 +
        t * cavityLogFactor A.1 A.2.1 A.2.2 (cavityFrameCoordinates p.2 x.1.1) x.2)
      {x | 1 + ‖cavityFrameCoordinates p.2 x.1.1‖^2 ≤ D} F‖ ≤ C := by
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]
      exact cavity_cutoff_replica_abs_le_all _ _ _ _ hC hF
  simpa only [restrictedProjectorCavityMean, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const hb

lemma measurable_restrictedProjectorCavityMean {Ω : Type*} [MeasurableSpace Ω]
    {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (Cset : Finset (Spin n)) (hCset : Cset.Nonempty) (T : LabeledTree depth) (c : Fin m → ℝ) (u : ℕ → ℝ) (t D : ℝ)
    (A : Ω → CavityFactorBlocks d n) (hA : Measurable A)
    (p : Ω → CavityProjectorFrame N m d) (hp : Measurable p)
    (F : Ω → (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ)
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun ω => restrictedProjectorCavityMean S hS Cset hCset T c u t D (A ω) (F ω) (p ω)) := by
  let X := (Spin N × LabeledLeaf depth) × Spin n
  let H := fun q : (Ω × (ℕ → ℝ)) × X =>
    cavityProjectorHamiltonian (p q.1.1).1 c u q.1.2 q.2.1 +
      t*cavityLogFactor (A q.1.1).1 (A q.1.1).2.1 (A q.1.1).2.2
        (cavityFrameCoordinates (p q.1.1).2 q.2.1.1) q.2.2
  have hH : Measurable H := by
    let π : (Ω × (ℕ → ℝ)) × X →
        (Ω × (ℕ → ℝ)) × (Spin N × LabeledLeaf depth) := fun q => (q.1,q.2.1)
    have hπ : Measurable π := measurable_fst.prodMk measurable_snd.fst
    have hb := measurable_cavityProjectorHamiltonian_pullback
      (N := N) (m := m) (depth := depth) (fun ω => (p ω).1) hp.fst c u
    have hg := hb.comp hπ
    apply Measurable.add hg
    apply measurable_from_prod_countable_left
    intro x
    exact ((measurable_cavityBlockPotential A hA (fun ω => (p ω).2) hp.snd x.1.1 x.2).comp
      measurable_fst).const_mul t
  have hs : MeasurableSet {q : (Ω × (ℕ → ℝ)) × X |
      1 + ‖cavityFrameCoordinates (p q.1.1).2 q.2.1.1‖^2 ≤ D} := by
    have hy : Measurable (fun q : (Ω × (ℕ → ℝ)) × X =>
        cavityFrameCoordinates (p q.1.1).2 q.2.1.1) := by
      apply measurable_from_prod_countable_left
      intro x
      exact ((continuous_cavityFrameCoordinates x.1.1).measurable.comp hp.snd).comp
        measurable_fst
    exact measurableSet_le (measurable_const.add (hy.norm.pow_const 2)) measurable_const
  have hG := measurable_cavityCutoffReplicaMean
    ((labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T).prod
      (restrictedSpinPrior Cset hCset)) H hH
    (fun q => {x | 1 + ‖cavityFrameCoordinates (p q.1).2 x.1.1‖^2 ≤ D}) hs
    (fun q => F q.1.1 q.2) (hF.comp (measurable_fst.fst.prodMk measurable_snd))
  exact hG.stronglyMeasurable.integral_prod_right'.measurable

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedProjectorHaarMean
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized coefficient replacement for the actual independent
compression and base-Haar factors. The chosen spectral axes remain in
the same base Gibbs law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology Matrix

namespace InvariantIsing

lemma measurable_restrictedProjectorHaarMean {Ω : Type*} [MeasurableSpace Ω]
    {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (Cset : Finset (Spin n)) (hCset : Cset.Nonempty) (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N) (a₀ : Fin d → Fin m)
    (ν : Measure (Orthogonal N)) [SFinite ν] (T : LabeledTree depth) (c : Fin m → ℝ)
    (u : ℕ → ℝ) (t D : ℝ) (A : Ω → CavityFactorBlocks d n) (hA : Measurable A)
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ) :
    Measurable (fun ω => ∫ V, restrictedProjectorCavityMean S hS Cset hCset T c u t D (A ω) F
      (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)) ∂ν) := by
  let a : Ω × Orthogonal N → CavityFactorBlocks d n := fun p => A p.1
  let p : Ω × Orthogonal N → CavityProjectorFrame N m d := fun q =>
    cavityLabeledProjectorAction q.2 (cavityCanonicalProjectorFrame k e a₀)
  have ha : Measurable a := hA.comp measurable_fst
  have hp : Measurable p := (measurable_cavityCanonicalProjectorAction k e a₀).comp measurable_snd
  have hF : Measurable (fun q : (Ω × Orthogonal N) ×
      (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) => F q.2) :=
    (measurable_of_countable F).comp measurable_snd
  have hm := measurable_restrictedProjectorCavityMean (N := N) (n := n) (m := m)
    (d := d) (depth := depth) S hS Cset hCset T c u t D a ha p hp (fun _ => F) hF
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma restrictedProjectorHaarMean_bound {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (Cset : Finset (Spin n)) (hCset : Cset.Nonempty) (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N) (a₀ : Fin d → Fin m)
    (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν]
    (T : LabeledTree depth) (c : Fin m → ℝ) (u : ℕ → ℝ) (t D : ℝ)
    (A : CavityFactorBlocks d n)
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ σ, |F σ| ≤ M) :
    |∫ V, restrictedProjectorCavityMean S hS Cset hCset T c u t D A F
      (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)) ∂ν| ≤ M := by
  have hb : ∀ᵐ V ∂ν, ‖restrictedProjectorCavityMean S hS Cset hCset T c u t D A F
      (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀))‖ ≤ M :=
    ae_of_all _ fun V => restrictedProjectorCavityMean_bound S hS Cset hCset T c u t D A F hM hF _
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const hb

lemma restricted_projector_haar_coefficient_error {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (Cset : Finset (Spin n)) (hCset : Cset.Nonempty)
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν]
    (T : LabeledTree depth) (lam v : Fin m → ℝ)
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t : ℝ) {D : ℝ} (hD : 0 ≤ D)
    (A A' : CavityFactorBlocks d n)
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ)
    {M s : ℝ} (hM : 0 ≤ M) (hF : ∀ σ, |F σ| ≤ M) (hs : 0 < s) :
    |(∫ V, restrictedProjectorCavityMean S hS Cset hCset T
      (fun a => t*lam a+2*perturbationScale N*v a) u t D A F
      (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)) ∂ν) -
      ∫ V, restrictedProjectorCavityMean S hS Cset hCset T
      (fun a => t*lam a+2*perturbationScale N*v a) u t D A' F
      (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)) ∂ν| ≤
      4*|t| *D*cavityFactorDeviation A A'/s+M^2*s/2 := by
  let c := fun a => t*lam a+2*perturbationScale N*v a
  let p := fun V : Orthogonal N =>
    cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)
  let g : Fin N → Fin m := fun i => Sum.elim (fun w => w.1) a₀ (e.symm i)
  have hpV (V : Orthogonal N) : (p V).1 =
      fun a => cavitySpectralProjector V (cavitySpectralGroup g a) :=
    cavityCanonicalProjectorFrame_action_fst k e a₀ V
  have hp : Measurable p := measurable_cavityCanonicalProjectorAction k e a₀
  have hFs : Measurable (fun q : Orthogonal N ×
      (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) => F q.2) :=
    (measurable_of_countable F).comp measurable_snd
  have hi (B : CavityFactorBlocks d n) :
      Integrable (fun V => restrictedProjectorCavityMean S hS Cset hCset T c u t D B F (p V)) ν :=
    Integrable.of_bound
      (measurable_restrictedProjectorCavityMean S hS Cset hCset T c u t D (fun _ => B) measurable_const
        p hp (fun _ => F) hFs).aestronglyMeasurable M
      (ae_of_all _ fun V => restrictedProjectorCavityMean_bound S hS Cset hCset T c u t D B F hM hF (p V))
  rw [← integral_sub (hi A) (hi A')]
  have hb : ∀ᵐ V ∂ν, ‖restrictedProjectorCavityMean S hS Cset hCset T c u t D A F (p V) -
      restrictedProjectorCavityMean S hS Cset hCset T c u t D A' F (p V)‖ ≤
      4*|t| *D*cavityFactorDeviation A A'/s+M^2*s/2 := by
    apply ae_of_all
    intro V
    have hh := restricted_projector_coefficient_error
      (N := N) (n := n) (m := m) (d := d) (depth := depth)
      S hS Cset hCset g V T lam v u hu t hD A A' (p V) (hpV V) F hM hF hs
    rw [Real.norm_eq_abs]
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const hb

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedHaarCoefficients
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized coefficient replacement for varying finite perturbation minimizers.

Normalized coefficient replacement under independent compression
and base-Haar averages. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology Matrix

namespace InvariantIsing

theorem restricted_haar_normalized_coefficient_tendsto {m d n : ℕ}
    (N depth : ℕ → ℕ)
    (S : (j : ℕ) → Finset (Spin (N j))) (hS : ∀ j, (S j).Nonempty)
    (Cset : Finset (Spin n)) (hCset : Cset.Nonempty) (k : ℕ → Fin m → ℕ)
    (e : (j : ℕ) → (((a : Fin m) × Fin (k j a)) ⊕ Fin d) ≃ Fin (N j))
    (a₀ : Fin d → Fin m)
    (μ : (j : ℕ) → Measure (Orthogonal (N j+n))) [∀ j, IsProbabilityMeasure (μ j)]
    (ν : (j : ℕ) → Measure (Orthogonal (N j))) [∀ j, IsProbabilityMeasure (ν j)]
    (T : (j : ℕ) → LabeledTree (depth j)) (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ)
    (u : ℕ → ℕ → ℝ) (hu : ∀ j i, |u j i| ≤ 2) (t : ℝ) {D : ℝ} (hD : 0 ≤ D)
    (A : (j : ℕ) → Orthogonal (N j+n) → CavityFactorBlocks d n)
    (hA : ∀ j, Measurable (A j)) (A₀ : CavityFactorBlocks d n)
    (F : (j : ℕ) → (Fin 2 → (Spin (N j) × LabeledLeaf (depth j)) × Spin n) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ j σ, |F j σ| ≤ M)
    (hprob : ∀ δ > 0, Tendsto (fun j => (μ j).real
      {U | δ < cavityFactorDeviation (A j U) A₀}) atTop (𝓝 0)) :
    Tendsto (fun j =>
      (∫ U, ∫ V, restrictedProjectorCavityMean (S j) (hS j) Cset hCset (T j)
        (fun a => t*lam a+2*perturbationScale (N j)*v j a) (u j) t D (A j U) (F j)
        (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame (k j) (e j) a₀)) ∂ν j ∂μ j) -
      ∫ _U, ∫ V, restrictedProjectorCavityMean (S j) (hS j) Cset hCset (T j)
        (fun a => t*lam a+2*perturbationScale (N j)*v j a) (u j) t D A₀ (F j)
        (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame (k j) (e j) a₀)) ∂ν j ∂μ j)
      atTop (𝓝 0) := by
  apply cavity_coefficient_values_tendsto μ A hA A₀ _ _
    (fun j => measurable_restrictedProjectorHaarMean (S j) (hS j) Cset hCset (k j) (e j) a₀ (ν j) (T j) _ (u j) t D
      (A j) (hA j) (F j))
    (fun j => measurable_restrictedProjectorHaarMean (S j) (hS j) Cset hCset (k j) (e j) a₀ (ν j) (T j) _ (u j) t D
      (fun _ => A₀) measurable_const (F j)) hM
    (show 0 ≤ 4*|t| *D by positivity)
    (fun j U => restrictedProjectorHaarMean_bound (S j) (hS j) Cset hCset (k j) (e j) a₀ (ν j) (T j) _ (u j) t D
      (A j U) (F j) hM (hF j))
    (fun j _ => restrictedProjectorHaarMean_bound (S j) (hS j) Cset hCset (k j) (e j) a₀ (ν j) (T j) _ (u j) t D
      A₀ (F j) hM (hF j))
    (fun j U s hs => restricted_projector_haar_coefficient_error (S j) (hS j) Cset hCset (k j) (e j) a₀ (ν j)
      (T j) lam (v j) (u j) (hu j) t hD (A j U) A₀ (F j) hM (hF j) hs) hprob

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedPhysicalCavityHaar
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint Haar factorization for the normalized cavity observable.
Compression-dependent coefficients and the selected frame are retained
inside the same normalized two-replica test. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

theorem restricted_physical_cavity_haar {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (Cset : Finset (Spin n)) (hCset : Cset.Nonempty)
    (g : Fin (N+n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N+n) // g i = a} ≃ Fin (k a+n))
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (l w : Fin m → ℕ)
    (hg : ∀ a i, g i=a ↔ l a ≤ i.val ∧ i.val < w a)
    (hln : ∀ a, l a+n ≤ w a) (hw : ∀ a, w a ≤ N+n)
    (μ : Measure (Orthogonal (N+n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]
    (T : LabeledTree depth) (c : Fin m → ℝ) (u : ℕ → ℝ) (t D : ℝ)
    (A : (Fin m → Matrix (Fin n) (Fin n) ℝ) → CavityFactorBlocks d n)
    (hA : Measurable A)
    (F : ((Fin m → Matrix (Fin n) (Fin n) ℝ) × CavityProjectorFrame N m d) →
      (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ)
    (hF : Measurable (Function.uncurry F))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ p σ, |F p σ| ≤ C) :
    (∫ U, restrictedProjectorCavityMean S hS Cset hCset T c u t D (A (cavityCompressionGrams g U))
      (F (cavityCompressionGrams g U,
        cavityPhysicalLabeledProjectors g (cavityConcreteComplement es B₀) a₀ U))
      (cavityPhysicalLabeledProjectors g (cavityConcreteComplement es B₀) a₀ U) ∂μ) =
    ∫ U, ∫ V, restrictedProjectorCavityMean S hS Cset hCset T c u t D (A (cavityCompressionGrams g U))
      (F (cavityCompressionGrams g U,
        cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)))
      (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)) ∂ν ∂μ := by
  let Ω := (Fin m → Matrix (Fin n) (Fin n) ℝ) × CavityProjectorFrame N m d
  let a : Ω → CavityFactorBlocks d n := fun p => A p.1
  let p : Ω → CavityProjectorFrame N m d := Prod.snd
  have ha : Measurable a := hA.comp measurable_fst
  have hp : Measurable p := measurable_snd
  have hm := measurable_restrictedProjectorCavityMean (Ω := Ω)
    (N := N) (n := n) (m := m) (d := d) (depth := depth) S hS Cset hCset T c u t D a ha p hp F hF
  have hbnd : ∀ q : Ω, ‖restrictedProjectorCavityMean S hS Cset hCset T c u t D (a q) (F q) (p q)‖ ≤ C := by
    intro q
    exact restrictedProjectorCavityMean_bound (N := N) (n := n) (m := m) (d := d)
      (depth := depth) S hS Cset hCset T c u t D (a q) (F q) hC (hb q) (p q)
  exact cavity_labeled_projector_joint_haar g k ek e es B₀ a₀ l w hg hln hw μ ν
    (fun q : Ω => restrictedProjectorCavityMean S hS Cset hCset T c u t D (a q) (F q) (p q)) hm C hbnd

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedHaarCutoffComparison
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original Ising cutoff, averaged over its actual Haar disorder,
is compared with an independent Haar base cavity law. All random block
coefficients remain inside the normalized test. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

theorem restricted_haar_cutoff_comparison {N n m d depth : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (Cset : Finset (Spin n)) (hCset : Cset.Nonempty)
    (g : Fin (N+n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N+n) // g i = a} ≃ Fin (k a+n))
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (l w : Fin m → ℕ) (hg : ∀ a i, g i=a ↔ l a ≤ i.val ∧ i.val < w a)
    (hln : ∀ a, l a+n ≤ w a) (hw : ∀ a, w a ≤ N+n)
    (μ : Measure (Orthogonal (N+n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]
    (T : LabeledTree depth) (lam v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2)
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t : ℝ)
    {D M s : ℝ} (hD : 1 ≤ D) (hM : 0 ≤ M) (hs : 0 < s)
    (F : (Fin 2 → (Spin N × Spin n) × LabeledLeaf depth) → ℝ)
    (hF : ∀ σ, |F σ| ≤ M) :
    let B := cavityConcreteComplement es B₀
    let A := cavityCompressionFactorBlocks es lam (fun j => lam (a₀ j)) B₀
    |(∫ U, ∫ V, restrictedProjectorCavityMean S hS Cset hCset T
        (fun a => t*lam a+2*perturbationScale N*v a) u t D
        (A (cavityCompressionGrams g U))
        (fun σ => F (fun i => cavityPairLeafUnswap (σ i)))
        (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)) ∂ν ∂μ) -
      (∫ U, restrictedOriginalGeometricMean S hS Cset hCset g B T
        (diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t)
        u D F (cavityOrientationLift (Nat.add_pos_left hN n) U) ∂μ)| ≤
      (2 * (2 : ℝ)^2 * (cavityCovarianceRate n (2*n+1) N * (2*D)) +
        2 * 2 * (cavityCovarianceRate n (2*n+1) N * (2*D)) +
        2 * 2 * (cavityDeterministicRate n m (2*(2*n+1)) N * D)) / s + M^2*s/2 := by
  intro B A
  let c := fun a => t*lam a+2*perturbationScale N*v a
  let f := fun U : Orthogonal (N+n) => restrictedProjectorCavityMean S hS Cset hCset T c u t D
    (A (cavityCompressionGrams g U))
    (fun σ => F (fun i => cavityPairLeafUnswap (σ i)))
    (cavityPhysicalLabeledProjectors g B a₀ U)
  let h := fun U : Orthogonal (N+n) => restrictedOriginalGeometricMean S hS Cset hCset g B T
    (diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t)
    u D F (cavityOrientationLift (Nat.add_pos_left hN n) U)
  have hBm : Measurable B := measurable_cavityConcreteComplement es B₀
  have hAm : Measurable A := measurable_cavityCompressionFactorBlocks es lam _ B₀
  have hFs : Measurable (fun σ : Fin 2 → (Spin N × LabeledLeaf depth) × Spin n =>
      F (fun i => cavityPairLeafUnswap (σ i))) := measurable_of_countable _
  have hfm : Measurable f := measurable_restrictedProjectorCavityMean
    (N := N) (n := n) (m := m) (d := d) (depth := depth) S hS Cset hCset T c u t D
    (fun U => A (cavityCompressionGrams g U))
    (hAm.comp (measurable_cavityCompressionGrams g))
    (cavityPhysicalLabeledProjectors g B a₀)
    (measurable_cavityPhysicalLabeledProjectors g B hBm a₀)
    (fun _ σ => F (fun i => cavityPairLeafUnswap (σ i)))
    (hFs.comp measurable_snd)
  have hhm : Measurable h := (measurable_restrictedOriginalGeometricMean S hS Cset hCset g B hBm T _ u D F).comp
    (measurable_cavityOrientationLift (Nat.add_pos_left hN n))
  have hfb U : ‖f U‖ ≤ M := restrictedProjectorCavityMean_bound S hS Cset hCset T c u t D _ _ hM
    (fun σ => hF _) _
  have hhb U : ‖h U‖ ≤ M := restrictedOriginalGeometricMean_bound S hS Cset hCset g B T _ u D F hM hF _
  have hfi : Integrable f μ := Integrable.of_bound hfm.aestronglyMeasurable M (ae_of_all _ hfb)
  have hhi : Integrable h μ := Integrable.of_bound hhm.aestronglyMeasurable M (ae_of_all _ hhb)
  have hcmp : ∀ᵐ U ∂μ, |f U-h U| ≤
      (2 * (2 : ℝ)^2 * (cavityCovarianceRate n (2*n+1) N * (2*D)) +
        2 * 2 * (cavityCovarianceRate n (2*n+1) N * (2*D)) +
        2 * 2 * (cavityDeterministicRate n m (2*(2*n+1)) N * D)) / s + M^2*s/2 := by
    filter_upwards [cavityCompressionGrams_posDef_ae g l w hg hln hw μ] with U hU
    let R := cavityOrientationLift (Nat.add_pos_left hN n) U
    have hpos : ∀ a, (cavityCompressionGrams g (cavitySpecialOrthogonal R) a).PosDef := by
      simpa only [R, cavityOrientationLift_compression] using hU
    have hh := restricted_physical_cutoff_comparison hN S hS Cset hCset g k ek e es R lam a₀ B
      (cavityConcreteComplement_gram g es B₀ (cavitySpecialOrthogonal R))
      (cavityConcreteComplement_perp g es B₀ (cavitySpecialOrthogonal R)) hpos
      T v hv u hu t hD hM hs F hF
    dsimp only at hh
    simpa only [f, h, c, A, B, cavityCompressionFactorBlocks, R,
      cavityOrientationLift_compression, cavityOrientationLift_projectors,
      restrictedOriginalGeometricMean] using hh
  have havg := restricted_physical_cavity_haar S hS Cset hCset g k ek e es B₀ a₀ l w hg hln hw μ ν
    T c u t D A hAm
    (fun _ σ => F (fun i => cavityPairLeafUnswap (σ i)))
    (hFs.comp measurable_snd) hM (fun _ σ => hF _)
  change (∫ U, f U ∂μ) = _ at havg
  rw [← havg, ← integral_sub hfi hhi]
  have hb := norm_integral_le_of_norm_le_const (f := fun U => f U-h U)
    (C := (2 * (2 : ℝ)^2 * (cavityCovarianceRate n (2*n+1) N * (2*D)) +
      2*2*(cavityCovarianceRate n (2*n+1) N*(2*D)) +
      2*2*(cavityDeterministicRate n m (2*(2*n+1)) N*D))/s+M^2*s/2)
    (hcmp.mono fun U hU => by simpa only [Real.norm_eq_abs] using hU)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hb

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedHaarCutoffLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At a fixed spatial cutoff the original spin test converges to the
independent base-Haar cavity test with deterministic limiting blocks. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology Matrix

namespace InvariantIsing

theorem restricted_haar_cutoff_limit_oai {m d n : ℕ}
    (N depth : ℕ → ℕ)
    (S : (j : ℕ) → Finset (Spin (N j))) (hS : ∀ j, (S j).Nonempty)
    (Cset : Finset (Spin n)) (hCset : Cset.Nonempty) (hN : ∀ j, 0 < N j) (hNlim : Tendsto N atTop atTop)
    (g : (j : ℕ) → Fin (N j+n) → Fin m) (k : ℕ → Fin m → ℕ)
    (ek : ∀ j a, {i : Fin (N j+n) // g j i = a} ≃ Fin (k j a+n))
    (e : (j : ℕ) → (((a : Fin m) × Fin (k j a)) ⊕ Fin d) ≃ Fin (N j))
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (l w : ℕ → Fin m → ℕ)
    (hg : ∀ j a i, g j i=a ↔ l j a ≤ i.val ∧ i.val < w j a)
    (hln : ∀ j a, l j a+n ≤ w j a) (hw : ∀ j a, w j a ≤ N j+n)
    (μ : (j : ℕ) → Measure (Orthogonal (N j+n)))
    [∀ j, IsProbabilityMeasure (μ j)] [∀ j, (μ j).IsMulRightInvariant]
    (ν : (j : ℕ) → Measure (Orthogonal (N j)))
    [∀ j, IsProbabilityMeasure (ν j)] [∀ j, (ν j).IsMulRightInvariant]
    (T : (j : ℕ) → LabeledTree (depth j)) (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ)
    (hv : ∀ j a, |v j a| ≤ 2) (u : ℕ → ℕ → ℝ) (hu : ∀ j i, |u j i| ≤ 2) (t : ℝ)
    {D M : ℝ} (hD : 1 ≤ D) (hM : 0 ≤ M)
    (F : (j : ℕ) → (Fin 2 → (Spin (N j) × Spin n) × LabeledLeaf (depth j)) → ℝ)
    (hF : ∀ j σ, |F j σ| ≤ M) (A₀ : CavityFactorBlocks d n)
    (hprob : ∀ δ > 0, Tendsto (fun j => (μ j).real
      {U | δ < cavityFactorDeviation
        (cavityCompressionFactorBlocks es lam (fun i => lam (a₀ i)) B₀
          (cavityCompressionGrams (g j) U)) A₀}) atTop (𝓝 0)) :
    Tendsto (fun j =>
      (∫ U, restrictedOriginalGeometricMean (S j) (hS j) Cset hCset (g j) (cavityConcreteComplement es B₀) (T j)
        (diagonalPerturbedEigenvalues (fun i => lam (g j i)) (cavitySpectralGroup (g j)) (v j) t)
        (u j) D (F j) (cavityOrientationLift (Nat.add_pos_left (hN j) n) U) ∂μ j) -
      ∫ V, restrictedProjectorCavityMean (S j) (hS j) Cset hCset (T j)
        (fun a => t*lam a+2*perturbationScale (N j)*v j a) (u j) t D A₀
        (fun σ => F j (fun i => cavityPairLeafUnswap (σ i)))
        (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame (k j) (e j) a₀)) ∂ν j)
      atTop (𝓝 0) := by
  let A : (j : ℕ) → Orthogonal (N j+n) → CavityFactorBlocks d n := fun j U =>
    cavityCompressionFactorBlocks es lam (fun i => lam (a₀ i)) B₀
      (cavityCompressionGrams (g j) U)
  let R : ℕ → ℝ := fun j => ∫ U, ∫ V, restrictedProjectorCavityMean (S j) (hS j) Cset hCset (T j)
    (fun a => t*lam a+2*perturbationScale (N j)*v j a) (u j) t D (A j U)
    (fun σ => F j (fun i => cavityPairLeafUnswap (σ i)))
    (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame (k j) (e j) a₀)) ∂ν j ∂μ j
  let O : ℕ → ℝ := fun j => ∫ U, restrictedOriginalGeometricMean (S j) (hS j) Cset hCset (g j)
    (cavityConcreteComplement es B₀) (T j)
    (diagonalPerturbedEigenvalues (fun i => lam (g j i)) (cavitySpectralGroup (g j)) (v j) t)
    (u j) D (F j) (cavityOrientationLift (Nat.add_pos_left (hN j) n) U) ∂μ j
  let L : ℕ → ℝ := fun j => ∫ V, restrictedProjectorCavityMean (S j) (hS j) Cset hCset (T j)
    (fun a => t*lam a+2*perturbationScale (N j)*v j a) (u j) t D A₀
    (fun σ => F j (fun i => cavityPairLeafUnswap (σ i)))
    (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame (k j) (e j) a₀)) ∂ν j
  have hcov := (cavityCovarianceRate_tendsto n (2*n+1)).comp hNlim
  have hdet := (cavityDeterministicRate_tendsto n m (2*(2*n+1))).comp hNlim
  have hδ : Tendsto (fun j =>
      2*(2:ℝ)^2*(cavityCovarianceRate n (2*n+1) (N j)*(2*D)) +
      2*2*(cavityCovarianceRate n (2*n+1) (N j)*(2*D)) +
      2*2*(cavityDeterministicRate n m (2*(2*n+1)) (N j)*D)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul, add_zero, Function.comp_apply] using
      (((hcov.mul_const (2*D)).const_mul (2*(2:ℝ)^2)).add
        ((hcov.mul_const (2*D)).const_mul (2*2))).add
        ((hdet.mul_const D).const_mul (2*2))
  have hRO : Tendsto (fun j => R j-O j) atTop (𝓝 0) := by
    apply cavity_secant_error_tendsto (C := M^2/2) (by positivity) hδ
    intro s hs
    apply Eventually.of_forall
    intro j
    have hh := restricted_haar_cutoff_comparison (hN j) (S j) (hS j) Cset hCset (g j) (k j) (ek j) (e j) es
      B₀ a₀ (l j) (w j) (hg j) (hln j) (hw j) (μ j) (ν j) (T j) lam (v j) (hv j)
      (u j) (hu j) t hD hM hs (F j) (hF j)
    change |R j-O j| ≤ _ at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hA j : Measurable (A j) :=
    (measurable_cavityCompressionFactorBlocks es lam _ B₀).comp
      (measurable_cavityCompressionGrams (g j))
  have hRL : Tendsto (fun j => R j-L j) atTop (𝓝 0) := by
    have hh := restricted_haar_normalized_coefficient_tendsto N depth S hS Cset hCset k e a₀ μ ν T lam v
      u hu t (show 0 ≤ D by linarith) A hA A₀
      (fun j σ => F j (fun i => cavityPairLeafUnswap (σ i))) hM (fun j σ => hF j _)
      hprob
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hh
  have hh := hRL.sub hRO
  convert (config := {transparency := .instances, preTransparency := .instances}) hh using 1
  · funext j
    dsimp only [R, O, L]
    ring
  · norm_num

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.restricted_haar_cutoff_limit_oai := @OAI.InvariantIsing.restricted_haar_cutoff_limit_oai
