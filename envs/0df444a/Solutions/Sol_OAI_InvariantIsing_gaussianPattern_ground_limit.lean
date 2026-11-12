-- Prove2me | solution 1 for OAI.InvariantIsing.gaussianPattern_ground_limit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:54:06.86885+00:00
-- url     : https://prove2.me/submissions/11311a36-20ca-4540-8468-e1fa0f8f14dd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
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
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Sort
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
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
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_gaussianPattern_pressure_limit

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
-- module Solutions.OAIQ258_II.InvariantIsing_Core_Model
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeNonempty
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.spinVector_apply
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

lemma logPartition_add_const {X : Type*} [Fintype X] [Nonempty X]
    (H : X → ℝ) (c : ℝ) :
    logPartition (fun x => H x + c) = logPartition H + c := by
  rw [logPartition_eq, logPartition_eq]
  simp_rw [Real.exp_add]
  rw [← Finset.sum_mul, Real.log_mul (sum_exp_pos H).ne' (Real.exp_ne_zero c),
    Real.log_exp]
  ring

lemma logPartition_le_add {X : Type*} [Fintype X] [Nonempty X]
    (H K : X → ℝ) (c : ℝ) (h : ∀ x, H x ≤ K x + c) :
    logPartition H ≤ logPartition K + c := by
  have hs : (∑ x, Real.exp (H x)) ≤ ∑ x, Real.exp (K x + c) :=
    Finset.sum_le_sum fun x _ => Real.exp_le_exp.mpr (h x)
  have hl : logPartition H ≤ logPartition (fun x => K x + c) := by
    rw [logPartition_eq, logPartition_eq]
    exact sub_le_sub_right (Real.log_le_log (sum_exp_pos H) hs) _
  simpa only [logPartition_add_const] using hl

lemma abs_logPartition_sub_le {X : Type*} [Fintype X] [Nonempty X]
    (H K : X → ℝ) (c : ℝ) (h : ∀ x, |H x - K x| ≤ c) :
    |logPartition H - logPartition K| ≤ c := by
  have h₁ := logPartition_le_add H K c fun x => by
    have := (abs_le.mp (h x)).2
    linarith
  have h₂ := logPartition_le_add K H c fun x => by
    have := (abs_le.mp (h x)).1
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The elementary log-sum bound, with the probability prior's entropy cost. -/
lemma logPartition_bounds {X : Type*} [Fintype X] [Nonempty X]
    (H : X → ℝ) (M : ℝ) (hM : ∀ x, H x ≤ M) (hx : ∃ x, H x = M) :
    M - Real.log (Fintype.card X) ≤ logPartition H ∧ logPartition H ≤ M := by
  have hc : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hlo : Real.exp M ≤ ∑ x, Real.exp (H x) := by
    obtain ⟨x, hx⟩ := hx
    rw [← hx]
    exact Finset.single_le_sum (fun y _ => (Real.exp_pos (H y)).le) (Finset.mem_univ x)
  have hup : (∑ x, Real.exp (H x)) ≤ Fintype.card X * Real.exp M := by
    calc
      _ ≤ ∑ _ : X, Real.exp M :=
        Finset.sum_le_sum fun x _ => Real.exp_le_exp.mpr (hM x)
      _ = _ := by simp
  rw [logPartition_eq]
  constructor
  · exact sub_le_sub_right (by simpa using Real.log_le_log (Real.exp_pos M) hlo) _
  · have hl := Real.log_le_log (sum_exp_pos H) hup
    rw [Real.log_mul hc.ne' (Real.exp_ne_zero M), Real.log_exp] at hl
    linarith

/-- Uniform cube entropy is `N log 2`. -/
lemma log_card_spin (N : ℕ) : Real.log (Fintype.card (Spin N)) = N * Real.log 2 := by
  simp only [Spin, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

/-- Soft maximum estimate used in the zero-temperature corollary, valid at every
finite dimension and every positive inverse temperature. -/
lemma finite_groundState_squeeze {N : ℕ} (hN : 0 < N) (H : Spin N → ℝ)
    (β E : ℝ) (hβ : 0 < β) (hE : ∀ σ, H σ ≤ N * E)
    (hatt : ∃ σ, H σ = N * E) :
    E - Real.log 2 / β ≤ (N : ℝ)⁻¹ * logPartition (fun σ => β * H σ) / β ∧
      (N : ℝ)⁻¹ * logPartition (fun σ => β * H σ) / β ≤ E := by
  have hscale : ∀ σ, β * H σ ≤ β * (N * E) :=
    fun σ => mul_le_mul_of_nonneg_left (hE σ) hβ.le
  have hatt' : ∃ σ, β * H σ = β * (N * E) := by
    obtain ⟨σ, hσ⟩ := hatt
    exact ⟨σ, by rw [hσ]⟩
  obtain ⟨hlo, hhi⟩ := logPartition_bounds (fun σ => β * H σ) (β * (N * E)) hscale hatt'
  rw [log_card_spin] at hlo
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · have hl := mul_le_mul_of_nonneg_left hlo (inv_nonneg.mpr hn.le)
    apply (le_div_iff₀ hβ).mpr
    calc
      (E - Real.log 2 / β) * β = E * β - Real.log 2 := by field_simp
      _ = (N : ℝ)⁻¹ * (β * (N * E) - N * Real.log 2) := by field_simp
      _ ≤ _ := hl
  · apply (div_le_iff₀ hβ).mpr
    have hh := mul_le_mul_of_nonneg_left hhi (inv_nonneg.mpr hn.le)
    calc
      _ ≤ (N : ℝ)⁻¹ * (β * (N * E)) := hh
      _ = E * β := by field_simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPhysicalFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cavity exponent difference in the original coordinates. The
retained interaction cancels; only the special and cavity projections
enter the factor. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavityQuadratic_dotProduct {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    cavityQuadratic A x = (1 / 2 : ℝ) * (x ⬝ᵥ (A *ᵥ x)) := by
  simp only [cavityQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

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
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_Rotation
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeNonempty
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_one _root_.OAI.InvariantIsing.spinValue_not
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

lemma rotatedEnergy_constant {N : ℕ} (a : ℝ) (U : Rotation N) (σ : Spin N) :
    rotatedEnergy (fun _ => a) U σ = a * N / 2 := by
  rw [rotatedEnergy, ← Finset.mul_sum, rotated_spin_sq_sum]
  ring

@[simp] lemma logPartition_zero {X : Type*} [Fintype X] [Nonempty X] :
    logPartition (fun _ : X => (0 : ℝ)) = 0 := by
  rw [logPartition_eq]
  simp

lemma rotatedPressure_constant {N : ℕ} (hN : 0 < N) (a : ℝ) (U : Rotation N) :
    rotatedPressure (fun _ => a) U (fun _ => 0) = a / 2 := by
  have he : (fun σ => rotatedEnergy (fun _ : Fin N => a) U σ +
      fieldEnergy (fun _ => 0) σ) = (fun _ : Spin N => 0 + a * N / 2) := by
    funext σ
    simp [rotatedEnergy_constant, fieldEnergy]
  rw [rotatedPressure, he, logPartition_add_const, logPartition_zero, zero_add]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  field_simp

/-- Pointwise operator comparison in spectral coordinates. -/
lemma abs_rotatedEnergy_sub_le {N : ℕ} (eig κ : Fin N → ℝ) (U : Rotation N)
    (δ : ℝ) (hδ : ∀ i, |eig i - κ i| ≤ δ) (σ : Spin N) :
    |rotatedEnergy eig U σ - rotatedEnergy κ U σ| ≤ δ * N / 2 := by
  have he : rotatedEnergy eig U σ - rotatedEnergy κ U σ =
      (1 / 2 : ℝ) * ∑ i, (eig i - κ i) * (U (spinVector σ) i) ^ 2 := by
    simp only [rotatedEnergy, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc
    _ ≤ (1 / 2 : ℝ) * ∑ i, |(eig i - κ i) * (U (spinVector σ) i) ^ 2| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ = (1 / 2 : ℝ) * ∑ i, |eig i - κ i| * (U (spinVector σ) i) ^ 2 := by
      simp only [abs_mul, abs_sq]
    _ ≤ (1 / 2 : ℝ) * ∑ i, δ * (U (spinVector σ) i) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hδ i) (sq_nonneg _)
    _ = δ * N / 2 := by rw [← Finset.mul_sum, rotated_spin_sq_sum]; ring

/-- Equation (6.6), pointwise in the rotation and independent of the field. -/
lemma abs_rotatedPressure_sub_le {N : ℕ} (hN : 0 < N)
    (eig κ : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (δ : ℝ) (hδ : ∀ i, |eig i - κ i| ≤ δ) :
    |rotatedPressure eig U c - rotatedPressure κ U c| ≤ δ / 2 := by
  have h := abs_logPartition_sub_le
    (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ)
    (fun σ => rotatedEnergy κ U σ + fieldEnergy c σ)
    (δ * N / 2) (fun σ => by
      simpa only [add_sub_add_right_eq_sub] using abs_rotatedEnergy_sub_le eig κ U δ hδ σ)
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  calc
    _ = (N : ℝ)⁻¹ * |logPartition (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ) -
        logPartition (fun σ => rotatedEnergy κ U σ + fieldEnergy c σ)| := by
      rw [rotatedPressure, rotatedPressure, ← mul_sub, abs_mul,
        abs_of_nonneg (show (0 : ℝ) ≤ (N : ℝ)⁻¹ by positivity)]
    _ ≤ (N : ℝ)⁻¹ * (δ * N / 2) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = δ / 2 := by field_simp

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

lemma cavityConjugate_mul {N : ℕ} (U V : Orthogonal N)
    (J : Matrix (Fin N) (Fin N) ℝ) :
    cavityConjugate (U * V) J = cavityConjugate U (cavityConjugate V J) := by
  change ((U : Matrix (Fin N) (Fin N) ℝ) * (V : Matrix (Fin N) (Fin N) ℝ)) * J *
    ((U : Matrix (Fin N) (Fin N) ℝ) * (V : Matrix (Fin N) (Fin N) ℝ)).transpose = _
  simp only [cavityConjugate, Matrix.transpose_mul, Matrix.mul_assoc]

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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_ThermalPressure
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Temperature differentiation for the actual finite Ising pressure. -/

noncomputable section

open IsingPerceptron MeasureTheory Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma abs_rotatedEnergy_le {N : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (K : ℝ) (heig : ∀ i, |eig i| ≤ K) (σ : Spin N) :
    |rotatedEnergy eig U σ| ≤ K * N / 2 := by
  simpa only [rotatedEnergy_constant, zero_mul, zero_div, sub_zero] using
    abs_rotatedEnergy_sub_le eig (fun _ => 0) U K (fun i => by simpa using heig i) σ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityQuadraticCompression
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quadratic energies in physical coordinates and after deleting the
annihilated cavity rows and columns. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavityQuadratic_conjugate {r d : ℕ}
    (U : Matrix (Fin r) (Fin d) ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (x : Fin d → ℝ) :
    cavityQuadratic (U.transpose * A * U) x = cavityQuadratic A (U *ᵥ x) := by
  rw [cavityQuadratic_dotProduct, cavityQuadratic_dotProduct,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

lemma cavityQuadratic_diagonal {d : ℕ} (a x : Fin d → ℝ) :
    cavityQuadratic (Matrix.diagonal a) x = (1 / 2 : ℝ) * ∑ i, a i * (x i)^2 := by
  rw [cavityQuadratic_dotProduct]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma cavity_rotatedEnergy_matrix {N : ℕ} (eig : Fin N → ℝ)
    (U : Orthogonal N) (σ : Spin N) :
    rotatedEnergy eig (matrixRotation U) σ =
      cavityQuadratic ((U : Matrix (Fin N) (Fin N) ℝ).transpose *
        Matrix.diagonal eig * (U : Matrix (Fin N) (Fin N) ℝ))
          (fun i => spinValue (σ i)) := by
  rw [cavityQuadratic_conjugate, cavityQuadratic_diagonal]
  rfl

lemma cavityQuadratic_inverse_rotation {N : ℕ} (eig : Fin N → ℝ)
    (V : Orthogonal N) (σ : Spin N) :
    cavityQuadratic ((V : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal eig *
      (V : Matrix (Fin N) (Fin N) ℝ).transpose) (fun i => spinValue (σ i)) =
      rotatedEnergy eig (matrixRotation V⁻¹) σ := by
  rw [cavity_rotatedEnergy_matrix]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOrientationOverlap
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The SO correction changes only coordinate signs in the spectral
basis, so every physical projected overlap and quadratic energy agrees. -/

noncomputable section
open scoped Matrix BigOperators

namespace InvariantIsing

lemma cavityOrientationLift_eval {N : ℕ} (hN : 0 < N) (U : Orthogonal N)
    (x : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    specialRotation (cavityOrientationLift hN U) x i =
      (if i=(⟨0,hN⟩ : Fin N) then (U : Matrix (Fin N) (Fin N) ℝ).det else 1)*
        matrixRotation U x i := by
  change ((cavityOrientationSign hN U*(U : Matrix (Fin N) (Fin N) ℝ))*ᵥ x) i = _
  rw [← Matrix.mulVec_mulVec]
  simp only [cavityOrientationSign, Matrix.mulVec_diagonal]
  rfl

lemma cavityOrientationLift_product {N : ℕ} (hN : 0 < N) (U : Orthogonal N)
    (x y : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    specialRotation (cavityOrientationLift hN U) x i *
      specialRotation (cavityOrientationLift hN U) y i =
        matrixRotation U x i * matrixRotation U y i := by
  rw [cavityOrientationLift_eval, cavityOrientationLift_eval]
  split_ifs
  · rcases orthogonal_det_eq_one_or_neg_one U with h | h <;> rw [h] <;> ring
  · ring

lemma cavityOrientationLift_energy {N : ℕ} (hN : 0 < N) (U : Orthogonal N)
    (eig : Fin N → ℝ) (σ : Spin N) :
    rotatedEnergy eig (specialRotation (cavityOrientationLift hN U)) σ =
      rotatedEnergy eig (matrixRotation U) σ := by
  unfold rotatedEnergy
  simp_rw [pow_two, cavityOrientationLift_product]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarSides
attribute [-instance] _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A right-invariant probability has the same inverse law and is
left-invariant. In particular the oriented base law supplies the SO Haar
hypothesis used by the finite-model concentration estimates. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InvariantIsing

instance cavityOrthogonal_measurableMul (N : ℕ) : MeasurableMul₂ (Orthogonal N) where
  measurable_mul := by
    apply Measurable.subtype_mk
    apply Measurable.of_eval_matrix
    intro i j
    change Measurable (fun p : Orthogonal N × Orthogonal N =>
      ∑ k, (p.1 : Matrix (Fin N) (Fin N) ℝ) i k * (p.2 : Matrix (Fin N) (Fin N) ℝ) k j)
    exact Finset.measurable_sum _ fun k _ =>
      (((Matrix.measurable_apply (i := i) (j := k)).comp measurable_subtype_coe).comp
        measurable_fst).mul
      (((Matrix.measurable_apply (i := k) (j := j)).comp measurable_subtype_coe).comp measurable_snd)

instance cavitySpecialOrthogonal_measurableMul (N : ℕ) : MeasurableMul₂ (SpecialOrthogonal N) where
  measurable_mul := by
    apply Measurable.subtype_mk
    apply Measurable.of_eval_matrix
    intro i j
    change Measurable (fun p : SpecialOrthogonal N × SpecialOrthogonal N =>
      ∑ k, (p.1 : Matrix (Fin N) (Fin N) ℝ) i k * (p.2 : Matrix (Fin N) (Fin N) ℝ) k j)
    exact Finset.measurable_sum _ fun k _ =>
      (((Matrix.measurable_apply (i := i) (j := k)).comp measurable_subtype_coe).comp
        measurable_fst).mul
      (((Matrix.measurable_apply (i := k) (j := j)).comp measurable_subtype_coe).comp measurable_snd)

instance cavitySpecialOrthogonal_measurableInv (N : ℕ) : MeasurableInv (SpecialOrthogonal N) where
  measurable_inv := by
    apply Measurable.subtype_mk
    apply Measurable.of_eval_matrix
    intro i j
    change Measurable (fun U : SpecialOrthogonal N => (U : Matrix (Fin N) (Fin N) ℝ) j i)
    exact (Matrix.measurable_apply (i := j) (j := i)).comp measurable_subtype_coe

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_InvariantOrbitLaw
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint orbit laws from measure-preserving rotations and pointwise Haar
kernels. The proof avoids measurable eigenvector selections. -/
noncomputable section
open MeasureTheory
namespace InvariantIsing

lemma paired_map_eq_of_comp {G D : Type*} [MeasurableSpace G] [MeasurableSpace D]
    (H : Measure G) (d : D) (f Y : G → ℝ) (T : G → G)
    (hf : Measurable f) (hT : Measurable T) (hmap : H.map T=H)
    (hY : ∀ u, Y u=f (T u)) :
    H.map (fun u => (d,Y u))=H.map (fun u => (d,f u)) := by
  have he : (fun u => (d,Y u))=(fun u => (d,f u)) ∘ T := by
    funext u
    exact Prod.ext rfl (hY u)
  rw [he,← Measure.map_map (measurable_const.prodMk hf) hT,hmap]

lemma map_prod_eq_of_fiber_maps {X G E : Type*}
    [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace E]
    (P : Measure X) (H : Measure G) [SFinite P] [SFinite H]
    (f g : X × G → E) (hf : Measurable f) (hg : Measurable g)
    (h : ∀ x, H.map (fun u => f (x,u))=H.map (fun u => g (x,u))) :
    (P.prod H).map f=(P.prod H).map g := by
  ext s hs
  rw [Measure.map_apply hf hs,Measure.map_apply hg hs,
    Measure.prod_apply (hf hs),Measure.prod_apply (hg hs)]
  apply lintegral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    have hh := congrArg (fun Q : Measure E => Q s) (h x)
    have hfx : Measurable (fun u => f (x,u)) := hf.comp (measurable_const.prodMk measurable_id)
    have hgx : Measurable (fun u => g (x,u)) := hg.comp (measurable_const.prodMk measurable_id)
    rw [Measure.map_apply hfx hs,Measure.map_apply hgx hs] at hh
    exact hh

theorem invariant_joint_orbit_law {X G D : Type*}
    [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace D]
    (P : Measure X) [IsProbabilityMeasure P] (H : Measure G) [IsProbabilityMeasure H]
    (act : G → X → X) (hact : Measurable (Function.uncurry act))
    (hpres : ∀ u, P.map (act u)=P)
    (d : X → D) (Y : X → ℝ) (hd : Measurable d) (hY : Measurable Y)
    (hinv : ∀ u x, d (act u x)=d x)
    (orbit : D → G → ℝ) (horbit : Measurable (fun z : D × G => orbit z.1 z.2))
    (hkernel : ∀ x, H.map (fun u => (d x,Y (act u x)))=
      H.map (fun u => (d x,orbit (d x) u))) :
    P.map (fun x => (d x,Y x))=
      ((P.map d).prod H).map (fun z => (z.1,orbit z.1 z.2)) := by
  have hs := (MeasurePreserving.id H).skew_product hact
    (Filter.Eventually.of_forall hpres)
  have hp := ((show MeasurePreserving Prod.snd (H.prod P) P from measurePreserving_snd).comp hs).comp
    (show MeasurePreserving Prod.swap (P.prod H) (H.prod P) from Measure.measurePreserving_swap)
  have hf : Measurable (fun x => (d x,Y x)) := hd.prodMk hY
  have he := congrArg (fun Q : Measure X => Q.map (fun x => (d x,Y x))) hp.map_eq
  rw [Measure.map_map hf hp.measurable] at he
  have hF : Measurable (fun z : X × G => (d z.1,Y (act z.2 z.1))) :=
    (hd.comp measurable_fst).prodMk (hY.comp (hact.comp measurable_swap))
  have hB : Measurable (fun z : X × G => (d z.1,orbit (d z.1) z.2)) :=
    (hd.comp measurable_fst).prodMk
      (horbit.comp ((hd.comp measurable_fst).prodMk measurable_snd))
  have havg : P.map (fun x => (d x,Y x))=
      (P.prod H).map (fun z : X × G => (d z.1,Y (act z.2 z.1))) := by
    refine he.symm.trans ?_
    congr 1
    funext z
    exact Prod.ext (hinv z.2 z.1) rfl
  rw [havg,map_prod_eq_of_fiber_maps P H _ _ hF hB hkernel]
  have hdp : MeasurePreserving d P (P.map d) := ⟨hd,rfl⟩
  have hprod := hdp.prod (MeasurePreserving.id H)
  have ht := congrArg (fun Q : Measure (D × G) =>
    Q.map (fun z => (z.1,orbit z.1 z.2))) hprod.map_eq
  rw [Measure.map_map (measurable_fst.prodMk horbit) hprod.measurable] at ht
  exact ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_CanonicalOrthogonalLaw
attribute [-instance] _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete orthogonal Haar probability from the square Gaussian frame.
This determines the orthogonal orbit law in the Wishart corollary. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
namespace InvariantIsing

lemma coe_squareFrameOrthogonal {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    (squareFrameOrthogonal A : Matrix (Fin N) (Fin N) ℝ)=if Aᵀ*A=1 then A else 1 := by
  classical
  unfold squareFrameOrthogonal
  split <;> simp_all

lemma measurable_squareFrameOrthogonal (N : ℕ) :
    Measurable (squareFrameOrthogonal (N := N)) := by
  classical
  apply Measurable.subtype_mk
  have hh : Measurable (fun A : Matrix (Fin N) (Fin N) ℝ => if Aᵀ*A=1 then A else 1) :=
    Measurable.ite
      ((isClosed_eq (continuous_id.matrix_transpose.matrix_mul continuous_id) continuous_const).measurableSet)
      measurable_id measurable_const
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext A
  exact coe_squareFrameOrthogonal A

lemma squareFrameOrthogonal_mul {N : ℕ} (U : Orthogonal N)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : Aᵀ*A=1) :
    squareFrameOrthogonal ((U : Matrix (Fin N) (Fin N) ℝ)*A)=U*squareFrameOrthogonal A := by
  have hUA : ((U : Matrix (Fin N) (Fin N) ℝ)*A)ᵀ*((U : Matrix (Fin N) (Fin N) ℝ)*A)=1 := by
    rw [cavityGram_left_orthogonal A _ ((Matrix.mem_orthogonalGroup_iff' _ _).mp U.property),hA]
  apply Subtype.ext
  simp only [squareFrameOrthogonal,dite_eq_left hA,dite_eq_left hUA]
  rfl

instance squareFrameLaw_probability (N : ℕ) : IsProbabilityMeasure (cavityConditionedFrameLaw N N) := by
  apply cavityConditionedFrameLaw_probability
  rw [cavityArrayGood_probability,cavityGoodGram_probability_one N N le_rfl]
  exact one_ne_zero

instance orthogonalGaussianLeftHaar_probability (N : ℕ) :
    IsProbabilityMeasure (orthogonalGaussianLeftHaar N) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_squareFrameOrthogonal N).aemeasurable).mpr inferInstance

instance orthogonalGaussianLeftHaar_leftInvariant (N : ℕ) :
    (orthogonalGaussianLeftHaar N).IsMulLeftInvariant := by
  constructor
  intro U
  have hact : Measurable (fun A : Matrix (Fin N) (Fin N) ℝ => (U : Matrix (Fin N) (Fin N) ℝ)*A) :=
    ((continuous_cavityFrameAction N N).comp (continuous_const.prodMk continuous_id)).measurable
  rw [orthogonalGaussianLeftHaar,Measure.map_map (measurable_const_mul U)
    (measurable_squareFrameOrthogonal N)]
  have he : (fun A : Matrix (Fin N) (Fin N) ℝ => U*squareFrameOrthogonal A)=ᵐ[cavityConditionedFrameLaw N N]
      (fun A => squareFrameOrthogonal ((U : Matrix (Fin N) (Fin N) ℝ)*A)) := by
    filter_upwards [cavityConditionedFrameLaw_orthonormal N N] with A hA
    exact (squareFrameOrthogonal_mul U A hA).symm
  change (cavityConditionedFrameLaw N N).map (fun A => U*squareFrameOrthogonal A)=_
  rw [Measure.map_congr he]
  change (cavityConditionedFrameLaw N N).map (squareFrameOrthogonal ∘ _)=_
  rw [← Measure.map_map (measurable_squareFrameOrthogonal N) hact,cavityConditionedFrameLaw_rotation]

instance orthogonalGaussianHaar_probability (N : ℕ) : IsProbabilityMeasure (orthogonalGaussianHaar N) := by
  unfold orthogonalGaussianHaar Measure.inv
  exact (Measure.isProbabilityMeasure_map_iff measurable_inv.aemeasurable).mpr inferInstance

instance orthogonalGaussianHaar_rightInvariant (N : ℕ) :
    (orthogonalGaussianHaar N).IsMulRightInvariant := by
  unfold orthogonalGaussianHaar
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianPatternModel
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gaussian-pattern Hamiltonian with its diagonal self-interactions.
The array is indexed by spin coordinate first and pattern coordinate second. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
namespace InvariantIsing

lemma quadraticEnergy_dotProduct {N : ℕ} (J : Matrix (Fin N) (Fin N) ℝ) (σ : Spin N) :
    quadraticEnergy J σ=(1/2 : ℝ)*
      ((fun i => spinValue (σ i)) ⬝ᵥ J *ᵥ (fun i => spinValue (σ i))) := by
  simp only [quadraticEnergy,dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]

lemma gaussianPattern_energy {N m : ℕ} (c : ℝ)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) (σ : Spin N) :
    quadraticEnergy (gaussianPatternCoupling c z) σ=c/(2*N)*‖gaussianPatternSum z σ‖^2 := by
  let v := fun i => spinValue (σ i)
  have hn : ‖gaussianPatternSum z σ‖^2=
      ((gaussianPatternArray z)ᵀ *ᵥ v) ⬝ᵥ ((gaussianPatternArray z)ᵀ *ᵥ v) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [gaussianPatternSum,dotProduct,pow_two]
    rfl
  rw [quadraticEnergy_dotProduct,gaussianPatternCoupling,Matrix.smul_mulVec,dotProduct_smul,
    ← Matrix.mulVec_mulVec,hn]
  rw [Matrix.dotProduct_transpose_mulVec]
  simp only [smul_eq_mul]
  ring

lemma gaussianPatternPressure_eq {N m : ℕ} (c : ℝ)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    gaussianPatternPressure c z=pressure (gaussianPatternCoupling c z) (fun _ => 0) := by
  simp only [gaussianPatternPressure,pressure,gaussianPattern_energy,fieldEnergy,
    zero_mul,Finset.sum_const_zero,add_zero]

lemma measurable_gaussianPatternPressure (N m : ℕ) (c : ℝ) :
    Measurable (gaussianPatternPressure (N := N) (m := m) c) := by
  unfold gaussianPatternPressure logPartition
  have hm (σ : Spin N) : Measurable (fun z : EuclideanSpace ℝ (Fin N × Fin m) =>
      c/(2*N)*‖gaussianPatternSum z σ‖^2) := by
    have hs : Continuous (fun z : EuclideanSpace ℝ (Fin N × Fin m) => gaussianPatternSum z σ) := by
      unfold gaussianPatternSum gaussianPatternArray
      fun_prop
    exact (hs.measurable.norm.pow_const 2).const_mul _
  exact ((Finset.measurable_sum _ fun σ _ => (hm σ).exp).const_mul _).log.const_mul _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianPatternRotation
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.orthogonalGaussianHaar_probability _root_.OAI.InvariantIsing.orthogonalGaussianHaar_rightInvariant _root_.OAI.InvariantIsing.orthogonalGaussianLeftHaar_leftInvariant _root_.OAI.InvariantIsing.orthogonalGaussianLeftHaar_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-dimensional Gaussian orthogonal invariance and invariance of the
ordered Wishart eigenvalues, including repeated zero eigenvalues. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
namespace InvariantIsing

lemma gaussianPatternArray_rotation {N m : ℕ} (U : Orthogonal N)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    gaussianPatternArray (cavityColumnRotation m (matrixRotation U) z)=
      (U : Matrix (Fin N) (Fin N) ℝ)*gaussianPatternArray z := by
  ext i j
  simp only [gaussianPatternArray,cavityColumnRotation_apply,matrixRotation_apply,Matrix.mul_apply]

lemma gaussianPatternCoupling_rotation {N m : ℕ} (c : ℝ) (U : Orthogonal N)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    gaussianPatternCoupling c (cavityColumnRotation m (matrixRotation U) z)=
      (U : Matrix (Fin N) (Fin N) ℝ)*gaussianPatternCoupling c z*
        (U : Matrix (Fin N) (Fin N) ℝ)ᵀ := by
  simp only [gaussianPatternCoupling,gaussianPatternArray_rotation,Matrix.transpose_mul,
    Matrix.mul_assoc,smul_mul_assoc,mul_smul_comm]

lemma gaussianPatternEigenvalues_rotation {N m : ℕ} (U : Orthogonal N)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    gaussianPatternEigenvalues (cavityColumnRotation m (matrixRotation U) z)=
      gaussianPatternEigenvalues z := by
  unfold gaussianPatternEigenvalues
  apply ((gaussianPatternCoupling_isHermitian 1 _).eigenvalues_eq_eigenvalues_iff
    (gaussianPatternCoupling_isHermitian 1 z)).mpr
  rw [gaussianPatternCoupling_rotation,Matrix.charpoly_mul_comm,← Matrix.mul_assoc]
  have hU := (Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mp U.property
  rw [hU,Matrix.one_mul]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralApproximationSqueeze
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The final two-scale squeeze used in compact spectral approximation. -/

noncomputable section
open Filter
open scoped Topology

namespace InvariantIsing

lemma spectral_approximation_squeeze (p : ℕ → ℝ) (lo hi : ℕ → ℕ → ℝ)
    (v δ : ℕ → ℝ) (L : ℝ) (hv : Tendsto v atTop (𝓝 L))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hlo : ∀ k, Tendsto (lo k) atTop (𝓝 (v k)))
    (hhi : ∀ k, Tendsto (hi k) atTop (𝓝 (v k)))
    (hbound : ∀ k, ∀ᶠ N in atTop, lo k N-δ k/2 ≤ p N ∧ p N ≤ hi k N+δ k/2) :
    Tendsto p atTop (𝓝 L) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨k,hk,hdk⟩ := ((Metric.tendsto_nhds.mp hv (ε/3) (by positivity)).and
    (Metric.tendsto_nhds.mp hδ (ε/3) (by positivity))).exists
  filter_upwards [Metric.tendsto_nhds.mp (hlo k) (ε/3) (by positivity),
    Metric.tendsto_nhds.mp (hhi k) (ε/3) (by positivity),hbound k] with N hl hu hp
  rw [Real.dist_eq,abs_lt] at hk hdk hl hu ⊢
  constructor <;> linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_GroundStateFinite
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.rotationMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual maximum Ising energy and its uniform finite-temperature squeeze. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace InvariantIsing

lemma groundStateEnergy_attained {N : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) :
    (∀ σ, rotatedEnergy eig U σ ≤ N*groundStateEnergy eig U) ∧
      ∃ σ, rotatedEnergy eig U σ=N*groundStateEnergy eig U := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : (N : ℝ)*groundStateEnergy eig U=
      Finset.univ.sup' Finset.univ_nonempty (rotatedEnergy eig U) := by
    unfold groundStateEnergy
    field_simp
  rw [he]
  constructor
  · intro σ
    exact Finset.le_sup' _ (Finset.mem_univ σ)
  · obtain ⟨σ,_,hσ⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (rotatedEnergy eig U)
    exact ⟨σ,hσ.symm⟩

lemma abs_groundStateEnergy_le {N : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (K : ℝ) (hK : ∀ i, |eig i| ≤ K) :
    |groundStateEnergy eig U| ≤ K/2 := by
  obtain ⟨σ,hσ⟩ := (groundStateEnergy_attained hN eig U).2
  have hh := abs_rotatedEnergy_le eig U K hK σ
  rw [hσ,abs_mul,abs_of_nonneg (Nat.cast_nonneg N)] at hh
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  nlinarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralExtremeLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convergence of the actual extreme eigenvalues implies the uniform
no-outlier formulation used by the pressure theorem. -/

noncomputable section
open Filter
open scoped Topology Classical

namespace InvariantIsing

lemma spectralMinimum_le {n : ℕ} (eig : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    spectralMinimum eig ≤ eig i :=
  Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)

lemma le_spectralMaximum {n : ℕ} (eig : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    eig i ≤ spectralMaximum eig :=
  Finset.le_max' _ _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_RandomOrbitLaw
attribute [-instance] _root_.OAI.InvariantIsing.orthogonalGaussianHaar_probability _root_.OAI.InvariantIsing.orthogonalGaussianHaar_rightInvariant _root_.OAI.InvariantIsing.orthogonalGaussianLeftHaar_leftInvariant _root_.OAI.InvariantIsing.orthogonalGaussianLeftHaar_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.squareFrameLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The joint conditional-Haar hypothesis for random spectra and fields.
Only the one-dimensional marginal orbit law is prescribed at each dimension. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace InvariantIsing

lemma measurable_random_specialPressure {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (eig field : Ω → Fin N → ℝ) (heig : Measurable eig) (hfield : Measurable field)
    (U : Ω → SpecialOrthogonal N) (hU : Measurable U) :
    Measurable (fun ω => rotatedPressure (eig ω) (specialRotation (U ω)) (field ω)) := by
  have hE (σ : Spin N) : Measurable (fun ω =>
      rotatedEnergy (eig ω) (specialRotation (U ω)) σ+fieldEnergy (field ω) σ) := by
    apply Measurable.add
    · exact ((Finset.measurable_sum _ fun i _ =>
        ((measurable_pi_apply i).comp heig).mul
          (((measurable_specialRotation_eval (spinVector σ) i).comp hU).pow_const 2))).const_mul (1/2 : ℝ)
    · exact Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp hfield).mul_const _
  unfold rotatedPressure logPartition
  exact ((Finset.measurable_sum _ fun σ _ => (hE σ).exp).const_mul
    (Fintype.card (Spin N) : ℝ)⁻¹).log.const_mul (N : ℝ)⁻¹

lemma measurable_dataPhysicalPressure {N : ℕ} (hN : 0 < N) :
    Measurable (fun z : FieldSpectralData N × Orthogonal N => dataPhysicalPressure z.1 z.2) := by
  have hh := measurable_random_specialPressure
    (fun z : FieldSpectralData N × Orthogonal N => z.1.1)
    (fun z : FieldSpectralData N × Orthogonal N => z.1.2)
    (measurable_fst.comp measurable_fst) (measurable_snd.comp measurable_fst)
    (fun z => cavityOrientationLift hN z.2⁻¹)
    ((measurable_cavityOrientationLift hN).comp measurable_snd.inv)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  simp only [dataPhysicalPressure,rotatedPressure,cavityOrientationLift_energy]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianPatternOrbit
attribute [-instance] _root_.OAI.InvariantIsing.orthogonalGaussianHaar_probability _root_.OAI.InvariantIsing.orthogonalGaussianHaar_rightInvariant _root_.OAI.InvariantIsing.orthogonalGaussianLeftHaar_leftInvariant _root_.OAI.InvariantIsing.orthogonalGaussianLeftHaar_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise diagonalization of the actual Gaussian-pattern pressure. No
measurable choice of eigenvectors is required for Haar averaging. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
namespace InvariantIsing

lemma pressure_conjugate_diagonal {N : ℕ} (eig : Fin N → ℝ) (U : Orthogonal N) :
    pressure (cavityConjugate U (Matrix.diagonal eig)) (fun _ => 0)=
      dataPhysicalPressure (eig,fun _ => 0) U := by
  unfold pressure dataPhysicalPressure rotatedPressure
  congr 2
  funext σ
  exact congrArg (fun x => x+fieldEnergy (fun _ => 0) σ)
    (cavityQuadratic_inverse_rotation eig U σ)

lemma gaussianPatternCoupling_smul {N m : ℕ} (c : ℝ)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    gaussianPatternCoupling c z=c • gaussianPatternCoupling 1 z := by
  simp only [gaussianPatternCoupling,smul_smul,one_div]
  rw [div_eq_mul_inv]

lemma cavityConjugate_diagonal_smul {N : ℕ} (c : ℝ) (U : Orthogonal N) (eig : Fin N → ℝ) :
    c • cavityConjugate U (Matrix.diagonal eig)=
      cavityConjugate U (Matrix.diagonal (fun i => c*eig i)) := by
  have hd : Matrix.diagonal (fun i => c*eig i)=c • Matrix.diagonal eig := by
    ext i j
    by_cases h : i=j <;> simp [h]
  rw [hd]
  simp only [cavityConjugate,smul_mul_assoc,mul_smul_comm]

lemma gaussianPattern_diagonalization {N m : ℕ}
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    ∃ V : Orthogonal N, gaussianPatternCoupling 1 z=
      cavityConjugate V (Matrix.diagonal (gaussianPatternEigenvalues z)) := by
  let hA := gaussianPatternCoupling_isHermitian 1 z
  refine ⟨hA.eigenvectorUnitary,?_⟩
  simpa [cavityConjugate,Unitary.conjStarAlgAut_apply,Function.comp_def,
    gaussianPatternEigenvalues,hA,Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using hA.spectral_theorem

lemma gaussianPattern_pressure_orbit {N m : ℕ} (c : ℝ)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    ∃ V : Orthogonal N, ∀ U : Orthogonal N,
      gaussianPatternPressure c (cavityColumnRotation m (matrixRotation U) z)=
        dataPhysicalPressure ((fun i => c*gaussianPatternEigenvalues z i),fun _ => 0) (U*V) := by
  obtain ⟨V,hV⟩ := gaussianPattern_diagonalization z
  refine ⟨V,fun U => ?_⟩
  rw [gaussianPatternPressure_eq,gaussianPatternCoupling_rotation,
    gaussianPatternCoupling_smul,hV,cavityConjugate_diagonal_smul]
  change pressure (cavityConjugate U (cavityConjugate V
    (Matrix.diagonal (fun i => c*gaussianPatternEigenvalues z i)))) (fun _ => 0)=_
  rw [← cavityConjugate_mul,pressure_conjugate_diagonal]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_RandomSpectralBound
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The extreme eigenvalues control a random spectrum without moment hypotheses. -/
noncomputable section
open Filter Set
open scoped Topology
namespace InvariantIsing

lemma abs_le_spectralRadius {n : ℕ} (eig : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    |eig i| ≤ spectralRadius eig := by
  apply abs_le.mpr
  constructor
  · exact (neg_le_neg (le_max_left _ _)).trans
      ((neg_abs_le (spectralMinimum eig)).trans (spectralMinimum_le eig i))
  · exact (le_spectralMaximum eig i).trans
      ((le_abs_self _).trans (le_max_right _ _))

lemma spectralRadius_le_iff {n : ℕ} (eig : Fin (n+1) → ℝ) (K : ℝ) :
    spectralRadius eig ≤ K ↔ ∀ i, |eig i| ≤ K := by
  constructor
  · intro h i
    exact (abs_le_spectralRadius eig i).trans h
  · intro h
    apply max_le
    · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (Finset.min'_mem
        (Finset.univ.image eig) (Finset.image_nonempty.mpr Finset.univ_nonempty))
      simpa only [spectralMinimum,← hi] using h i
    · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (Finset.max'_mem
        (Finset.univ.image eig) (Finset.image_nonempty.mpr Finset.univ_nonempty))
      simpa only [spectralMaximum,← hi] using h i

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_RandomSpectralMeasurability
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability of the finite-dimensional spectral norm bound. -/
noncomputable section
open MeasureTheory
namespace InvariantIsing

lemma spectralRadius_eq_sup_abs {n : ℕ} (eig : Fin (n+1) → ℝ) :
    spectralRadius eig=Finset.univ.sup' Finset.univ_nonempty (fun i => |eig i|) := by
  apply le_antisymm
  · apply (spectralRadius_le_iff _ _).mpr
    intro i
    exact Finset.le_sup' (fun i => |eig i|) (Finset.mem_univ i)
  · exact Finset.sup'_le Finset.univ_nonempty _ fun i _ => abs_le_spectralRadius eig i

lemma measurable_spectralRadius {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (eig : Ω → Fin (n+1) → ℝ) (heig : Measurable eig) :
    Measurable (fun ω => spectralRadius (eig ω)) := by
  have hh := Finset.measurable_sup' (s := (Finset.univ : Finset (Fin (n+1))))
    Finset.univ_nonempty (fun i _ => ((measurable_pi_apply i).comp heig).abs)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext ω
  rw [spectralRadius_eq_sup_abs,Finset.sup'_apply]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianPatternGroundFinite
attribute [-instance] _root_.OAI.InvariantIsing.orthogonalGaussianHaar_probability _root_.OAI.InvariantIsing.orthogonalGaussianHaar_rightInvariant _root_.OAI.InvariantIsing.orthogonalGaussianLeftHaar_leftInvariant _root_.OAI.InvariantIsing.orthogonalGaussianLeftHaar_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Gaussian-pattern maximum energies and their finite-temperature squeeze. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
namespace InvariantIsing

lemma measurable_gaussianPatternGroundEnergy (N m : ℕ) (ε : ℝ) :
    Measurable (gaussianPatternGroundEnergy (N := N) (m := m) ε) := by
  have hm (σ : Spin N) : Measurable (fun z : EuclideanSpace ℝ (Fin N × Fin m) =>
      ε/(2*N)*‖gaussianPatternSum z σ‖^2) := by
    have hs : Continuous (fun z : EuclideanSpace ℝ (Fin N × Fin m) => gaussianPatternSum z σ) := by
      unfold gaussianPatternSum gaussianPatternArray
      fun_prop
    exact (hs.measurable.norm.pow_const 2).const_mul _
  have hh := Finset.measurable_sup' Finset.univ_nonempty (fun σ _ => hm σ)
  convert hh.const_mul (N : ℝ)⁻¹ using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  simp only [gaussianPatternGroundEnergy,Finset.sup'_apply]

lemma gaussianPatternGroundEnergy_squeeze {N m : ℕ} (hN : 0 < N) (ε β : ℝ)
    (hβ : 0 < β) (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    gaussianPatternPressure (ε*β) z/β ≤ gaussianPatternGroundEnergy ε z ∧
    gaussianPatternGroundEnergy ε z ≤ gaussianPatternPressure (ε*β) z/β+Real.log 2/β := by
  let E := fun σ : Spin N => ε/(2*N)*‖gaussianPatternSum z σ‖^2
  have hval : (N : ℝ)*gaussianPatternGroundEnergy ε z=
      Finset.univ.sup' Finset.univ_nonempty E := by
    unfold gaussianPatternGroundEnergy
    rw [← mul_assoc,mul_inv_cancel₀ (show (N : ℝ) ≠ 0 by exact_mod_cast hN.ne'),one_mul]
  have hb : ∀ σ, E σ ≤ N*gaussianPatternGroundEnergy ε z := by
    rw [hval]
    exact fun σ => Finset.le_sup' E (Finset.mem_univ σ)
  have ha : ∃ σ, E σ=N*gaussianPatternGroundEnergy ε z := by
    obtain ⟨σ,_,hσ⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty E
    exact ⟨σ,hσ.symm.trans hval.symm⟩
  have hh := finite_groundState_squeeze hN E β (gaussianPatternGroundEnergy ε z) hβ hb ha
  have hp : gaussianPatternPressure (ε*β) z=(N : ℝ)⁻¹*logPartition (fun σ => β*E σ) := by
    unfold gaussianPatternPressure
    congr 2
    funext σ
    dsimp [E]
    ring
  rw [hp]
  exact ⟨hh.2,by linarith [hh.1]⟩

lemma gaussianPatternGroundEnergy_orbit {N m : ℕ} (ε : ℝ)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    ∃ V : Orthogonal N, gaussianPatternGroundEnergy ε z=
      groundStateEnergy (fun i => ε*gaussianPatternEigenvalues z i) (matrixRotation V⁻¹) := by
  obtain ⟨V,hV⟩ := gaussianPattern_diagonalization z
  refine ⟨V,?_⟩
  have he (σ : Spin N) : ε/(2*N)*‖gaussianPatternSum z σ‖^2=
      rotatedEnergy (fun i => ε*gaussianPatternEigenvalues z i) (matrixRotation V⁻¹) σ := by
    rw [← gaussianPattern_energy,gaussianPatternCoupling_smul,hV,cavityConjugate_diagonal_smul]
    exact cavityQuadratic_inverse_rotation _ V σ
  unfold gaussianPatternGroundEnergy groundStateEnergy
  simp only [he]

lemma abs_gaussianPatternGroundEnergy_le {n m : ℕ} (ε : ℝ)
    (z : EuclideanSpace ℝ (Fin (n+1) × Fin m)) :
    |gaussianPatternGroundEnergy ε z| ≤
      spectralRadius (fun i => ε*gaussianPatternEigenvalues z i)/2 := by
  obtain ⟨V,hV⟩ := gaussianPatternGroundEnergy_orbit ε z
  rw [hV]
  exact abs_groundStateEnergy_le (Nat.succ_pos n) _ _ _ (abs_le_spectralRadius _)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_PhysicalOrbitKernel
attribute [-instance] _root_.OAI.InvariantIsing.orthogonalGaussianHaar_probability _root_.OAI.InvariantIsing.orthogonalGaussianHaar_rightInvariant _root_.OAI.InvariantIsing.orthogonalGaussianLeftHaar_leftInvariant _root_.OAI.InvariantIsing.orthogonalGaussianLeftHaar_probability _root_.OAI.InvariantIsing.squareFrameLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-data sections of the physical pressure and right-Haar transport. -/
noncomputable section
open MeasureTheory
namespace InvariantIsing

lemma measurable_dataPhysicalPressure_section {N : ℕ} (hN : 0 < N)
    (d : FieldSpectralData N) : Measurable (dataPhysicalPressure d) := by
  exact Measurable.of_uncurry_left (f := dataPhysicalPressure) (x := d)
    (measurable_dataPhysicalPressure hN)

lemma physical_orbit_kernel {N : ℕ} (hN : 0 < N)
    (H : Measure (Orthogonal N)) [H.IsMulRightInvariant]
    (d : FieldSpectralData N) (Y : Orthogonal N → ℝ) (V : Orthogonal N)
    (hY : ∀ U, Y U=dataPhysicalPressure d (U*V)) :
    H.map (fun U => (d,Y U))=H.map (fun U => (d,dataPhysicalPressure d U)) := by
  exact paired_map_eq_of_comp H d (dataPhysicalPressure d) Y (fun U => U*V)
    (measurable_dataPhysicalPressure_section hN d) (measurable_id.mul_const V)
    (map_mul_right_eq_self H V) hY

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianPatternOrbitLaw
attribute [-instance] _root_.OAI.InvariantIsing.orthogonalGaussianHaar_probability _root_.OAI.InvariantIsing.orthogonalGaussianHaar_rightInvariant _root_.OAI.InvariantIsing.orthogonalGaussianLeftHaar_leftInvariant _root_.OAI.InvariantIsing.orthogonalGaussianLeftHaar_probability _root_.OAI.InvariantIsing.squareFrameLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Haar disintegration of the actual Gaussian-pattern pressure, proved from
finite Gaussian invariance and pointwise spectral diagonalization. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace InvariantIsing

lemma continuous_gaussianPatternRotation (N m : ℕ) :
    Continuous (fun p : Orthogonal N × EuclideanSpace ℝ (Fin N × Fin m) =>
      cavityColumnRotation m (matrixRotation p.1) p.2) := by
  change Continuous (fun p : Orthogonal N × EuclideanSpace ℝ (Fin N × Fin m) =>
    WithLp.toLp 2 (fun ij : Fin N × Fin m => ∑ k, (p.1 : Matrix (Fin N) (Fin N) ℝ) ij.1 k * p.2 (k,ij.2)))
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro ij
  apply continuous_finsetSum
  intro k _
  have hU : Continuous (fun p : Orthogonal N × EuclideanSpace ℝ (Fin N × Fin m) =>
      (p.1 : Matrix (Fin N) (Fin N) ℝ)) := continuous_subtype_val.comp continuous_fst
  have hu : Continuous (fun p : Orthogonal N × EuclideanSpace ℝ (Fin N × Fin m) =>
      (p.1 : Matrix (Fin N) (Fin N) ℝ) ij.1 k) :=
    (continuous_apply k).comp ((continuous_apply ij.1).comp hU)
  exact hu.mul ((PiLp.continuous_apply 2 _ (k,ij.2)).comp continuous_snd)

lemma gaussianPattern_orbit_kernel {N m : ℕ} (hN : 0 < N) (c : ℝ)
    (H : Measure (Orthogonal N)) [IsProbabilityMeasure H] [H.IsMulRightInvariant]
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    H.map (fun U => (((fun i => c*gaussianPatternEigenvalues z i),fun _ : Fin N => (0 : ℝ)),
      gaussianPatternPressure c (cavityColumnRotation m (matrixRotation U) z)))=
    H.map (fun U => (((fun i => c*gaussianPatternEigenvalues z i),fun _ : Fin N => (0 : ℝ)),
      dataPhysicalPressure ((fun i => c*gaussianPatternEigenvalues z i),fun _ => 0) U)) := by
  obtain ⟨V,hV⟩ := gaussianPattern_pressure_orbit c z
  exact physical_orbit_kernel hN H _ _ V hV

theorem gaussianPattern_conditionalOrbit {N m : ℕ} (hN : 0 < N) (c : ℝ)
    (heig : Measurable (gaussianPatternEigenvalues (N := N) (m := m)))
    (H : Measure (Orthogonal N)) [IsProbabilityMeasure H] [H.IsMulRightInvariant] :
    ConditionalFieldOrbitLaw (stdGaussian (EuclideanSpace ℝ (Fin N × Fin m)))
      (fun z => ((fun i => c*gaussianPatternEigenvalues z i),fun _ => 0))
      (gaussianPatternPressure c) H := by
  let d : EuclideanSpace ℝ (Fin N × Fin m) → FieldSpectralData N := fun z =>
    ((fun i => c*gaussianPatternEigenvalues z i),fun _ => 0)
  have hd : Measurable d := (measurable_pi_iff.mpr fun i =>
    ((measurable_pi_apply i).comp heig).const_mul c).prodMk measurable_const
  have hi : ∀ (U : Orthogonal N) (z : EuclideanSpace ℝ (Fin N × Fin m)),
      d (cavityColumnRotation m (matrixRotation U) z)=d z := by
    intro U z
    simp only [d,gaussianPatternEigenvalues_rotation]
  exact invariant_joint_orbit_law (stdGaussian (EuclideanSpace ℝ (Fin N × Fin m))) H
    (fun U z => cavityColumnRotation m (matrixRotation U) z)
    (continuous_gaussianPatternRotation N m).measurable
    (fun U => cavityColumnRotation_gaussian (matrixRotation U)) d
    (gaussianPatternPressure c) hd (measurable_gaussianPatternPressure N m c) hi
    dataPhysicalPressure (measurable_dataPhysicalPressure hN)
    (gaussianPattern_orbit_kernel hN c H)

theorem gaussianPattern_conditionalOrbit_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {N m : ℕ} (hN : 0 < N) (c : ℝ) (P : Measure Ω)
    (Z : Ω → EuclideanSpace ℝ (Fin N × Fin m)) (hZ : Measurable Z)
    (hlaw : HasLaw Z (stdGaussian _) P)
    (heig : Measurable (gaussianPatternEigenvalues (N := N) (m := m)))
    (H : Measure (Orthogonal N)) [IsProbabilityMeasure H] [H.IsMulRightInvariant] :
    ConditionalFieldOrbitLaw P
      (fun ω => ((fun i => c*gaussianPatternEigenvalues (Z ω) i),fun _ => 0))
      (fun ω => gaussianPatternPressure c (Z ω)) H := by
  let d := fun z : EuclideanSpace ℝ (Fin N × Fin m) =>
    ((fun i => c*gaussianPatternEigenvalues z i),fun _ : Fin N => (0 : ℝ))
  have hd : Measurable d := (measurable_pi_iff.mpr fun i =>
    ((measurable_pi_apply i).comp heig).const_mul c).prodMk measurable_const
  have hp := measurable_gaussianPatternPressure N m c
  have hdm : P.map (fun ω => d (Z ω))=(stdGaussian _).map d := by
    change P.map (d ∘ Z)=_
    rw [← Measure.map_map hd hZ,hlaw.map_eq]
  have hym : P.map (fun ω => (d (Z ω),gaussianPatternPressure c (Z ω)))=
      (stdGaussian _).map (fun z => (d z,gaussianPatternPressure c z)) := by
    change P.map ((fun z => (d z,gaussianPatternPressure c z)) ∘ Z)=_
    rw [← Measure.map_map (hd.prodMk hp) hZ,hlaw.map_eq]
  change P.map (fun ω => (d (Z ω),gaussianPatternPressure c (Z ω)))=
    ((P.map (fun ω => d (Z ω))).prod H).map _
  rw [hym,hdm]
  exact gaussianPattern_conditionalOrbit hN c heig H

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_RandomOrbitSupport
attribute [-instance] _root_.OAI.InvariantIsing.orthogonalGaussianHaar_probability _root_.OAI.InvariantIsing.orthogonalGaussianHaar_rightInvariant _root_.OAI.InvariantIsing.orthogonalGaussianLeftHaar_leftInvariant _root_.OAI.InvariantIsing.orthogonalGaussianLeftHaar_probability _root_.OAI.InvariantIsing.squareFrameLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transporting deterministic orbit bounds through the joint conditional law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace InvariantIsing

lemma ConditionalFieldOrbitLaw.ae_property {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (hN : 0 < N) (P : Measure Ω) (d : Ω → FieldSpectralData N) (Y : Ω → ℝ)
    (hd : Measurable d) (hY : Measurable Y)
    (H : Measure (Orthogonal N)) [SFinite H]
    (hlaw : ConditionalFieldOrbitLaw P d Y H)
    (Q : FieldSpectralData N × ℝ → Prop) (hQ : MeasurableSet {z | Q z})
    (hbound : ∀ data U, Q (data,dataPhysicalPressure data U)) :
    ∀ᵐ ω ∂P, Q (d ω,Y ω) := by
  apply ae_of_ae_map (hd.prodMk hY).aemeasurable
  rw [hlaw]
  apply (ae_map_iff (measurable_fst.prodMk (measurable_dataPhysicalPressure hN)).aemeasurable hQ).mpr
  exact Filter.Eventually.of_forall fun z => hbound z.1 z.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_RandomUniformIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The uniform-integrability conclusion of Proposition gen:random. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
namespace InvariantIsing

lemma uniformIntegrable_of_abs_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Z : ℕ → Ω → ℝ) (hX : ∀ n, AEStronglyMeasurable (X n) P)
    (hZ : UniformIntegrable Z 1 P) (hXZ : ∀ n, ∀ᵐ ω ∂P, |X n ω| ≤ |Z n ω|) :
    UniformIntegrable X 1 P := by
  have hd n : (fun ω => ‖X n ω‖ₑ) ≤ᵐ[P] (fun ω => ‖Z n ω‖ₑ) :=
    (hXZ n).mono fun ω hω => by
      simpa only [Real.enorm_eq_ofReal_abs] using ENNReal.ofReal_le_ofReal hω
  have hu : UnifIntegrable X 1 P := by
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := hZ.2.1 hε
    refine ⟨δ, hδ, fun n s hs hμ => ?_⟩
    refine le_trans (eLpNorm_mono_enorm_ae ?_) (h n s hs hμ)
    filter_upwards [hd n] with ω hω
    by_cases hω' : ω ∈ s
    · simpa [Set.indicator_of_mem hω'] using hω
    · simp [Set.indicator_of_notMem hω']
  obtain ⟨C,hC⟩ := hZ.2.2
  exact ⟨hX, hu, C, fun n => (eLpNorm_mono_enorm_ae (hd n)).trans (hC n)⟩

lemma pressure_L1_of_probability_and_uniformIntegrability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (L : ℝ) (hUI : UniformIntegrable X 1 P)
    (hprob : TendstoInMeasure P X atTop (fun _ => L)) :
    Tendsto (fun n => eLpNorm (fun ω => X n ω-L) 1 P) atTop (𝓝 0) ∧
    Tendsto (fun n => ∫ ω, X n ω ∂P) atTop (𝓝 L) := by
  have hL := tendsto_Lp_finite_of_tendstoInMeasure (p := 1) le_rfl (by simp)
    hUI.aestronglyMeasurable (memLp_const L) hUI.2.1 hprob
  refine ⟨hL,?_⟩
  have hh := tendsto_integral_of_L1' (hfi := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | exact MemLp.aestronglyMeasurable (by assumption) | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (fun _ : Ω => L)
    (Filter.Eventually.of_forall fun n => (memLp_one_iff_integrable.mp (hUI.memLp n))) hL
  simpa only [integral_const,probReal_univ,one_smul] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_RandomPressureBound
attribute [-instance] _root_.OAI.InvariantIsing.orthogonalGaussianHaar_probability _root_.OAI.InvariantIsing.orthogonalGaussianHaar_rightInvariant _root_.OAI.InvariantIsing.orthogonalGaussianLeftHaar_leftInvariant _root_.OAI.InvariantIsing.orthogonalGaussianLeftHaar_probability _root_.OAI.InvariantIsing.squareFrameLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The operator-norm sufficient condition for uniform integrability of the
actual random pressure under its conditional orbit law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace InvariantIsing

lemma ConditionalFieldOrbitLaw.zero_field_bound {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (eig : Ω → Fin (n+1) → ℝ) (Y : Ω → ℝ)
    (heig : Measurable eig) (hY : Measurable Y)
    (H : Measure (Orthogonal (n+1))) [SFinite H]
    (hlaw : ConditionalFieldOrbitLaw P (fun ω => (eig ω,fun _ => 0)) Y H) :
    ∀ᵐ ω ∂P, |Y ω| ≤ spectralRadius (eig ω)/2 := by
  let Q := fun z : FieldSpectralData (n+1) × ℝ =>
    z.1.2 ≠ (fun _ => 0) ∨ |z.2| ≤ spectralRadius z.1.1/2
  have hQ : MeasurableSet {z | Q z} :=
    (measurableSet_eq_fun (measurable_snd.comp measurable_fst) measurable_const).compl.union
      (measurableSet_le measurable_snd.abs
        ((measurable_spectralRadius (fun z : FieldSpectralData (n+1) × ℝ => z.1.1)
          (measurable_fst.comp measurable_fst)).div_const 2))
  have hB (data : FieldSpectralData (n+1)) (U : Orthogonal (n+1)) :
      Q (data,dataPhysicalPressure data U) := by
    by_cases hc : data.2=(fun _ => 0)
    · right
      dsimp only [dataPhysicalPressure]
      rw [hc]
      have hh := abs_rotatedPressure_sub_le (Nat.succ_pos n) data.1 (fun _ => 0)
        (matrixRotation U⁻¹) (fun _ => 0) (spectralRadius data.1)
        (fun i => by simpa only [sub_zero] using abs_le_spectralRadius data.1 i)
      simpa only [rotatedPressure_constant (Nat.succ_pos n),zero_div,sub_zero] using hh
    · exact Or.inl hc
  have hh := hlaw.ae_property (Nat.succ_pos n) P _ Y (heig.prodMk measurable_const)
    hY H Q hQ hB
  simpa only [Q,ne_eq,not_true_eq_false,false_or] using hh

theorem random_pressure_uniformIntegrable_of_spectralRadius
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (eig : (N : ℕ) → Ω → Fin N → ℝ) (Y : ℕ → Ω → ℝ)
    (heig : ∀ N, Measurable (eig N)) (hY : ∀ N, Measurable (Y N))
    (H : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (H N)]
    (hlaw : ∀ N, ConditionalFieldOrbitLaw P (fun ω => (eig N ω,fun _ => 0)) (Y N) (H N))
    (hUI : UniformIntegrable (fun k ω => spectralRadius (eig (k+1) ω)) 1 P) :
    UniformIntegrable (fun k => Y (k+1)) 1 P := by
  apply uniformIntegrable_of_abs_le P _ _ (fun k => (hY (k+1)).aestronglyMeasurable) hUI
  intro k
  filter_upwards [(hlaw (k+1)).zero_field_bound P (eig (k+1)) (Y (k+1))
    (heig (k+1)) (hY (k+1)) (H (k+1))] with ω hω
  have hR : 0 ≤ spectralRadius (eig (k+1) ω) :=
    (abs_nonneg (eig (k+1) ω 0)).trans (abs_le_spectralRadius (eig (k+1) ω) 0)
  exact hω.trans ((half_le_self hR).trans (le_abs_self _))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianPatternZeroOrbit
attribute [-instance] _root_.OAI.InvariantIsing.orthogonalGaussianHaar_probability _root_.OAI.InvariantIsing.orthogonalGaussianHaar_rightInvariant _root_.OAI.InvariantIsing.orthogonalGaussianLeftHaar_leftInvariant _root_.OAI.InvariantIsing.orthogonalGaussianLeftHaar_probability _root_.OAI.InvariantIsing.squareFrameLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The empty spin space has constant zero pressure. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace InvariantIsing

lemma conditionalFieldOrbitLaw_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (d : Ω → FieldSpectralData 0)
    (H : Measure (Orthogonal 0)) [IsProbabilityMeasure H] :
    ConditionalFieldOrbitLaw P d (fun _ => 0) H := by
  let d0 : FieldSpectralData 0 := (fun _ => 0,fun _ => 0)
  have hd (ω : Ω) : d ω=d0 := Subsingleton.elim _ _
  have hp (z : FieldSpectralData 0 × Orthogonal 0) : dataPhysicalPressure z.1 z.2=0 := by
    simp [dataPhysicalPressure,rotatedPressure]
  unfold ConditionalFieldOrbitLaw
  rw [show d=(fun _ => d0) from funext hd]
  simp only [hp]
  show Measure.map (fun ω => (d0, (0 : ℝ))) P = Measure.map (fun z => (z.1, (0 : ℝ))) ((Measure.map (fun x => d0) P).prod H)
  simp only [Measure.map_const,measure_univ,one_smul,Measure.dirac_prod]
  rw [Measure.map_map (measurable_fst.prodMk measurable_const) measurable_prodMk_left]
  simp [Function.comp_def,Measure.map_const]

lemma gaussianPattern_conditionalOrbit_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {m : ℕ}
    (Z : Ω → EuclideanSpace ℝ (Fin 0 × Fin m)) (c : ℝ)
    (H : Measure (Orthogonal 0)) [IsProbabilityMeasure H] :
    ConditionalFieldOrbitLaw P
      (fun ω => (fun i => c*gaussianPatternEigenvalues (Z ω) i,fun _ => 0))
      (fun ω => gaussianPatternPressure c (Z ω)) H := by
  have hY : (fun ω => gaussianPatternPressure c (Z ω))=(fun _ : Ω => 0) := by
    funext ω
    simp [gaussianPatternPressure]
  rw [hY]
  exact conditionalFieldOrbitLaw_zero P _ H

lemma gaussianPattern_conditionalOrbit_all {Ω : Type*} [MeasurableSpace Ω]
    {N m : ℕ} (c : ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → EuclideanSpace ℝ (Fin N × Fin m)) (hZ : Measurable Z)
    (hlaw : HasLaw Z (stdGaussian _) P)
    (heig : Measurable (gaussianPatternEigenvalues (N := N) (m := m)))
    (H : Measure (Orthogonal N)) [IsProbabilityMeasure H] [H.IsMulRightInvariant] :
    ConditionalFieldOrbitLaw P
      (fun ω => ((fun i => c*gaussianPatternEigenvalues (Z ω) i),fun _ => 0))
      (fun ω => gaussianPatternPressure c (Z ω)) H := by
  cases N with
  | zero => exact gaussianPattern_conditionalOrbit_zero P Z c H
  | succ n => exact gaussianPattern_conditionalOrbit_hasLaw (Nat.succ_pos n) c P Z hZ hlaw heig H

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianPatternPressureLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gaussian-pattern pressure limit from Haar concentration, cascade
identities, Marchenko–Pastur convergence, and spectral edge estimates. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
universe u
namespace InvariantIsing

theorem gaussianPattern_pressure_uniformIntegrable
    (α : ℝ) (hα : 0 < α) (hmp : MarchenkoPasturInput.{u} α hα)
    (hds : DavidsonSzarekInput.{u} α hα)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, Measurable (Z N)) (hlaw : ∀ N, HasLaw (Z N) (stdGaussian _) P)
    (c : ℝ) : UniformIntegrable (fun k ω => gaussianPatternPressure (N := k+1) (m := gaussianPatternCount α (k+1)) c (Z (k+1) ω)) 1 P := by
  let : ∀ N, IsProbabilityMeasure (orthogonalGaussianHaar N) :=
    fun N => orthogonalGaussianHaar_probability N
  let : ∀ N, (orthogonalGaussianHaar N).IsMulRightInvariant :=
    fun N => orthogonalGaussianHaar_rightInvariant N
  let eig := fun (N : ℕ) (ω : Ω) (i : Fin N) => c*gaussianPatternEigenvalues (N := N) (m := gaussianPatternCount α N) (Z N ω) i
  let Y := fun (N : ℕ) (ω : Ω) => gaussianPatternPressure (N := N) (m := gaussianPatternCount α N) c (Z N ω)
  have heig (N : ℕ) : Measurable (eig N) := by
    exact measurable_pi_iff.mpr fun i =>
      (((measurable_pi_apply i).comp (hmp.measurable_eigenvalues N)).comp (hZ N)).const_mul c
  have hY (N : ℕ) : Measurable (Y N) :=
    (measurable_gaussianPatternPressure N _ c).comp (hZ N)
  have horbit (N : ℕ) : ConditionalFieldOrbitLaw P
      (fun ω => (eig N ω,fun _ => 0)) (Y N) (orthogonalGaussianHaar N) := by
    exact gaussianPattern_conditionalOrbit_all c P (Z N) (hZ N) (hlaw N)
      (hmp.measurable_eigenvalues N) _
  have hspec := hds.uniform_integrable P Z hlaw c
  change UniformIntegrable (fun k ω => spectralRadius (eig (k+1) ω)) 1 P at hspec
  change UniformIntegrable (fun k => Y (k+1)) 1 P
  exact random_pressure_uniformIntegrable_of_spectralRadius P eig Y heig hY
    orthogonalGaussianHaar horbit hspec

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_ThermalLimitSqueeze
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer temperatures determine a unique deterministic zero-temperature limit. -/

noncomputable section
open Filter
open scoped Topology

namespace InvariantIsing

lemma thermal_squeeze_tendsto (p : ℕ → ℕ → ℝ) (g v : ℕ → ℝ) (c L : ℝ)
    (hc : 0 ≤ c) (hv : Tendsto v atTop (𝓝 L))
    (hp : ∀ k, Tendsto (p k) atTop (𝓝 (v k)))
    (hb : ∀ k, ∀ᶠ N in atTop, p k N ≤ g N ∧ g N ≤ p k N+c/(k+1)) :
    Tendsto g atTop (𝓝 L) := by
  have hδ : Tendsto (fun k : ℕ => 2*(c/(k+1))) atTop (𝓝 0) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2*c)
    simp only [mul_zero] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext k
    ring
  apply spectral_approximation_squeeze g p p v (fun k => 2*(c/(k+1))) L hv hδ hp hp
  intro k
  filter_upwards [hb k] with N hN
  have hnonneg : 0 ≤ c/(k+1) := by positivity
  constructor <;> linarith [hN.1,hN.2]

lemma exists_thermal_ground_limit (p : ℕ → ℕ → ℝ) (g v : ℕ → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hp : ∀ k, Tendsto (p k) atTop (𝓝 (v k)))
    (hb : ∀ k, ∀ᶠ N in atTop, p k N ≤ g N ∧ g N ≤ p k N+c/(k+1)) :
    ∃ L : ℝ, Tendsto v atTop (𝓝 L) ∧ Tendsto g atTop (𝓝 L) := by
  have horder (k l : ℕ) : v k ≤ v l+c/(l+1) := by
    apply le_of_tendsto_of_tendsto (hp k) ((hp l).add_const _)
    filter_upwards [hb k,hb l] with N hk hl
    exact hk.1.trans hl.2
  have hδ : Tendsto (fun k : ℕ => c/(k+1)) atTop (𝓝 0) := by
    simpa only [mul_one_div,mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul c
  have hC : CauchySeq v := by
    apply cauchySeq_of_le_tendsto_0 (fun k : ℕ => c/(k+1)) _ hδ
    intro n m k hn hm
    have hn' : (k : ℝ)+1 ≤ (n : ℝ)+1 := by exact_mod_cast Nat.add_le_add_right hn 1
    have hm' : (k : ℝ)+1 ≤ (m : ℝ)+1 := by exact_mod_cast Nat.add_le_add_right hm 1
    have hen : c/((n : ℝ)+1) ≤ c/((k : ℝ)+1) :=
      div_le_div_of_nonneg_left hc (by positivity) hn'
    have hem : c/((m : ℝ)+1) ≤ c/((k : ℝ)+1) :=
      div_le_div_of_nonneg_left hc (by positivity) hm'
    rw [Real.dist_eq,abs_le]
    constructor <;> linarith [horder n m,horder m n]
  obtain ⟨L,hL⟩ := cauchySeq_tendsto_of_complete hC
  exact ⟨L,hL,thermal_squeeze_tendsto p g v c L hc hL hp hb⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_RandomThermalSqueeze
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A soft-maximum squeeze for convergence in probability. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace InvariantIsing

lemma tendstoInMeasure_continuous_comp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (X : ℕ → Ω → ℝ) (L : ℝ)
    (hX : ∀ n, Measurable (X n)) (h : TendstoInMeasure P X atTop (fun _ => L))
    (f : ℝ → ℝ) (hf : Continuous f) :
    TendstoInMeasure P (fun n ω => f (X n ω)) atTop (fun _ => f L) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff
    (fun n => (hf.measurable.comp (hX n)).aestronglyMeasurable)).mpr
  intro ns hns
  obtain ⟨u,hu,he⟩ := (h.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨u,hu,he.mono fun ω hω => (hf.tendsto L).comp hω⟩

lemma thermal_squeeze_in_measure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → ℕ → Ω → ℝ) (G : ℕ → Ω → ℝ)
    (v : ℕ → ℝ) (L c : ℝ) (hc : 0 ≤ c)
    (hv : Tendsto v atTop (𝓝 L))
    (hp : ∀ k, TendstoInMeasure P (X k) atTop (fun _ => v k))
    (hb : ∀ k n ω, X k n ω ≤ G n ω ∧ G n ω ≤ X k n ω+c/(k+1)) :
    TendstoInMeasure P G atTop (fun _ => L) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hd : Tendsto (fun k : ℕ => c/(k+1)) atTop (𝓝 0) := by
    simpa only [mul_one_div,mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul c
  have hvd : Tendsto (fun k => |v k-L|+c/(k+1)) atTop (𝓝 0) := by
    simpa using ((hv.sub_const L).abs.add hd)
  obtain ⟨k,hk⟩ := (hvd.eventually (gt_mem_nhds (half_pos hε))).exists
  have hprob := (tendstoInMeasure_iff_norm.mp (hp k)) (ε/2) (half_pos hε)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hprob
    (Filter.Eventually.of_forall fun _ => bot_le)
    (Filter.Eventually.of_forall fun n => measure_mono ?_)
  intro ω hω
  simp only [mem_ofPred_eq,Real.norm_eq_abs] at hω ⊢
  by_contra! hbad
  have hB := hb k n ω
  have hc' : 0 ≤ c/(k+1) := by positivity
  have hG : |G n ω-L| ≤ |X k n ω-v k|+|v k-L|+c/(k+1) := by
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (X k n ω-v k),le_abs_self (X k n ω-v k),
      neg_abs_le (v k-L),le_abs_self (v k-L)]
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_RandomGroundLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A zero-temperature limit from fixed-temperature random pressures. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace InvariantIsing

theorem random_ground_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ → ℕ → Ω → ℝ) (G : ℕ → Ω → ℝ) (A : ℝ → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hG : UniformIntegrable G 1 P)
    (hpm : ∀ β n, Measurable (p β n))
    (hpi : ∀ β, 0 < β → ∀ n, Integrable (p β n) P)
    (hp : ∀ β, 0 < β → TendstoInMeasure P (p β) atTop (fun _ => A β))
    (hpmean : ∀ β, 0 < β → Tendsto (fun n => ∫ ω, p β n ω ∂P) atTop (𝓝 (A β)))
    (hb : ∀ β, 0 < β → ∀ n ω, p β n ω/β ≤ G n ω ∧ G n ω ≤ p β n ω/β+c/β) :
    ∃ L : ℝ, TendstoInMeasure P G atTop (fun _ => L) ∧
      Tendsto (fun n => eLpNorm (fun ω => G n ω-L) 1 P) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ ω, G n ω ∂P) atTop (𝓝 L) ∧
      Tendsto (fun β => A β/β) atTop (𝓝 L) := by
  let g := fun n => ∫ ω, G n ω ∂P
  let q := fun (k n : ℕ) => (∫ ω, p ((k : ℝ)+1) n ω ∂P)/((k : ℝ)+1)
  let v := fun k : ℕ => A ((k : ℝ)+1)/((k : ℝ)+1)
  have hg (n : ℕ) : Integrable (G n) P := memLp_one_iff_integrable.mp (hG.memLp n)
  have hmean (β : ℝ) (hβ : 0 < β) (n : ℕ) :
      (∫ ω, p β n ω ∂P)/β ≤ g n ∧ g n ≤ (∫ ω, p β n ω ∂P)/β+c/β := by
    have hpi' := (hpi β hβ n).div_const β
    have hl := integral_mono hpi' (hg n) (fun ω => (hb β hβ n ω).1)
    have hu := integral_mono (hg n) (hpi'.add (integrable_const (c/β)))
      (fun ω => (hb β hβ n ω).2)
    rw [integral_div] at hl
    simp only [Pi.add_apply] at hu
    rw [integral_add hpi' (integrable_const _),integral_div,integral_const,
      probReal_univ,one_smul] at hu
    exact ⟨hl,hu⟩
  obtain ⟨L,hv,hglim⟩ := exists_thermal_ground_limit q g v c hc
    (fun k => (hpmean ((k : ℝ)+1) (by positivity)).div_const _)
    (fun k => Filter.Eventually.of_forall (hmean ((k : ℝ)+1) (by positivity)))
  have hprob : TendstoInMeasure P G atTop (fun _ => L) := by
    apply thermal_squeeze_in_measure P (fun k n ω => p ((k : ℝ)+1) n ω/((k : ℝ)+1))
      G v L c hc hv
    · intro k
      exact tendstoInMeasure_continuous_comp P _ _ (hpm _) (hp _ (by positivity))
        (fun x => x/((k : ℝ)+1)) (continuous_id.div_const _)
    · intro k n ω
      exact hb ((k : ℝ)+1) (by positivity) n ω
  have hL1 := pressure_L1_of_probability_and_uniformIntegrability P G L hG hprob
  refine ⟨L,hprob,hL1.1,hL1.2,?_⟩
  have hbounds (β : ℝ) (hβ : 0 < β) : A β/β ≤ L ∧ L ≤ A β/β+c/β := by
    have ht := (hpmean β hβ).div_const β
    exact ⟨le_of_tendsto_of_tendsto ht hglim
        (Filter.Eventually.of_forall fun n => (hmean β hβ n).1),
      le_of_tendsto_of_tendsto hglim (ht.add_const _)
        (Filter.Eventually.of_forall fun n => (hmean β hβ n).2)⟩
  apply tendsto_sub_nhds_zero_iff.mp
  apply squeeze_zero_norm' _ (tendsto_id.const_div_atTop c)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
  rw [Real.norm_eq_abs,abs_le]
  simp only [id_eq]
  have hh := hbounds β hβ
  constructor <;> linarith [hh.1,hh.2,div_nonneg hc hβ.le]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianPatternGroundLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subsequent zero-temperature limits for both signs of the Gaussian energy. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
universe u
namespace InvariantIsing

lemma gaussianPattern_ground_uniformIntegrable
    (α : ℝ) (hα : 0 < α) (hds : DavidsonSzarekInput.{u} α hα)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, Measurable (Z N)) (hlaw : ∀ N, HasLaw (Z N) (stdGaussian _) P)
    (ε : ℝ) : UniformIntegrable (fun k ω => gaussianPatternGroundEnergy ε (Z (k+1) ω)) 1 P := by
  apply uniformIntegrable_of_abs_le P _ _
    (fun k => ((measurable_gaussianPatternGroundEnergy _ _ ε).comp (hZ (k+1))).aestronglyMeasurable)
    (hds.uniform_integrable P Z hlaw ε)
  intro k
  filter_upwards [] with ω
  have hr : 0 ≤ spectralRadius (fun i => ε*gaussianPatternEigenvalues (Z (k+1) ω) i) :=
    (abs_nonneg (ε*gaussianPatternEigenvalues (Z (k+1) ω) 0)).trans (abs_le_spectralRadius (fun i => ε*gaussianPatternEigenvalues (Z (k+1) ω) i) 0)
  exact (abs_gaussianPatternGroundEnergy_le ε _).trans ((half_le_self hr).trans (le_abs_self _))

theorem gaussianPattern_ground_limit_oai
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    (α : ℝ) (hα : 0 < α) (hmp : MarchenkoPasturInput.{u} α hα)
    (hds : DavidsonSzarekInput.{u} α hα)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, Measurable (Z N)) (hlaw : ∀ N, HasLaw (Z N) (stdGaussian _) P)
    (ε : ℝ) :
    ∃ e : ℝ,
      TendstoInMeasure P (fun k ω => gaussianPatternGroundEnergy ε (Z (k+1) ω)) atTop (fun _ => e) ∧
      Tendsto (fun k => eLpNorm (fun ω => gaussianPatternGroundEnergy ε (Z (k+1) ω)-e) 1 P)
        atTop (𝓝 0) ∧
      Tendsto (fun k => ∫ ω, gaussianPatternGroundEnergy ε (Z (k+1) ω) ∂P) atTop (𝓝 e) ∧
      Tendsto (fun β => gaussianPatternLimit α (ε*β)/β) atTop (𝓝 e) := by
  apply random_ground_limit P
    (fun β k ω => gaussianPatternPressure (ε*β) (Z (k+1) ω))
    (fun k ω => gaussianPatternGroundEnergy ε (Z (k+1) ω))
    (fun β => gaussianPatternLimit α (ε*β)) (Real.log 2)
    (Real.log_pos (by norm_num : (1 : ℝ)<2)).le
    (gaussianPattern_ground_uniformIntegrable α hα hds P Z hZ hlaw ε)
  · intro β k
    exact (measurable_gaussianPatternPressure _ _ _).comp (hZ (k+1))
  · intro β _ k
    exact memLp_one_iff_integrable.mp
      ((gaussianPattern_pressure_uniformIntegrable α hα hmp hds P Z hZ hlaw (ε*β)).memLp k)
  · intro β _
    exact (gaussianPattern_pressure_limit hhaar hgauss hpub α hα hmp hds P Z hZ hlaw (ε*β)).1
  · intro β _
    exact (gaussianPattern_pressure_limit hhaar hgauss hpub α hα hmp hds P Z hZ hlaw (ε*β)).2.2
  · intro β hβ k ω
    exact gaussianPatternGroundEnergy_squeeze (Nat.succ_pos k) ε β hβ _

end InvariantIsing

end

end OAI
end

theorem solution.{u} : type_of% @OAI.InvariantIsing.gaussianPattern_ground_limit_oai.{u} := @OAI.InvariantIsing.gaussianPattern_ground_limit_oai.{u}
