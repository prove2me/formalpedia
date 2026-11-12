-- Prove2me | solution 1 for OAI.InvariantIsing.cavity_labeled_projector_joint_integral
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:24:03.098785+00:00
-- url     : https://prove2.me/submissions/2f3bf5d6-b3b7-4f36-aa84-d538dd198466

import Mathlib
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.StrongLaw
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003
import Theorems.Thm_OAI_InvariantIsing_cavity_labeled_projector_joint_law

section
-- module Solutions.OAIQ258_II.Compat
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFrameMeasurable
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCouplingAlgebra
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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

lemma measurable_cavityEigenspaceFrame (r m n : ℕ) :
    Measurable (cavityEigenspaceFrame :
      (Fin m → Matrix (Fin r) (Fin n) ℝ) → Matrix (Fin r) (Fin (m * n)) ℝ) := by
  apply Measurable.of_eval_matrix
  intro i j
  exact ((measurable_cavityNormalizeFrame r n).comp
    (measurable_pi_apply (finProdFinEquiv.symm j).1)).eval_matrix

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpectralImages
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPhysicalBase
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBaseHaarFactorization
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCompressionBlocks
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityConcreteComplement
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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

lemma measurable_cavityConcreteComplement {m n d : ℕ}
    (e : Fin (m * n) ≃ Fin (d + n)) (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ) :
    Measurable (cavityConcreteComplement e B₀) := by
  have h := (measurable_cavitySelectedComplement B₀).comp (measurable_cavityReindexedStack e)
  apply Measurable.of_eval_matrix
  intro i j
  exact h.eval_matrix

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityConcreteFrameOrbit
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLabeledProjectors
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectorHaarMean
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectorJointLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact joint law of physical compression matrices and base
projectors.  This also transports measurable logarithmic observables. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_labeled_projector_joint_integral_oai {N n m d : ℕ}
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
    (hf : Measurable f) :
    (∫ U, f (cavityCompressionGrams g U,
      cavityPhysicalLabeledProjectors g (cavityConcreteComplement es B₀) a₀ U) ∂μ) =
    ∫ p, f (cavityCompressionGrams g p.1,
      cavityLabeledProjectorAction p.2 (cavityCanonicalProjectorFrame k e a₀)) ∂μ.prod ν := by
  have hF := (measurable_cavityCompressionGrams g).prodMk
    (measurable_cavityPhysicalLabeledProjectors g _ (measurable_cavityConcreteComplement es B₀) a₀)
  have hG := ((measurable_cavityCompressionGrams g).comp measurable_fst).prodMk
    ((measurable_cavityCanonicalProjectorAction k e a₀).comp measurable_snd)
  simp only [Function.comp_def] at hG
  rw [← integral_map hF.aemeasurable hf.aestronglyMeasurable,
    cavity_labeled_projector_joint_law g k ek e es B₀ a₀ l u hg hln hu μ ν,
    integral_map hG.aemeasurable hf.aestronglyMeasurable]

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.cavity_labeled_projector_joint_integral_oai := @OAI.InvariantIsing.cavity_labeled_projector_joint_integral_oai
