-- Prove2me | solution 1 for OAI.ContinuumCoulomb.SourceUnitCoulomb.promise_of_hubbard_interval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:50:31.509143+00:00
-- url     : https://prove2.me/submissions/a72f3a2d-590e-413d-976c-e1e5c85b141a

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_OAIQ092A010
import Theorems.Thm_OAI_ContinuumCoulomb_SourceUnitCoulomb_actual_threshold_error

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_Spin
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The two-spin Heisenberg interaction

The basis order is `↑↑, ↑↓, ↓↑, ↓↓`.  The matrix below is
`X ⊗ X + Y ⊗ Y + Z ⊗ Z = 2 SWAP - I` in that basis.
The exact singlet/triplet computation supplies the interaction bound
used when rounding or deleting source coefficients in both continuum
Coulomb manuscripts (their sections on rational source normalization).
-/

namespace ContinuumCoulomb

open Matrix Complex
open scoped BigOperators

theorem heisenberg_eq_pauli :
    heisenberg = twoSpinTensor pauliX pauliX +
      twoSpinTensor pauliY pauliY + twoSpinTensor pauliZ pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [heisenberg, twoSpinTensor, pauliX, pauliY, pauliZ]

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceHamiltonian
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_coordinate _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_edges _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_lower _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_upper _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_vertices _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.contactEdge_left _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.contactEdge_right _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Signed square-lattice Heisenberg source

The finite source is the field-free Heisenberg problem of
Cubitt–Montanaro–Piddock, *Universal quantum Hamiltonians*,
arXiv:1701.05182v4, Theorem 48, Lemma 47 and Section 10.1.
The coordinate-swap action realizes `2 SWAP - I`. Coefficient-rounding
estimates hold for arbitrary many-spin states, including entangled states.
-/

noncomputable section

namespace ContinuumCoulomb

open scoped BigOperators

theorem sourceSpinSwap_apply {n : ℕ} (i j : Fin n)
    (s : SourceSpinBasis n) (k : Fin n) :
    sourceSpinSwap i j s k = s (Equiv.swap i j k) := by
  simp [sourceSpinSwap, Equiv.arrowCongr_apply]

/-- Real quadratic form of the explicitly defined complete Hamiltonian. -/
theorem sourceHamiltonianForm_eq_expectation (d : SquareLatticeHeisenberg)
    (u : SourceSpinVector d.vertices) :
    sourceHamiltonianForm d u =
      (∑ s, star (u s) * sourceHamiltonian d u s).re := by
  unfold sourceHamiltonian sourceHamiltonianForm sourceHeisenbergForm
  simp only [Finset.mul_sum, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro e _
  simp [Complex.mul_re, Complex.star_def]
  ring

/-- Rounding arbitrary signed coefficients incurs the sum of the local
`3|ΔJ|` errors, for the actual complete many-spin state. -/
theorem sourceHamiltonianForm_rounding
    (d : SquareLatticeHeisenberg) (rounded : Fin d.edges → ℝ)
    (u : SourceSpinVector d.vertices) (hu : sourceSpinMass u = 1) :
    |sourceHamiltonianForm d u -
      ∑ e, rounded e * sourceHeisenbergForm (d.left e) (d.right e) u| ≤
      3 * ∑ e, |(d.coefficient e : ℝ) - rounded e| := by
  unfold sourceHamiltonianForm
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ e, ((d.coefficient e : ℝ) * sourceHeisenbergForm (d.left e) (d.right e) u -
        rounded e * sourceHeisenbergForm (d.left e) (d.right e) u)| ≤
        ∑ e, |(d.coefficient e : ℝ) * sourceHeisenbergForm (d.left e) (d.right e) u -
          rounded e * sourceHeisenbergForm (d.left e) (d.right e) u| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e, 3 * |(d.coefficient e : ℝ) - rounded e| := by
      apply Finset.sum_le_sum
      intro e _
      rw [← sub_mul, abs_mul]
      have h := sourceHeisenbergForm_abs_le (d.left e) (d.right e) u
      rw [hu, mul_one] at h
      nlinarith [abs_nonneg ((d.coefficient e : ℝ) - rounded e)]
    _ = 3 * ∑ e, |(d.coefficient e : ℝ) - rounded e| := (Finset.mul_sum _ _ _).symm

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_DiagonalPenalty
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The concrete inverse of a charge-sector penalty

The high block of the Hubbard penalty is diagonal in the occupation basis.
That block and its inverse are continuous linear maps satisfying the
positivity, symmetry and inverse-norm hypotheses of the second-order
perturbation theorem.
-/

noncomputable section
open scoped BigOperators InnerProductSpace
namespace ContinuumCoulomb

variable {Basis : Type*} [Fintype Basis]

theorem diagonalPenalty_form (weight : Basis → ℝ) (x : EuclideanSpace ℂ Basis) :
    ⟪x, diagonalPenalty weight x⟫_ℝ = ∑ s, weight s * ‖x s‖ ^ 2 := by
  simp only [PiLp.inner_apply, diagonalPenalty_apply,
    real_inner_smul_right, real_inner_self_eq_norm_sq]

theorem diagonalPenalty_symmetric (weight : Basis → ℝ)
    (x y : EuclideanSpace ℂ Basis) :
    ⟪x, diagonalPenalty weight y⟫_ℝ = ⟪diagonalPenalty weight x, y⟫_ℝ := by
  simp only [PiLp.inner_apply, diagonalPenalty_apply,
    real_inner_smul_right, real_inner_smul_left]

theorem diagonalPenalty_gap (weight : Basis → ℝ) (g : ℝ)
    (hgap : ∀ s, g ≤ weight s) (x : EuclideanSpace ℂ Basis) :
    g * ‖x‖ ^ 2 ≤ ⟪x, diagonalPenalty weight x⟫_ℝ := by
  rw [diagonalPenalty_form, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right (hgap s) (sq_nonneg _)

theorem diagonalPenalty_norm_le (weight : Basis → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hweight : ∀ s, |weight s| ≤ C) :
    ‖diagonalPenalty weight‖ ≤ C := by
  apply (diagonalPenalty weight).opNorm_le_bound hC
  intro x
  have hsq : ‖diagonalPenalty weight x‖ ^ 2 ≤ (C * ‖x‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s _
    have hw : weight s ^ 2 ≤ C ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).2 (hweight s)
    simpa only [diagonalPenalty_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] using
      mul_le_mul_of_nonneg_right hw (sq_nonneg ‖x s‖)
  have hn := norm_nonneg (diagonalPenalty weight x)
  have hcx : 0 ≤ C * ‖x‖ := mul_nonneg hC (norm_nonneg _)
  nlinarith

theorem diagonalPenalty_inverse_right (weight : Basis → ℝ)
    (hweight : ∀ s, weight s ≠ 0) (x : EuclideanSpace ℂ Basis) :
    diagonalPenalty weight (diagonalPenalty (fun s => (weight s)⁻¹) x) = x := by
  ext s
  simp [hweight s]

theorem diagonalPenalty_inverse_norm {g : ℝ} (hg : 0 < g) (weight : Basis → ℝ)
    (hgap : ∀ s, g ≤ weight s) :
    ‖diagonalPenalty (fun s => (weight s)⁻¹)‖ ≤ 1 / g := by
  apply diagonalPenalty_norm_le _ (by positivity)
  intro s
  have hw : 0 < weight s := hg.trans_le (hgap s)
  rw [abs_of_pos (inv_pos.mpr hw)]
  simpa only [one_div] using one_div_le_one_div_of_le hg (hgap s)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_Perturbation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Second-order block estimates

The finite reductions use the bottom-energy estimate from the binary
manuscript's `lem:second-order` and the unit manuscript's `lem:perturbation`.
Explicit positivity and operator norm bounds give vector and variational
estimates for the penalty, inverse, coupling and high perturbation blocks.

Real inner products also express the real quadratic forms of complex spin
Hilbert spaces by restriction of scalars.
-/

noncomputable section

open scoped InnerProductSpace

namespace ContinuumCoulomb
namespace Perturbation

variable {L H : Type*}
variable [NormedAddCommGroup L] [InnerProductSpace ℝ L]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem inverseForm_nonneg (A T : H →L[ℝ] H) (B : L →L[ℝ] H)
    (hAT : ∀ x, A (T x) = x) (hA : ∀ q, 0 ≤ penaltyForm A q) (p : L) :
    0 ≤ inverseForm T B p := by
  have h := hA (T (B p))
  simpa only [penaltyForm, hAT, real_inner_comm, inverseForm] using h

/-- The precise square-completion identity, before any estimates. -/
theorem penalty_square_identity (A T : H →L[ℝ] H) (B : L →L[ℝ] H)
    (hAT : ∀ x, A (T x) = x)
    (hAsymm : ∀ x y, ⟪x, A y⟫_ℝ = ⟪A x, y⟫_ℝ)
    (p : L) (q : H) {σ : ℝ} (hσ : σ ≠ 0) :
    σ * penaltyForm A q + 2 * ⟪q, B p⟫_ℝ =
      σ * penaltyForm A (q + σ⁻¹ • T (B p)) - σ⁻¹ * inverseForm T B p := by
  have hcross : ⟪T (B p), A q⟫_ℝ = ⟪q, B p⟫_ℝ := by
    rw [hAsymm, hAT, real_inner_comm]
  simp only [penaltyForm, inverseForm, map_add, map_smul, inner_add_left,
    inner_add_right, real_inner_smul_left, real_inner_smul_right, hAT, hcross]
  rw [real_inner_comm (T (B p)) (B p)]
  field_simp
  ring

/-- The trial vector used in the second-order variational upper bound. -/
theorem blockEnergy_trial_identity (A T D : H →L[ℝ] H) (B : L →L[ℝ] H)
    (hAT : ∀ x, A (T x) = x) (p : L) :
    blockEnergy A D B p (-(T (B p))) =
      -inverseForm T B p + ⟪-(T (B p)), D (-(T (B p)))⟫_ℝ := by
  simp only [blockEnergy, penaltyForm, inverseForm, map_neg, hAT,
    inner_neg_left, inner_neg_right]
  rw [real_inner_comm (T (B p)) (B p)]
  ring

theorem inverse_coupling_norm_le (T : H →L[ℝ] H) (B : L →L[ℝ] H)
    {g ε : ℝ} (hg : 0 < g) (_hε : 0 ≤ ε)
    (hT : ‖T‖ ≤ 1 / g) (hB : ‖B‖ ≤ ε * g) (p : L) :
    ‖T (B p)‖ ≤ ε * ‖p‖ := by
  have hBp : ‖B p‖ ≤ ε * g * ‖p‖ :=
    (B.le_opNorm p).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  calc
    ‖T (B p)‖ ≤ ‖T‖ * ‖B p‖ := T.le_opNorm _
    _ ≤ (1 / g) * (ε * g * ‖p‖) := by
      exact mul_le_mul hT hBp (norm_nonneg _) (by positivity)
    _ = ε * ‖p‖ := by field_simp

theorem inverseForm_le (T : H →L[ℝ] H) (B : L →L[ℝ] H)
    {g ε : ℝ} (hg : 0 < g) (hε : 0 ≤ ε)
    (hT : ‖T‖ ≤ 1 / g) (hB : ‖B‖ ≤ ε * g) (p : L) :
    inverseForm T B p ≤ g * ε ^ 2 * ‖p‖ ^ 2 := by
  have hBp : ‖B p‖ ≤ ε * g * ‖p‖ :=
    (B.le_opNorm p).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  have hTBp := inverse_coupling_norm_le T B hg hε hT hB p
  calc
    inverseForm T B p ≤ ‖B p‖ * ‖T (B p)‖ := real_inner_le_norm _ _
    _ ≤ (ε * g * ‖p‖) * (ε * ‖p‖) :=
      mul_le_mul hBp hTBp (norm_nonneg _) (by positivity)
    _ = g * ε ^ 2 * ‖p‖ ^ 2 := by ring

theorem highPerturbation_abs_le (D : H →L[ℝ] H)
    {g ε : ℝ} (hD : ‖D‖ ≤ ε * g) (q : H) :
    |⟪q, D q⟫_ℝ| ≤ ε * g * ‖q‖ ^ 2 := by
  calc
    |⟪q, D q⟫_ℝ| ≤ ‖q‖ * ‖D q‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖q‖ * (ε * g * ‖q‖) := by
      exact mul_le_mul_of_nonneg_left
        ((D.le_opNorm q).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _)))
        (norm_nonneg _)
    _ = ε * g * ‖q‖ ^ 2 := by ring

theorem effectiveForm_smul (C : L →L[ℝ] L) (T : H →L[ℝ] H)
    (B : L →L[ℝ] H) (r : ℝ) (p : L) :
    effectiveForm C T B (r • p) = r ^ 2 * effectiveForm C T B p := by
  simp only [effectiveForm, inverseForm, map_smul, real_inner_smul_left,
    real_inner_smul_right]
  ring

/-- Finite dimensionality supplies the effective ground vector; this
is not an additional simulation assumption. -/
theorem effectiveForm_minimizer [FiniteDimensional ℝ L]
    (C : L →L[ℝ] L) (T : H →L[ℝ] H) (B : L →L[ℝ] H)
    (u : L) (hu : ‖u‖ = 1) :
    ∃ p : L, ‖p‖ = 1 ∧
      ∀ x : L, effectiveForm C T B p * ‖x‖ ^ 2 ≤ effectiveForm C T B x := by
  have := FiniteDimensional.proper_rclike ℝ L
  have hc : Continuous (effectiveForm C T B) :=
    (continuous_id.inner C.continuous).sub
      (B.continuous.inner (T.continuous.comp B.continuous))
  have hnonempty : (Metric.sphere (0 : L) 1).Nonempty := ⟨u, by simpa using hu⟩
  obtain ⟨p, hp, hmin⟩ :=
    (isCompact_sphere (0 : L) 1).exists_isMinOn hnonempty hc.continuousOn
  refine ⟨p, by simpa using hp, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp [hx, effectiveForm, inverseForm]
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hunit : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := norm_smul_inv_norm hx
  have h := hmin (show (‖x‖⁻¹ : ℝ) • x ∈ Metric.sphere (0 : L) 1 by simpa using hunit)
  change effectiveForm C T B p ≤ effectiveForm C T B ((‖x‖⁻¹ : ℝ) • x) at h
  rw [effectiveForm_smul] at h
  calc
    effectiveForm C T B p * ‖x‖ ^ 2 ≤
        (‖x‖⁻¹ ^ 2 * effectiveForm C T B x) * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right h (sq_nonneg _)
    _ = effectiveForm C T B x := by field_simp

theorem effectiveBottom_eq (C : L →L[ℝ] L) (T : H →L[ℝ] H) (B : L →L[ℝ] H)
    (p : L) (hp : ‖p‖ = 1)
    (hmin : ∀ x : L, effectiveForm C T B p * ‖x‖ ^ 2 ≤ effectiveForm C T B x) :
    effectiveBottom C T B = effectiveForm C T B p := by
  have hlower (e : ℝ) (he : ∃ x : L, ‖x‖ = 1 ∧ e = effectiveForm C T B x) :
      effectiveForm C T B p ≤ e := by
    obtain ⟨x, hx, rfl⟩ := he
    simpa only [hx, one_pow, mul_one] using hmin x
  exact le_antisymm (csInf_le ⟨_, hlower⟩ ⟨p, hp, rfl⟩)
    (le_csInf ⟨_, p, hp, rfl⟩ hlower)

theorem effectiveForm_bounds (C : L →L[ℝ] L) (A T : H →L[ℝ] H)
    (B : L →L[ℝ] H) {g ε : ℝ} (hg : 0 < g) (hε : 0 ≤ ε)
    (hAT : ∀ x, A (T x) = x) (hA : ∀ q, 0 ≤ penaltyForm A q)
    (hT : ‖T‖ ≤ 1 / g) (hB : ‖B‖ ≤ ε * g) (hC : ‖C‖ ≤ ε * g)
    (p : L) :
    -(ε * g + g * ε ^ 2) * ‖p‖ ^ 2 ≤ effectiveForm C T B p ∧
      effectiveForm C T B p ≤ ε * g * ‖p‖ ^ 2 := by
  have hCp := abs_le.mp (highPerturbation_abs_le C hC p)
  have hK0 := inverseForm_nonneg A T B hAT hA p
  have hK := inverseForm_le T B hg hε hT hB p
  unfold effectiveForm
  constructor <;> nlinarith

theorem first_order_inverse_cubic_loss {g ε k r : ℝ}
    (hg : 0 < g) (hε : 0 ≤ ε) (hεquarter : ε ≤ 1 / 4)
    (hr : 0 ≤ r) (hk : k ≤ g * ε ^ 2 * r) :
    -4 * g * ε ^ 3 * r ≤ k - (1 - 2 * ε)⁻¹ * k := by
  have hσ : 0 < 1 - 2 * ε := by linarith
  have hid : k - (1 - 2 * ε)⁻¹ * k = (-2 * ε * k) / (1 - 2 * ε) := by
    field_simp
    ring
  rw [hid]
  apply (le_div_iff₀ hσ).mpr
  have h := mul_le_mul_of_nonneg_left hk hε
  have hsmall : 0 ≤ g * ε ^ 3 * r * (1 - 4 * ε) :=
    mul_nonneg (by positivity) (by linarith)
  nlinarith

/-- A shifted square gives the lower bound even when the first-order
compression is nonzero.  The effective form is only assumed bounded
below pointwise; the full-energy conclusion is proved here. -/
theorem lowBlockEnergy_shift_lower (C : L →L[ℝ] L) (A T D : H →L[ℝ] H)
    (B : L →L[ℝ] H) {g ε μ : ℝ}
    (hg : 0 < g) (hε : 0 ≤ ε) (hεquarter : ε ≤ 1 / 4)
    (hAT : ∀ x, A (T x) = x)
    (hAsymm : ∀ x y, ⟪x, A y⟫_ℝ = ⟪A x, y⟫_ℝ)
    (hA : ∀ q, 0 ≤ penaltyForm A q)
    (hgap : ∀ q, g * ‖q‖ ^ 2 ≤ penaltyForm A q)
    (hT : ‖T‖ ≤ 1 / g) (hB : ‖B‖ ≤ ε * g) (hD : ‖D‖ ≤ ε * g)
    (hμupper : μ ≤ ε * g)
    (hmin : ∀ p, μ * ‖p‖ ^ 2 ≤ effectiveForm C T B p)
    (p : L) (q : H) :
    -4 * g * ε ^ 3 * ‖p‖ ^ 2 ≤
      lowBlockEnergy C A D B p q - μ * (‖p‖ ^ 2 + ‖q‖ ^ 2) := by
  have hσ : 0 < 1 - 2 * ε := by linarith
  have hid := penalty_square_identity A T B hAT hAsymm p q (ne_of_gt hσ)
  have hsquare := mul_nonneg (le_of_lt hσ) (hA (q + (1 - 2 * ε)⁻¹ • T (B p)))
  have hDq := (abs_le.mp (highPerturbation_abs_le D hD q)).1
  have hμq := mul_le_mul_of_nonneg_right hμupper (sq_nonneg ‖q‖)
  have hgap' := mul_le_mul_of_nonneg_left (hgap q) (show 0 ≤ 2 * ε by positivity)
  have hminp := hmin p
  have hK := inverseForm_le T B hg hε hT hB p
  have hloss := first_order_inverse_cubic_loss hg hε hεquarter (sq_nonneg ‖p‖) hK
  unfold effectiveForm at hminp
  unfold lowBlockEnergy blockEnergy
  nlinarith

theorem lowBlockRayleigh_lower (C : L →L[ℝ] L) (A T D : H →L[ℝ] H)
    (B : L →L[ℝ] H) {g ε μ : ℝ}
    (hg : 0 < g) (hε : 0 ≤ ε) (hεquarter : ε ≤ 1 / 4)
    (hAT : ∀ x, A (T x) = x)
    (hAsymm : ∀ x y, ⟪x, A y⟫_ℝ = ⟪A x, y⟫_ℝ)
    (hA : ∀ q, 0 ≤ penaltyForm A q)
    (hgap : ∀ q, g * ‖q‖ ^ 2 ≤ penaltyForm A q)
    (hT : ‖T‖ ≤ 1 / g) (hB : ‖B‖ ≤ ε * g) (hD : ‖D‖ ≤ ε * g)
    (hμupper : μ ≤ ε * g)
    (hmin : ∀ p, μ * ‖p‖ ^ 2 ≤ effectiveForm C T B p)
    (p : L) (q : H) (hnorm : 0 < ‖p‖ ^ 2 + ‖q‖ ^ 2) :
    μ - 4 * g * ε ^ 3 ≤ lowBlockRayleigh C A D B p q := by
  have hlower := lowBlockEnergy_shift_lower C A T D B hg hε hεquarter hAT hAsymm
    hA hgap hT hB hD hμupper hmin p q
  have hcost : 0 ≤ 4 * g * ε ^ 3 * ‖q‖ ^ 2 := by positivity
  unfold lowBlockRayleigh
  apply (le_div_iff₀ hnorm).mpr
  nlinarith

/-- The same inverse-coupling trial vector works with the unreplaced
low-block terms retained. -/
theorem lowBlockRayleigh_trial_upper (C : L →L[ℝ] L) (A T D : H →L[ℝ] H)
    (B : L →L[ℝ] H) {g ε μ : ℝ}
    (hg : 0 < g) (hε : 0 ≤ ε)
    (hAT : ∀ x, A (T x) = x)
    (hT : ‖T‖ ≤ 1 / g) (hB : ‖B‖ ≤ ε * g) (hD : ‖D‖ ≤ ε * g)
    (hμlower : -2 * ε * g ≤ μ)
    (p : L) (hp : ‖p‖ = 1) (hattain : effectiveForm C T B p = μ) :
    lowBlockRayleigh C A D B p (-(T (B p))) ≤ μ + 3 * g * ε ^ 3 := by
  have hnorm : ‖-(T (B p))‖ ≤ ε := by
    simpa only [norm_neg, hp, mul_one] using inverse_coupling_norm_le T B hg hε hT hB p
  have hr : ‖-(T (B p))‖ ^ 2 ≤ ε ^ 2 := by nlinarith [norm_nonneg (-(T (B p)))]
  have hr0 : 0 ≤ ‖-(T (B p))‖ ^ 2 := sq_nonneg _
  have hd := (abs_le.mp (highPerturbation_abs_le D hD (-(T (B p))))).2
  have hμr := mul_le_mul_of_nonneg_right hμlower hr0
  have hr' := mul_le_mul_of_nonneg_left hr (show 0 ≤ 3 * ε * g by positivity)
  have hden : 0 < 1 + ‖-(T (B p))‖ ^ 2 := by positivity
  have hcost : 0 ≤ 3 * g * ε ^ 3 * ‖-(T (B p))‖ ^ 2 := by positivity
  unfold lowBlockRayleigh lowBlockEnergy
  rw [blockEnergy_trial_identity A T D B hAT p, hp, one_pow]
  unfold effectiveForm at hattain
  apply (div_le_iff₀ hden).mpr
  nlinarith

/-- Quantitative version of the unit manuscript's `lem:perturbation`,
retaining the nonzero first-order compression.  `μ` is the attained
variational minimum of `C - B* T B`; the full variational bottom is
proved within `4 g ε³` of it. -/
theorem lowBlockBottom_second_order (C : L →L[ℝ] L) (A T D : H →L[ℝ] H)
    (B : L →L[ℝ] H) {g ε μ : ℝ}
    (hg : 0 < g) (hε : 0 ≤ ε) (hεquarter : ε ≤ 1 / 4)
    (hAT : ∀ x, A (T x) = x)
    (hAsymm : ∀ x y, ⟪x, A y⟫_ℝ = ⟪A x, y⟫_ℝ)
    (hA : ∀ q, 0 ≤ penaltyForm A q)
    (hgap : ∀ q, g * ‖q‖ ^ 2 ≤ penaltyForm A q)
    (hT : ‖T‖ ≤ 1 / g) (hB : ‖B‖ ≤ ε * g)
    (hC : ‖C‖ ≤ ε * g) (hD : ‖D‖ ≤ ε * g)
    (hmin : ∀ p, μ * ‖p‖ ^ 2 ≤ effectiveForm C T B p)
    (p₀ : L) (hp₀ : ‖p₀‖ = 1) (hattain : effectiveForm C T B p₀ = μ) :
    |lowBlockBottom C A D B - μ| ≤ 4 * g * ε ^ 3 := by
  have hbounds := effectiveForm_bounds C A T B hg hε hAT hA hT hB hC p₀
  simp only [hattain, hp₀, one_pow, mul_one] at hbounds
  have hμupper : μ ≤ ε * g := hbounds.2
  have hμlower : -2 * ε * g ≤ μ := by
    have hsmall : 0 ≤ g * ε * (1 - ε) :=
      mul_nonneg (by positivity) (by linarith)
    nlinarith [hbounds.1]
  have hnorm : 0 < ‖p₀‖ ^ 2 + ‖-(T (B p₀))‖ ^ 2 := by rw [hp₀]; positivity
  have hnonempty :
      {e | ∃ (p : L) (q : H), 0 < ‖p‖ ^ 2 + ‖q‖ ^ 2 ∧
        e = lowBlockRayleigh C A D B p q}.Nonempty :=
    ⟨_, p₀, -(T (B p₀)), hnorm, rfl⟩
  have hlower (e : ℝ)
      (he : ∃ (p : L) (q : H), 0 < ‖p‖ ^ 2 + ‖q‖ ^ 2 ∧
        e = lowBlockRayleigh C A D B p q) : μ - 4 * g * ε ^ 3 ≤ e := by
    obtain ⟨p, q, hpq, rfl⟩ := he
    exact lowBlockRayleigh_lower C A T D B hg hε hεquarter hAT hAsymm hA hgap
      hT hB hD hμupper hmin p q hpq
  have hbdd : BddBelow
      {e | ∃ (p : L) (q : H), 0 < ‖p‖ ^ 2 + ‖q‖ ^ 2 ∧
        e = lowBlockRayleigh C A D B p q} := ⟨_, hlower⟩
  have hbottomLower : μ - 4 * g * ε ^ 3 ≤ lowBlockBottom C A D B :=
    le_csInf hnonempty hlower
  have hbottomUpper : lowBlockBottom C A D B ≤ μ + 3 * g * ε ^ 3 :=
    (csInf_le hbdd ⟨p₀, -(T (B p₀)), hnorm, rfl⟩).trans
      (lowBlockRayleigh_trial_upper C A T D B hg hε hAT hT hB hD hμlower p₀ hp₀ hattain)
  apply abs_le.mpr
  constructor <;> nlinarith [show 0 ≤ g * ε ^ 3 by positivity]

/-- The finite-dimensional, nonzero-low-block perturbation estimate
compares the two actual variational infima. -/
theorem finite_lowBlockBottom_second_order [FiniteDimensional ℝ L]
    (C : L →L[ℝ] L) (A T D : H →L[ℝ] H) (B : L →L[ℝ] H)
    {g ε : ℝ} (hg : 0 < g) (hε : 0 ≤ ε) (hεquarter : ε ≤ 1 / 4)
    (hAT : ∀ x, A (T x) = x)
    (hAsymm : ∀ x y, ⟪x, A y⟫_ℝ = ⟪A x, y⟫_ℝ)
    (hA : ∀ q, 0 ≤ penaltyForm A q)
    (hgap : ∀ q, g * ‖q‖ ^ 2 ≤ penaltyForm A q)
    (hT : ‖T‖ ≤ 1 / g) (hB : ‖B‖ ≤ ε * g)
    (hC : ‖C‖ ≤ ε * g) (hD : ‖D‖ ≤ ε * g)
    (u : L) (hu : ‖u‖ = 1) :
    |lowBlockBottom C A D B - effectiveBottom C T B| ≤ 4 * g * ε ^ 3 := by
  obtain ⟨p, hp, hmin⟩ := effectiveForm_minimizer C T B u hu
  rw [effectiveBottom_eq C T B p hp hmin]
  exact lowBlockBottom_second_order C A T D B hg hε hεquarter hAT hAsymm hA hgap
    hT hB hC hD hmin p hp rfl

end Perturbation
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FockBlocks
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete hopping blocks on the actual half-filled Fock basis. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators InnerProductSpace

section Coordinates
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem coordinateInclusion_single [DecidableEq α] [DecidableEq β] (f : α → β) (a : α) :
    coordinateInclusion f (EuclideanSpace.single a (1 : ℂ)) =
      EuclideanSpace.single (f a) (1 : ℂ) := by
  classical
  simp [coordinateInclusion, coordinateInclusionLinear, PiLp.single_apply]
  ext b
  simp [PiLp.single_apply]

theorem coordinateInclusion_norm_le (f : α → β) (hf : Function.Injective f) :
    ‖coordinateInclusion f‖ ≤ 1 := by
  apply (coordinateInclusion f).opNorm_le_bound zero_le_one
  intro x
  rw [coordinateInclusion_norm_map f hf, one_mul]

@[simp] theorem coordinateRestriction_apply (f : α → β)
    (x : EuclideanSpace ℂ β) (a : α) : coordinateRestriction f x a = x (f a) := by
  classical
  have h := ContinuousLinearMap.adjoint_inner_right (coordinateInclusion f)
    (EuclideanSpace.single a (1 : ℂ)) x
  rw [coordinateInclusion_single, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_left] at h
  simpa only [coordinateRestriction, map_one, one_mul] using h

theorem coordinateRestriction_norm_le (f : α → β) (hf : Function.Injective f) :
    ‖coordinateRestriction f‖ ≤ 1 := by
  change ‖(coordinateInclusion f).adjoint‖ ≤ 1
  rw [LinearIsometryEquiv.norm_map]
  exact coordinateInclusion_norm_le f hf

theorem coordinateCompression_norm (R : EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ γ)
    (T : EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ β)
    (I : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ β)
    (hR : ‖R‖ ≤ 1) (hI : ‖I‖ ≤ 1) : ‖R.comp (T.comp I)‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖R‖ * ‖T.comp I‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (‖T‖ * 1) := mul_le_mul hR
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left hI (norm_nonneg _))) (norm_nonneg _) zero_le_one
    _ = _ := by ring

end Coordinates

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_Singlet
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact singlet mediator calculations

The positive-spin conversion uses the singlet mediator of Piddock–Montanaro,
*The complexity of antiferromagnetic interactions and 2D lattices*, Quantum
Information and Computation 17 (2017), Section 2.4 and Lemma 5.
The Pauli contractions and penalty identities use an unnormalized singlet
vector, whose expectation values are twice the normalized values.
-/

noncomputable section

namespace ContinuumCoulomb

open Matrix
open scoped BigOperators

theorem singlet_first_pauli (μ : Fin 3) :
    singletMatrixElement (firstPauli μ) = 0 := by
  fin_cases μ <;>
    norm_num [singletMatrixElement, firstPauli, pauli, twoSpinTensor,
      pauliX, pauliY, pauliZ, spinSinglet, Matrix.mulVec,
      dotProduct, Matrix.one_apply, Fin.sum_univ_succ]

theorem singlet_second_pauli (μ : Fin 3) :
    singletMatrixElement (secondPauli μ) = 0 := by
  fin_cases μ <;>
    norm_num [singletMatrixElement, secondPauli, pauli, twoSpinTensor,
      pauliX, pauliY, pauliZ, spinSinglet, Matrix.mulVec,
      dotProduct, Matrix.one_apply, Fin.sum_univ_succ]

/-- Same-member singlet contraction: normalized value `δμν`. -/
theorem singlet_first_first (μ ν : Fin 3) :
    singletMatrixElement (firstPauli μ * firstPauli ν) =
      if μ = ν then 2 else 0 := by
  fin_cases μ <;> fin_cases ν <;>
    norm_num [singletMatrixElement, firstPauli, pauli, twoSpinTensor,
      pauliX, pauliY, pauliZ, spinSinglet, Matrix.mulVec, Matrix.mul_apply,
      dotProduct, Matrix.one_apply, Fin.sum_univ_succ]

/-- Same-member singlet contraction on the other mediator. -/
theorem singlet_second_second (μ ν : Fin 3) :
    singletMatrixElement (secondPauli μ * secondPauli ν) =
      if μ = ν then 2 else 0 := by
  fin_cases μ <;> fin_cases ν <;>
    norm_num [singletMatrixElement, secondPauli, pauli, twoSpinTensor,
      pauliX, pauliY, pauliZ, spinSinglet, Matrix.mulVec, Matrix.mul_apply,
      dotProduct, Matrix.one_apply, Fin.sum_univ_succ]

/-- Opposite-member singlet contraction: normalized value `-δμν`. -/
theorem singlet_first_second (μ ν : Fin 3) :
    singletMatrixElement (firstPauli μ * secondPauli ν) =
      if μ = ν then -2 else 0 := by
  fin_cases μ <;> fin_cases ν <;>
    norm_num [singletMatrixElement, firstPauli, secondPauli, pauli, twoSpinTensor,
      pauliX, pauliY, pauliZ, spinSinglet, Matrix.mulVec, Matrix.mul_apply,
      dotProduct, Matrix.one_apply, Fin.sum_univ_succ]

theorem singlet_second_first (μ ν : Fin 3) :
    singletMatrixElement (secondPauli μ * firstPauli ν) =
      if μ = ν then -2 else 0 := by
  fin_cases μ <;> fin_cases ν <;>
    norm_num [singletMatrixElement, firstPauli, secondPauli, pauli, twoSpinTensor,
      pauliX, pauliY, pauliZ, spinSinglet, Matrix.mulVec, Matrix.mul_apply,
      dotProduct, Matrix.one_apply, Fin.sum_univ_succ]

theorem firstPauli_sq (μ : Fin 3) : firstPauli μ * firstPauli μ = 1 := by
  fin_cases μ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [firstPauli, pauli, twoSpinTensor, pauliX, pauliY, pauliZ,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

theorem secondPauli_sq (μ : Fin 3) : secondPauli μ * secondPauli μ = 1 := by
  fin_cases μ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [secondPauli, pauli, twoSpinTensor, pauliX, pauliY, pauliZ,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

theorem first_second_pauli (μ : Fin 3) :
    firstPauli μ * secondPauli μ = twoSpinTensor (pauli μ) (pauli μ) := by
  fin_cases μ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [firstPauli, secondPauli, pauli, twoSpinTensor, pauliX, pauliY, pauliZ,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

theorem sum_first_second_pauli :
    (∑ μ : Fin 3, firstPauli μ * secondPauli μ) = heisenberg := by
  simp_rw [first_second_pauli]
  rw [heisenberg_eq_pauli]
  simp [pauli, Fin.sum_univ_succ, add_assoc]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_GlobalSinglet
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.value_sqrtHalf _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical singlet/triplet coordinates for simultaneous fresh mediator pairs. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace

theorem bellRaw_gram : bellRaw.conjTranspose * bellRaw = (2 : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bellRaw, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      Matrix.one_apply]

theorem bellRaw_cogram : bellRaw * bellRaw.conjTranspose = (2 : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bellRaw, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      Matrix.one_apply]

theorem bellScale_twice_sq : bellScale * (bellScale * 2) = 1 := by
  calc
    _ = 2 * bellScale ^ 2 := by ring
    _ = 1 := by rw [bellScale_sq]; norm_num

theorem bellMatrix_gram : bellMatrix.conjTranspose * bellMatrix = 1 := by
  simp only [bellMatrix, Matrix.conjTranspose_smul, bellScale_star,
    smul_mul_assoc, mul_smul_comm, bellRaw_gram, smul_smul, bellScale_twice_sq, one_smul]

theorem bellMatrix_cogram : bellMatrix * bellMatrix.conjTranspose = 1 := by
  simp only [bellMatrix, Matrix.conjTranspose_smul, bellScale_star,
    smul_mul_assoc, mul_smul_comm, bellRaw_cogram, smul_smul, bellScale_twice_sq, one_smul]

theorem bellMatrix_singlet (i : Fin 4) : bellMatrix i 0 = bellScale * spinSinglet i := by
  fin_cases i <;> simp [bellMatrix, bellRaw, spinSinglet]

theorem bellRaw_heisenberg : heisenberg * bellRaw =
    bellRaw * Matrix.diagonal (fun a : Fin 4 => if a = 0 then (-3 : ℂ) else 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bellRaw, heisenberg, Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_succ]

theorem bellMatrix_heisenberg : heisenberg * bellMatrix =
    bellMatrix * Matrix.diagonal (fun a : Fin 4 => if a = 0 then (-3 : ℂ) else 1) := by
  simp only [bellMatrix, mul_smul_comm, smul_mul_assoc, bellRaw_heisenberg]

theorem bellTransform_mul (M N : Matrix (Fin 4) (Fin 4) ℂ) :
    bellTransform M * bellTransform N = bellTransform (M * N) := by
  unfold bellTransform
  calc
    _ = bellMatrix.conjTranspose * M * (bellMatrix * bellMatrix.conjTranspose) * N * bellMatrix := by
      simp only [mul_assoc]
    _ = _ := by rw [bellMatrix_cogram]; simp only [mul_one, mul_assoc]

/-- The transformed zero coordinate is the actual normalized singlet
matrix element, including the normalization factor one half. -/
theorem bellTransform_zero_zero (M : Matrix (Fin 4) (Fin 4) ℂ) :
    bellTransform M 0 0 = (1 / 2 : ℂ) * singletMatrixElement M := by
  unfold bellTransform
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, bellMatrix_singlet,
    star_mul, bellScale_star, Finset.sum_mul]
  have hpoint (i j : Fin 4) :
      star (spinSinglet i) * bellScale * M i j * (bellScale * spinSinglet j) =
        bellScale ^ 2 * (star (spinSinglet i) * M i j * spinSinglet j) := by ring
  simp_rw [hpoint, bellScale_sq]
  unfold singletMatrixElement
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

theorem bell_first_pauli_zero (μ : Fin 3) : bellTransform (firstPauli μ) 0 0 = 0 := by
  rw [bellTransform_zero_zero, singlet_first_pauli, mul_zero]

theorem bell_second_pauli_zero (μ : Fin 3) : bellTransform (secondPauli μ) 0 0 = 0 := by
  rw [bellTransform_zero_zero, singlet_second_pauli, mul_zero]

theorem bell_first_first_zero (μ ν : Fin 3) :
    (bellTransform (firstPauli μ) * bellTransform (firstPauli ν)) 0 0 =
      if μ = ν then 1 else 0 := by
  rw [bellTransform_mul, bellTransform_zero_zero, singlet_first_first]
  split_ifs <;> norm_num

theorem bell_first_second_zero (μ ν : Fin 3) :
    (bellTransform (firstPauli μ) * bellTransform (secondPauli ν)) 0 0 =
      if μ = ν then -1 else 0 := by
  rw [bellTransform_mul, bellTransform_zero_zero, singlet_first_second]
  split_ifs <;> norm_num

theorem bell_column_inner (a b : Fin 4) :
    (∑ s, star (bellMatrix s a) * bellMatrix s b) = if a = b then 1 else 0 := by
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M a b) bellMatrix_gram
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h

theorem bell_row_inner (a b : Fin 4) :
    (∑ s, bellMatrix a s * star (bellMatrix b s)) = if a = b then 1 else 0 := by
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M a b) bellMatrix_cogram
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h

theorem product_delta (r : ℕ) (a b : MediatorBasis r) :
    (∏ e, if a e = b e then (1 : ℂ) else 0) = if a = b then 1 else 0 := by
  classical
  by_cases hab : a = b
  · subst b
    simp
  · obtain ⟨e, he⟩ := Function.ne_iff.mp hab
    rw [ite_eq_right hab]
    exact Finset.prod_eq_zero (Finset.mem_univ e) (by simp [he])

/-- The tensor product of all local Bell changes of coordinates is
unitary for every number of simultaneous mediators. -/
theorem globalBellMatrix_gram (r : ℕ) :
    (globalBellMatrix r).conjTranspose * globalBellMatrix r = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, globalBellMatrix,
    star_prod, ← Finset.prod_mul_distrib, Matrix.one_apply]
  rw [← Fintype.prod_sum (fun e s => star (bellMatrix s (a e)) * bellMatrix s (b e))]
  simp_rw [bell_column_inner]
  exact product_delta r a b

theorem globalBellMatrix_cogram (r : ℕ) :
    globalBellMatrix r * (globalBellMatrix r).conjTranspose = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, globalBellMatrix,
    star_prod, ← Finset.prod_mul_distrib, Matrix.one_apply]
  rw [← Fintype.prod_sum (fun e s => bellMatrix (a e) s * star (bellMatrix (b e) s))]
  simp_rw [bell_row_inner]
  exact product_delta r a b

theorem mediatorExcitationNumber_pos (r : ℕ) (a : MediatorBasis r)
    (ha : a ≠ mediatorVacuum r) : 1 ≤ mediatorExcitationNumber r a := by
  obtain ⟨e, he⟩ := Function.ne_iff.mp ha
  exact Finset.card_pos.mpr ⟨e, by simpa [mediatorVacuum] using he⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_SuperexchangeSpectrum
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact spectral identification of the global Hubbard inverse term. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators InnerProductSpace
variable {Edge : Type*} [Fintype Edge]

theorem graphSourceForm_expectation (m : ℕ)
    (left right : Edge → Fin (m + 1)) (J : Edge → ℝ)
    (u : SourceSpinVector (m + 1)) :
    graphSourceForm m left right J u =
      (∑ s, star (u s) * graphSourceAction m left right (fun e => (J e : ℂ)) u s).re := by
  have hpoint (e : Edge) (s : SourceSpinBasis (m + 1)) :
      (star (u s) * ((J e : ℂ) *
        (sourceHeisenbergAction (left e) (right e) u s - u s))).re =
      J e * ((star (u s) * sourceHeisenbergAction (left e) (right e) u s).re -
        Complex.normSq (u s)) := by
    simp [Complex.mul_re, Complex.normSq_apply]
    ring
  simp only [graphSourceForm, graphSourceAction, Finset.mul_sum, Complex.re_sum]
  rw [Finset.sum_comm]
  simp_rw [hpoint]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  rfl

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HubbardFermionSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete half-filled Fock variational problem has the concrete block form. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators InnerProductSpace

theorem euclidean_real_inner {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℂ ι) :
    ⟪x, y⟫_ℝ = (⟪x, y⟫_ℂ).re := by
  simp only [PiLp.inner_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro s _
  rfl

theorem coordinateInclusion_real_inner {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (x : EuclideanSpace ℂ α) (y : EuclideanSpace ℂ β) :
    ⟪coordinateInclusion f x, y⟫_ℝ = ⟪x, coordinateRestriction f y⟫_ℝ := by
  rw [euclidean_real_inner, euclidean_real_inner]
  exact congrArg Complex.re (ContinuousLinearMap.adjoint_inner_right (coordinateInclusion f) x y).symm

theorem coordinateRestriction_inclusion {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (hf : Function.Injective f) (x : EuclideanSpace ℂ α) :
    coordinateRestriction f (coordinateInclusion f x) = x := by
  ext a
  rw [coordinateRestriction_apply, coordinateInclusion_apply_image f hf]

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorCompression
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact simultaneous singlet-penalty diagonalization and inverse compression.
All tensor matrices here act on the complete mediator configuration basis. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators

theorem mediatorTensor_one (r : ℕ) : mediatorTensor r (fun _ => 1) = 1 := by
  ext a b
  simpa only [mediatorTensor, Matrix.one_apply] using product_delta r a b

theorem mediatorTensor_mul (r : ℕ) (M N : Fin r → Matrix (Fin 4) (Fin 4) ℂ) :
    mediatorTensor r M * mediatorTensor r N = mediatorTensor r (fun e => M e * N e) := by
  ext a b
  simp only [Matrix.mul_apply, mediatorTensor, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun e s => M e (a e) s * N e s (b e))).symm

theorem mediatorTensor_star (r : ℕ) (M : Fin r → Matrix (Fin 4) (Fin 4) ℂ) :
    (mediatorTensor r M).conjTranspose = mediatorTensor r (fun e => (M e).conjTranspose) := by
  ext a b
  simp only [mediatorTensor, Matrix.conjTranspose_apply, star_prod]

theorem mediatorTensor_diagonal (r : ℕ) (d : Fin r → Fin 4 → ℂ) :
    mediatorTensor r (fun e => Matrix.diagonal (d e)) =
      Matrix.diagonal (fun a => ∏ e, d e (a e)) := by
  classical
  ext a b
  by_cases hab : a = b
  · subst b
    simp [mediatorTensor]
  · obtain ⟨e, he⟩ := Function.ne_iff.mp hab
    simp only [Matrix.diagonal_apply, ite_eq_right hab, mediatorTensor]
    exact Finset.prod_eq_zero (Finset.mem_univ e) (by simp [he])

theorem mediatorLocal_apply (r : ℕ) (e : Fin r) (M : Matrix (Fin 4) (Fin 4) ℂ)
    (a b : MediatorBasis r) :
    mediatorLocal r e M a b = M (a e) (b e) *
      ∏ f ∈ Finset.univ.erase e, if a f = b f then (1 : ℂ) else 0 := by
  classical
  unfold mediatorLocal mediatorTensor
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ e)]
  simp only
  congr 1
  apply Finset.prod_congr rfl
  intro f hf
  simp only [ite_eq_right (Finset.mem_erase.mp hf).1, Matrix.one_apply]

theorem mediatorLocal_vacuum (r : ℕ) (e : Fin r) (M : Matrix (Fin 4) (Fin 4) ℂ) :
    mediatorLocal r e M (mediatorVacuum r) (mediatorVacuum r) = M 0 0 := by
  simp [mediatorLocal_apply, mediatorVacuum]

theorem mediatorLocal_mul_same (r : ℕ) (e : Fin r)
    (M N : Matrix (Fin 4) (Fin 4) ℂ) :
    mediatorLocal r e M * mediatorLocal r e N = mediatorLocal r e (M * N) := by
  unfold mediatorLocal
  rw [mediatorTensor_mul]
  congr 1
  funext f
  by_cases h : f = e <;> simp [h]

theorem mediatorLocal_diagonal (r : ℕ) (e : Fin r) (d : Fin 4 → ℂ) :
    mediatorLocal r e (Matrix.diagonal d) = Matrix.diagonal (fun a => d (a e)) := by
  classical
  have h (f : Fin r) :
      (if f = e then Matrix.diagonal d else (1 : Matrix (Fin 4) (Fin 4) ℂ)) =
        Matrix.diagonal (fun s => if f = e then d s else 1) := by
    by_cases hf : f = e <;> simp [hf]
  unfold mediatorLocal
  simp_rw [h]
  rw [mediatorTensor_diagonal]
  congr 1
  funext a
  exact Fintype.prod_ite_eq' e (fun f => d (a f))

/-- Conjugating the actual physical one-pair operator by the global Bell
basis gives exactly the same local operator in Bell coordinates. -/
theorem mediatorLocal_bellTransform (r : ℕ) (e : Fin r)
    (M : Matrix (Fin 4) (Fin 4) ℂ) :
    (globalBellMatrix r).conjTranspose * mediatorLocal r e M * globalBellMatrix r =
      mediatorLocal r e (bellTransform M) := by
  change (mediatorTensor r (fun _ => bellMatrix)).conjTranspose *
    mediatorTensor r (fun f => if f = e then M else 1) *
      mediatorTensor r (fun _ => bellMatrix) = _
  rw [mediatorTensor_star, mediatorTensor_mul, mediatorTensor_mul]
  unfold mediatorLocal
  congr 1
  funext f
  by_cases hf : f = e
  · simp only [ite_eq_left hf, bellTransform]
  · simp only [ite_eq_right hf, mul_one, bellMatrix_gram]

theorem bellTransform_penalty :
    bellTransform (heisenberg + (3 : ℂ) • 1) =
      Matrix.diagonal (fun a : Fin 4 => if a = 0 then (0 : ℂ) else 4) := by
  have hH : bellTransform heisenberg =
      Matrix.diagonal (fun a : Fin 4 => if a = 0 then (-3 : ℂ) else 1) := by
    unfold bellTransform
    rw [mul_assoc, bellMatrix_heisenberg, ← mul_assoc, bellMatrix_gram, one_mul]
  have hsum : bellTransform (heisenberg + (3 : ℂ) • 1) =
      bellTransform heisenberg + (3 : ℂ) • 1 := by
    unfold bellTransform
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one,
      bellMatrix_gram]
  rw [hsum, hH]
  ext a b
  by_cases hab : a = b
  · subst b
    by_cases ha : a = 0 <;> norm_num [ha]
  · simp [hab]

theorem mediatorExcitationNumber_sum (r : ℕ) (a : MediatorBasis r) :
    (∑ e : Fin r, if a e = 0 then (0 : ℂ) else 1) =
      (mediatorExcitationNumber r a : ℂ) := by
  classical
  simp [mediatorExcitationNumber, Finset.card_filter]

/-- Exact diagonalization of the entire simultaneous central Hamiltonian. -/
theorem physicalMediatorPenalty_diagonal (r : ℕ) (Delta : ℝ) :
    (globalBellMatrix r).conjTranspose * physicalMediatorPenalty r Delta * globalBellMatrix r =
      Matrix.diagonal (fun a => (mediatorPenaltyWeight r Delta a : ℂ)) := by
  unfold physicalMediatorPenalty
  simp only [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  simp_rw [mediatorLocal_bellTransform, bellTransform_penalty, mediatorLocal_diagonal]
  ext a b
  by_cases hab : a = b
  · subst b
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply, Matrix.diagonal_apply, ite_true, if_true]
    have hsum : (∑ e : Fin r, if a e = 0 then (0 : ℂ) else 4) =
        4 * (mediatorExcitationNumber r a : ℂ) := by
      rw [← mediatorExcitationNumber_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> ring
    rw [hsum]
    unfold mediatorPenaltyWeight
    push_cast
    ring
  · simp [Matrix.sum_apply, hab]

theorem mediatorLocal_column_support (r : ℕ) (e : Fin r)
    (N : Matrix (Fin 4) (Fin 4) ℂ) (a : MediatorBasis r)
    (ha : mediatorLocal r e N a (mediatorVacuum r) ≠ 0) :
    ∀ f, f ≠ e → a f = 0 := by
  classical
  intro f hf
  by_contra hzero
  apply ha
  rw [mediatorLocal_apply]
  have hz : (∏ j ∈ Finset.univ.erase e,
      if a j = mediatorVacuum r j then (1 : ℂ) else 0) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hf, Finset.mem_univ f⟩)
    simp [mediatorVacuum, hzero]
  rw [hz, mul_zero]

theorem mediatorLocal_column_excitation (r : ℕ) (e : Fin r)
    (N : Matrix (Fin 4) (Fin 4) ℂ) (hN : N 0 0 = 0) (a : MediatorBasis r)
    (ha : mediatorLocal r e N a (mediatorVacuum r) ≠ 0) :
    a ≠ mediatorVacuum r ∧ mediatorExcitationNumber r a = 1 := by
  classical
  have havac : a ≠ mediatorVacuum r := by
    intro h
    subst a
    exact ha (by rw [mediatorLocal_vacuum, hN])
  have hs := mediatorLocal_column_support r e N a ha
  have he : a e ≠ 0 := by
    intro hzero
    apply havac
    funext f
    by_cases hf : f = e
    · simpa [hf, mediatorVacuum] using hzero
    · exact hs f hf
  refine ⟨havac, ?_⟩
  have hset : Finset.univ.filter (fun f => a f ≠ 0) = {e} := by
    ext f
    by_cases hf : f = e
    · simp [hf, he]
    · simp [hf, hs f hf]
  simp only [mediatorExcitationNumber, hset, Finset.card_singleton]

/-- Every single fresh-pair excitation has the same denominator four Delta. -/
theorem mediatorInverse_local_column (r : ℕ) (Delta : ℝ) (e : Fin r)
    (N : Matrix (Fin 4) (Fin 4) ℂ) (hN : N 0 0 = 0) (a : MediatorBasis r) :
    mediatorInverseWeight r Delta a * mediatorLocal r e N a (mediatorVacuum r) =
      ((4 * Delta)⁻¹ : ℝ) * mediatorLocal r e N a (mediatorVacuum r) := by
  by_cases ha : mediatorLocal r e N a (mediatorVacuum r) = 0
  · simp only [ha, mul_zero]
  · obtain ⟨havac, hcount⟩ := mediatorLocal_column_excitation r e N hN a ha
    simp only [mediatorInverseWeight, ite_eq_right havac, mediatorPenaltyWeight,
      hcount, Nat.cast_one, mul_one]

theorem mediatorLocal_cross_vacuum (r : ℕ) (e f : Fin r) (hef : e ≠ f)
    (M N : Matrix (Fin 4) (Fin 4) ℂ) (hM : M 0 0 = 0) :
    (mediatorLocal r e M * mediatorLocal r f N)
      (mediatorVacuum r) (mediatorVacuum r) = 0 := by
  classical
  unfold mediatorLocal
  rw [mediatorTensor_mul]
  unfold mediatorTensor
  apply Finset.prod_eq_zero (Finset.mem_univ e)
  simp [hef, mediatorVacuum, hM]

/-- Exact inverse-compressed contraction. Different fresh pairs cancel;
the same pair has the actual excitation denominator four Delta. -/
theorem mediator_inverse_compression (r : ℕ) (Delta : ℝ) (e f : Fin r)
    (M N : Matrix (Fin 4) (Fin 4) ℂ) (hM : M 0 0 = 0) (hN : N 0 0 = 0) :
    (mediatorLocal r e M * mediatorInverseMatrix r Delta * mediatorLocal r f N)
      (mediatorVacuum r) (mediatorVacuum r) =
      if e = f then ((4 * Delta)⁻¹ : ℝ) * (M * N) 0 0 else 0 := by
  classical
  have hinv : (mediatorLocal r e M * mediatorInverseMatrix r Delta * mediatorLocal r f N)
      (mediatorVacuum r) (mediatorVacuum r) =
      ((4 * Delta)⁻¹ : ℝ) * (mediatorLocal r e M * mediatorLocal r f N)
        (mediatorVacuum r) (mediatorVacuum r) := by
    rw [mul_assoc]
    rw [Matrix.mul_apply]
    simp_rw [mediatorInverseMatrix, Matrix.diagonal_mul,
      mediatorInverse_local_column r Delta f N hN]
    rw [Matrix.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hinv]
  by_cases hef : e = f
  · subst f
    rw [mediatorLocal_mul_same, mediatorLocal_vacuum, ite_eq_left (Eq.refl e)]
  · rw [mediatorLocal_cross_vacuum r e f hef M N hM, mul_zero, ite_eq_right hef]


theorem bell_second_second_zero (μ ν : Fin 3) :
    (bellTransform (secondPauli μ) * bellTransform (secondPauli ν)) 0 0 =
      if μ = ν then 1 else 0 := by
  rw [bellTransform_mul, bellTransform_zero_zero, singlet_second_second]
  split_ifs <;> norm_num

theorem bell_second_first_zero (μ ν : Fin 3) :
    (bellTransform (secondPauli μ) * bellTransform (firstPauli ν)) 0 0 =
      if μ = ν then -1 else 0 := by
  rw [bellTransform_mul, bellTransform_zero_zero, singlet_second_first]
  split_ifs <;> norm_num

theorem bellMemberPauli_zero (member : Fin 2) (μ : Fin 3) :
    bellMemberPauli member μ 0 0 = 0 := by
  unfold bellMemberPauli
  split_ifs
  · exact bell_first_pauli_zero μ
  · exact bell_second_pauli_zero μ

theorem bellMemberPauli_product (member other : Fin 2) (μ ν : Fin 3) :
    (bellMemberPauli member μ * bellMemberPauli other ν) 0 0 =
      if μ = ν then (if member = other then 1 else -1) else 0 := by
  fin_cases member <;> fin_cases other <;>
    simp [bellMemberPauli, bell_first_first_zero, bell_first_second_zero,
      bell_second_first_zero, bell_second_second_zero]

/-- The exact global inverse contraction, with arbitrary spectator mediator
pairs: different pairs or Pauli axes vanish, and opposite members change sign. -/
theorem mediator_pauli_inverse_compression (r : ℕ) (Delta : ℝ) (e f : Fin r)
    (member other : Fin 2) (μ ν : Fin 3) :
    (mediatorLocal r e (bellMemberPauli member μ) * mediatorInverseMatrix r Delta *
      mediatorLocal r f (bellMemberPauli other ν)) (mediatorVacuum r) (mediatorVacuum r) =
      if e = f ∧ μ = ν then
        ((4 * Delta)⁻¹ : ℝ) * (if member = other then (1 : ℂ) else -1) else 0 := by
  rw [mediator_inverse_compression r Delta e f _ _
    (bellMemberPauli_zero member μ) (bellMemberPauli_zero other ν), bellMemberPauli_product]
  by_cases hef : e = f <;> by_cases hμν : μ = ν <;> simp [hef, hμν]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourcePauli
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual one-site Pauli matrices on the complete source spin basis. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators

theorem pauli_sq (μ : Fin 3) : pauli μ * pauli μ = 1 := by
  fin_cases μ <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [pauli, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem sourceLocalPauli_sq (n : ℕ) (i : Fin n) (μ : Fin 3) :
    sourceLocalPauli n i μ * sourceLocalPauli n i μ = 1 := by
  unfold sourceLocalPauli
  rw [sourceTensor_mul]
  have h (k : Fin n) :
      (if k = i then pauli μ else 1) * (if k = i then pauli μ else 1) = 1 := by
    by_cases hki : k = i <;> simp [hki, pauli_sq]
  simp_rw [h]
  exact sourceTensor_one n

theorem sourceLocalPauli_commute (n : ℕ) (i j : Fin n) (hij : i ≠ j) (μ ν : Fin 3) :
    sourceLocalPauli n i μ * sourceLocalPauli n j ν =
      sourceLocalPauli n j ν * sourceLocalPauli n i μ := by
  unfold sourceLocalPauli
  rw [sourceTensor_mul, sourceTensor_mul]
  congr 1
  funext k
  by_cases hki : k = i
  · subst k
    simp [hij]
  · by_cases hkj : k = j
    · subst k
      simp [hij.symm]
    · simp [hki, hkj]

/-- The Pauli contraction on two actual two-state spins. -/
theorem pauli_entry_sum (a b c d : Fin 2) :
    (∑ μ : Fin 3, pauli μ a c * pauli μ b d) =
      2 * (if a = d ∧ b = c then (1 : ℂ) else 0) -
        (if a = c ∧ b = d then 1 else 0) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [pauli, pauliX, pauliY, pauliZ, Fin.sum_univ_succ]

theorem sourceSpinSwap_eq_iff {n : ℕ} (i j : Fin n) (_hij : i ≠ j)
    (s t : SourceSpinBasis n) :
    sourceSpinSwap i j s = t ↔ s j = t i ∧ s i = t j ∧
      ∀ k, k ≠ i → k ≠ j → s k = t k := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa [sourceSpinSwap_apply] using congrFun h i
    · simpa [sourceSpinSwap_apply] using congrFun h j
    · intro k hki hkj
      simpa [sourceSpinSwap_apply, Equiv.swap_apply_of_ne_of_ne hki hkj] using congrFun h k
  · rintro ⟨hi, hj, hrest⟩
    funext k
    by_cases hki : k = i
    · subst k
      simpa [sourceSpinSwap_apply] using hi
    · by_cases hkj : k = j
      · subst k
        simpa [sourceSpinSwap_apply] using hj
      · simpa [sourceSpinSwap_apply, Equiv.swap_apply_of_ne_of_ne hki hkj] using hrest k hki hkj

/-- The Pauli sum on distinct sites equals the complete source Hamiltonian
matrix, with every other spin acting as an untouched spectator. -/
theorem sourceLocalPauli_sum (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (∑ μ : Fin 3, sourceLocalPauli n i μ * sourceLocalPauli n j μ) =
      sourceHeisenbergMatrix n i j := by
  classical
  ext s t
  rw [Matrix.sum_apply]
  simp_rw [sourceLocalPauli_product_entry n i j hij]
  rw [← Finset.sum_mul, pauli_entry_sum]
  by_cases hrest : ∀ k, k ≠ i → k ≠ j → s k = t k
  · rw [sourceSpectatorDelta_eq_one n i j s t hrest, mul_one]
    have hsame : s = t ↔ s i = t i ∧ s j = t j := by
      constructor
      · intro h
        exact ⟨congrFun h i, congrFun h j⟩
      · rintro ⟨hi, hj⟩
        funext k
        by_cases hki : k = i
        · simpa [hki] using hi
        · by_cases hkj : k = j
          · simpa [hkj] using hj
          · exact hrest k hki hkj
    have hswap : sourceSpinSwap i j s = t ↔ s i = t j ∧ s j = t i := by
      rw [sourceSpinSwap_eq_iff i j hij]
      exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, hrest⟩⟩
    change _ = 2 * (if sourceSpinSwap i j s = t then (1 : ℂ) else 0) -
      (if s = t then 1 else 0)
    simp only [hswap, hsame]
  · rw [sourceSpectatorDelta_eq_zero n i j s t hrest, mul_zero]
    have hswap : sourceSpinSwap i j s ≠ t := by
      intro h
      exact hrest ((sourceSpinSwap_eq_iff i j hij s t).mp h).2.2
    have hsame : s ≠ t := by
      intro h
      apply hrest
      intro k _ _
      exact congrFun h k
    simp [sourceHeisenbergMatrix, hswap, hsame]

/-- Matrix multiplication agrees with the swap-based Heisenberg action. -/
theorem sourceHeisenbergMatrix_mulVec (n : ℕ) (i j : Fin n) (u : SourceSpinVector n) :
    sourceHeisenbergMatrix n i j *ᵥ u = sourceHeisenbergAction i j u := by
  classical
  funext s
  simp only [sourceHeisenbergMatrix, Matrix.mulVec, dotProduct, sub_mul,
    Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, ite_mul, one_mul, zero_mul]
  simp [sourceHeisenbergAction]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorEffective
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact effective matrices for simultaneous singlet mediators, on the
complete original-spin Hilbert space. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker

theorem mediatorCompression_kronecker (n r : ℕ)
    (A : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (M : Matrix (MediatorBasis r) (MediatorBasis r) ℂ) :
    mediatorCompression n r (A ⊗ₖ M) =
      M (mediatorVacuum r) (mediatorVacuum r) • A := by
  ext s t
  change A s t * M (mediatorVacuum r) (mediatorVacuum r) =
    M (mediatorVacuum r) (mediatorVacuum r) * A s t
  ring

/-- Fresh-pair cancellation with arbitrary original-spin operators.
This is a matrix identity and therefore covers entangled original states. -/
theorem elementaryMediatorSpoke_compression (n r : ℕ) (Delta : ℝ) (e f : Fin r)
    (member other : Fin 2) (μ ν : Fin 3)
    (A B : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :
    mediatorCompression n r
      (elementaryMediatorSpoke n r e member μ A * liftedMediatorInverse n r Delta *
        elementaryMediatorSpoke n r f other ν B) =
      if e = f ∧ μ = ν then
        (((4 * Delta)⁻¹ : ℝ) * (if member = other then (1 : ℂ) else -1)) • (A * B)
      else 0 := by
  unfold elementaryMediatorSpoke liftedMediatorInverse
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, mul_one,
    mediatorCompression_kronecker, mediator_pauli_inverse_compression]
  split_ifs <;> simp

theorem mediatorEdgeSpoke_cross_compression (n r : ℕ) (Delta : ℝ)
    (e f : Fin r) (hef : e ≠ f) (i j k l : Fin n) (member other : Fin 2) :
    mediatorCompression n r
      (mediatorEdgeSpoke n r e i j member * liftedMediatorInverse n r Delta *
        mediatorEdgeSpoke n r f k l other) = 0 := by
  unfold mediatorEdgeSpoke
  simp only [Finset.sum_mul, Finset.mul_sum, add_mul, mul_add, map_sum, map_add]
  simp_rw [elementaryMediatorSpoke_compression]
  simp [hef]


theorem mediatorAxisSpoke_compression (n r : ℕ) (Delta : ℝ) (e f : Fin r)
    (i j : Fin n) (member other : Fin 2) :
    mediatorCompression n r
      (mediatorAxisSpoke n r e i member * liftedMediatorInverse n r Delta *
        mediatorAxisSpoke n r f j other) =
      if e = f then
        (((4 * Delta)⁻¹ : ℝ) * (if member = other then (1 : ℂ) else -1)) •
          ∑ μ : Fin 3, sourceLocalPauli n i μ * sourceLocalPauli n j μ
      else 0 := by
  classical
  unfold mediatorAxisSpoke
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum]
  simp_rw [elementaryMediatorSpoke_compression]
  by_cases hef : e = f
  · subst f
    simp [Finset.smul_sum]
  · simp [hef]

theorem mediatorEdgeSpoke_as_add (n r : ℕ) (e : Fin r) (i j : Fin n) (member : Fin 2) :
    mediatorEdgeSpoke n r e i j member =
      mediatorAxisSpoke n r e i 0 + mediatorAxisSpoke n r e j member := by
  unfold mediatorEdgeSpoke mediatorAxisSpoke
  rw [Finset.sum_add_distrib]

/-- Exact two-spoke self-energy, including the scalar shift six/(four Delta). -/
theorem mediatorEdgeSpoke_self_compression (n r : ℕ) (Delta : ℝ) (e : Fin r)
    (i j : Fin n) (hij : i ≠ j) (member : Fin 2) :
    mediatorCompression n r
      (mediatorEdgeSpoke n r e i j member * liftedMediatorInverse n r Delta *
        mediatorEdgeSpoke n r e i j member) =
      (((4 * Delta)⁻¹ : ℝ) : ℂ) •
        ((6 : ℂ) • 1 + (2 * mediatorMemberSign member) • sourceHeisenbergMatrix n i j) := by
  classical
  simp only [mediatorEdgeSpoke_as_add]
  simp only [add_mul, mul_add, map_add, mediatorAxisSpoke_compression, ite_true, if_true]
  have hsquare (k : Fin n) :
      (∑ μ : Fin 3, sourceLocalPauli n k μ * sourceLocalPauli n k μ) = (3 : ℂ) • 1 := by
    simp_rw [sourceLocalPauli_sq]
    ext s t
    norm_num [Matrix.sum_apply, Fin.sum_univ_succ, Matrix.one_apply]
  have hreverse : (∑ μ : Fin 3, sourceLocalPauli n j μ * sourceLocalPauli n i μ) =
      sourceHeisenbergMatrix n i j := by
    rw [← sourceLocalPauli_sum n i j hij]
    apply Finset.sum_congr rfl
    intro μ _
    exact sourceLocalPauli_commute n j i hij.symm μ μ
  rw [hsquare i, hsquare j, sourceLocalPauli_sum n i j hij, hreverse]
  have hsign : (if (0 : Fin 2) = member then (1 : ℂ) else -1) = mediatorMemberSign member := by
    simp only [mediatorMemberSign, eq_comm]
  simp only [hsign, mediatorMemberSign, mul_one]
  ext s t
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem mediatorEdgeSpoke_compression (n r : ℕ) (Delta : ℝ) (e f : Fin r)
    (left right : Fin r → Fin n) (hneq : ∀ e, left e ≠ right e) (member : Fin r → Fin 2) :
    mediatorCompression n r
      (mediatorEdgeSpoke n r e (left e) (right e) (member e) *
        liftedMediatorInverse n r Delta *
        mediatorEdgeSpoke n r f (left f) (right f) (member f)) =
      if e = f then
        (((4 * Delta)⁻¹ : ℝ) : ℂ) • ((6 : ℂ) • 1 +
          (2 * mediatorMemberSign (member e)) • sourceHeisenbergMatrix n (left e) (right e))
      else 0 := by
  classical
  by_cases hef : e = f
  · subst f
    simp only [ite_true, if_true]
    exact mediatorEdgeSpoke_self_compression n r Delta e _ _ (hneq e) _
  · rw [ite_eq_right hef]
    exact mediatorEdgeSpoke_cross_compression n r Delta e f hef _ _ _ _ _ _

/-- The simultaneous second-order matrix contains no cross-edge terms. -/
theorem totalMediatorSpokes_compression (n r : ℕ) (Delta : ℝ)
    (left right : Fin r → Fin n) (hneq : ∀ e, left e ≠ right e)
    (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    mediatorCompression n r
      (totalMediatorSpokes n r left right member amplitude * liftedMediatorInverse n r Delta *
        totalMediatorSpokes n r left right member amplitude) =
      ∑ e, ((amplitude e : ℂ) ^ 2 * ((4 * Delta)⁻¹ : ℝ)) •
        ((6 : ℂ) • 1 + (2 * mediatorMemberSign (member e)) •
          sourceHeisenbergMatrix n (left e) (right e)) := by
  classical
  unfold totalMediatorSpokes
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, map_sum, map_smul]
  simp_rw [mediatorEdgeSpoke_compression n r Delta _ _ left right hneq member]
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true, smul_smul]
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  ring

theorem signedMediatorAmplitude_nonneg (Delta J : ℝ) :
    0 ≤ signedMediatorAmplitude Delta J := Real.sqrt_nonneg _

theorem signedMediatorAmplitude_calibration {Delta : ℝ} (hDelta : 0 ≤ Delta) (J : ℝ) :
    signedMediatorAmplitude Delta J ^ 2 = 2 * Delta * |J| := by
  unfold signedMediatorAmplitude
  exact Real.sq_sqrt (by positivity)

/-- The exact manuscript calibration, with the constant self-energy retained. -/
theorem calibratedMediator_edge {Delta amplitude J : ℝ} (hDelta : 0 < Delta)
    (hcal : amplitude ^ 2 = 2 * Delta * |J|)
    {n : ℕ} (i j : Fin n) :
    ((amplitude : ℂ) ^ 2 * ((4 * Delta)⁻¹ : ℝ)) •
      ((6 : ℂ) • 1 + (2 * mediatorMemberSign (signedMediatorMember J)) •
        sourceHeisenbergMatrix n i j) =
      (3 * |J| : ℝ) • (1 : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) -
        (J : ℂ) • sourceHeisenbergMatrix n i j := by
  have hratioReal : amplitude ^ 2 * (4 * Delta)⁻¹ = |J| / 2 := by
    rw [hcal]
    field_simp [ne_of_gt hDelta]
    ring
  have hratio : (amplitude : ℂ) ^ 2 * ((4 * Delta)⁻¹ : ℝ) = (|J| / 2 : ℝ) := by
    exact_mod_cast hratioReal
  rw [hratio, smul_add, smul_smul, smul_smul]
  have hconstant : ((|J| / 2 : ℝ) : ℂ) * 6 = ((3 * |J| : ℝ) : ℂ) := by
    push_cast
    ring
  have hcoupling : ((|J| / 2 : ℝ) : ℂ) *
      (2 * mediatorMemberSign (signedMediatorMember J)) = -(J : ℂ) := by
    by_cases hJ : J < 0
    · simp only [signedMediatorMember, ite_eq_left hJ, mediatorMemberSign, ite_true, if_true,
        abs_of_neg hJ]
      push_cast
      ring
    · have hJpos : 0 ≤ J := le_of_not_gt hJ
      norm_num only [signedMediatorMember, ite_eq_right hJ, mediatorMemberSign,
        show (1 : Fin 2) ≠ 0 by decide, ite_false, abs_of_nonneg hJpos]
      push_cast
      ring
  rw [hconstant, hcoupling, neg_smul, sub_eq_add_neg]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

/-- Exact signed-source simulation at second order for all original-spin
states. Unreplaced terms survive as the explicit low block C. -/
theorem signedMediator_effective_matrix (n r : ℕ) {Delta : ℝ} (hDelta : 0 < Delta)
    (left right : Fin r → Fin n) (hneq : ∀ e, left e ≠ right e)
    (J amplitude : Fin r → ℝ) (hcal : ∀ e, amplitude e ^ 2 = 2 * Delta * |J e|)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :
    C - mediatorCompression n r
      (totalMediatorSpokes n r left right (fun e => signedMediatorMember (J e)) amplitude *
        liftedMediatorInverse n r Delta *
        totalMediatorSpokes n r left right (fun e => signedMediatorMember (J e)) amplitude) =
      C + (∑ e, (J e : ℂ) • sourceHeisenbergMatrix n (left e) (right e)) -
        (3 * ∑ e, |J e| : ℝ) • 1 := by
  rw [totalMediatorSpokes_compression n r Delta left right hneq]
  simp_rw [calibratedMediator_edge hDelta (hcal _) ]
  rw [Finset.sum_sub_distrib]
  have hconstant : (∑ e, (3 * |J e| : ℝ) •
      (1 : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)) =
      (3 * ∑ e, |J e| : ℝ) • 1 := by
    rw [← Finset.sum_smul, Finset.mul_sum]
  rw [hconstant]
  abel


theorem physicalMemberPauli_transform (member : Fin 2) (μ : Fin 3) :
    bellTransform (physicalMemberPauli member μ) = bellMemberPauli member μ := by
  unfold physicalMemberPauli bellMemberPauli
  split_ifs <;> rfl

theorem fullMediatorBellMatrix_gram (n r : ℕ) :
    (fullMediatorBellMatrix n r).conjTranspose * fullMediatorBellMatrix n r = 1 := by
  unfold fullMediatorBellMatrix
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.conjTranspose_one, one_mul, globalBellMatrix_gram,
    Matrix.one_kronecker_one]

theorem fullMediatorBellMatrix_cogram (n r : ℕ) :
    fullMediatorBellMatrix n r * (fullMediatorBellMatrix n r).conjTranspose = 1 := by
  unfold fullMediatorBellMatrix
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.conjTranspose_one, one_mul, globalBellMatrix_cogram,
    Matrix.one_kronecker_one]

/-- The elementary matrices above are precisely Bell transforms of the
physical original-spin to mediator-member Pauli interactions. -/
theorem physicalSpoke_bellTransform (n r : ℕ) (e : Fin r) (member : Fin 2) (μ : Fin 3)
    (A : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :
    (fullMediatorBellMatrix n r).conjTranspose *
      (A ⊗ₖ mediatorLocal r e (physicalMemberPauli member μ)) * fullMediatorBellMatrix n r =
      elementaryMediatorSpoke n r e member μ A := by
  unfold fullMediatorBellMatrix elementaryMediatorSpoke
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul]
  simp only [Matrix.conjTranspose_one, one_mul, mul_one, mediatorLocal_bellTransform,
    physicalMemberPauli_transform]


theorem elementaryMediatorSpoke_low_compression (n r : ℕ) (e : Fin r)
    (member : Fin 2) (μ : Fin 3)
    (A : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :
    mediatorCompression n r (elementaryMediatorSpoke n r e member μ A) = 0 := by
  unfold elementaryMediatorSpoke
  rw [mediatorCompression_kronecker, mediatorLocal_vacuum, bellMemberPauli_zero, zero_smul]

theorem totalMediatorSpokes_low_compression (n r : ℕ) (left right : Fin r → Fin n)
    (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    mediatorCompression n r (totalMediatorSpokes n r left right member amplitude) = 0 := by
  unfold totalMediatorSpokes mediatorEdgeSpoke
  simp only [map_sum, map_smul, map_add, elementaryMediatorSpoke_low_compression,
    add_zero, smul_zero, Finset.sum_const_zero]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_SpinMatrixNorm
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.ContinuumCoulomb.spinMatrixOperator_diagonal _root_.OAI.ContinuumCoulomb.spinMatrixOperator_sub _root_.OAI.ContinuumCoulomb.spinMatrixOperator_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dimension-independent operator bounds for the actual spin matrices. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem spinMatrixOperator_sum {κ : Type*} (s : Finset κ) (M : κ → Matrix ι ι ℂ) :
    spinMatrixOperator (∑ k ∈ s, M k) = ∑ k ∈ s, spinMatrixOperator (M k) := by
  unfold spinMatrixOperator
  rw [map_sum, map_sum]

theorem spinMatrixOperator_unitary_norm_map (M : Matrix ι ι ℂ)
    (hM : M.conjTranspose * M = 1) (x : EuclideanSpace ℂ ι) :
    ‖spinMatrixOperator M x‖ = ‖x‖ := by
  have hcomp : (spinMatrixOperator M).adjoint.comp (spinMatrixOperator M) = 1 := by
    rw [← spinMatrixOperator_star, ← spinMatrixOperator_mul, hM, spinMatrixOperator_one]
  have hsq : ‖spinMatrixOperator M x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right, hcomp]
    simp only [one_apply_eq_self, inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

theorem spinMatrixOperator_unitary_norm (M : Matrix ι ι ℂ)
    (hM : M.conjTranspose * M = 1) : ‖spinMatrixOperator M‖ ≤ 1 := by
  apply (spinMatrixOperator M).opNorm_le_bound zero_le_one
  intro x
  rw [spinMatrixOperator_unitary_norm_map M hM, one_mul]

/-- Actual one-site Paulis are Hermitian. -/
theorem pauli_star (μ : Fin 3) : (pauli μ).conjTranspose = pauli μ := by
  fin_cases μ <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [pauli, pauliX, pauliY, pauliZ, Matrix.conjTranspose_apply]

theorem sourceTensor_star (n : ℕ) (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    (sourceTensor n M).conjTranspose = sourceTensor n (fun i => (M i).conjTranspose) := by
  ext s t
  simp only [sourceTensor, Matrix.conjTranspose_apply, star_prod]

theorem sourceLocalPauli_star (n : ℕ) (i : Fin n) (μ : Fin 3) :
    (sourceLocalPauli n i μ).conjTranspose = sourceLocalPauli n i μ := by
  unfold sourceLocalPauli
  rw [sourceTensor_star]
  congr 1
  funext k
  by_cases hki : k = i <;> simp [hki, pauli_star]

theorem sourceLocalPauli_operator_norm (n : ℕ) (i : Fin n) (μ : Fin 3) :
    ‖spinMatrixOperator (sourceLocalPauli n i μ)‖ ≤ 1 := by
  apply spinMatrixOperator_unitary_norm
  rw [sourceLocalPauli_star, sourceLocalPauli_sq]

theorem bellTransform_star (M : Matrix (Fin 4) (Fin 4) ℂ) :
    (bellTransform M).conjTranspose = bellTransform M.conjTranspose := by
  unfold bellTransform
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, mul_assoc]

theorem bellTransform_one : bellTransform 1 = 1 := by
  simp only [bellTransform, mul_one, bellMatrix_gram]

theorem firstPauli_star (μ : Fin 3) : (firstPauli μ).conjTranspose = firstPauli μ := by
  fin_cases μ <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [firstPauli, pauli, twoSpinTensor, pauliX, pauliY, pauliZ,
      Matrix.conjTranspose_apply]

theorem secondPauli_star (μ : Fin 3) : (secondPauli μ).conjTranspose = secondPauli μ := by
  fin_cases μ <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [secondPauli, pauli, twoSpinTensor, pauliX, pauliY, pauliZ,
      Matrix.conjTranspose_apply]

theorem bellMemberPauli_star (member : Fin 2) (μ : Fin 3) :
    (bellMemberPauli member μ).conjTranspose = bellMemberPauli member μ := by
  unfold bellMemberPauli
  split_ifs <;> rw [bellTransform_star]
  · rw [firstPauli_star]
  · rw [secondPauli_star]

theorem bellMemberPauli_sq (member : Fin 2) (μ : Fin 3) :
    bellMemberPauli member μ * bellMemberPauli member μ = 1 := by
  unfold bellMemberPauli
  split_ifs <;> rw [bellTransform_mul]
  · rw [firstPauli_sq, bellTransform_one]
  · rw [secondPauli_sq, bellTransform_one]

theorem mediatorLocal_star (r : ℕ) (e : Fin r) (M : Matrix (Fin 4) (Fin 4) ℂ) :
    (mediatorLocal r e M).conjTranspose = mediatorLocal r e M.conjTranspose := by
  unfold mediatorLocal
  rw [mediatorTensor_star]
  congr 1
  funext f
  by_cases hfe : f = e <;> simp [hfe]

theorem mediatorLocal_one (r : ℕ) (e : Fin r) : mediatorLocal r e 1 = 1 := by
  unfold mediatorLocal
  simp only [ite_self]
  exact mediatorTensor_one r

theorem elementaryMediatorSpoke_star (n r : ℕ) (e : Fin r) (member : Fin 2) (μ : Fin 3)
    (i : Fin n) :
    (elementaryMediatorSpoke n r e member μ (sourceLocalPauli n i μ)).conjTranspose =
      elementaryMediatorSpoke n r e member μ (sourceLocalPauli n i μ) := by
  unfold elementaryMediatorSpoke
  rw [Matrix.conjTranspose_kronecker, sourceLocalPauli_star, mediatorLocal_star,
    bellMemberPauli_star]

theorem elementaryMediatorSpoke_sq (n r : ℕ) (e : Fin r) (member : Fin 2) (μ : Fin 3)
    (i : Fin n) :
    elementaryMediatorSpoke n r e member μ (sourceLocalPauli n i μ) *
      elementaryMediatorSpoke n r e member μ (sourceLocalPauli n i μ) = 1 := by
  unfold elementaryMediatorSpoke
  rw [← Matrix.mul_kronecker_mul, sourceLocalPauli_sq, mediatorLocal_mul_same,
    bellMemberPauli_sq, mediatorLocal_one, Matrix.one_kronecker_one]

theorem elementaryMediatorSpoke_operator_norm (n r : ℕ) (e : Fin r)
    (member : Fin 2) (μ : Fin 3) (i : Fin n) :
    ‖spinMatrixOperator (elementaryMediatorSpoke n r e member μ (sourceLocalPauli n i μ))‖ ≤ 1 := by
  apply spinMatrixOperator_unitary_norm
  rw [elementaryMediatorSpoke_star, elementaryMediatorSpoke_sq]

/-- Two three-axis spokes have norm at most six, including all spectators. -/
theorem mediatorEdgeSpoke_operator_norm (n r : ℕ) (e : Fin r) (i j : Fin n) (member : Fin 2) :
    ‖spinMatrixOperator (mediatorEdgeSpoke n r e i j member)‖ ≤ 6 := by
  unfold mediatorEdgeSpoke
  rw [spinMatrixOperator_sum]
  simp only [spinMatrixOperator_add]
  calc
    _ ≤ ∑ μ : Fin 3, ‖spinMatrixOperator
        (elementaryMediatorSpoke n r e 0 μ (sourceLocalPauli n i μ)) +
          spinMatrixOperator (elementaryMediatorSpoke n r e member μ (sourceLocalPauli n j μ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _μ : Fin 3, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro μ _
      exact ((norm_add_le _ _).trans (add_le_add
        (elementaryMediatorSpoke_operator_norm n r e 0 μ i)
        (elementaryMediatorSpoke_operator_norm n r e member μ j))).trans_eq (by norm_num)
    _ = 6 := by norm_num

/-- The actual simultaneous hopping norm is polynomial in the edge list. -/
theorem totalMediatorSpokes_operator_norm (n r : ℕ) (left right : Fin r → Fin n)
    (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    ‖spinMatrixOperator (totalMediatorSpokes n r left right member amplitude)‖ ≤
      6 * ∑ e, |amplitude e| := by
  unfold totalMediatorSpokes
  rw [spinMatrixOperator_sum]
  simp only [spinMatrixOperator_smul]
  calc
    _ ≤ ∑ e, ‖(amplitude e : ℂ) • spinMatrixOperator
        (mediatorEdgeSpoke n r e (left e) (right e) (member e))‖ := norm_sum_le _ _
    _ ≤ ∑ e, 6 * |amplitude e| := by
      apply Finset.sum_le_sum
      intro e _
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (mediatorEdgeSpoke_operator_norm n r e _ _ _) (abs_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem mediatorEdgeSpoke_star (n r : ℕ) (e : Fin r) (i j : Fin n) (member : Fin 2) :
    (mediatorEdgeSpoke n r e i j member).conjTranspose = mediatorEdgeSpoke n r e i j member := by
  unfold mediatorEdgeSpoke
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_add, elementaryMediatorSpoke_star]

theorem totalMediatorSpokes_star (n r : ℕ) (left right : Fin r → Fin n)
    (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    (totalMediatorSpokes n r left right member amplitude).conjTranspose =
      totalMediatorSpokes n r left right member amplitude := by
  unfold totalMediatorSpokes
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Complex.star_def,
    Complex.conj_ofReal, mediatorEdgeSpoke_star]


theorem sourceHeisenbergMatrix_star (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (sourceHeisenbergMatrix n i j).conjTranspose = sourceHeisenbergMatrix n i j := by
  simp_rw [← sourceLocalPauli_sum n i j hij]
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, sourceLocalPauli_star]
  apply Finset.sum_congr rfl
  intro μ _
  exact sourceLocalPauli_commute n j i hij.symm μ μ

theorem sourceHeisenbergMatrix_operator_norm (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    ‖spinMatrixOperator (sourceHeisenbergMatrix n i j)‖ ≤ 3 := by
  rw [← sourceLocalPauli_sum n i j hij, spinMatrixOperator_sum]
  simp only [spinMatrixOperator_mul]
  calc
    _ ≤ ∑ μ : Fin 3, ‖(spinMatrixOperator (sourceLocalPauli n i μ)).comp
        (spinMatrixOperator (sourceLocalPauli n j μ))‖ := norm_sum_le _ _
    _ ≤ ∑ _μ : Fin 3, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro μ _
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_mul (sourceLocalPauli_operator_norm n i μ)
          (sourceLocalPauli_operator_norm n j μ) (norm_nonneg _) zero_le_one).trans_eq
            (one_mul _))
    _ = 3 := by norm_num

theorem sourceGraphMatrix_operator_norm (n r : ℕ) (left right : Fin r → Fin n)
    (hloop : ∀ e, left e ≠ right e) (J : Fin r → ℝ) :
    ‖spinMatrixOperator (sourceGraphMatrix n r left right J)‖ ≤ 3 * ∑ e, |J e| := by
  unfold sourceGraphMatrix
  rw [spinMatrixOperator_sum]
  simp only [spinMatrixOperator_smul]
  calc
    _ ≤ ∑ e, ‖(J e : ℂ) • spinMatrixOperator
        (sourceHeisenbergMatrix n (left e) (right e))‖ := norm_sum_le _ _
    _ ≤ ∑ e, 3 * |J e| := by
      apply Finset.sum_le_sum
      intro e _
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (sourceHeisenbergMatrix_operator_norm n _ _ (hloop e)) (abs_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorBlocks
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.ContinuumCoulomb.spinMatrixOperator_diagonal _root_.OAI.ContinuumCoulomb.spinMatrixOperator_sub _root_.OAI.ContinuumCoulomb.spinMatrixOperator_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete low and high blocks for simultaneous singlet mediators.
The nonzero original-spin block is retained throughout. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

theorem mediatorLowIndex_injective (n r : ℕ) : Function.Injective (mediatorLowIndex n r) := by
  intro s t h
  exact congrArg Prod.fst h

theorem mediatorHighIndex_injective (n r : ℕ) : Function.Injective (mediatorHighIndex n r) := by
  rintro ⟨s, a⟩ ⟨t, b⟩ h
  change (s, a.val) = (t, b.val) at h
  have hs : s = t := congrArg (fun x : SourceSpinBasis n × MediatorBasis r => x.1) h
  have ha : a.val = b.val := congrArg (fun x : SourceSpinBasis n × MediatorBasis r => x.2) h
  exact Prod.ext hs (Subtype.ext ha)

theorem mediatorLowInclusion_norm (n r : ℕ) : ‖mediatorLowInclusion n r‖ ≤ 1 :=
  HubbardGlobal.coordinateInclusion_norm_le _ (mediatorLowIndex_injective n r)

theorem mediatorHighInclusion_norm (n r : ℕ) : ‖mediatorHighInclusion n r‖ ≤ 1 :=
  HubbardGlobal.coordinateInclusion_norm_le _ (mediatorHighIndex_injective n r)

theorem mediatorLowRestriction_norm (n r : ℕ) : ‖mediatorLowRestriction n r‖ ≤ 1 :=
  HubbardGlobal.coordinateRestriction_norm_le _ (mediatorLowIndex_injective n r)

theorem mediatorHighRestriction_norm (n r : ℕ) : ‖mediatorHighRestriction n r‖ ≤ 1 :=
  HubbardGlobal.coordinateRestriction_norm_le _ (mediatorHighIndex_injective n r)

theorem actualMediator_inverse_data (n r : ℕ) {Delta : ℝ} (hDelta : 0 < Delta) :
    (∀ x, diagonalPenalty (actualMediatorWeight n r Delta)
      (diagonalPenalty (fun s => (actualMediatorWeight n r Delta s)⁻¹) x) = x) ∧
    ‖diagonalPenalty (fun s => (actualMediatorWeight n r Delta s)⁻¹)‖ ≤ 1 / (4 * Delta) ∧
    (∀ x, (4 * Delta) * ‖x‖ ^ 2 ≤ ⟪x, diagonalPenalty (actualMediatorWeight n r Delta) x⟫_ℝ) := by
  have hg : 0 < 4 * Delta := by positivity
  have hgap (s : SourceSpinBasis n × MediatorHighBasis r) :
      4 * Delta ≤ actualMediatorWeight n r Delta s := by
    have hcount : (1 : ℝ) ≤ mediatorExcitationNumber r s.2.val := by
      exact_mod_cast mediatorExcitationNumber_pos r s.2.val s.2.property
    simpa only [mul_one, actualMediatorWeight, mediatorPenaltyWeight] using
      mul_le_mul_of_nonneg_left hcount hg.le
  exact ⟨diagonalPenalty_inverse_right _ (fun s => ne_of_gt (hg.trans_le (hgap s))),
    diagonalPenalty_inverse_norm hg _ hgap, diagonalPenalty_gap _ _ hgap⟩

theorem actualMediatorLowBlock_norm (n r : ℕ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :
    ‖actualMediatorLowBlock n r C‖ ≤ ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ := by
  unfold actualMediatorLowBlock
  rw [ContinuousLinearMap.norm_restrictScalars]
  exact HubbardGlobal.coordinateCompression_norm _ _ _
    (mediatorLowRestriction_norm n r) (mediatorLowInclusion_norm n r)

theorem actualMediatorCoupling_norm (n r : ℕ) (left right : Fin r → Fin n)
    (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    ‖actualMediatorCoupling n r left right member amplitude‖ ≤ 6 * ∑ e, |amplitude e| := by
  unfold actualMediatorCoupling
  rw [ContinuousLinearMap.norm_restrictScalars]
  exact (HubbardGlobal.coordinateCompression_norm _ _ _
    (mediatorHighRestriction_norm n r) (mediatorLowInclusion_norm n r)).trans
      (totalMediatorSpokes_operator_norm n r left right member amplitude)

theorem spinMatrixOperator_add_norm_bound {α : Type*} [Fintype α] [DecidableEq α]
    (M N : Matrix α α ℂ) (K : ℝ) (hN : ‖spinMatrixOperator N‖ ≤ K) :
    ‖spinMatrixOperator (M + N)‖ ≤ ‖spinMatrixOperator M‖ + K := by
  rw [spinMatrixOperator_add]
  calc
    ‖spinMatrixOperator M + spinMatrixOperator N‖ ≤
        ‖spinMatrixOperator M‖ + ‖spinMatrixOperator N‖ := norm_add_le _ _
    _ ≤ ‖spinMatrixOperator M‖ + K := by linarith only [hN]

theorem liftedMediatorPerturbation_norm (n r : ℕ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ) +
      totalMediatorSpokes n r left right member amplitude)‖ ≤
      ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ + 6 * ∑ e, |amplitude e| := by
  exact spinMatrixOperator_add_norm_bound _ _ _
    (totalMediatorSpokes_operator_norm n r left right member amplitude)

theorem actualMediatorHighBlock_norm (n r : ℕ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    ‖actualMediatorHighBlock n r C left right member amplitude‖ ≤
      ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ + 6 * ∑ e, |amplitude e| := by
  unfold actualMediatorHighBlock
  rw [ContinuousLinearMap.norm_restrictScalars]
  exact (HubbardGlobal.coordinateCompression_norm _ _ _
    (mediatorHighRestriction_norm n r) (mediatorHighInclusion_norm n r)).trans
      (liftedMediatorPerturbation_norm n r C left right member amplitude)

/-- A supporting block estimate for the actual simultaneous mediator
construction, retaining the unreplaced low Hamiltonian C. -/
theorem actualMediator_second_order (n r : ℕ) {Delta : ℝ} (hDelta : 0 < Delta)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (amplitude : Fin r → ℝ)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1 / 4)
    (hbound : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      6 * ∑ e, |amplitude e| ≤ epsilon * (4 * Delta)) :
    |Perturbation.lowBlockBottom (actualMediatorLowBlock n r C)
        (diagonalPenalty (actualMediatorWeight n r Delta))
        (actualMediatorHighBlock n r C left right member amplitude)
        (actualMediatorCoupling n r left right member amplitude) -
      Perturbation.effectiveBottom (actualMediatorLowBlock n r C)
        (diagonalPenalty (fun s => (actualMediatorWeight n r Delta s)⁻¹))
        (actualMediatorCoupling n r left right member amplitude)| ≤ 16 * Delta * epsilon ^ 3 := by
  obtain ⟨hAT, hT, hgap⟩ := actualMediator_inverse_data n r hDelta
  have hg : 0 < 4 * Delta := by positivity
  have hamp : 0 ≤ 6 * ∑ e, |amplitude e| := by positivity
  have hB : ‖actualMediatorCoupling n r left right member amplitude‖ ≤ epsilon * (4 * Delta) :=
    (actualMediatorCoupling_norm n r left right member amplitude).trans
      ((le_add_of_nonneg_left (norm_nonneg _)).trans hbound)
  have hC : ‖actualMediatorLowBlock n r C‖ ≤ epsilon * (4 * Delta) :=
    (actualMediatorLowBlock_norm n r C).trans ((le_add_of_nonneg_right hamp).trans hbound)
  have hD := (actualMediatorHighBlock_norm n r C left right member amplitude).trans hbound
  have hu : ‖(EuclideanSpace.single (fun _ : Fin n => (0 : Fin 2)) (1 : ℂ) : MediatorLowSpace n)‖ = 1 := by
    simp
  convert Perturbation.finite_lowBlockBottom_second_order
    (actualMediatorLowBlock n r C) (diagonalPenalty (actualMediatorWeight n r Delta))
    (diagonalPenalty (fun s => (actualMediatorWeight n r Delta s)⁻¹))
    (actualMediatorHighBlock n r C left right member amplitude)
    (actualMediatorCoupling n r left right member amplitude)
    hg hepsilon hsmall hAT (diagonalPenalty_symmetric _)
    (fun q => (mul_nonneg hg.le (sq_nonneg ‖q‖)).trans (hgap q)) hgap hT hB hC hD _ hu using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorSector
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.ContinuumCoulomb.spinMatrixOperator_sub _root_.OAI.ContinuumCoulomb.spinMatrixOperator_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The singlet and excited mediator coordinates form the full spin space. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

theorem mediatorLowInclusion_apply (n r : ℕ) (p : MediatorLowSpace n)
    (s : SourceSpinBasis n) (a : MediatorBasis r) :
    mediatorLowInclusion n r p (s, a) = if a = mediatorVacuum r then p s else 0 := by
  classical
  by_cases ha : a = mediatorVacuum r
  · subst a
    simpa only [ite_true, if_true, mediatorLowInclusion, mediatorLowIndex] using HubbardGlobal.coordinateInclusion_apply_image
      (mediatorLowIndex n r) (mediatorLowIndex_injective n r) p s
  · rw [ite_eq_right ha]
    apply HubbardGlobal.coordinateInclusion_apply_outside
    intro t ht
    exact ha (congrArg (fun x : MediatedSpinBasis n r => x.2) ht).symm

theorem mediatorHighInclusion_apply (n r : ℕ) (q : MediatorHighSpace n r)
    (s : SourceSpinBasis n) (a : MediatorHighBasis r) :
    mediatorHighInclusion n r q (s, a.val) = q (s, a) :=
  HubbardGlobal.coordinateInclusion_apply_image (mediatorHighIndex n r)
    (mediatorHighIndex_injective n r) q (s, a)

theorem mediatorHighInclusion_vacuum (n r : ℕ) (q : MediatorHighSpace n r)
    (s : SourceSpinBasis n) : mediatorHighInclusion n r q (s, mediatorVacuum r) = 0 := by
  apply HubbardGlobal.coordinateInclusion_apply_outside
  intro t ht
  exact t.2.property (congrArg (fun x : MediatedSpinBasis n r => x.2) ht)

@[simp] theorem mediatorLowRestriction_apply (n r : ℕ) (x : MediatorFullSpace n r)
    (s : SourceSpinBasis n) : mediatorLowRestriction n r x s = x (s, mediatorVacuum r) :=
  HubbardGlobal.coordinateRestriction_apply _ x s

@[simp] theorem mediatorHighRestriction_apply (n r : ℕ) (x : MediatorFullSpace n r)
    (s : SourceSpinBasis n × MediatorHighBasis r) :
    mediatorHighRestriction n r x s = x (s.1, s.2.val) :=
  HubbardGlobal.coordinateRestriction_apply _ x s

@[simp] theorem mediatorLowRestriction_inclusion (n r : ℕ) (p : MediatorLowSpace n) :
    mediatorLowRestriction n r (mediatorLowInclusion n r p) = p :=
  HubbardGlobal.coordinateRestriction_inclusion _ (mediatorLowIndex_injective n r) p

@[simp] theorem mediatorHighRestriction_inclusion (n r : ℕ) (q : MediatorHighSpace n r) :
    mediatorHighRestriction n r (mediatorHighInclusion n r q) = q :=
  HubbardGlobal.coordinateRestriction_inclusion _ (mediatorHighIndex_injective n r) q

@[simp] theorem mediatorLowRestriction_high (n r : ℕ) (q : MediatorHighSpace n r) :
    mediatorLowRestriction n r (mediatorHighInclusion n r q) = 0 := by
  ext s
  simp only [mediatorLowRestriction_apply, mediatorHighInclusion_vacuum, PiLp.zero_apply]

@[simp] theorem mediatorHighRestriction_low (n r : ℕ) (p : MediatorLowSpace n) :
    mediatorHighRestriction n r (mediatorLowInclusion n r p) = 0 := by
  ext s
  simp only [mediatorHighRestriction_apply, mediatorLowInclusion_apply,
    ite_eq_right s.2.property, PiLp.zero_apply]

/-- Every full spin state decomposes into its singlet and triplet sectors. -/
theorem mediator_full_decomposition (n r : ℕ) (x : MediatorFullSpace n r) :
    mediatorLowInclusion n r (mediatorLowRestriction n r x) +
      mediatorHighInclusion n r (mediatorHighRestriction n r x) = x := by
  classical
  ext ⟨s, a⟩
  by_cases ha : a = mediatorVacuum r
  · subst a
    simp only [PiLp.add_apply, mediatorLowInclusion_apply, ite_true, if_true,
      mediatorLowRestriction_apply, mediatorHighInclusion_vacuum, add_zero]
  · rw [PiLp.add_apply, mediatorLowInclusion_apply, ite_eq_right ha, zero_add]
    exact (mediatorHighInclusion_apply n r _ s ⟨a, ha⟩).trans
      (mediatorHighRestriction_apply n r x (s, ⟨a, ha⟩))

theorem mediatorLow_real_inner (n r : ℕ) (p : MediatorLowSpace n) (x : MediatorFullSpace n r) :
    ⟪mediatorLowInclusion n r p, x⟫_ℝ = ⟪p, mediatorLowRestriction n r x⟫_ℝ :=
  HubbardGlobal.coordinateInclusion_real_inner _ p x

theorem mediatorHigh_real_inner (n r : ℕ) (q : MediatorHighSpace n r) (x : MediatorFullSpace n r) :
    ⟪mediatorHighInclusion n r q, x⟫_ℝ = ⟪q, mediatorHighRestriction n r x⟫_ℝ :=
  HubbardGlobal.coordinateInclusion_real_inner _ q x

theorem mediatorLowInclusion_norm_map (n r : ℕ) (p : MediatorLowSpace n) :
    ‖mediatorLowInclusion n r p‖ = ‖p‖ :=
  HubbardGlobal.coordinateInclusion_norm_map _ (mediatorLowIndex_injective n r) p

theorem mediatorHighInclusion_norm_map (n r : ℕ) (q : MediatorHighSpace n r) :
    ‖mediatorHighInclusion n r q‖ = ‖q‖ :=
  HubbardGlobal.coordinateInclusion_norm_map _ (mediatorHighIndex_injective n r) q

theorem assembleMediator_norm_sq (n r : ℕ) (p : MediatorLowSpace n) (q : MediatorHighSpace n r) :
    ‖assembleMediator n r p q‖ ^ 2 = ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
  unfold assembleMediator
  rw [norm_add_sq_real, mediatorLow_real_inner, mediatorLowRestriction_high,
    inner_zero_right, mediatorLowInclusion_norm_map, mediatorHighInclusion_norm_map]
  ring

/-- The matrix vacuum compression agrees with the actual Hilbert-space block. -/
theorem mediatorLow_operator_compression (n r : ℕ)
    (M : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ) :
    (mediatorLowRestriction n r).comp
      ((spinMatrixOperator M).comp (mediatorLowInclusion n r)) =
        spinMatrixOperator (mediatorCompression n r M) := by
  classical
  ext p s
  simp only [ContinuousLinearMap.comp_apply, mediatorLowRestriction_apply,
    spinMatrixOperator_apply, Fintype.sum_prod_type, mediatorLowInclusion_apply,
    mul_ite, mul_zero]
  simp [mediatorCompression]
  rfl

theorem liftedMediatorInverse_diagonal (n r : ℕ) (Delta : ℝ) :
    liftedMediatorInverse n r Delta =
      Matrix.diagonal (fun s : MediatedSpinBasis n r => mediatorInverseWeight r Delta s.2) := by
  unfold liftedMediatorInverse mediatorInverseMatrix
  rw [← Matrix.diagonal_one (n := SourceSpinBasis n), Matrix.diagonal_kronecker_diagonal]
  simp only [one_mul]

/-- The full inverse matrix is the actual diagonal high-sector inverse,
extended by zero on the singlet sector. -/
theorem mediatorInverse_highInclusion (n r : ℕ) (Delta : ℝ) (q : MediatorHighSpace n r) :
    spinMatrixOperator (liftedMediatorInverse n r Delta) (mediatorHighInclusion n r q) =
      mediatorHighInclusion n r (diagonalPenalty
        (fun s => (actualMediatorWeight n r Delta s)⁻¹) q) := by
  classical
  rw [liftedMediatorInverse_diagonal]
  ext ⟨s, a⟩
  rw [spinMatrixOperator_diagonal]
  by_cases ha : a = mediatorVacuum r
  · subst a
    simp only [mediatorHighInclusion_vacuum, mul_zero]
  · rw [mediatorHighInclusion_apply n r q s ⟨a, ha⟩,
      mediatorHighInclusion_apply n r _ s ⟨a, ha⟩]
    simp only [diagonalPenalty_apply, mediatorInverseWeight, ite_eq_right ha,
      actualMediatorWeight, RCLike.real_smul_eq_coe_mul]
    rfl

/-- The original Hamiltonian acts only on the original-spin coordinates. -/
theorem liftedSource_lowInclusion (n r : ℕ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (p : MediatorLowSpace n) :
    spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))
        (mediatorLowInclusion n r p) = mediatorLowInclusion n r (spinMatrixOperator C p) := by
  classical
  ext ⟨s, a⟩
  simp only [spinMatrixOperator_apply, Fintype.sum_prod_type, Matrix.kronecker_apply,
    Matrix.one_apply, mediatorLowInclusion_apply, mul_ite, ite_mul, mul_zero, zero_mul,
    mul_one]
  by_cases ha : a = mediatorVacuum r
  · subst a
    simp
  · simp [ha]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorForms
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full simultaneous-mediator quadratic forms and their exact effective matrix. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

theorem spinMatrixOperator_real_symmetric {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (hM : M.conjTranspose = M) (x y : EuclideanSpace ℂ ι) :
    ⟪x, spinMatrixOperator M y⟫_ℝ = ⟪spinMatrixOperator M x, y⟫_ℝ := by
  rw [HubbardGlobal.euclidean_real_inner, HubbardGlobal.euclidean_real_inner]
  have h := ContinuousLinearMap.adjoint_inner_right (spinMatrixOperator M) x y
  rw [← spinMatrixOperator_star, hM] at h
  exact congrArg Complex.re h

theorem actualMediatorLowBlock_eq (n r : ℕ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :
    actualMediatorLowBlock n r C = (spinMatrixOperator C).restrictScalars ℝ := by
  unfold actualMediatorLowBlock
  rw [mediatorLow_operator_compression, mediatorCompression_kronecker]
  simp

theorem mediatorLowRestriction_spokes_low (n r : ℕ) (left right : Fin r → Fin n)
    (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) (p : MediatorLowSpace n) :
    mediatorLowRestriction n r (spinMatrixOperator (totalMediatorSpokes n r left right member amplitude)
      (mediatorLowInclusion n r p)) = 0 := by
  have h := congrArg (fun T : MediatorLowSpace n →L[ℂ] MediatorLowSpace n => T p)
    (mediatorLow_operator_compression n r (totalMediatorSpokes n r left right member amplitude))
  simpa only [ContinuousLinearMap.comp_apply, totalMediatorSpokes_low_compression,
    spinMatrixOperator_zero, _root_.zero_apply] using h

/-- Hopping a singlet-sector state creates only actual mediator excitations. -/
theorem mediatorHighInclusion_coupling (n r : ℕ) (left right : Fin r → Fin n)
    (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) (p : MediatorLowSpace n) :
    mediatorHighInclusion n r (actualMediatorCoupling n r left right member amplitude p) =
      spinMatrixOperator (totalMediatorSpokes n r left right member amplitude)
        (mediatorLowInclusion n r p) := by
  change mediatorHighInclusion n r (mediatorHighRestriction n r
    (spinMatrixOperator (totalMediatorSpokes n r left right member amplitude)
      (mediatorLowInclusion n r p))) = _
  have h := mediator_full_decomposition n r
    (spinMatrixOperator (totalMediatorSpokes n r left right member amplitude)
      (mediatorLowInclusion n r p))
  simpa only [mediatorLowRestriction_spokes_low, map_zero, zero_add] using h

theorem bellMediatorPenalty_low (n r : ℕ) (Delta : ℝ) (p : MediatorLowSpace n) :
    spinMatrixOperator (bellMediatorPenaltyMatrix n r Delta) (mediatorLowInclusion n r p) = 0 := by
  classical
  ext ⟨s, a⟩
  rw [bellMediatorPenaltyMatrix, spinMatrixOperator_diagonal, mediatorLowInclusion_apply]
  by_cases ha : a = mediatorVacuum r
  · subst a
    simp [mediatorPenaltyWeight, mediatorExcitationNumber, mediatorVacuum]
  · simp [ha]

theorem bellMediatorPenalty_high (n r : ℕ) (Delta : ℝ) (q : MediatorHighSpace n r) :
    spinMatrixOperator (bellMediatorPenaltyMatrix n r Delta) (mediatorHighInclusion n r q) =
      mediatorHighInclusion n r (diagonalPenalty (actualMediatorWeight n r Delta) q) := by
  classical
  ext ⟨s, a⟩
  rw [bellMediatorPenaltyMatrix, spinMatrixOperator_diagonal]
  by_cases ha : a = mediatorVacuum r
  · subst a
    simp only [mediatorHighInclusion_vacuum, mul_zero]
  · rw [mediatorHighInclusion_apply n r q s ⟨a, ha⟩,
      mediatorHighInclusion_apply n r _ s ⟨a, ha⟩]
    simp only [diagonalPenalty_apply, actualMediatorWeight, RCLike.real_smul_eq_coe_mul]
    rfl

/-- Exact effective quadratic form for every entangled original-spin vector. -/
theorem actualMediator_effectiveForm (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (amplitude : Fin r → ℝ)
    (p : MediatorLowSpace n) :
    Perturbation.effectiveForm (actualMediatorLowBlock n r C)
      (diagonalPenalty (fun s => (actualMediatorWeight n r Delta s)⁻¹))
      (actualMediatorCoupling n r left right member amplitude) p =
      ⟪p, spinMatrixOperator (C - mediatorCompression n r
        (totalMediatorSpokes n r left right member amplitude * liftedMediatorInverse n r Delta *
          totalMediatorSpokes n r left right member amplitude)) p⟫_ℝ := by
  let W := totalMediatorSpokes n r left right member amplitude
  let B := actualMediatorCoupling n r left right member amplitude
  let T := diagonalPenalty (fun s => (actualMediatorWeight n r Delta s)⁻¹)
  have hB : mediatorHighInclusion n r (B p) = spinMatrixOperator W (mediatorLowInclusion n r p) :=
    mediatorHighInclusion_coupling n r left right member amplitude p
  have hT : mediatorHighInclusion n r (T (B p)) =
      spinMatrixOperator (liftedMediatorInverse n r Delta) (mediatorHighInclusion n r (B p)) :=
    (mediatorInverse_highInclusion n r Delta (B p)).symm
  have hinner : ⟪B p, T (B p)⟫_ℝ =
      ⟪p, spinMatrixOperator (mediatorCompression n r
        (W * liftedMediatorInverse n r Delta * W)) p⟫_ℝ := by
    calc
      _ = ⟪mediatorHighInclusion n r (B p), mediatorHighInclusion n r (T (B p))⟫_ℝ := by
        rw [mediatorHigh_real_inner, mediatorHighRestriction_inclusion]
      _ = ⟪spinMatrixOperator W (mediatorLowInclusion n r p),
          spinMatrixOperator (liftedMediatorInverse n r Delta)
            (spinMatrixOperator W (mediatorLowInclusion n r p))⟫_ℝ := by rw [hT, hB]
      _ = ⟪mediatorLowInclusion n r p, spinMatrixOperator W
          (spinMatrixOperator (liftedMediatorInverse n r Delta)
            (spinMatrixOperator W (mediatorLowInclusion n r p)))⟫_ℝ :=
        (spinMatrixOperator_real_symmetric W (totalMediatorSpokes_star n r left right member amplitude) _ _).symm
      _ = ⟪p, spinMatrixOperator (mediatorCompression n r
          (W * liftedMediatorInverse n r Delta * W)) p⟫_ℝ := by
        rw [mediatorLow_real_inner]
        have hc := congrArg (fun A : MediatorLowSpace n →L[ℂ] MediatorLowSpace n => A p)
          (mediatorLow_operator_compression n r (W * liftedMediatorInverse n r Delta * W))
        simpa only [spinMatrixOperator_mul, ContinuousLinearMap.comp_apply] using congrArg
          (fun x : MediatorLowSpace n => ⟪p, x⟫_ℝ) hc
  unfold Perturbation.effectiveForm Perturbation.inverseForm
  rw [actualMediatorLowBlock_eq, hinner, spinMatrixOperator_sub]
  simp only [ContinuousLinearMap.coe_restrictScalars', _root_.sub_apply, inner_sub_right]
  rfl


/-- Full-state quadratic-form equality for the concrete low/high blocks. -/
theorem bellMediatorHamiltonian_form_blocks (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (amplitude : Fin r → ℝ)
    (p : MediatorLowSpace n) (q : MediatorHighSpace n r) :
    ⟪assembleMediator n r p q,
      spinMatrixOperator (bellMediatorHamiltonian n r Delta C left right member amplitude)
        (assembleMediator n r p q)⟫_ℝ =
      Perturbation.lowBlockEnergy (actualMediatorLowBlock n r C)
        (diagonalPenalty (actualMediatorWeight n r Delta))
        (actualMediatorHighBlock n r C left right member amplitude)
        (actualMediatorCoupling n r left right member amplitude) p q := by
  let W := totalMediatorSpokes n r left right member amplitude
  let H := spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ) + W)
  let P := spinMatrixOperator (bellMediatorPenaltyMatrix n r Delta)
  let lp := mediatorLowInclusion n r p
  let hq := mediatorHighInclusion n r q
  have hHermitian : (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ) + W).conjTranspose =
      C ⊗ₖ 1 + W := by
    dsimp only [W]
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_kronecker, hC,
      Matrix.conjTranspose_one, totalMediatorSpokes_star]
  have hPlow : P lp = 0 := bellMediatorPenalty_low n r Delta p
  have hPhigh : P hq = mediatorHighInclusion n r
      (diagonalPenalty (actualMediatorWeight n r Delta) q) := bellMediatorPenalty_high n r Delta q
  have hPenaltyCross : ⟪lp, P hq⟫_ℝ = 0 := by
    rw [hPhigh, mediatorLow_real_inner, mediatorLowRestriction_high, inner_zero_right]
  have hPenaltyHigh : ⟪hq, P hq⟫_ℝ =
      ⟪q, diagonalPenalty (actualMediatorWeight n r Delta) q⟫_ℝ := by
    rw [hPhigh, mediatorHigh_real_inner, mediatorHighRestriction_inclusion]
  have hHlow : H lp = mediatorLowInclusion n r (spinMatrixOperator C p) + spinMatrixOperator W lp := by
    dsimp only [H, lp]
    rw [spinMatrixOperator_add, _root_.add_apply, liftedSource_lowInclusion]
  have hLow : ⟪lp, H lp⟫_ℝ = ⟪p, actualMediatorLowBlock n r C p⟫_ℝ := by
    rw [hHlow, inner_add_right, mediatorLow_real_inner, mediatorLowRestriction_inclusion,
      mediatorLow_real_inner, mediatorLowRestriction_spokes_low, inner_zero_right, add_zero,
      actualMediatorLowBlock_eq]
    rfl
  have hCross : ⟪hq, H lp⟫_ℝ =
      ⟪q, actualMediatorCoupling n r left right member amplitude p⟫_ℝ := by
    rw [hHlow, inner_add_right, mediatorHigh_real_inner, mediatorHighRestriction_low,
      inner_zero_right, zero_add, mediatorHigh_real_inner]
    rfl
  have hReverse : ⟪lp, H hq⟫_ℝ =
      ⟪q, actualMediatorCoupling n r left right member amplitude p⟫_ℝ := by
    rw [spinMatrixOperator_real_symmetric _ hHermitian, real_inner_comm, hCross]
  have hHigh : ⟪hq, H hq⟫_ℝ =
      ⟪q, actualMediatorHighBlock n r C left right member amplitude q⟫_ℝ := by
    rw [mediatorHigh_real_inner]
    rfl
  have hform : ⟪assembleMediator n r p q,
      spinMatrixOperator (bellMediatorHamiltonian n r Delta C left right member amplitude)
        (assembleMediator n r p q)⟫_ℝ =
      ⟪lp + hq, P (lp + hq) + H (lp + hq)⟫_ℝ := by
    unfold bellMediatorHamiltonian assembleMediator
    rw [spinMatrixOperator_add, _root_.add_apply]
  rw [hform, map_add, map_add]
  simp only [inner_add_left, inner_add_right, hPlow, inner_zero_right,
    hPenaltyCross, hPenaltyHigh, hLow, hCross, hReverse, hHigh,
    Perturbation.lowBlockEnergy, Perturbation.blockEnergy, Perturbation.penaltyForm]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorSpectrum
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual variational bottoms for the complete simultaneous-mediator spin
Hamiltonian and its effective source matrix. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

theorem mediatorFullBottom_eq_lowBlockBottom (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    mediatorFullBottom n r (bellMediatorHamiltonian n r Delta C left right member amplitude) =
      Perturbation.lowBlockBottom (actualMediatorLowBlock n r C)
        (diagonalPenalty (actualMediatorWeight n r Delta))
        (actualMediatorHighBlock n r C left right member amplitude)
        (actualMediatorCoupling n r left right member amplitude) := by
  unfold mediatorFullBottom Perturbation.lowBlockBottom
  congr 1
  ext e
  constructor
  · rintro ⟨x, hx, rfl⟩
    let p := mediatorLowRestriction n r x
    let q := mediatorHighRestriction n r x
    have hassemble : assembleMediator n r p q = x := mediator_full_decomposition n r x
    have hnorm : 0 < ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
      rw [← assembleMediator_norm_sq, hassemble]
      exact hx
    refine ⟨p, q, hnorm, ?_⟩
    unfold Perturbation.lowBlockRayleigh
    rw [← bellMediatorHamiltonian_form_blocks n r Delta C hC left right member amplitude,
      ← assembleMediator_norm_sq, hassemble]
  · rintro ⟨p, q, hpq, rfl⟩
    refine ⟨assembleMediator n r p q, ?_, ?_⟩
    · rw [assembleMediator_norm_sq]
      exact hpq
    · rw [bellMediatorHamiltonian_form_blocks n r Delta C hC left right member amplitude,
        assembleMediator_norm_sq]
      rfl

theorem actualMediator_effectiveBottom_matrix (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    Perturbation.effectiveBottom (actualMediatorLowBlock n r C)
      (diagonalPenalty (fun s => (actualMediatorWeight n r Delta s)⁻¹))
      (actualMediatorCoupling n r left right member amplitude) =
      sourceMatrixBottom n (C - mediatorCompression n r
        (totalMediatorSpokes n r left right member amplitude * liftedMediatorInverse n r Delta *
          totalMediatorSpokes n r left right member amplitude)) := by
  unfold Perturbation.effectiveBottom sourceMatrixBottom
  simp_rw [actualMediator_effectiveForm]

theorem sourceMatrixBottom_minimizer (n : ℕ)
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :
    ∃ p : MediatorLowSpace n, ‖p‖ = 1 ∧
      sourceMatrixBottom n M = ⟪p, spinMatrixOperator M p⟫_ℝ ∧
      ∀ q : MediatorLowSpace n, ‖q‖ = 1 →
        ⟪p, spinMatrixOperator M p⟫_ℝ ≤ ⟪q, spinMatrixOperator M q⟫_ℝ := by
  let C := (spinMatrixOperator M).restrictScalars ℝ
  let T : MediatorLowSpace n →L[ℝ] MediatorLowSpace n := 0
  let B : MediatorLowSpace n →L[ℝ] MediatorLowSpace n := 0
  let u : MediatorLowSpace n := EuclideanSpace.single (fun _ => 0) 1
  have hu : ‖u‖ = 1 := by simp [u]
  obtain ⟨p, hp, hmin⟩ := Perturbation.effectiveForm_minimizer C T B u hu
  have hform (q : MediatorLowSpace n) :
      Perturbation.effectiveForm C T B q = ⟪q, spinMatrixOperator M q⟫_ℝ := by
    simp [Perturbation.effectiveForm, Perturbation.inverseForm, C, T, B]
  have hbottom : Perturbation.effectiveBottom C T B = sourceMatrixBottom n M := by
    unfold Perturbation.effectiveBottom sourceMatrixBottom
    simp_rw [hform]
  refine ⟨p, hp, ?_, ?_⟩
  · rw [← hbottom, Perturbation.effectiveBottom_eq C T B p hp hmin, hform]
  · intro q hq
    simpa only [hform, hq, one_pow, mul_one] using hmin q

theorem sourceMatrixForm_shift (n : ℕ)
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (k : ℝ)
    (p : MediatorLowSpace n) (hp : ‖p‖ = 1) :
    ⟪p, spinMatrixOperator (M - (k : ℂ) • 1) p⟫_ℝ =
      ⟪p, spinMatrixOperator M p⟫_ℝ - k := by
  rw [spinMatrixOperator_sub, spinMatrixOperator_smul, spinMatrixOperator_one,
    _root_.sub_apply, _root_.smul_apply, one_apply_eq_self,
    inner_sub_right]
  have hscalar : ⟪p, (k : ℂ) • p⟫_ℝ = k := by
    rw [HubbardGlobal.euclidean_real_inner, inner_smul_right, inner_self_eq_norm_sq_to_K, hp]
    simp
  rw [hscalar]

theorem sourceMatrixBottom_shift (n : ℕ)
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (k : ℝ) :
    sourceMatrixBottom n (M - (k : ℂ) • 1) = sourceMatrixBottom n M - k := by
  obtain ⟨p, hp, hbottom, hmin⟩ := sourceMatrixBottom_minimizer n M
  let S := {e | ∃ q : MediatorLowSpace n, ‖q‖ = 1 ∧
    e = ⟪q, spinMatrixOperator (M - (k : ℂ) • 1) q⟫_ℝ}
  have hmem : ⟪p, spinMatrixOperator (M - (k : ℂ) • 1) p⟫_ℝ ∈ S := ⟨p, hp, rfl⟩
  have hlower : ∀ e ∈ S, sourceMatrixBottom n M - k ≤ e := by
    rintro e ⟨q, hq, rfl⟩
    rw [sourceMatrixForm_shift n M k q hq, hbottom]
    exact sub_le_sub_right (hmin q hq) k
  have hbdd : BddBelow S := ⟨_, hlower⟩
  apply le_antisymm
  · exact (csInf_le hbdd hmem).trans_eq (by rw [sourceMatrixForm_shift n M k p hp, hbottom])
  · exact le_csInf ⟨_, hmem⟩ hlower

/-- Full simultaneous singlet-mediator spectrum, retaining unreplaced
terms C and the exact constant shift. This compares actual variational
infima and has only explicit construction norm/calibration hypotheses. -/
theorem simultaneousMediator_bottom (n r : ℕ) {Delta : ℝ} (hDelta : 0 < Delta)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    (left right : Fin r → Fin n) (hneq : ∀ e, left e ≠ right e)
    (J amplitude : Fin r → ℝ) (hcal : ∀ e, amplitude e ^ 2 = 2 * Delta * |J e|)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1 / 4)
    (hbound : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      6 * ∑ e, |amplitude e| ≤ epsilon * (4 * Delta)) :
    |mediatorFullBottom n r (bellMediatorHamiltonian n r Delta C left right
        (fun e => signedMediatorMember (J e)) amplitude) + 3 * ∑ e, |J e| -
      sourceMatrixBottom n (C + ∑ e, (J e : ℂ) • sourceHeisenbergMatrix n (left e) (right e))| ≤
        16 * Delta * epsilon ^ 3 := by
  have h := actualMediator_second_order n r hDelta C left right
    (fun e => signedMediatorMember (J e)) amplitude hepsilon hsmall hbound
  rw [← mediatorFullBottom_eq_lowBlockBottom n r Delta C hC left right
    (fun e => signedMediatorMember (J e)) amplitude,
    actualMediator_effectiveBottom_matrix,
    signedMediator_effective_matrix n r hDelta left right hneq J amplitude hcal] at h
  have hshift : (C + ∑ e, (J e : ℂ) • sourceHeisenbergMatrix n (left e) (right e)) -
      (3 * ∑ e, |J e| : ℝ) • 1 =
      (C + ∑ e, (J e : ℂ) • sourceHeisenbergMatrix n (left e) (right e)) -
      ((3 * ∑ e, |J e| : ℝ) : ℂ) • 1 := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  rw [hshift, sourceMatrixBottom_shift] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorPhysical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical positive-spoke spin matrices and their full spectral comparison. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

theorem physicalMediatorPenalty_full_transform (n r : ℕ) (Delta : ℝ) :
    (fullMediatorBellMatrix n r).conjTranspose *
      ((1 : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) ⊗ₖ physicalMediatorPenalty r Delta) *
        fullMediatorBellMatrix n r = bellMediatorPenaltyMatrix n r Delta := by
  unfold fullMediatorBellMatrix
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul]
  simp only [Matrix.conjTranspose_one, one_mul, physicalMediatorPenalty_diagonal]
  rw [← Matrix.diagonal_one (n := SourceSpinBasis n), Matrix.diagonal_kronecker_diagonal]
  simp only [one_mul]
  rfl

theorem liftedSource_full_transform (n r : ℕ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :
    (fullMediatorBellMatrix n r).conjTranspose *
      (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ)) * fullMediatorBellMatrix n r =
      C ⊗ₖ 1 := by
  unfold fullMediatorBellMatrix
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul]
  simp only [Matrix.conjTranspose_one, one_mul, mul_one, globalBellMatrix_gram]

theorem physicalMediatorEdgeSpoke_transform (n r : ℕ) (e : Fin r) (i j : Fin n) (member : Fin 2) :
    (fullMediatorBellMatrix n r).conjTranspose * physicalMediatorEdgeSpoke n r e i j member *
      fullMediatorBellMatrix n r = mediatorEdgeSpoke n r e i j member := by
  unfold physicalMediatorEdgeSpoke mediatorEdgeSpoke
  simp only [Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, physicalSpoke_bellTransform]

theorem physicalTotalMediatorSpokes_transform (n r : ℕ) (left right : Fin r → Fin n)
    (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    (fullMediatorBellMatrix n r).conjTranspose *
      physicalTotalMediatorSpokes n r left right member amplitude * fullMediatorBellMatrix n r =
        totalMediatorSpokes n r left right member amplitude := by
  unfold physicalTotalMediatorSpokes totalMediatorSpokes
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    physicalMediatorEdgeSpoke_transform]

/-- Exact change of coordinates for the entire physical construction. -/
theorem physicalMediatorHamiltonian_transform (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    (fullMediatorBellMatrix n r).conjTranspose *
      physicalMediatorHamiltonian n r Delta C left right member amplitude *
        fullMediatorBellMatrix n r = bellMediatorHamiltonian n r Delta C left right member amplitude := by
  unfold physicalMediatorHamiltonian bellMediatorHamiltonian
  simp only [mul_add, add_mul, physicalMediatorPenalty_full_transform,
    liftedSource_full_transform, physicalTotalMediatorSpokes_transform]

theorem spinMatrixOperator_unitary_form (n r : ℕ)
    (U H : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ)
    (x : MediatorFullSpace n r) :
    ⟪x, spinMatrixOperator (U.conjTranspose * H * U) x⟫_ℝ =
      ⟪spinMatrixOperator U x, spinMatrixOperator H (spinMatrixOperator U x)⟫_ℝ := by
  simp only [spinMatrixOperator_mul, spinMatrixOperator_star, ContinuousLinearMap.comp_apply]
  rw [HubbardGlobal.euclidean_real_inner, HubbardGlobal.euclidean_real_inner]
  exact congrArg Complex.re (ContinuousLinearMap.adjoint_inner_right
    (spinMatrixOperator U) x (spinMatrixOperator H (spinMatrixOperator U x)))

/-- The complete variational infimum is invariant under the explicit unitary. -/
theorem mediatorFullBottom_unitary (n r : ℕ)
    (U H : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ)
    (hGram : U.conjTranspose * U = 1) (hCogram : U * U.conjTranspose = 1) :
    mediatorFullBottom n r (U.conjTranspose * H * U) = mediatorFullBottom n r H := by
  unfold mediatorFullBottom
  congr 1
  ext e
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨spinMatrixOperator U x, ?_, ?_⟩
    · rw [spinMatrixOperator_unitary_norm_map U hGram]
      exact hx
    · rw [spinMatrixOperator_unitary_form, spinMatrixOperator_unitary_norm_map U hGram]
  · rintro ⟨x, hx, rfl⟩
    have hUstar : U.conjTranspose.conjTranspose * U.conjTranspose = 1 := by
      simpa only [Matrix.conjTranspose_conjTranspose] using hCogram
    have hcancel : spinMatrixOperator U (spinMatrixOperator U.conjTranspose x) = x := by
      have h := congrArg (fun M => spinMatrixOperator M x) hCogram
      simpa only [spinMatrixOperator_mul, ContinuousLinearMap.comp_apply,
        spinMatrixOperator_one, one_apply_eq_self] using h
    refine ⟨spinMatrixOperator U.conjTranspose x, ?_, ?_⟩
    · rw [spinMatrixOperator_unitary_norm_map U.conjTranspose hUstar]
      exact hx
    · rw [spinMatrixOperator_unitary_form, hcancel,
        spinMatrixOperator_unitary_norm_map U.conjTranspose hUstar]

/-- Physical full-spin spectral comparison for the simultaneous positive
singlet spokes, including all excited sectors and unreplaced terms. -/
theorem physicalSimultaneousMediator_bottom (n r : ℕ) {Delta : ℝ} (hDelta : 0 < Delta)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    (left right : Fin r → Fin n) (hneq : ∀ e, left e ≠ right e)
    (J amplitude : Fin r → ℝ) (hcal : ∀ e, amplitude e ^ 2 = 2 * Delta * |J e|)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1 / 4)
    (hbound : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      6 * ∑ e, |amplitude e| ≤ epsilon * (4 * Delta)) :
    |mediatorFullBottom n r (physicalMediatorHamiltonian n r Delta C left right
        (fun e => signedMediatorMember (J e)) amplitude) + 3 * ∑ e, |J e| -
      sourceMatrixBottom n (C + ∑ e, (J e : ℂ) • sourceHeisenbergMatrix n (left e) (right e))| ≤
        16 * Delta * epsilon ^ 3 := by
  have hbottom := mediatorFullBottom_unitary n r (fullMediatorBellMatrix n r)
    (physicalMediatorHamiltonian n r Delta C left right (fun e => signedMediatorMember (J e)) amplitude)
    (fullMediatorBellMatrix_gram n r) (fullMediatorBellMatrix_cogram n r)
  rw [physicalMediatorHamiltonian_transform] at hbottom
  rw [← hbottom]
  exact simultaneousMediator_bottom n r hDelta C hC left right hneq J amplitude hcal
    hepsilon hsmall hbound

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorOffsets
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scalar offsets relating the shifted mediator penalty to the
physical Hamiltonian containing only the specified Heisenberg bonds. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

theorem mediatorLocal_add (r : ℕ) (e : Fin r) (M N : Matrix (Fin 4) (Fin 4) ℂ) :
    mediatorLocal r e (M + N) = mediatorLocal r e M + mediatorLocal r e N := by
  ext a b
  simp only [mediatorLocal_apply, Matrix.add_apply, add_mul]

theorem mediatorLocal_smul (r : ℕ) (e : Fin r) (c : ℂ) (M : Matrix (Fin 4) (Fin 4) ℂ) :
    mediatorLocal r e (c • M) = c • mediatorLocal r e M := by
  ext a b
  simp only [mediatorLocal_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem physicalMediatorPenalty_offset (r : ℕ) (Delta : ℝ) :
    physicalMediatorPenalty r Delta =
      (Delta : ℂ) • (∑ e : Fin r, mediatorLocal r e heisenberg) +
        ((3 * r * Delta : ℝ) : ℂ) • 1 := by
  unfold physicalMediatorPenalty
  simp_rw [mediatorLocal_add, mediatorLocal_smul, mediatorLocal_one]
  rw [Finset.sum_add_distrib, smul_add]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  congr 1
  push_cast
  ring

theorem physicalMediatorHamiltonian_offset (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    physicalMediatorHamiltonian n r Delta C left right member amplitude =
      physicalRawMediatorHamiltonian n r Delta C left right member amplitude +
        ((3 * r * Delta : ℝ) : ℂ) • 1 := by
  unfold physicalMediatorHamiltonian physicalRawMediatorHamiltonian
  rw [physicalMediatorPenalty_offset, Matrix.kronecker_add, Matrix.kronecker_smul,
    Matrix.kronecker_smul, Matrix.one_kronecker_one]
  abel

theorem mediatorFullForm_add_scalar (n r : ℕ)
    (H : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ) (k : ℝ)
    (x : MediatorFullSpace n r) :
    ⟪x, spinMatrixOperator (H + (k : ℂ) • 1) x⟫_ℝ =
      ⟪x, spinMatrixOperator H x⟫_ℝ + k * ‖x‖ ^ 2 := by
  rw [spinMatrixOperator_add, spinMatrixOperator_smul, spinMatrixOperator_one,
    _root_.add_apply, _root_.smul_apply, one_apply_eq_self, inner_add_right]
  have hscalar : ⟪x, (k : ℂ) • x⟫_ℝ = k * ‖x‖ ^ 2 := by
    rw [HubbardGlobal.euclidean_real_inner, inner_smul_right, inner_self_eq_norm_sq_to_K]
    change ((k : ℂ) * (‖x‖ : ℂ) ^ 2).re = k * ‖x‖ ^ 2
    norm_cast
  rw [hscalar]

theorem mediatorFullBottom_add_scalar (n r : ℕ)
    (H : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ) (k : ℝ) :
    mediatorFullBottom n r (H + (k : ℂ) • 1) = mediatorFullBottom n r H + k := by
  let S := {e | ∃ x : MediatorFullSpace n r, 0 < ‖x‖ ^ 2 ∧
    e = ⟪x, spinMatrixOperator H x⟫_ℝ / ‖x‖ ^ 2}
  have hnonempty : S.Nonempty := by
    let x : MediatorFullSpace n r := EuclideanSpace.single ((fun _ => 0), mediatorVacuum r) 1
    refine ⟨_, x, ?_, rfl⟩
    simp [x]
  have hbounded : BddBelow S := by
    refine ⟨-‖spinMatrixOperator H‖, ?_⟩
    rintro e ⟨x, hx, rfl⟩
    have hform : |⟪x, spinMatrixOperator H x⟫_ℝ| ≤ ‖spinMatrixOperator H‖ * ‖x‖ ^ 2 := by
      calc
        _ ≤ ‖x‖ * ‖spinMatrixOperator H x‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖x‖ * (‖spinMatrixOperator H‖ * ‖x‖) :=
          mul_le_mul_of_nonneg_left ((spinMatrixOperator H).le_opNorm x) (norm_nonneg _)
        _ = _ := by ring
    exact (le_div_iff₀ hx).mpr (by nlinarith [(abs_le.mp hform).1])
  have hset : {e | ∃ x : MediatorFullSpace n r, 0 < ‖x‖ ^ 2 ∧
      e = ⟪x, spinMatrixOperator (H + (k : ℂ) • 1) x⟫_ℝ / ‖x‖ ^ 2} =
      (OrderIso.addRight k) '' S := by
    ext e
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟪x, spinMatrixOperator H x⟫_ℝ / ‖x‖ ^ 2, ⟨x, hx, rfl⟩, ?_⟩
      change _ + k = _
      rw [mediatorFullForm_add_scalar, add_div, mul_div_cancel_right₀ _ (ne_of_gt hx)]
    · rintro ⟨e, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      change _ + k = _
      rw [mediatorFullForm_add_scalar, add_div, mul_div_cancel_right₀ _ (ne_of_gt hx)]
  unfold mediatorFullBottom
  rw [hset]
  exact ((OrderIso.addRight k).map_csInf' hnonempty hbounded).symm

/-- Complete physical signed-to-positive mediator spectrum, with both
central-bond and spoke self-energy offsets displayed explicitly. -/
theorem physicalRawSimultaneousMediator_bottom (n r : ℕ) {Delta : ℝ} (hDelta : 0 < Delta)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    (left right : Fin r → Fin n) (hneq : ∀ e, left e ≠ right e)
    (J amplitude : Fin r → ℝ) (hcal : ∀ e, amplitude e ^ 2 = 2 * Delta * |J e|)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1 / 4)
    (hbound : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      6 * ∑ e, |amplitude e| ≤ epsilon * (4 * Delta)) :
    |mediatorFullBottom n r (physicalRawMediatorHamiltonian n r Delta C left right
        (fun e => signedMediatorMember (J e)) amplitude) + 3 * r * Delta + 3 * ∑ e, |J e| -
      sourceMatrixBottom n (C + ∑ e, (J e : ℂ) • sourceHeisenbergMatrix n (left e) (right e))| ≤
        16 * Delta * epsilon ^ 3 := by
  have h := physicalSimultaneousMediator_bottom n r hDelta C hC left right hneq J amplitude hcal
    hepsilon hsmall hbound
  rw [physicalMediatorHamiltonian_offset, mediatorFullBottom_add_scalar] at h
  exact h


/-- Canonical nonnegative spoke amplitudes, rather than arbitrary choices
satisfying only a square calibration. -/
theorem physicalCanonicalMediator_bottom (n r : ℕ) {Delta : ℝ} (hDelta : 0 < Delta)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    (left right : Fin r → Fin n) (hneq : ∀ e, left e ≠ right e) (J : Fin r → ℝ)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1 / 4)
    (hbound : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      6 * ∑ e, signedMediatorAmplitude Delta (J e) ≤ epsilon * (4 * Delta)) :
    |mediatorFullBottom n r (physicalRawMediatorHamiltonian n r Delta C left right
        (fun e => signedMediatorMember (J e)) (fun e => signedMediatorAmplitude Delta (J e))) +
        3 * r * Delta + 3 * ∑ e, |J e| -
      sourceMatrixBottom n (C + ∑ e, (J e : ℂ) • sourceHeisenbergMatrix n (left e) (right e))| ≤
        16 * Delta * epsilon ^ 3 := by
  apply physicalRawSimultaneousMediator_bottom n r hDelta C hC left right hneq J _
    (fun e => signedMediatorAmplitude_calibration hDelta.le (J e)) hepsilon hsmall
  simpa only [abs_of_nonneg (signedMediatorAmplitude_nonneg _ _)] using hbound

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorRounding
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full finite-spin spectral stability under rational approximation of the
physical mediator spokes. The infimum ranges over all entangled states. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

theorem mediatorRayleigh_abs_le (n r : ℕ)
    (H : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ)
    (x : MediatorFullSpace n r) :
    |⟪x, spinMatrixOperator H x⟫_ℝ| ≤ ‖spinMatrixOperator H‖ * ‖x‖ ^ 2 := by
  calc
    _ ≤ ‖x‖ * ‖spinMatrixOperator H x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖spinMatrixOperator H‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left ((spinMatrixOperator H).le_opNorm x) (norm_nonneg _)
    _ = _ := by ring

theorem mediatorRayleigh_boundedBelow (n r : ℕ)
    (H : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ) :
    BddBelow {e | ∃ x : MediatorFullSpace n r, 0 < ‖x‖ ^ 2 ∧
      e = ⟪x, spinMatrixOperator H x⟫_ℝ / ‖x‖ ^ 2} := by
  refine ⟨-‖spinMatrixOperator H‖, ?_⟩
  rintro e ⟨x, hx, rfl⟩
  apply (le_div_iff₀ hx).mpr
  have h := (abs_le.mp (mediatorRayleigh_abs_le n r H x)).1
  nlinarith

theorem mediatorRayleigh_nonempty (n r : ℕ)
    (H : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ) :
    {e | ∃ x : MediatorFullSpace n r, 0 < ‖x‖ ^ 2 ∧
      e = ⟪x, spinMatrixOperator H x⟫_ℝ / ‖x‖ ^ 2}.Nonempty := by
  let x : MediatorFullSpace n r := EuclideanSpace.single ((fun _ => 0), mediatorVacuum r) 1
  exact ⟨_, x, by simp [x], rfl⟩

theorem mediatorRayleigh_difference (n r : ℕ)
    (H K : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ)
    (x : MediatorFullSpace n r) (hx : 0 < ‖x‖ ^ 2) :
    |⟪x, spinMatrixOperator H x⟫_ℝ / ‖x‖ ^ 2 -
      ⟪x, spinMatrixOperator K x⟫_ℝ / ‖x‖ ^ 2| ≤ ‖spinMatrixOperator (H - K)‖ := by
  rw [← sub_div, ← inner_sub_right, ← _root_.sub_apply, ← spinMatrixOperator_sub,
    abs_div, abs_of_pos hx]
  exact (div_le_iff₀ hx).mpr (mediatorRayleigh_abs_le n r (H - K) x)

theorem mediatorFullBottom_lipschitz (n r : ℕ)
    (H K : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ) :
    |mediatorFullBottom n r H - mediatorFullBottom n r K| ≤ ‖spinMatrixOperator (H - K)‖ := by
  have hbound : mediatorFullBottom n r K - ‖spinMatrixOperator (H - K)‖ ≤
      mediatorFullBottom n r H := by
    apply le_csInf (mediatorRayleigh_nonempty n r H)
    rintro e ⟨x, hx, rfl⟩
    have htrial : mediatorFullBottom n r K ≤ ⟪x, spinMatrixOperator K x⟫_ℝ / ‖x‖ ^ 2 :=
      csInf_le (mediatorRayleigh_boundedBelow n r K) ⟨x, hx, rfl⟩
    have h := (abs_le.mp (mediatorRayleigh_difference n r H K x hx)).1
    linarith
  have hbound' : mediatorFullBottom n r H - ‖spinMatrixOperator (H - K)‖ ≤
      mediatorFullBottom n r K := by
    apply le_csInf (mediatorRayleigh_nonempty n r K)
    rintro e ⟨x, hx, rfl⟩
    have htrial : mediatorFullBottom n r H ≤ ⟪x, spinMatrixOperator H x⟫_ℝ / ‖x‖ ^ 2 :=
      csInf_le (mediatorRayleigh_boundedBelow n r H) ⟨x, hx, rfl⟩
    have h := (abs_le.mp (mediatorRayleigh_difference n r H K x hx)).2
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem spinMatrixOperator_conjugate_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U M : Matrix ι ι ℂ) (hGram : U.conjTranspose * U = 1)
    (hCogram : U * U.conjTranspose = 1) :
    ‖spinMatrixOperator (U * M * U.conjTranspose)‖ ≤ ‖spinMatrixOperator M‖ := by
  have hU := spinMatrixOperator_unitary_norm U hGram
  have hUs := spinMatrixOperator_unitary_norm U.conjTranspose
    (by simpa only [Matrix.conjTranspose_conjTranspose] using hCogram)
  rw [spinMatrixOperator_mul, spinMatrixOperator_mul]
  calc
    _ ≤ ‖spinMatrixOperator U‖ * ‖spinMatrixOperator M‖ *
        ‖spinMatrixOperator U.conjTranspose‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖spinMatrixOperator M‖ * 1 := by gcongr
    _ = _ := by ring

theorem physicalMediatorEdgeSpoke_operator_norm (n r : ℕ) (e : Fin r)
    (i j : Fin n) (member : Fin 2) :
    ‖spinMatrixOperator (physicalMediatorEdgeSpoke n r e i j member)‖ ≤ 6 := by
  let U := fullMediatorBellMatrix n r
  have hGram : U.conjTranspose * U = 1 := fullMediatorBellMatrix_gram n r
  have hCogram : U * U.conjTranspose = 1 := fullMediatorBellMatrix_cogram n r
  have hback : U * mediatorEdgeSpoke n r e i j member * U.conjTranspose =
      physicalMediatorEdgeSpoke n r e i j member := by
    rw [← physicalMediatorEdgeSpoke_transform]
    change U * (U.conjTranspose * physicalMediatorEdgeSpoke n r e i j member * U) * U.conjTranspose = _
    calc
      _ = (U * U.conjTranspose) * physicalMediatorEdgeSpoke n r e i j member *
          (U * U.conjTranspose) := by noncomm_ring
      _ = _ := by rw [hCogram]; simp
  rw [← hback]
  exact (spinMatrixOperator_conjugate_norm_le U _ hGram hCogram).trans
    (mediatorEdgeSpoke_operator_norm n r e i j member)

theorem physicalTotalMediatorSpokes_operator_norm (n r : ℕ)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    ‖spinMatrixOperator (physicalTotalMediatorSpokes n r left right member amplitude)‖ ≤
      6 * ∑ e, |amplitude e| := by
  unfold physicalTotalMediatorSpokes
  rw [spinMatrixOperator_sum]
  simp only [spinMatrixOperator_smul]
  calc
    _ ≤ ∑ e, ‖(amplitude e : ℂ) • spinMatrixOperator
        (physicalMediatorEdgeSpoke n r e (left e) (right e) (member e))‖ := norm_sum_le _ _
    _ ≤ ∑ e, 6 * |amplitude e| := by
      apply Finset.sum_le_sum
      intro e _
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right (physicalMediatorEdgeSpoke_operator_norm n r e _ _ _)
        (abs_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem physicalTotalMediatorSpokes_sub (n r : ℕ) (left right : Fin r → Fin n)
    (member : Fin r → Fin 2) (a b : Fin r → ℝ) :
    physicalTotalMediatorSpokes n r left right member a -
      physicalTotalMediatorSpokes n r left right member b =
        physicalTotalMediatorSpokes n r left right member (fun e => a e - b e) := by
  unfold physicalTotalMediatorSpokes
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [← sub_smul, Complex.ofReal_sub]

/-- The physical rounded Hamiltonian is compared on the entire tensor
space, without a restriction to the singlet kernel. -/
theorem physicalRawMediator_bottom_rounding (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (a b : Fin r → ℝ) :
    |mediatorFullBottom n r (physicalRawMediatorHamiltonian n r Delta C left right member a) -
      mediatorFullBottom n r (physicalRawMediatorHamiltonian n r Delta C left right member b)| ≤
        6 * ∑ e, |a e - b e| := by
  have hdiff : physicalRawMediatorHamiltonian n r Delta C left right member a -
      physicalRawMediatorHamiltonian n r Delta C left right member b =
        physicalTotalMediatorSpokes n r left right member (fun e => a e - b e) := by
    rw [← physicalTotalMediatorSpokes_sub]
    unfold physicalRawMediatorHamiltonian
    abel
  exact (mediatorFullBottom_lipschitz n r _ _).trans (by
    rw [hdiff]
    exact physicalTotalMediatorSpokes_operator_norm n r left right member _)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BinaryRoots
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! Bounded binary-root search required by the appendix's perfect-power check.
The search uses only comparisons and powers with exponent at most the input
bit bound; no unbounded Nat.nthRoot primitive is used by the algorithm. -/
namespace ExactQuantumFactoring.Primality

lemma rootSearch_spec {m e : ℕ} (_he : 0 < e) (k guess : ℕ)
    (hlo : guess^e ≤ m) (hhi : m < (guess+2^k)^e) :
    (rootSearch m e k guess)^e ≤ m ∧ m < (rootSearch m e k guess+1)^e := by
  induction k generalizing guess with
  | zero => simpa only [rootSearch,pow_zero] using And.intro hlo hhi
  | succ k ih =>
    simp only [rootSearch]
    by_cases hnext : (guess+2^k)^e ≤ m
    · rw [ite_eq_left hnext]
      apply ih _ hnext
      have hh : guess+2^k+2^k=guess+2^(k+1) := by rw [pow_succ]; omega
      rw [hh]
      exact hhi
    · rw [ite_eq_right hnext]
      exact ih _ hlo (by omega)

lemma boundedRoot_spec {m e n : ℕ} (he : 0 < e) (hm : m < 2^n) :
    (boundedRoot m e n)^e ≤ m ∧ m < (boundedRoot m e n+1)^e := by
  apply rootSearch_spec he n 0
  · simp [Nat.ne_of_gt he]
  · simp only [zero_add]
    exact hm.trans_le (Nat.le_self_pow he.ne' (2^n))

end ExactQuantumFactoring.Primality


end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_SquareRootProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bitwise integer square-root search and its actual polynomial-time
Boolean-stack implementation. This supplies arithmetic for finite-precision
geometric constants and mediator amplitudes without a real square-root oracle. -/

namespace ContinuumCoulomb.SquareRootProgram
open ExactQuantumFactoring.BitStackProgram

/-- The returned integer brackets the true square root by adjacent integers. -/
theorem root_spec (m : ℕ) : root m ^ 2 ≤ m ∧ m < (root m + 1) ^ 2 := by
  apply ExactQuantumFactoring.Primality.boundedRoot_spec (by decide)
  simpa only [Nat.size_eq_bits_len] using Nat.lt_size_self m

end ContinuumCoulomb.SquareRootProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_DyadicRootProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A computed dyadic square root of a nonnegative rational, with strict
error below one unit in the requested binary precision. Precision is unary;
numerator, denominator, and result are binary. -/

namespace ContinuumCoulomb.DyadicRootProgram
open ExactQuantumFactoring.BitStackProgram

theorem value_error (b N F : ℕ) (hF : 0 < F) :
    0 ≤ Real.sqrt ((N : ℝ) / F) - (value b N F : ℝ) ∧
      Real.sqrt ((N : ℝ) / F) - (value b N F : ℝ) < 1 / (2 : ℝ) ^ b := by
  let p : ℕ := 2 ^ b
  let m : ℕ := N * p ^ 2 / F
  let r : ℕ := SquareRootProgram.root m
  have hp : (0 : ℝ) < p := by dsimp [p]; positivity
  have hFr : (0 : ℝ) < F := by exact_mod_cast hF
  have hlo : r ^ 2 * F ≤ N * p ^ 2 :=
    (Nat.mul_le_mul_right F (SquareRootProgram.root_spec m).1).trans (Nat.div_mul_le_self _ _)
  have hhi : N * p ^ 2 < (r + 1) ^ 2 * F :=
    (Nat.div_lt_iff_lt_mul hF).mp (SquareRootProgram.root_spec m).2
  have hlo' : (r : ℝ) ^ 2 * F ≤ (N : ℝ) * (p : ℝ) ^ 2 := by exact_mod_cast hlo
  have hhi' : (N : ℝ) * (p : ℝ) ^ 2 < ((r : ℝ) + 1) ^ 2 * F := by exact_mod_cast hhi
  have hrad : 0 ≤ (N : ℝ) / F := by positivity
  have hsquare : (Real.sqrt ((N : ℝ) / F) * p) ^ 2 * F = (N : ℝ) * (p : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hrad]
    field_simp [hFr.ne']
  have hs : 0 ≤ Real.sqrt ((N : ℝ) / F) * p := by positivity
  have hslo : (r : ℝ) ^ 2 ≤ (Real.sqrt ((N : ℝ) / F) * p) ^ 2 := by
    apply (mul_le_mul_iff_left₀ hFr).mp
    rw [hsquare]
    exact hlo'
  have hshi : (Real.sqrt ((N : ℝ) / F) * p) ^ 2 < ((r : ℝ) + 1) ^ 2 := by
    apply (mul_lt_mul_iff_left₀ hFr).mp
    rw [hsquare]
    exact hhi'
  have hl : (r : ℝ) ≤ Real.sqrt ((N : ℝ) / F) * p := by
    nlinarith only [hslo, hs, show 0 ≤ (r : ℝ) by positivity]
  have hu : Real.sqrt ((N : ℝ) / F) * p < (r : ℝ) + 1 := by
    nlinarith only [hshi, hs, show 0 ≤ (r : ℝ) by positivity]
  have hvalue : (value b N F : ℝ) = (r : ℝ) / p := by
    simp only [value, Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat, p, r, m,
      Nat.cast_pow, Nat.cast_ofNat]
  have hpcast : (p : ℝ) = (2 : ℝ) ^ b := by simp only [p, Nat.cast_pow, Nat.cast_ofNat]
  rw [hvalue, ← hpcast]
  constructor
  · exact sub_nonneg.mpr ((div_le_iff₀ hp).mpr hl)
  · apply (lt_div_iff₀ hp).mpr
    rw [sub_mul, div_mul_cancel₀ _ hp.ne']
    linarith

end ContinuumCoulomb.DyadicRootProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorParameters
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial scales and rational positive spokes for one actual
simultaneous singlet-mediator stage. The norm hypothesis concerns the
unchanged low-block terms; no spectral conclusion is assumed. -/

namespace ContinuumCoulomb.MediatorParameters
open scoped BigOperators Kronecker InnerProductSpace

theorem scale_pos (r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G) : 0 < scale r W G := by
  unfold scale
  positivity

theorem scale_lower (r : ℕ) {W G : ℕ} (_hW : 0 < W) (hG : 0 < G) :
    16 * (r + 1) * W ≤ scale r W G := by
  have hrpow := Nat.le_self_pow (by decide : 3 ≠ 0) (r + 1)
  have hWpow := Nat.le_self_pow (by decide : 3 ≠ 0) W
  calc
    _ ≤ 1048576 * (r + 1) * W := by gcongr; norm_num
    _ ≤ 1048576 * (r + 1) ^ 3 * W ^ 3 * G := by
      calc
        _ ≤ 1048576 * (r + 1) ^ 3 * W ^ 3 := by gcongr
        _ ≤ _ := Nat.le_mul_of_pos_right _ hG
    _ = scale r W G := rfl

theorem epsilon_nonneg (r W G : ℕ) : 0 ≤ epsilon r W G := by unfold epsilon; positivity

theorem epsilon_small (r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G) :
    epsilon r W G ≤ 1 / 4 := by
  have hS : (0 : ℝ) < scale r W G := by exact_mod_cast scale_pos r hW hG
  have hl : 16 * ((r : ℝ) + 1) * W ≤ scale r W G := by exact_mod_cast scale_lower r hW hG
  unfold epsilon
  apply (div_le_iff₀ hS).mpr
  nlinarith

theorem second_order_error (r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G) :
    16 * (delta r W G : ℝ) * epsilon r W G ^ 3 = 1 / (1024 * (G : ℝ)) := by
  have hr : (r : ℝ) + 1 ≠ 0 := by positivity
  have hWr : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  have hGr : (G : ℝ) ≠ 0 := by exact_mod_cast hG.ne'
  unfold delta epsilon scale
  push_cast
  field_simp [hr, hWr, hGr]
  ring

theorem canonical_amplitude_upper (r : ℕ) {W G : ℕ} (hW : 0 < W) (_hG : 0 < G)
    {J : ℝ} (hJ : |J| ≤ W) :
    signedMediatorAmplitude (delta r W G : ℝ) J ≤ 2 * (scale r W G : ℝ) * W := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW2 : (W : ℝ) ≤ 2 * (W : ℝ) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left (hJ.trans hW2)
    (show 0 ≤ 2 * (scale r W G : ℝ) ^ 2 by positivity)
  unfold signedMediatorAmplitude
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  unfold delta
  push_cast
  nlinarith only [hmul]

theorem canonical_amplitude_lower (r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G)
    {J : ℝ} (hJ : 1 / (W : ℝ) ≤ |J|) :
    1 ≤ signedMediatorAmplitude (delta r W G : ℝ) J := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hSl : (W : ℝ) ≤ scale r W G := by
    have h := scale_lower r hW hG
    have : W ≤ scale r W G := by nlinarith
    exact_mod_cast this
  have hS1 : (1 : ℝ) ≤ scale r W G := by exact_mod_cast scale_pos r hW hG
  have hmul : 1 ≤ (W : ℝ) * |J| := by
    simpa only [mul_comm] using (div_le_iff₀ hWr).mp hJ
  have hSW : (W : ℝ) ≤ (scale r W G : ℝ) ^ 2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hSW (abs_nonneg J)
  unfold signedMediatorAmplitude
  apply Real.le_sqrt_of_sq_le
  unfold delta
  push_cast
  nlinarith

theorem rational_sqrt_error (b : ℕ) {q : ℚ} (hq : 0 ≤ q) :
    0 ≤ Real.sqrt (q : ℝ) - (DyadicRootProgram.value b q.num.toNat q.den : ℝ) ∧
      Real.sqrt (q : ℝ) - (DyadicRootProgram.value b q.num.toNat q.den : ℝ) < 1 / (2 : ℝ) ^ b := by
  have hnum : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq)
  have hnumq : (q.num.toNat : ℚ) = (q.num : ℚ) := by exact_mod_cast hnum
  have hrepr : (q.num.toNat : ℚ) / q.den = q := by rw [hnumq, Rat.num_div_den]
  have hre : (q.num.toNat : ℝ) / q.den = (q : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_natCast] using congrArg (fun x : ℚ => (x : ℝ)) hrepr
  simpa only [hre] using DyadicRootProgram.value_error b q.num.toNat q.den q.pos

theorem spoke_error (r W G : ℕ) (J : ℚ) :
    0 ≤ signedMediatorAmplitude (delta r W G : ℝ) (J : ℝ) - (spoke r W G J : ℝ) ∧
      signedMediatorAmplitude (delta r W G : ℝ) (J : ℝ) - (spoke r W G J : ℝ) <
        1 / (2 : ℝ) ^ precision r G := by
  have h := rational_sqrt_error (precision r G)
    (show 0 ≤ radicand r W G J by unfold radicand; positivity)
  simpa only [spoke, radicand, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast,
    Rat.cast_abs, signedMediatorAmplitude] using h

theorem spoke_pos (r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G)
    {J : ℚ} (hJ : 1 / (W : ℝ) ≤ |(J : ℝ)|) : 0 < spoke r W G J := by
  have ha := canonical_amplitude_lower r hW hG hJ
  have he := (spoke_error r W G J).2
  have hp : 1 / (2 : ℝ) ^ precision r G ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    exact one_le_pow₀ (by norm_num)
  have : (0 : ℝ) < spoke r W G J := by linarith
  exact_mod_cast this

theorem precision_power (r G : ℕ) :
    1048576 * (r + 1) * (G + 1) ≤ 2 ^ precision r G := by
  have hlinear (n : ℕ) : n + 1 ≤ 2 ^ n := by
    induction n with
    | zero => norm_num
    | succ n ih => rw [pow_succ]; omega
  have hr : r + 1 ≤ 2 ^ r := hlinear r
  have hG : G + 1 ≤ 2 ^ G := hlinear G
  unfold precision
  rw [pow_add, pow_add]
  norm_num
  nlinarith [Nat.mul_le_mul hr hG]

theorem rounding_error (r : ℕ) {G : ℕ} (hG : 0 < G) :
    6 * r * (1 / (2 : ℝ) ^ precision r G) ≤ 1 / (1024 * (G : ℝ)) := by
  have hp : 1048576 * ((r : ℝ) + 1) * ((G : ℝ) + 1) ≤ (2 : ℝ) ^ precision r G := by
    exact_mod_cast precision_power r G
  have hGr : (0 : ℝ) < G := by exact_mod_cast hG
  rw [mul_one_div]
  apply (le_div_iff₀ (by positivity : 0 < 1024 * (G : ℝ))).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ precision r G)).mpr
  have hrG : 0 ≤ (r : ℝ) * G := by positivity
  nlinarith [show 0 ≤ (r : ℝ) by positivity]

noncomputable section

/-- Explicit parameters discharge the small-perturbation hypotheses of the
actual simultaneous-mediator theorem, retaining arbitrary unchanged C. -/
theorem canonical_bottom (n r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    (left right : Fin r → Fin n) (hneq : ∀ e, left e ≠ right e)
    (J : Fin r → ℚ) (hJ : ∀ e, |(J e : ℝ)| ≤ W)
    (hNorm : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ ≤ W) :
    |mediatorFullBottom n r (physicalRawMediatorHamiltonian n r (delta r W G) C left right
        (fun e => signedMediatorMember (J e))
        (fun e => signedMediatorAmplitude (delta r W G) (J e))) +
      3 * r * delta r W G + 3 * ∑ e, |(J e : ℝ)| -
        sourceMatrixBottom n (C + ∑ e, (J e : ℂ) • sourceHeisenbergMatrix n (left e) (right e))| ≤
          1 / (1024 * (G : ℝ)) := by
  have hS : (1 : ℝ) ≤ scale r W G := by exact_mod_cast scale_pos r hW hG
  have hSp : (0 : ℝ) < scale r W G := by exact_mod_cast scale_pos r hW hG
  have hDelta : (0 : ℝ) < delta r W G := by
    unfold delta
    rw [Nat.cast_pow]
    exact pow_pos hSp 2
  have hamp : (∑ e : Fin r, signedMediatorAmplitude (delta r W G) (J e)) ≤
      r * (2 * (scale r W G : ℝ) * W) := by
    calc
      _ ≤ ∑ _e : Fin r, 2 * (scale r W G : ℝ) * W :=
        Finset.sum_le_sum (fun e _ => canonical_amplitude_upper r hW hG (hJ e))
      _ = _ := by simp
  have heq : epsilon r W G * (4 * (delta r W G : ℝ)) =
      16 * ((r : ℝ) + 1) * scale r W G * W := by
    unfold epsilon delta
    push_cast
    field_simp [hSp.ne']
    ring
  have hbound : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      6 * ∑ e, signedMediatorAmplitude (delta r W G) (J e) ≤
        epsilon r W G * (4 * (delta r W G : ℝ)) := by
    rw [heq]
    have hSW : (W : ℝ) ≤ (scale r W G : ℝ) * W := by
      nlinarith [show 0 ≤ (W : ℝ) by positivity]
    have hExtra : 0 ≤ 4 * (r : ℝ) * scale r W G * W := by positivity
    nlinarith only [hNorm, hamp, hSW, hExtra]
  have h := physicalCanonicalMediator_bottom n r hDelta C hC left right hneq
    (fun e => (J e : ℝ)) (epsilon_nonneg r W G) (epsilon_small r hW hG) hbound
  exact h.trans_eq (second_order_error r hW hG)

/-- A concrete positive rational-spoke stage, with a full-spin spectral
error bound including the arithmetic approximation of every spoke. -/
theorem rational_bottom (n r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    (left right : Fin r → Fin n) (hneq : ∀ e, left e ≠ right e)
    (J : Fin r → ℚ) (hJ : ∀ e, |(J e : ℝ)| ≤ W)
    (hJlower : ∀ e, 1 / (W : ℝ) ≤ |(J e : ℝ)|)
    (hNorm : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ ≤ W) :
    (∀ e, 0 < spoke r W G (J e)) ∧
    |mediatorFullBottom n r (physicalRawMediatorHamiltonian n r (delta r W G) C left right
        (fun e => signedMediatorMember (J e)) (fun e => (spoke r W G (J e) : ℝ))) +
      3 * r * delta r W G + 3 * ∑ e, |(J e : ℝ)| -
        sourceMatrixBottom n (C + ∑ e, (J e : ℂ) • sourceHeisenbergMatrix n (left e) (right e))| ≤
          1 / (512 * (G : ℝ)) := by
  refine ⟨fun e => spoke_pos r hW hG (hJlower e), ?_⟩
  have hcanonical := canonical_bottom n r hW hG C hC left right hneq J hJ hNorm
  have hsum : (∑ e, |(spoke r W G (J e) : ℝ) -
      signedMediatorAmplitude (delta r W G) (J e)|) ≤ r * (1 / (2 : ℝ) ^ precision r G) := by
    calc
      _ ≤ ∑ _e : Fin r, 1 / (2 : ℝ) ^ precision r G := by
        apply Finset.sum_le_sum
        intro e _
        rw [abs_sub_comm, abs_of_nonneg (spoke_error r W G (J e)).1]
        exact (spoke_error r W G (J e)).2.le
      _ = _ := by simp
  have hround := (physicalRawMediator_bottom_rounding n r (delta r W G) C left right
    (fun e => signedMediatorMember (J e)) (fun e => (spoke r W G (J e) : ℝ))
    (fun e => signedMediatorAmplitude (delta r W G) (J e))).trans
      (mul_le_mul_of_nonneg_left hsum (by norm_num))
  have hround' : _ ≤ 1 / (1024 * (G : ℝ)) := hround.trans (by
    have h := rounding_error r hG
    rwa [mul_assoc] at h)
  have htriangle := abs_add_le
    (mediatorFullBottom n r (physicalRawMediatorHamiltonian n r (delta r W G) C left right
      (fun e => signedMediatorMember (J e)) (fun e => (spoke r W G (J e) : ℝ))) -
      mediatorFullBottom n r (physicalRawMediatorHamiltonian n r (delta r W G) C left right
        (fun e => signedMediatorMember (J e))
        (fun e => signedMediatorAmplitude (delta r W G) (J e))))
    (mediatorFullBottom n r (physicalRawMediatorHamiltonian n r (delta r W G) C left right
      (fun e => signedMediatorMember (J e))
      (fun e => signedMediatorAmplitude (delta r W G) (J e))) +
      3 * r * delta r W G + 3 * ∑ e, |(J e : ℝ)| -
      sourceMatrixBottom n (C + ∑ e, (J e : ℂ) • sourceHeisenbergMatrix n (left e) (right e)))
  have hnormalize : (1 / (1024 * (G : ℝ))) + 1 / (1024 * (G : ℝ)) = 1 / (512 * (G : ℝ)) := by ring
  have hfin := htriangle.trans (add_le_add hround' hcanonical)
  rw [hnormalize] at hfin
  refine le_trans (le_of_eq ?_) hfin
  congr 1
  ring

end
end ContinuumCoulomb.MediatorParameters

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorGraph
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_old _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_fresh _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.ContinuumCoulomb.qmaSubdivisionCell_fresh _root_.OAI.ContinuumCoulomb.qmaSubdivisionCell_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit ordinary-spin coordinates for a simultaneous mediator stage.
The new sites are the two actual members of every fresh pair. -/

noncomputable section
namespace ContinuumCoulomb.MediatorGraph
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

theorem submatrix_sum {ι κ α β γ : Type*} [Fintype γ]
    (M : γ → Matrix ι κ ℂ) (f : α → ι) (g : β → κ) :
    (∑ e, M e).submatrix f g = ∑ e, (M e).submatrix f g := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.sum_apply]

theorem submatrix_add_apply {ι κ α β : Type*} (M N : Matrix ι κ ℂ) (f : α → ι) (g : β → κ) :
    (M + N).submatrix f g = M.submatrix f g + N.submatrix f g := rfl

theorem submatrix_smul_apply {ι κ α β : Type*} (c : ℂ) (M : Matrix ι κ ℂ)
    (f : α → ι) (g : β → κ) : (c • M).submatrix f g = c • M.submatrix f g := rfl

theorem sum_kronecker {ι κ α β γ : Type*} [Fintype γ]
    (M : γ → Matrix ι κ ℂ) (N : Matrix α β ℂ) :
    (∑ e, M e) ⊗ₖ N = ∑ e, M e ⊗ₖ N := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  simp only [Matrix.kronecker_apply, Matrix.sum_apply, Finset.sum_mul]

theorem kronecker_sum {ι κ α β γ : Type*} [Fintype γ]
    (M : Matrix ι κ ℂ) (N : γ → Matrix α β ℂ) :
    M ⊗ₖ (∑ e, N e) = ∑ e, M ⊗ₖ N e := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  simp only [Matrix.kronecker_apply, Matrix.sum_apply, Finset.mul_sum]

theorem pairTensor_entry (A B : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 4) :
    twoSpinTensor A B a b =
      A (pairEquiv.symm a 0) (pairEquiv.symm b 0) *
        B (pairEquiv.symm a 1) (pairEquiv.symm b 1) := by
  fin_cases a <;> fin_cases b <;> rfl

/-- Splitting the ordinary spin tensor into old spins and actual two-spin
mediator pairs is an exact basis permutation. -/
theorem sourceTensor_joined (n r : ℕ) (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (B : Fin r → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) :
    (sourceTensor (n + r * 2) (joinedMatrices n r A B)).submatrix
      (basisEquiv n r) (basisEquiv n r) =
        sourceTensor n A ⊗ₖ mediatorTensor r (fun e => twoSpinTensor (B e 0) (B e 1)) := by
  ext p q
  change (∏ k, joinedMatrices n r A B k (basisEquiv n r p k) (basisEquiv n r q k)) = _
  rw [← (vertexEquiv n r).prod_comp]
  simp only [joinedMatrices, Equiv.symm_apply_apply]
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type]
  simp only [Sum.elim_inl, Sum.elim_inr, basisEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply]
  change (∏ i, A i (p.1 i) (q.1 i)) *
      (∏ e, ∏ σ, B e σ (pairEquiv.symm (p.2 e) σ) (pairEquiv.symm (q.2 e) σ)) =
    (∏ i, A i (p.1 i) (q.1 i)) * (∏ e, twoSpinTensor (B e 0) (B e 1) (p.2 e) (q.2 e))
  simp only [Fin.prod_univ_two, pairTensor_entry]

section Reindex
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem reindex_operator_apply (e : ι ≃ κ) (H : Matrix κ κ ℂ) (x : EuclideanSpace ℂ ι) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e (spinMatrixOperator (H.submatrix e e) x) =
      spinMatrixOperator H (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e x) := by
  ext k
  change (∑ j, H (e (e.symm k)) (e j) * x j) = ∑ j, H k j * x (e.symm j)
  simp only [Equiv.apply_symm_apply]
  simpa only [Equiv.symm_apply_apply] using
    e.sum_comp (fun j => H k j * x (e.symm j))

theorem reindex_form (e : ι ≃ κ) (H : Matrix κ κ ℂ) (x : EuclideanSpace ℂ ι) :
    ⟪x, spinMatrixOperator (H.submatrix e e) x⟫_ℝ =
      ⟪LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e x,
        spinMatrixOperator H (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e x)⟫_ℝ := by
  rw [← reindex_operator_apply]
  rw [HubbardGlobal.euclidean_real_inner, HubbardGlobal.euclidean_real_inner]
  exact congrArg Complex.re
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).inner_map_map x
      (spinMatrixOperator (H.submatrix e e) x)).symm

theorem normalizedBottom_reindex (e : ι ≃ κ) (H : Matrix κ κ ℂ) :
    normalizedBottom (H.submatrix e e) = normalizedBottom H := by
  unfold normalizedBottom
  congr 1
  ext a
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨U x, (U.norm_map x).trans hx, reindex_form e H x⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨U.symm x, (U.symm.norm_map x).trans hx, ?_⟩
    rw [reindex_form]
    change ⟪x, spinMatrixOperator H x⟫_ℝ = ⟪U (U.symm x), spinMatrixOperator H (U (U.symm x))⟫_ℝ
    rw [U.apply_symm_apply]

theorem reindex_operator_norm (e : ι ≃ κ) (H : Matrix κ κ ℂ) :
    ‖spinMatrixOperator (H.submatrix e e)‖ = ‖spinMatrixOperator H‖ := by
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have h := (spinMatrixOperator H).le_opNorm (U x)
    rw [← reindex_operator_apply] at h
    change ‖U (spinMatrixOperator (H.submatrix e e) x)‖ ≤ ‖spinMatrixOperator H‖ * ‖U x‖ at h
    rw [U.norm_map, U.norm_map] at h
    exact h
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have h := (spinMatrixOperator (H.submatrix e e)).le_opNorm (U.symm x)
    have hn : ‖spinMatrixOperator (H.submatrix e e) (U.symm x)‖ =
        ‖spinMatrixOperator H x‖ := by
      rw [← U.norm_map (spinMatrixOperator (H.submatrix e e) (U.symm x))]
      rw [reindex_operator_apply]
      change ‖spinMatrixOperator H (U (U.symm x))‖ = _
      rw [U.apply_symm_apply]
    rw [hn, U.symm.norm_map] at h
    exact h

theorem matrixForm_smul (H : Matrix ι ι ℂ) (a : ℝ) (x : EuclideanSpace ℂ ι) :
    ⟪a • x, spinMatrixOperator H (a • x)⟫_ℝ = a ^ 2 * ⟪x, spinMatrixOperator H x⟫_ℝ := by
  change ⟪a • x, (spinMatrixOperator H).restrictScalars ℝ (a • x)⟫_ℝ = _
  rw [map_smul, real_inner_smul_left, real_inner_smul_right]
  change a * (a * ⟪x, spinMatrixOperator H x⟫_ℝ) = _
  ring

theorem normalizedBottom_eq_rayleigh (H : Matrix ι ι ℂ) :
    normalizedBottom H = sInf {e | ∃ x : EuclideanSpace ℂ ι,
      0 < ‖x‖ ^ 2 ∧ e = ⟪x, spinMatrixOperator H x⟫_ℝ / ‖x‖ ^ 2} := by
  unfold normalizedBottom
  congr 1
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, by rw [hx]; norm_num, by rw [hx]; simp⟩
  · rintro ⟨x, hx, rfl⟩
    have hnx : ‖x‖ ≠ 0 := by intro h; simp [h] at hx
    refine ⟨(‖x‖⁻¹ : ℝ) • x, norm_smul_inv_norm (norm_ne_zero_iff.mp hnx), ?_⟩
    rw [matrixForm_smul]
    field_simp

end Reindex

theorem sourceMatrixBottom_eq_mediator (n r : ℕ)
    (H : Matrix (SourceSpinBasis (n + r * 2)) (SourceSpinBasis (n + r * 2)) ℂ) :
    sourceMatrixBottom (n + r * 2) H =
      mediatorFullBottom n r (H.submatrix (basisEquiv n r) (basisEquiv n r)) := by
  change normalizedBottom H = _
  rw [← normalizedBottom_reindex (basisEquiv n r) H, normalizedBottom_eq_rayleigh]
  rfl

theorem twoSpinTensor_one : twoSpinTensor (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [twoSpinTensor, Matrix.one_apply]

theorem localPauli_old (n r : ℕ) (i : Fin n) (μ : Fin 3) :
    (sourceLocalPauli (n + r * 2) (old n r i) μ).submatrix
      (basisEquiv n r) (basisEquiv n r) =
        sourceLocalPauli n i μ ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ) := by
  have hfun : (fun k => if k = old n r i then pauli μ else 1) =
      joinedMatrices n r (fun j => if j = i then pauli μ else 1) (fun _ _ => 1) := by
    funext k
    obtain ⟨a, rfl⟩ := (vertexEquiv n r).surjective k
    cases a with
    | inl j => simp [old, joinedMatrices, (vertexEquiv n r).injective.eq_iff]
    | inr a => simp [old, joinedMatrices, (vertexEquiv n r).injective.eq_iff]
  unfold sourceLocalPauli
  rw [hfun, sourceTensor_joined]
  simp only [twoSpinTensor_one, mediatorTensor_one]

theorem pairPauli (member : Fin 2) (μ : Fin 3) :
    twoSpinTensor (if (0 : Fin 2) = member then pauli μ else 1)
      (if (1 : Fin 2) = member then pauli μ else 1) = physicalMemberPauli member μ := by
  fin_cases member <;> simp [physicalMemberPauli, firstPauli, secondPauli]

theorem localPauli_fresh (n r : ℕ) (e : Fin r) (member : Fin 2) (μ : Fin 3) :
    (sourceLocalPauli (n + r * 2) (fresh n r e member) μ).submatrix
      (basisEquiv n r) (basisEquiv n r) =
        (1 : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) ⊗ₖ
          mediatorLocal r e (physicalMemberPauli member μ) := by
  have hfun : (fun k => if k = fresh n r e member then pauli μ else 1) =
      joinedMatrices n r (fun _ => 1)
        (fun f σ => if f = e ∧ σ = member then pauli μ else 1) := by
    funext k
    obtain ⟨a, rfl⟩ := (vertexEquiv n r).surjective k
    cases a with
    | inl j => simp [fresh, joinedMatrices, (vertexEquiv n r).injective.eq_iff]
    | inr a =>
      rcases a with ⟨f, σ⟩
      simp [fresh, joinedMatrices, (vertexEquiv n r).injective.eq_iff]
  unfold sourceLocalPauli
  rw [hfun, sourceTensor_joined, sourceTensor_one]
  congr 1
  unfold mediatorLocal
  congr 1
  funext f
  by_cases hf : f = e
  · simp only [hf, true_and, ite_true, if_true]
    exact pairPauli member μ
  · simp [hf, twoSpinTensor_one]

theorem heisenberg_old (n r : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (sourceHeisenbergMatrix (n + r * 2) (old n r i) (old n r j)).submatrix
      (basisEquiv n r) (basisEquiv n r) =
        sourceHeisenbergMatrix n i j ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ) := by
  rw [← sourceLocalPauli_sum _ _ _ (fun h => hij (old_injective n r h))]
  simp only [submatrix_sum, ← Matrix.submatrix_mul_equiv _ _ _ (basisEquiv n r) _,
    localPauli_old, ← Matrix.mul_kronecker_mul, one_mul]
  rw [← sum_kronecker, sourceLocalPauli_sum n i j hij]

theorem heisenberg_spoke (n r : ℕ) (i : Fin n) (e : Fin r) (member : Fin 2) :
    (sourceHeisenbergMatrix (n + r * 2) (old n r i) (fresh n r e member)).submatrix
      (basisEquiv n r) (basisEquiv n r) =
        ∑ μ : Fin 3, sourceLocalPauli n i μ ⊗ₖ
          mediatorLocal r e (physicalMemberPauli member μ) := by
  rw [← sourceLocalPauli_sum _ _ _ (old_ne_fresh n r i e member)]
  simp only [submatrix_sum, ← Matrix.submatrix_mul_equiv _ _ _ (basisEquiv n r) _,
    localPauli_old, localPauli_fresh, ← Matrix.mul_kronecker_mul, mul_one, one_mul]

theorem heisenberg_central (n r : ℕ) (e : Fin r) :
    (sourceHeisenbergMatrix (n + r * 2) (fresh n r e 0) (fresh n r e 1)).submatrix
      (basisEquiv n r) (basisEquiv n r) =
        (1 : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) ⊗ₖ
          mediatorLocal r e heisenberg := by
  have hne : fresh n r e 0 ≠ fresh n r e 1 := by
    intro h
    have := fresh_injective n r (a₁ := (e, 0)) (a₂ := (e, 1)) h
    have := congrArg Prod.snd this
    norm_num at this
  rw [← sourceLocalPauli_sum _ _ _ hne]
  simp only [submatrix_sum, ← Matrix.submatrix_mul_equiv _ _ _ (basisEquiv n r) _,
    localPauli_fresh, ← Matrix.mul_kronecker_mul, one_mul]
  simp only [physicalMemberPauli, ite_true, if_true, show (1 : Fin 2) ≠ 0 by decide, ite_false, if_false,
    mediatorLocal_mul_same]
  rw [← kronecker_sum]
  congr 1
  ext a b
  simp only [Matrix.sum_apply, mediatorLocal_apply, ← Finset.sum_mul]
  rw [← Matrix.sum_apply, sum_first_second_pauli]

/-- The emitted ordinary graph has exactly the physical central and
spoke matrices used in the proved simultaneous-mediator estimate. -/
theorem stageMatrix_physical (n q r : ℕ) (keepLeft keepRight : Fin q → Fin n)
    (hkeep : ∀ e, keepLeft e ≠ keepRight e) (keepWeight : Fin q → ℚ)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (Delta : ℚ)
    (amplitude : Fin r → ℚ) :
    (stageMatrix n q r keepLeft keepRight keepWeight left right member Delta amplitude).submatrix
      (basisEquiv n r) (basisEquiv n r) =
        physicalRawMediatorHamiltonian n r (Delta : ℝ)
          (sourceGraphMatrix n q keepLeft keepRight (fun e => (keepWeight e : ℝ)))
          left right member (fun e => (amplitude e : ℝ)) := by
  unfold stageMatrix sourceGraphMatrix
  rw [← (edgeEquiv q r).sum_comp]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two,
    stageLeft, stageRight, stageWeight, Equiv.symm_apply_apply, ite_true, if_true,
    show (1 : Fin 2) ≠ 0 by decide, ite_false, if_false, submatrix_add_apply, submatrix_sum,
    submatrix_smul_apply, heisenberg_old n r _ _ (hkeep _), heisenberg_central,
    heisenberg_spoke]
  unfold physicalRawMediatorHamiltonian physicalTotalMediatorSpokes physicalMediatorEdgeSpoke
  simp only [sum_kronecker, kronecker_sum, Matrix.smul_kronecker,
    Matrix.kronecker_smul, Finset.sum_add_distrib, smul_add, Finset.smul_sum]
  push_cast
  abel

theorem oldGraph_matrix (n q r : ℕ) (left right : Fin q → Fin n)
    (hneq : ∀ e, left e ≠ right e) (J : Fin q → ℝ) :
    (sourceGraphMatrix (n + r * 2) q (fun e => old n r (left e))
      (fun e => old n r (right e)) J).submatrix (basisEquiv n r) (basisEquiv n r) =
        sourceGraphMatrix n q left right J ⊗ₖ
          (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ) := by
  unfold sourceGraphMatrix
  simp only [submatrix_sum, submatrix_smul_apply, heisenberg_old n r _ _ (hneq _),
    Matrix.smul_kronecker, sum_kronecker]

theorem oldGraph_operator_norm (n q r : ℕ) (left right : Fin q → Fin n)
    (hneq : ∀ e, left e ≠ right e) (J : Fin q → ℝ) :
    ‖spinMatrixOperator (sourceGraphMatrix n q left right J ⊗ₖ
      (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ ≤ 3 * ∑ e, |J e| := by
  rw [← oldGraph_matrix n q r left right hneq J, reindex_operator_norm]
  exact sourceGraphMatrix_operator_norm _ q _ _
    (fun e h => hneq e (old_injective n r h)) J

theorem graph_star (n q : ℕ) (left right : Fin q → Fin n)
    (hneq : ∀ e, left e ≠ right e) (J : Fin q → ℝ) :
    (sourceGraphMatrix n q left right J).conjTranspose = sourceGraphMatrix n q left right J := by
  unfold sourceGraphMatrix
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Complex.star_def,
    Complex.conj_ofReal, sourceHeisenbergMatrix_star n _ _ (hneq _)]

/-- One ordinary, fully enumerated positive graph stage, with explicit
scales and rational spoke outputs. The only bounds concern entering
weights, unreplaced weights and the entering inverse precision. -/
theorem stage_bottom (n q r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G)
    (keepLeft keepRight : Fin q → Fin n) (hkeep : ∀ e, keepLeft e ≠ keepRight e)
    (keepWeight : Fin q → ℚ) (hkeepWeight : 3 * ∑ e, |(keepWeight e : ℝ)| ≤ W)
    (left right : Fin r → Fin n) (hneq : ∀ e, left e ≠ right e)
    (J : Fin r → ℚ) (hJ : ∀ e, |(J e : ℝ)| ≤ W)
    (hJlower : ∀ e, 1 / (W : ℝ) ≤ |(J e : ℝ)|) :
    |sourceMatrixBottom (n + r * 2)
        (stageMatrix n q r keepLeft keepRight keepWeight left right
          (fun e => signedMediatorMember (J e)) (MediatorParameters.delta r W G)
          (fun e => MediatorParameters.spoke r W G (J e))) +
      3 * r * MediatorParameters.delta r W G + 3 * ∑ e, |(J e : ℝ)| -
        sourceMatrixBottom n (sourceGraphMatrix n q keepLeft keepRight
          (fun e => (keepWeight e : ℝ)) + sourceGraphMatrix n r left right (fun e => (J e : ℝ)))| ≤
          1 / (512 * (G : ℝ)) := by
  have h := (MediatorParameters.rational_bottom n r hW hG
    (sourceGraphMatrix n q keepLeft keepRight (fun e => (keepWeight e : ℝ)))
    (graph_star n q keepLeft keepRight hkeep _) left right hneq J hJ hJlower
    ((oldGraph_operator_norm n q r keepLeft keepRight hkeep _).trans hkeepWeight)).2
  rw [sourceMatrixBottom_eq_mediator, stageMatrix_physical n q r keepLeft keepRight hkeep]
  simpa only [Rat.cast_natCast, Complex.ofReal_ratCast, sourceGraphMatrix] using h

end ContinuumCoulomb.MediatorGraph

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorScaleBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete weight and inverse-weight bounds for the three mediator
stages. Each bound is a fixed polynomial in entering unary parameters. -/

namespace ContinuumCoulomb.MediatorParameters

theorem spoke_lower_half (r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G)
    {J : ℚ} (hJ : 1 / (W : ℝ) ≤ |(J : ℝ)|) :
    (1 / 2 : ℝ) ≤ spoke r W G J := by
  have ha := canonical_amplitude_lower r hW hG hJ
  have he := (spoke_error r W G J).2
  have hpower : (2 : ℝ) ≤ (2 : ℝ) ^ precision r G := by
    exact_mod_cast Nat.le_self_pow (by unfold precision; omega : precision r G ≠ 0) 2
  have hp : 1 / (2 : ℝ) ^ precision r G ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hpower
  linarith

theorem spoke_upper (r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G)
    {J : ℚ} (hJ : |(J : ℝ)| ≤ W) :
    (spoke r W G J : ℝ) ≤ 2 * (scale r W G : ℝ) * W := by
  have he := (spoke_error r W G J).1
  have ha := canonical_amplitude_upper r hW hG hJ
  linarith

theorem secondWeight_two_le (r W G : ℕ) : 2 ≤ secondWeight r W G := by
  unfold secondWeight
  omega

theorem thirdWeight_two_le (r W G : ℕ) : 2 ≤ thirdWeight r W G := by
  unfold thirdWeight
  omega

theorem second_spoke_bounds (r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G)
    {J : ℚ} (hJ : |(J : ℝ)| ≤ W) (hJlower : 1 / (W : ℝ) ≤ |(J : ℝ)|) :
    1 / (secondWeight r W G : ℝ) ≤ |(spoke r W G J : ℝ)| ∧
      |(spoke r W G J : ℝ)| ≤ secondWeight r W G := by
  have hl := spoke_lower_half r hW hG hJlower
  have hu := spoke_upper r hW hG hJ
  have htwo : (2 : ℝ) ≤ secondWeight r W G := by exact_mod_cast secondWeight_two_le r W G
  have hmax : 2 * (scale r W G : ℝ) * W ≤ secondWeight r W G := by
    exact_mod_cast (show 2 * scale r W G * W ≤ secondWeight r W G by unfold secondWeight; omega)
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ spoke r W G J)]
  exact ⟨(one_div_le_one_div_of_le (by norm_num) htwo).trans hl, hu.trans hmax⟩

theorem third_spoke_bounds (r : ℕ) {W G : ℕ} (hG : 0 < G)
    {J : ℚ} (hJ : |(J : ℝ)| ≤ secondWeight r W G)
    (hJlower : 1 / (secondWeight r W G : ℝ) ≤ |(J : ℝ)|) :
    1 / (thirdWeight r W G : ℝ) ≤
        |(spoke (2 * r) (secondWeight r W G) G J : ℝ)| ∧
      |(spoke (2 * r) (secondWeight r W G) G J : ℝ)| ≤ thirdWeight r W G := by
  have hW2 : 0 < secondWeight r W G := lt_of_lt_of_le (by norm_num) (secondWeight_two_le r W G)
  have hl := spoke_lower_half (2 * r) hW2 hG hJlower
  have hu := spoke_upper (2 * r) hW2 hG hJ
  have htwo : (2 : ℝ) ≤ thirdWeight r W G := by exact_mod_cast thirdWeight_two_le r W G
  have hmax : 2 * (scale (2 * r) (secondWeight r W G) G : ℝ) * secondWeight r W G ≤
      thirdWeight r W G := by
    exact_mod_cast (show 2 * scale (2 * r) (secondWeight r W G) G * secondWeight r W G ≤
      thirdWeight r W G by unfold thirdWeight; omega)
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ spoke (2 * r) (secondWeight r W G) G J)]
  exact ⟨(one_div_le_one_div_of_le (by norm_num) htwo).trans hl, hu.trans hmax⟩

theorem third_central_bounds (r : ℕ) {W G : ℕ} (hG : 0 < G) :
    1 / (thirdWeight r W G : ℝ) ≤ delta (2 * r) (secondWeight r W G) G ∧
      (delta (2 * r) (secondWeight r W G) G : ℝ) ≤ thirdWeight r W G := by
  have hW2 : 0 < secondWeight r W G := lt_of_lt_of_le (by norm_num) (secondWeight_two_le r W G)
  have hdelta : (1 : ℝ) ≤ delta (2 * r) (secondWeight r W G) G := by
    have hp : 0 < delta (2 * r) (secondWeight r W G) G := by
      unfold delta
      exact pow_pos (scale_pos (2 * r) hW2 hG) 2
    exact_mod_cast hp
  have htwo : (2 : ℝ) ≤ thirdWeight r W G := by exact_mod_cast thirdWeight_two_le r W G
  refine ⟨(one_div_le_one_div_of_le (by norm_num) htwo).trans (by linarith), ?_⟩
  exact_mod_cast (show delta (2 * r) (secondWeight r W G) G ≤ thirdWeight r W G by
    unfold thirdWeight; omega)

end ContinuumCoulomb.MediatorParameters

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorIteration
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_left _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_right _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_toList _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_weight _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.toList_length _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three actual mediator stages. Only the original central bonds
survive the last subdivision; each original spoke becomes a nine-link
path, giving eighteen new spins and nineteen positive bonds per edge. -/

namespace ContinuumCoulomb.MediatorIteration
open Matrix MediatorGraph
open scoped BigOperators Kronecker InnerProductSpace

theorem empty_noLoops (n : ℕ) : (empty n).NoLoops := by intro e; exact Fin.elim0 e

theorem lift_noLoops {n q : ℕ} (r : ℕ) (F : Bonds n q) (hF : F.NoLoops) :
    (lift r F).NoLoops := by
  intro e h
  exact hF e (old_injective n r h)

theorem central_noLoops (n r : ℕ) (Delta : ℚ) : (central n r Delta).NoLoops := by
  intro e h
  have hpair := fresh_injective n r (a₁ := (e, 0)) (a₂ := (e, 1)) h
  have := congrArg Prod.snd hpair
  norm_num at this

theorem spokes_noLoops {n r : ℕ} (F : Bonds n r) (member : Fin r → Fin 2)
    (amplitude : Fin r → ℚ) : (spokes F member amplitude).NoLoops := by
  intro a
  exact old_ne_fresh n r _ _ _

theorem join_noLoops {n q r : ℕ} (F : Bonds n q) (K : Bonds n r)
    (hF : F.NoLoops) (hK : K.NoLoops) : (join F K).NoLoops := by
  intro a
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective a
  cases b with
  | inl e => simpa [join] using hF e
  | inr e => simpa [join] using hK e

theorem join_matrix {n q r : ℕ} (F : Bonds n q) (K : Bonds n r) :
    (join F K).matrix = F.matrix + K.matrix := by
  unfold Bonds.matrix sourceGraphMatrix
  rw [← finSumFinEquiv.sum_comp]
  simp only [Fintype.sum_sum_type, join, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]

theorem empty_matrix (n : ℕ) : (empty n).matrix = 0 := by
  simp [Bonds.matrix, sourceGraphMatrix]

theorem stage_matrix_split {n q r : ℕ} (K : Bonds n q) (F : Bonds n r)
    (member : Fin r → Fin 2) (Delta : ℚ) (amplitude : Fin r → ℚ) :
    stageMatrix n q r K.left K.right K.weight F.left F.right member Delta amplitude =
      (lift r K).matrix + (central n r Delta).matrix + (spokes F member amplitude).matrix := by
  unfold stageMatrix sourceGraphMatrix
  rw [← (edgeEquiv q r).sum_comp]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, stageLeft, stageRight, stageWeight,
    Equiv.symm_apply_apply]
  unfold Bonds.matrix sourceGraphMatrix
  rw [← (finProdFinEquiv : Fin r × Fin 2 ≃ Fin (r * 2)).sum_comp]
  simp only [Fintype.sum_prod_type, spokes, Equiv.symm_apply_apply, lift, central]
  push_cast
  abel

theorem member_eq (J : ℚ) : member J = signedMediatorMember (J : ℝ) := by
  simp only [member, signedMediatorMember, Rat.cast_lt_zero]

theorem join_weight_property {n q r : ℕ} (F : Bonds n q) (K : Bonds n r)
    (P : ℚ → Prop) (hF : ∀ e, P (F.weight e)) (hK : ∀ e, P (K.weight e)) :
    ∀ e, P ((join F K).weight e) := by
  intro e
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective e
  cases a with
  | inl a => simpa [join] using hF a
  | inr a => simpa [join] using hK a

theorem firstSpokes_bounds {n r W G : ℕ} (F : Bonds n r) (hW : 0 < W) (hG : 0 < G)
    (hJ : ∀ e, |(F.weight e : ℝ)| ≤ W) (hJl : ∀ e, 1 / (W : ℝ) ≤ |(F.weight e : ℝ)|) :
    ∀ e, 1 / (secondBound r W G : ℝ) ≤ |((firstSpokes F W G).weight e : ℝ)| ∧
      |((firstSpokes F W G).weight e : ℝ)| ≤ secondBound r W G := by
  intro e
  exact MediatorParameters.second_spoke_bounds r hW hG (hJ _) (hJl _)

theorem secondPaths_bounds {n r W G : ℕ} (F : Bonds n r) (hW : 0 < W) (hG : 0 < G)
    (hJ : ∀ e, |(F.weight e : ℝ)| ≤ W) (hJl : ∀ e, 1 / (W : ℝ) ≤ |(F.weight e : ℝ)|) :
    ∀ e, 1 / (thirdBound r W G : ℝ) ≤ |((secondPaths F W G).weight e : ℝ)| ∧
      |((secondPaths F W G).weight e : ℝ)| ≤ thirdBound r W G := by
  apply join_weight_property _ _
    (fun J => 1 / (thirdBound r W G : ℝ) ≤ |(J : ℝ)| ∧ |(J : ℝ)| ≤ thirdBound r W G)
  · intro e
    have h := MediatorParameters.third_central_bounds r (W := W) hG
    change 1 / (thirdBound r W G : ℝ) ≤ |(deltaTwo r W G : ℝ)| ∧
      |(deltaTwo r W G : ℝ)| ≤ thirdBound r W G
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ deltaTwo r W G)]
    simpa only [deltaTwo, secondBound, thirdBound, Nat.mul_comm] using h
  · intro e
    have hbound := firstSpokes_bounds F hW hG hJ hJl (finProdFinEquiv.symm e).1
    have h := MediatorParameters.third_spoke_bounds r hG hbound.2 hbound.1
    simpa only [secondSpokes, spokes, secondBound, thirdBound, Nat.mul_comm] using h

theorem firstCentral_weight_sum {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    (∑ e, |((firstCentral F W G).weight e : ℝ)|) = r * (deltaOne r W G : ℝ) := by
  simp [firstCentral, central]

theorem firstCentral_bound {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    3 * ∑ e, |((firstCentral F W G).weight e : ℝ)| ≤ secondBound r W G := by
  rw [firstCentral_weight_sum]
  rw [← mul_assoc]
  have h : 3 * r * deltaOne r W G ≤ secondBound r W G := by
    unfold deltaOne secondBound MediatorParameters.secondWeight
    omega
  exact_mod_cast h

theorem retainedCentral_bound {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    3 * ∑ e, |((retainedCentral F W G).weight e : ℝ)| ≤ thirdBound r W G := by
  change 3 * ∑ e, |((firstCentral F W G).weight e : ℝ)| ≤ thirdBound r W G
  rw [firstCentral_weight_sum]
  rw [← mul_assoc]
  have h : 3 * r * deltaOne r W G ≤ thirdBound r W G := by
    unfold deltaOne thirdBound MediatorParameters.thirdWeight
    omega
  exact_mod_cast h

theorem lift_empty_matrix (n r : ℕ) : (lift r (empty n)).matrix = 0 := by
  simp [Bonds.matrix, sourceGraphMatrix]

theorem family_stage_bound {n q r W G : ℕ} (K : Bonds n q) (F : Bonds n r)
    (hK : K.NoLoops) (hF : F.NoLoops) (hW : 0 < W) (hG : 0 < G)
    (hKweight : 3 * ∑ e, |(K.weight e : ℝ)| ≤ W)
    (hJ : ∀ e, |(F.weight e : ℝ)| ≤ W) (hJl : ∀ e, 1 / (W : ℝ) ≤ |(F.weight e : ℝ)|) :
    |sourceMatrixBottom (n + r * 2)
        ((lift r K).matrix + (central n r (MediatorParameters.delta r W G)).matrix +
          (spokes F (fun e => member (F.weight e))
            (fun e => MediatorParameters.spoke r W G (F.weight e))).matrix) +
      3 * r * MediatorParameters.delta r W G + 3 * ∑ e, |(F.weight e : ℝ)| -
        sourceMatrixBottom n (K.matrix + F.matrix)| ≤ 1 / (512 * (G : ℝ)) := by
  have h := MediatorGraph.stage_bottom n q r hW hG K.left K.right hK K.weight hKweight
    F.left F.right hF F.weight hJ hJl
  rw [stage_matrix_split] at h
  simpa only [member_eq, Bonds.matrix] using h

theorem first_stage {n r W G : ℕ} (F : Bonds n r) (hF : F.NoLoops)
    (hW : 0 < W) (hG : 0 < G) (hJ : ∀ e, |(F.weight e : ℝ)| ≤ W)
    (hJl : ∀ e, 1 / (W : ℝ) ≤ |(F.weight e : ℝ)|) :
    |sourceMatrixBottom (n + r * 2) (firstGraph F W G).matrix +
      3 * r * deltaOne r W G + 3 * ∑ e, |(F.weight e : ℝ)| -
        sourceMatrixBottom n F.matrix| ≤ 1 / (512 * (G : ℝ)) := by
  have h := family_stage_bound (empty n) F (empty_noLoops n) hF hW hG (by simp) hJ hJl
  rw [lift_empty_matrix, empty_matrix, zero_add, zero_add] at h
  simpa only [firstGraph, join_matrix, firstCentral, firstSpokes, deltaOne] using h

theorem second_stage {n r W G : ℕ} (F : Bonds n r) (hW : 0 < W) (hG : 0 < G)
    (hJ : ∀ e, |(F.weight e : ℝ)| ≤ W) (hJl : ∀ e, 1 / (W : ℝ) ≤ |(F.weight e : ℝ)|) :
    |sourceMatrixBottom (n + r * 2 + r * 2 * 2) (secondGraph F W G).matrix +
      3 * (r * 2) * deltaTwo r W G + 3 * ∑ e, |((firstSpokes F W G).weight e : ℝ)| -
        sourceMatrixBottom (n + r * 2) (firstGraph F W G).matrix| ≤ 1 / (512 * (G : ℝ)) := by
  have hW2 : 0 < secondBound r W G := lt_of_lt_of_le (by norm_num)
    (MediatorParameters.secondWeight_two_le r W G)
  have hbounds := firstSpokes_bounds F hW hG hJ hJl
  have h := family_stage_bound (firstCentral F W G) (firstSpokes F W G)
    (central_noLoops _ _ _) (spokes_noLoops _ _ _) hW2 hG
    (firstCentral_bound F W G) (fun e => (hbounds e).2) (fun e => (hbounds e).1)
  simpa only [secondGraph, firstGraph, join_matrix, retainedCentral, secondPaths,
    secondCentral, secondSpokes, deltaTwo, add_assoc, Nat.cast_mul, Nat.cast_ofNat] using h

theorem third_stage {n r W G : ℕ} (F : Bonds n r) (hW : 0 < W) (hG : 0 < G)
    (hJ : ∀ e, |(F.weight e : ℝ)| ≤ W) (hJl : ∀ e, 1 / (W : ℝ) ≤ |(F.weight e : ℝ)|) :
    |sourceMatrixBottom (n + r * 2 + r * 2 * 2 + (r * 2 + r * 2 * 2) * 2) (finalGraph F W G).matrix +
      3 * (r * 2 + r * 2 * 2) * deltaThree r W G +
        3 * ∑ e, |((secondPaths F W G).weight e : ℝ)| -
      sourceMatrixBottom (n + r * 2 + r * 2 * 2) (secondGraph F W G).matrix| ≤
        1 / (512 * (G : ℝ)) := by
  have hW3 : 0 < thirdBound r W G := lt_of_lt_of_le (by norm_num)
    (MediatorParameters.thirdWeight_two_le r W G)
  have hbounds := secondPaths_bounds F hW hG hJ hJl
  have h := family_stage_bound (retainedCentral F W G) (secondPaths F W G)
    (lift_noLoops _ _ (central_noLoops _ _ _))
    (join_noLoops _ _ (central_noLoops _ _ _) (spokes_noLoops _ _ _))
    hW3 hG (retainedCentral_bound F W G) (fun e => (hbounds e).2) (fun e => (hbounds e).1)
  simpa only [finalGraph, secondGraph, join_matrix, thirdCentral, thirdSpokes,
    deltaThree, add_assoc, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using h

/-- Three concrete rational graph stages give the promised finite-spin
energy comparison, including all three exact rational scalar offsets. -/
theorem three_stage_bottom {n r W G : ℕ} (F : Bonds n r) (hF : F.NoLoops)
    (hW : 0 < W) (hG : 0 < G) (hJ : ∀ e, |(F.weight e : ℝ)| ≤ W)
    (hJl : ∀ e, 1 / (W : ℝ) ≤ |(F.weight e : ℝ)|) :
    |sourceMatrixBottom (n + r * 2 + r * 2 * 2 + (r * 2 + r * 2 * 2) * 2) (finalGraph F W G).matrix +
      (offset F W G : ℝ) - sourceMatrixBottom n F.matrix| ≤ 3 / (512 * (G : ℝ)) := by
  have h1 := first_stage F hF hW hG hJ hJl
  have h2 := second_stage F hW hG hJ hJl
  have h3 := third_stage F hW hG hJ hJl
  have h12 := (abs_add_le _ _).trans (add_le_add h2 h1)
  have h123 := (abs_add_le _ _).trans (add_le_add h3 h12)
  convert h123 using 1
  all_goals try with_reducible_and_instances rfl
  · congr 1
    simp only [offset, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat,
      Rat.cast_sum, Rat.cast_abs]
    ring
  · ring

end ContinuumCoulomb.MediatorIteration

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceSpectrum
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_coordinate _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_edges _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_lower _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_upper _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_vertices _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.contactEdge_left _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.contactEdge_right _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Source spectral bottom and rational normalization

The bottom ranges over every normalized many-spin vector. Uniform
coefficient error controls that variational bottom and the YES/NO
thresholds of the square-lattice Heisenberg problem.
-/

noncomputable section

namespace ContinuumCoulomb

open scoped BigOperators

/-- Uniform perturbation of every state controls both variational bottoms. -/
theorem realSourceGroundEnergy_rounding (d : SquareLatticeHeisenberg)
    (rounded : Fin d.edges → ℚ) :
    |realSourceGroundEnergy (d.withCoefficients rounded) - realSourceGroundEnergy d| ≤
      3 * ∑ e, |(d.coefficient e : ℝ) - (rounded e : ℝ)| := by
  let ε : ℝ := 3 * ∑ e, |(d.coefficient e : ℝ) - (rounded e : ℝ)|
  have hpoint (u : SourceSpinVector d.vertices) (hu : sourceSpinMass u = 1) :
      |sourceHamiltonianForm d u - sourceHamiltonianForm (d.withCoefficients rounded) u| ≤
        ε :=
    sourceHamiltonianForm_rounding d (fun e => (rounded e : ℝ)) u hu
  have hl : realSourceGroundEnergy (d.withCoefficients rounded) - ε ≤
      realSourceGroundEnergy d := by
    apply realSourceGroundEnergy_lower_of_forall
    intro u hu
    have h := (abs_le.mp (hpoint u hu)).1
    have htrial := realSourceGroundEnergy_le_trial (d.withCoefficients rounded) u hu
    linarith
  have hu : realSourceGroundEnergy d - ε ≤
      realSourceGroundEnergy (d.withCoefficients rounded) := by
    apply realSourceGroundEnergy_lower_of_forall
    intro u hu
    have h := (abs_le.mp (hpoint u hu)).2
    have htrial := realSourceGroundEnergy_le_trial d u hu
    linarith
  apply abs_le.mpr
  constructor <;> dsimp [ε] at * <;> linarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceMatrix
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_coordinate _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_edges _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_lower _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_upper _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_vertices _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.contactEdge_left _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.contactEdge_right _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the encoded source's original swap-form variational
energy with the complete finite matrix used by all mediator stages. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace

theorem sourceSpinMass_norm_sq {n : ℕ} (p : MediatorLowSpace n) :
    sourceSpinMass (fun s => p s) = ‖p‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [sourceSpinMass, Complex.normSq_eq_norm_sq]

theorem sourceGraphMatrix_action (d : SquareLatticeHeisenberg)
    (u : SourceSpinVector d.vertices) :
    d.bonds.matrix *ᵥ u = sourceHamiltonian d u := by
  unfold MediatorIteration.Bonds.matrix SquareLatticeHeisenberg.bonds sourceGraphMatrix
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, sourceHeisenbergMatrix_mulVec,
    ]
  funext s
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_ratCast]
  rfl

theorem sourceGraphMatrix_form (d : SquareLatticeHeisenberg)
    (p : MediatorLowSpace d.vertices) :
    ⟪p, spinMatrixOperator d.bonds.matrix p⟫_ℝ = sourceHamiltonianForm d (fun s => p s) := by
  rw [HubbardGlobal.euclidean_real_inner, sourceHamiltonianForm_eq_expectation]
  have hact : spinMatrixOperator d.bonds.matrix p =
      WithLp.toLp 2 (sourceHamiltonian d (fun s => p s)) := by
    ext s
    exact congrFun (sourceGraphMatrix_action d (fun s => p s)) s
  rw [hact, PiLp.inner_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  simp only [RCLike.inner_apply, mul_comm]
  rfl

/-- The mediator input is the actual source energy in the published promise. -/
theorem sourceMatrixBottom_eq_realSource (d : SquareLatticeHeisenberg) :
    sourceMatrixBottom d.vertices d.bonds.matrix = realSourceGroundEnergy d := by
  obtain ⟨p, hp, hb, hmin⟩ := sourceMatrixBottom_minimizer d.vertices d.bonds.matrix
  have hmass : sourceSpinMass (fun s => p s) = 1 := by rw [sourceSpinMass_norm_sq, hp]; norm_num
  apply le_antisymm
  · apply realSourceGroundEnergy_lower_of_forall
    intro u hu
    let q : MediatorLowSpace d.vertices := WithLp.toLp 2 u
    have hq : ‖q‖ = 1 := by
      have hs : ‖q‖ ^ 2 = 1 := (sourceSpinMass_norm_sq q).symm.trans hu
      exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa using hs)
    rw [hb]
    simpa only [sourceGraphMatrix_form, q] using hmin q hq
  · rw [hb, sourceGraphMatrix_form]
    exact realSourceGroundEnergy_le_trial d (fun s => p s) hmass

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HeisenbergOffsets
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scalar offsets and positive homogeneity connecting the ordinary
finite-spin Hamiltonian with the Hubbard superexchange source form. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace

variable {Edge : Type*} [Fintype Edge]

theorem sourceMatrixForm_smul (n : ℕ)
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (a : ℝ)
    (p : MediatorLowSpace n) :
    ⟪p, spinMatrixOperator ((a : ℂ) • M) p⟫_ℝ = a * ⟪p, spinMatrixOperator M p⟫_ℝ := by
  rw [spinMatrixOperator_smul, _root_.smul_apply,
    HubbardGlobal.euclidean_real_inner, inner_smul_right, HubbardGlobal.euclidean_real_inner]
  change ((a : ℂ) * ⟪p, spinMatrixOperator M p⟫_ℂ).re =
    a * (⟪p, spinMatrixOperator M p⟫_ℂ).re
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem sourceMatrixBottom_smul (n : ℕ)
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) {a : ℝ} (ha : 0 ≤ a) :
    sourceMatrixBottom n ((a : ℂ) • M) = a * sourceMatrixBottom n M := by
  obtain ⟨p, hp, hb, hmin⟩ := sourceMatrixBottom_minimizer n M
  obtain ⟨q, hq, hbq, hminq⟩ := sourceMatrixBottom_minimizer n ((a : ℂ) • M)
  rw [hb, hbq, sourceMatrixForm_smul]
  apply le_antisymm
  · have h := hminq p hp
    rw [sourceMatrixForm_smul, sourceMatrixForm_smul] at h
    exact h
  · exact mul_le_mul_of_nonneg_left (hmin q hq) ha

theorem finiteHeisenbergBottom_smul (n : ℕ) (left right : Edge → Fin n) (J : Edge → ℝ)
    {a : ℝ} (ha : 0 ≤ a) :
    finiteHeisenbergBottom n left right (fun e => a * J e) =
      a * finiteHeisenbergBottom n left right J := by
  have hmat : finiteHeisenbergMatrix n left right (fun e => a * J e) =
      (a : ℂ) • finiteHeisenbergMatrix n left right J := by
    simp only [finiteHeisenbergMatrix, Finset.smul_sum, Complex.ofReal_mul, smul_smul]
  rw [finiteHeisenbergBottom, hmat, sourceMatrixBottom_smul n _ ha]
  rfl

theorem finiteHeisenbergBottom_bonds {n r : ℕ} (F : MediatorIteration.Bonds n r) :
    finiteHeisenbergBottom n F.left F.right (fun e => (F.weight e : ℝ)) =
      sourceMatrixBottom n F.matrix := rfl

namespace HubbardGlobal

theorem graphSourceAction_matrix (m : ℕ) (left right : Edge → Fin (m + 1))
    (J : Edge → ℝ) (u : SourceSpinVector (m + 1)) :
    (finiteHeisenbergMatrix (m + 1) left right J - ((∑ e, J e : ℝ) : ℂ) • 1) *ᵥ u =
      graphSourceAction m left right (fun e => (J e : ℂ)) u := by
  rw [Matrix.sub_mulVec]
  simp only [finiteHeisenbergMatrix, Matrix.sum_mulVec, Matrix.smul_mulVec,
    sourceHeisenbergMatrix_mulVec, Matrix.one_mulVec]
  ext s
  simp only [graphSourceAction, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_sub_distrib, mul_sub, Complex.ofReal_sum, Finset.sum_mul]

theorem graphSourceForm_matrix (m : ℕ) (left right : Edge → Fin (m + 1)) (J : Edge → ℝ)
    (p : MediatorLowSpace (m + 1)) :
    graphSourceForm m left right J (fun s => p s) =
      ⟪p, spinMatrixOperator
        (finiteHeisenbergMatrix (m + 1) left right J - ((∑ e, J e : ℝ) : ℂ) • 1) p⟫_ℝ := by
  rw [graphSourceForm_expectation, euclidean_real_inner]
  have hact : spinMatrixOperator
      (finiteHeisenbergMatrix (m + 1) left right J - ((∑ e, J e : ℝ) : ℂ) • 1) p =
        WithLp.toLp 2 (graphSourceAction m left right (fun e => (J e : ℂ)) (fun s => p s)) := by
    ext s
    exact congrFun (graphSourceAction_matrix m left right J (fun s => p s)) s
  rw [hact, PiLp.inner_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  simp only [RCLike.inner_apply]
  exact mul_comm _ _

/-- Hubbard's `Heisenberg - I` convention contributes exactly one scalar
minus the sum of all edge coefficients. -/
theorem graphSourceBottom_offset (m : ℕ) (left right : Edge → Fin (m + 1)) (J : Edge → ℝ) :
    graphSourceBottom m left right J =
      finiteHeisenbergBottom (m + 1) left right J - ∑ e, J e := by
  have heq : graphSourceBottom m left right J = sourceMatrixBottom (m + 1)
      (finiteHeisenbergMatrix (m + 1) left right J - ((∑ e, J e : ℝ) : ℂ) • 1) := by
    unfold graphSourceBottom sourceMatrixBottom
    congr 1
    ext e
    constructor
    · rintro ⟨u, hu, rfl⟩
      let p : MediatorLowSpace (m + 1) := WithLp.toLp 2 u
      have hp : ‖p‖ = 1 := by
        have hsq : ‖p‖ ^ 2 = 1 := (sourceSpinMass_norm_sq p).symm.trans hu
        nlinarith [norm_nonneg p]
      exact ⟨p, hp, graphSourceForm_matrix m left right J p⟩
    · rintro ⟨p, hp, rfl⟩
      refine ⟨fun s => p s, ?_, (graphSourceForm_matrix m left right J p).symm⟩
      rw [sourceSpinMass_norm_sq, hp]
      norm_num
  rw [heq, sourceMatrixBottom_shift]
  rfl

theorem graphSourceBottom_smul (m : ℕ) (left right : Edge → Fin (m + 1)) (J : Edge → ℝ)
    {a : ℝ} (ha : 0 ≤ a) :
    graphSourceBottom m left right (fun e => a * J e) =
      a * (finiteHeisenbergBottom (m + 1) left right J - ∑ e, J e) := by
  rw [graphSourceBottom_offset, finiteHeisenbergBottom_smul _ _ _ _ ha, ← Finset.mul_sum]
  ring

theorem graphSourceBottom_bonds_smul {m r : ℕ} (F : MediatorIteration.Bonds (m + 1) r)
    {a : ℝ} (ha : 0 ≤ a) :
    graphSourceBottom m F.left F.right (fun e => a * (F.weight e : ℝ)) =
      a * (sourceMatrixBottom (m + 1) F.matrix - ∑ e, (F.weight e : ℝ)) := by
  rw [graphSourceBottom_smul m F.left F.right (fun e => (F.weight e : ℝ)) ha,
    finiteHeisenbergBottom_bonds]

end HubbardGlobal
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorListCorrectness
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_left _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_right _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_toList _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_weight _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_fresh _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_fresh _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.ContinuumCoulomb.qmaSubdivisionCell_fresh _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete TM2 bond lists are exactly the enumerations of the finite
spin matrices whose three-stage bottom-energy estimates were proved. -/

namespace ContinuumCoulomb.MediatorIteration
open MediatorGraph

theorem Bonds.toList_get {n r : ℕ} (F : Bonds n r) (i : ℕ) (hi : i < r) :
    (F.toList.drop i).headD MediatorListProgram.zeroBond =
      ((F.left ⟨i, hi⟩).val, (F.right ⟨i, hi⟩).val, F.weight ⟨i, hi⟩) := by
  simp only [List.headD_eq_head?_getD, List.head?_drop]
  rw [List.getElem?_eq_getElem (by simpa using hi)]
  simp only [Option.getD_some, Bonds.toList, List.getElem_ofFn]

theorem lift_toList {n q : ℕ} (r : ℕ) (F : Bonds n q) : (lift r F).toList = F.toList := by
  unfold Bonds.toList
  congr 1

theorem join_toList {n q r : ℕ} (F : Bonds n q) (K : Bonds n r) :
    (join F K).toList = F.toList ++ K.toList := by
  unfold Bonds.toList
  rw [List.ofFn_add]
  congr 1
  · congr 1
    funext e
    change ((join F K).left (Fin.castAdd r e) |>.val,
      (join F K).right (Fin.castAdd r e) |>.val, (join F K).weight (Fin.castAdd r e)) = _
    simp only [join, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
  · congr 1
    funext e
    simp only [join, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]

theorem central_toList_input {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    (central n r (MediatorParameters.delta r W G : ℚ)).toList =
      MediatorListProgram.central ((r, W, G, n), F.toList) := by
  apply List.ext_getElem
  · simp [MediatorListProgram.central]
  · intro i hi hj
    simp only [Bonds.toList, List.getElem_ofFn, MediatorListProgram.central,
      List.getElem_map, List.getElem_range, central, fresh_val, Fin.val_zero, Fin.val_one, add_zero]

theorem spokes_toList_input {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    (spokes F (fun e => member (F.weight e))
      (fun e => MediatorParameters.spoke r W G (F.weight e))).toList =
      MediatorListProgram.spokes ((r, W, G, n), F.toList) := by
  apply List.ext_getElem
  · simp only [Bonds.toList_length, MediatorListProgram.spokes, List.length_map,
      List.length_range]
    omega
  · intro i hi hj
    have hir : i < r * 2 := by simpa only [Bonds.toList_length] using hi
    have hdiv : i / 2 < r := by omega
    let S := spokes F (fun e => member (F.weight e))
      (fun e => MediatorParameters.spoke r W G (F.weight e))
    change (List.ofFn (fun e => ((S.left e).val, (S.right e).val, S.weight e)))[i]'(by
      simpa only [List.length_ofFn] using hir) = _
    rw [List.getElem_ofFn]
    simp only [MediatorListProgram.spokes, List.getElem_map, List.getElem_range]
    rw [Bonds.toList_get F (i / 2) hdiv]
    dsimp only [S]
    simp only [spokes, MediatorListProgram.spoke, old_val, fresh_val]
    change ( (if (⟨i, hir⟩ : Fin (r * 2)).modNat = 0 then
        F.left ((⟨i, hir⟩ : Fin (r * 2)).divNat) else F.right ((⟨i, hir⟩ : Fin (r * 2)).divNat)).val,
      n + 2 * (i / 2) +
        (if (⟨i, hir⟩ : Fin (r * 2)).modNat = 0 then (0 : Fin 2) else member (F.weight ⟨i / 2, hdiv⟩)).val,
      MediatorParameters.spoke r W G (F.weight ⟨i / 2, hdiv⟩)) = _
    have hmod : (⟨i, hir⟩ : Fin (r * 2)).modNat = (0 : Fin 2) ↔ i % 2 = 0 := by
      exact Fin.ext_iff
    by_cases hm : i % 2 = 0
    · simp only [hm, hmod.mpr hm, ite_true, if_true, Fin.val_zero]
      rfl
    · simp only [hm, ite_false, if_false, (not_congr hmod).mpr hm, member]
      split <;> rfl

end ContinuumCoulomb.MediatorIteration

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceCoefficientRounding
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact common-denominator source coefficient rounding, implemented by
actual integer/rational machine arithmetic. Nonzero rounded weights have
an inverse-polynomial lower bound without assuming one for the source. -/

namespace ContinuumCoulomb.SourceCoefficientRounding
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

theorem coefficient_error {M : ℕ} (hM : 0 < M) (q : ℚ) :
    |q - coefficient M q| ≤ 1 / (2 * (M : ℚ)) := by
  have hm : (0 : ℚ) < M := by exact_mod_cast hM
  have heq : q - coefficient M q = ((M : ℚ) * q - round ((M : ℚ) * q)) / M := by
    unfold coefficient
    field_simp
  rw [heq, abs_div, abs_of_pos hm]
  calc
    _ ≤ (1 / 2 : ℚ) / M := div_le_div_of_nonneg_right (abs_sub_round ((M : ℚ) * q)) hm.le
    _ = _ := by ring

theorem coefficient_nonzero_lower {M : ℕ} (hM : 0 < M) (q : ℚ)
    (hq : coefficient M q ≠ 0) : 1 / (M : ℚ) ≤ |coefficient M q| := by
  have hm : (0 : ℚ) < M := by exact_mod_cast hM
  have hk : round ((M : ℚ) * q) ≠ 0 := by
    intro hk
    apply hq
    simp only [coefficient, hk, Int.cast_zero, zero_div]
  have ha : (1 : ℤ) ≤ |round ((M : ℚ) * q)| := by
    have hp := abs_nonneg (round ((M : ℚ) * q))
    have hn := abs_ne_zero.mpr hk
    omega
  have ha' : (1 : ℚ) ≤ |(round ((M : ℚ) * q) : ℚ)| := by exact_mod_cast ha
  rw [coefficient, abs_div, abs_of_pos hm]
  exact div_le_div_of_nonneg_right ha' hm.le

theorem coefficient_upper {M W : ℕ} (hM : 0 < M) (q : ℚ) (hq : |q| ≤ W) :
    |coefficient M q| ≤ W + 1 := by
  have hm : (1 : ℚ) ≤ M := by exact_mod_cast hM
  have he := coefficient_error hM q
  have hhalf : (1 : ℚ) / (2 * M) ≤ 1 := by apply (div_le_one (by positivity)).mpr; linarith
  have h := abs_add_le (coefficient M q - q) q
  rw [sub_add_cancel] at h
  rw [abs_sub_comm] at he
  linarith

end ContinuumCoulomb.SourceCoefficientRounding

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceZeroFilter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual deletion of zero source bonds after common-denominator rounding. -/

namespace ContinuumCoulomb.SourceZeroFilter
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

theorem nonzero_mem (xs : List Bond) (e : Bond) (he : e ∈ xs.filter keep) : e.2.2 ≠ 0 := by
  exact of_decide_eq_true (List.mem_filter.mp he).2

end ContinuumCoulomb.SourceZeroFilter

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceBondLists
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete matrix semantics for the literal bond registers. Removing zero
terms preserves the actual Hamiltonian, while valid bounded indices give
the exact finite family used in the mediator comparison. -/

noncomputable section
namespace ContinuumCoulomb.SourceBondLists
open Matrix MediatorIteration MediatorListProgram
open scoped BigOperators

theorem bondMatrix_zero (n : ℕ) (e : _root_.OAI.ContinuumCoulomb.MediatorListProgram.Bond) (he : e.2.2 = 0) : bondMatrix n e = 0 := by
  unfold bondMatrix
  split <;> simp only [he, Rat.cast_zero, zero_smul]

theorem filter_matrix (n : ℕ) (xs : List _root_.OAI.ContinuumCoulomb.MediatorListProgram.Bond) :
    matrix n (xs.filter SourceZeroFilter.keep) = matrix n xs := by
  induction xs with
  | nil => rfl
  | cons e xs ih =>
    by_cases h : e.2.2 = 0
    · have hk : ¬SourceZeroFilter.keep e := by simp [SourceZeroFilter.keep, h]
      rw [List.filter_cons_of_neg hk]
      simp only [matrix, List.map_cons, List.sum_cons, bondMatrix_zero n e h, zero_add] at *
      exact ih
    · have hk : SourceZeroFilter.keep e := by simp [SourceZeroFilter.keep, h]
      rw [List.filter_cons_of_pos hk]
      simp only [matrix, List.map_cons, List.sum_cons] at *
      rw [ih]

theorem matrix_bonds (n : ℕ) (xs : List _root_.OAI.ContinuumCoulomb.MediatorListProgram.Bond) (h : bounded n xs) :
    matrix n xs = (bonds n xs h).matrix := by
  have hlist : xs.map (bondMatrix n) = List.ofFn (fun i : Fin xs.length => bondMatrix n (xs.get i)) := by
    simpa only [List.get_eq_getElem] using (List.ofFn_getElem_eq_map xs (bondMatrix n)).symm
  rw [matrix, hlist, List.sum_ofFn]
  unfold Bonds.matrix sourceGraphMatrix
  apply Finset.sum_congr rfl
  intro i _
  rw [bondMatrix, dite_eq_left (h _ (List.get_mem xs i))]
  simp only [bonds, Complex.ofReal_ratCast]

end ContinuumCoulomb.SourceBondLists

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorFullListCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact list semantics for all three computed mediator stages and their
rational scalar offset. The emitted list is the full finite spin graph. -/

namespace ContinuumCoulomb.MediatorIteration
open MediatorListProgram MediatorUnaryProgram
open scoped BigOperators

theorem secondInput_literal {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    (secondEnv (literalInput F W G).1, MediatorListProgram.spokes (literalInput F W G)) =
      literalInput (firstSpokes F W G) (secondBound r W G) G := by
  apply Prod.ext
  · simp only [literalInput, secondEnv, secondBound]
    apply Prod.ext
    · omega
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · dsimp only
          omega
  · exact (spokes_toList_input F W G).symm

theorem secondPaths_toList {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    (secondPaths F W G).toList =
      MediatorListProgram.central (secondEnv (literalInput F W G).1,
        MediatorListProgram.spokes (literalInput F W G)) ++
      MediatorListProgram.spokes (secondEnv (literalInput F W G).1,
        MediatorListProgram.spokes (literalInput F W G)) := by
  rw [secondInput_literal]
  unfold secondPaths
  rw [join_toList]
  exact congrArg₂ List.append
    (central_toList_input (firstSpokes F W G) (secondBound r W G) G)
    (spokes_toList_input (firstSpokes F W G) (secondBound r W G) G)

theorem thirdInput_literal {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    (thirdEnv (literalInput F W G).1,
      MediatorListProgram.central (secondEnv (literalInput F W G).1,
        MediatorListProgram.spokes (literalInput F W G)) ++
      MediatorListProgram.spokes (secondEnv (literalInput F W G).1,
        MediatorListProgram.spokes (literalInput F W G))) =
      literalInput (secondPaths F W G) (thirdBound r W G) G := by
  apply Prod.ext
  · simp only [literalInput, thirdEnv, thirdBound]
    apply Prod.ext
    · omega
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · dsimp only
          omega
  · exact (secondPaths_toList F W G).symm

theorem finalGraph_toList {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    (finalGraph F W G).toList = MediatorThreeStageProgram.finalBonds (literalInput F W G) := by
  unfold finalGraph retainedCentral
  rw [join_toList, lift_toList, lift_toList, join_toList]
  have hc1 := central_toList_input F W G
  have hc3 := central_toList_input (secondPaths F W G) (thirdBound r W G) G
  have hs3 := spokes_toList_input (secondPaths F W G) (thirdBound r W G) G
  change (firstCentral F W G).toList ++
    ((thirdCentral F W G).toList ++ (thirdSpokes F W G).toList) = _
  rw [show (firstCentral F W G).toList = MediatorListProgram.central (literalInput F W G) from hc1]
  rw [show (thirdCentral F W G).toList =
    MediatorListProgram.central (literalInput (secondPaths F W G) (thirdBound r W G) G) from hc3]
  rw [show (thirdSpokes F W G).toList =
    MediatorListProgram.spokes (literalInput (secondPaths F W G) (thirdBound r W G) G) from hs3]
  rw [← thirdInput_literal]
  simp only [MediatorThreeStageProgram.finalBonds, List.append_assoc]

theorem stageOffset_toList {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    MediatorOffsetProgram.stageOffset (literalInput F W G) =
      3 * r * MediatorParameters.delta r W G + 3 * ∑ e, |F.weight e| := by
  simp only [MediatorOffsetProgram.stageOffset, literalInput, Bonds.toList,
    List.map_ofFn, List.sum_ofFn, Function.comp_apply]

theorem offset_toList {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    MediatorOffsetProgram.offset (literalInput F W G) = offset F W G := by
  unfold MediatorOffsetProgram.offset
  rw [thirdInput_literal, secondInput_literal]
  rw [stageOffset_toList, stageOffset_toList, stageOffset_toList]
  simp only [MediatorIteration.offset, deltaOne, deltaTwo, deltaThree, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add]

theorem bonds_toList (n : ℕ) (xs : List MediatorListProgram.Bond)
    (h : SourceBondLists.bounded n xs) : (SourceBondLists.bonds n xs h).toList = xs := by
  change List.ofFn (fun e => ((xs.get e).1, (xs.get e).2.1, (xs.get e).2.2)) = xs
  simpa only [Prod.eta] using List.ofFn_get xs

theorem Bonds.matrix_toList {n r : ℕ} (F : Bonds n r) :
    SourceBondLists.matrix n F.toList = F.matrix := by
  simp only [SourceBondLists.matrix, Bonds.toList, List.map_ofFn, List.sum_ofFn]
  unfold Bonds.matrix sourceGraphMatrix
  apply Finset.sum_congr rfl
  intro e _
  simp only [Function.comp_apply, SourceBondLists.bondMatrix, Fin.is_lt, and_self,
    dite_true, Fin.eta, Complex.ofReal_ratCast]

end ContinuumCoulomb.MediatorIteration

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CenteredPhysicalThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical threshold reference for the exact half-cell boundary of the
centered grid. The finite threshold is scaled by lambda and the true rational
slab reference by lambda squared times the electron count. -/

noncomputable section
namespace ContinuumCoulomb.CenteredPhysicalThreshold

theorem amplification_bound (rho mesh : ℕ) (hrho : 0 < rho) :
    0 ≤ (amplification rho mesh:ℝ) ∧ (amplification rho mesh:ℝ) ≤ 8*(mesh:ℝ)^3 := by
  have hp : 0 < (rho:ℝ) := by exact_mod_cast hrho
  have h1 : 1 ≤ (rho:ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hrho)
  simp only [amplification,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_pow,Rat.cast_natCast]
  constructor
  · positivity
  · exact div_le_self (by positivity) h1

end ContinuumCoulomb.CenteredPhysicalThreshold

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceNormalizedSpectrum
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_coordinate _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_edges _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_lower _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_upper _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_vertices _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.contactEdge_left _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.contactEdge_right _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal source rounding and zero deletion feed the complete three-stage
spin comparison. Only the source's upper coefficient and gap bounds are
needed; a nonzero lower coefficient bound is proved by rounding. -/

noncomputable section
namespace ContinuumCoulomb.SourceNormalizedSpectrum
open Matrix MediatorIteration MediatorListProgram SourceBondLists
open scoped BigOperators

theorem family_noLoops (d : SquareLatticeHeisenberg) (M : ℕ) : (family d M).NoLoops := by
  apply bonds_noLoops
  intro e he hloop
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_filter.mp he).1
  exact d.edge_ne i (Fin.ext hloop)

theorem rounded_matrix (d : SquareLatticeHeisenberg) (M : ℕ) :
    matrix d.vertices (rounded d M) =
      (d.withCoefficients (fun e => SourceCoefficientRounding.coefficient M (d.coefficient e))).bonds.matrix := by
  unfold matrix rounded
  rw [List.map_ofFn, List.sum_ofFn]
  unfold Bonds.matrix SquareLatticeHeisenberg.bonds sourceGraphMatrix
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_apply]
  rw [bondMatrix, dite_eq_left ⟨(d.left i).isLt, (d.right i).isLt⟩]
  simp only [SquareLatticeHeisenberg.withCoefficients, Complex.ofReal_ratCast]
  rfl

theorem family_matrix (d : SquareLatticeHeisenberg) (M : ℕ) :
    (family d M).matrix =
      (d.withCoefficients (fun e => SourceCoefficientRounding.coefficient M (d.coefficient e))).bonds.matrix := by
  exact (matrix_bonds d.vertices (retained d M) (retained_bounded d M)).symm.trans
    ((filter_matrix d.vertices (rounded d M)).trans (rounded_matrix d M))

theorem family_bottom_error (d : SquareLatticeHeisenberg) {M : ℕ} (hM : 0 < M) :
    |sourceMatrixBottom d.vertices (family d M).matrix - realSourceGroundEnergy d| ≤
      3 * d.edges / (2 * (M : ℝ)) := by
  rw [family_matrix]
  change |sourceMatrixBottom
      (d.withCoefficients (fun e => SourceCoefficientRounding.coefficient M (d.coefficient e))).vertices
      (d.withCoefficients (fun e => SourceCoefficientRounding.coefficient M (d.coefficient e))).bonds.matrix -
      realSourceGroundEnergy d| ≤ _
  rw [sourceMatrixBottom_eq_realSource]
  have h := realSourceGroundEnergy_rounding d
    (fun e => SourceCoefficientRounding.coefficient M (d.coefficient e))
  have hp : ∀ e, |(d.coefficient e : ℝ) -
      (SourceCoefficientRounding.coefficient M (d.coefficient e) : ℝ)| ≤ 1 / (2 * (M : ℝ)) := by
    intro e
    have hq := Rat.cast_le (K := ℝ).mpr
      (SourceCoefficientRounding.coefficient_error hM (d.coefficient e))
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_one,
      Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using hq
  have hs := Finset.sum_le_sum (fun e (_ : e ∈ (Finset.univ : Finset (Fin d.edges))) => hp e)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  exact h.trans ((mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 3)).trans_eq (by ring))

theorem family_bounds (d : SquareLatticeHeisenberg) {M W : ℕ} (hM : 0 < M)
    (hW : ∀ e, |(d.coefficient e : ℝ)| ≤ W) :
    ∀ e, 1 / ((M + W + 1 : ℕ) : ℝ) ≤ |((family d M).weight e : ℝ)| ∧
      |((family d M).weight e : ℝ)| ≤ (M + W + 1 : ℕ) := by
  intro e
  have he := List.get_mem (retained d M) e
  have hz := SourceZeroFilter.nonzero_mem (rounded d M) _ he
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp (List.mem_filter.mp he).1
  have hw : (family d M).weight e = SourceCoefficientRounding.coefficient M (d.coefficient i) := by
    exact congrArg (fun a : _root_.OAI.ContinuumCoulomb.MediatorListProgram.Bond => a.2.2) hi.symm
  have hz' : SourceCoefficientRounding.coefficient M (d.coefficient i) ≠ 0 := by simpa only [← hi] using hz
  have hl : 1 / (M : ℝ) ≤ |(SourceCoefficientRounding.coefficient M (d.coefficient i) : ℝ)| := by
    have hq := Rat.cast_le (K := ℝ).mpr
      (SourceCoefficientRounding.coefficient_nonzero_lower hM (d.coefficient i) hz')
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, Rat.cast_abs] using hq
  have hq : |d.coefficient i| ≤ (W : ℚ) := by exact_mod_cast hW i
  have hu : |(SourceCoefficientRounding.coefficient M (d.coefficient i) : ℝ)| ≤ W + 1 := by
    exact_mod_cast SourceCoefficientRounding.coefficient_upper hM (d.coefficient i) hq
  rw [hw]
  constructor
  · exact (one_div_le_one_div_of_le (by exact_mod_cast hM)
      (by norm_cast; omega : (M : ℝ) ≤ (M + W + 1 : ℕ))).trans hl
  · have hm : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    push_cast
    linarith

/-- Full three-stage error after genuine source normalization, with no
lower-weight hypothesis on the original published source. -/
theorem normalized_three_stage_bottom (d : SquareLatticeHeisenberg) {M W G : ℕ}
    (hM : 0 < M) (hG : 0 < G) (hW : ∀ e, |(d.coefficient e : ℝ)| ≤ W) :
    |sourceMatrixBottom
      (d.vertices + (retained d M).length * 2 + (retained d M).length * 2 * 2 +
        ((retained d M).length * 2 + (retained d M).length * 2 * 2) * 2)
      (finalGraph (family d M) (M + W + 1) G).matrix +
      (MediatorIteration.offset (family d M) (M + W + 1) G : ℝ) - realSourceGroundEnergy d| ≤
        3 / (512 * (G : ℝ)) + 3 * d.edges / (2 * (M : ℝ)) := by
  have hB := family_bounds d hM hW
  have h := three_stage_bottom (family d M) (family_noLoops d M)
    (by omega : 0 < M + W + 1) hG (fun e => (hB e).2) (fun e => (hB e).1)
  have he := family_bottom_error d hM
  have ht := (abs_add_le
    (sourceMatrixBottom _ (finalGraph (family d M) (M + W + 1) G).matrix +
      (MediatorIteration.offset (family d M) (M + W + 1) G : ℝ) -
      sourceMatrixBottom d.vertices (family d M).matrix)
    (sourceMatrixBottom d.vertices (family d M).matrix - realSourceGroundEnergy d)).trans (add_le_add h he)
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end ContinuumCoulomb.SourceNormalizedSpectrum

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceNormalizedPromise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed polynomial common denominator absorbs both coefficient rounding
and all three mediator errors into one inverse-polynomial promise budget. -/

noncomputable section
namespace ContinuumCoulomb.SourceNormalizedSpectrum

theorem denominator_pos (r : ℕ) {G : ℕ} (hG : 0 < G) : 0 < denominator r G := by
  unfold denominator
  positivity

end ContinuumCoulomb.SourceNormalizedSpectrum

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceNormalizationCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The machine-normalized source registers are the literal bond family
whose complete positive-spin spectral and promise estimates were proved. -/

namespace ContinuumCoulomb.SourceMetadataProgram
open MediatorListProgram

theorem size_pos (d : BinaryHeisenberg) : 0 < size d := by
  unfold size
  omega

theorem polynomialPromise_weight (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid)
    (hp : d.PolynomialPromise k) :
    ∀ e, |((d.toSource h).coefficient e : ℝ)| ≤ (size d ^ k : ℕ) := by
  intro e
  simpa only [size, Nat.cast_pow, Nat.cast_add, Nat.cast_one, BinaryHeisenberg.toSource] using
    hp.weight_bound e

end ContinuumCoulomb.SourceMetadataProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_SourceContactProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal composition from the encoded source to the calibrated
contact coordinates. The signed retained bonds determine the geometric
strips; the final positive bond list supplies their nineteen target weights. -/

namespace ContinuumCoulomb.SourceContactProgram
open ExactQuantumFactoring.BitStackProgram

theorem size_ge_two (d : BinaryHeisenberg) : 2 ≤ size d := by
  simp only [size,SourceMetadataProgram.size]
  omega

end ContinuumCoulomb.SourceContactProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourcePositiveCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact semantics of the computed positive-spin source reduction: the
literal output has the full three-stage matrix and the proved rational
thresholds, including the common coefficient-rounding error. -/

noncomputable section
namespace ContinuumCoulomb.SourcePositiveProgram
open MediatorIteration SourceMetadataProgram

theorem normalized_literal (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    normalized k d = literalInput (sourceFamily k d h) (sourceBound k d) (size d ^ k) := by
  rw [normalized, normalized_eq k d h]
  unfold literalInput sourceFamily SourceNormalizedSpectrum.family
  rw [bonds_toList]
  rfl

theorem bonds_eq (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    (output k d).bonds =
      (finalGraph (sourceFamily k d h) (sourceBound k d) (size d ^ k)).toList := by
  change MediatorThreeStageProgram.finalBonds (normalized k d) = _
  rw [normalized_literal]
  exact (finalGraph_toList _ _ _).symm

theorem offset_eq (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    offset k d = MediatorIteration.offset (sourceFamily k d h) (sourceBound k d) (size d ^ k) := by
  unfold offset
  rw [normalized_literal, offset_toList]

theorem energy_eq (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    energy (output k d) = SourceNormalizedSpectrum.positiveEnergy (d.toSource h) (size d ^ k) (size d ^ k) := by
  unfold energy
  rw [bonds_eq k d h, vertices_eq k d h]
  change sourceMatrixBottom _ (SourceBondLists.matrix _
    (finalGraph (sourceFamily k d h) (sourceBound k d) (size d ^ k)).toList) =
    sourceMatrixBottom _ (finalGraph (sourceFamily k d h) (sourceBound k d) (size d ^ k)).matrix
  exact congrArg (sourceMatrixBottom _)
    (Bonds.matrix_toList (finalGraph (sourceFamily k d h) (sourceBound k d) (size d ^ k)))

theorem lower_eq (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    (output k d).lower = SourceNormalizedSpectrum.lowerThreshold
      (d.toSource h) (size d ^ k) (size d ^ k) d.lower.value := by
  change d.lower.value - offset k d + error k d = _
  rw [offset_eq]
  rfl

theorem upper_eq (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    (output k d).upper = SourceNormalizedSpectrum.upperThreshold
      (d.toSource h) (size d ^ k) (size d ^ k) d.upper.value := by
  change d.upper.value - offset k d - error k d = _
  rw [offset_eq]
  rfl

end ContinuumCoulomb.SourcePositiveProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourcePositiveMargin
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal positive-spin thresholds retain a quantitative part of the
rounding budget. This margin pays for the later Hubbard and continuum errors. -/

noncomputable section
namespace ContinuumCoulomb.SourceNormalizedSpectrum

theorem normalization_margin (r : ℕ) {G : ℕ} (hG : 0 < G) :
    3 / (512 * (G : ℝ)) + 3 * r / (2 * (denominator r G : ℝ)) +
      1 / (2048 * (G : ℝ)) ≤ 1 / (128 * (G : ℝ)) := by
  have hg : (0 : ℝ) < G := by exact_mod_cast hG
  have hden : (denominator r G : ℝ) = 1024 * ((r : ℝ) + 1) * G := by
    simp only [denominator,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  rw [hden]
  have hr : 3 * (r : ℝ) / (2 * (1024 * (r + 1) * G)) ≤ 3 / (2048 * G) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have he : 3 / (512 * (G : ℝ)) + 3 / (2048 * G) + 1 / (2048 * G) =
      1 / (128 * G) := by field_simp; ring
  linarith

theorem source_positive_margin (d : SquareLatticeHeisenberg) {W G : ℕ}
    (hG : 0 < G) (hW : ∀ e, |(d.coefficient e : ℝ)| ≤ W) :
    |positiveEnergy d W G +
      (MediatorIteration.offset (family d (denominator d.edges G))
        (denominator d.edges G + W + 1) G : ℝ) - realSourceGroundEnergy d| +
      1 / (2048 * (G : ℝ)) ≤ 1 / (128 * (G : ℝ)) := by
  have h := normalized_three_stage_bottom d (denominator_pos d.edges hG) hG hW
  exact (add_le_add h le_rfl).trans (normalization_margin d.edges hG)

theorem source_positive_yes_margin (d : SquareLatticeHeisenberg) {W G : ℕ}
    (hG : 0 < G) (hW : ∀ e, |(d.coefficient e : ℝ)| ≤ W) {a : ℚ}
    (hyes : realSourceGroundEnergy d ≤ a) :
    positiveEnergy d W G + 1 / (2048 * (G : ℝ)) ≤ lowerThreshold d W G a := by
  have hm := source_positive_margin d hG hW
  have ha := le_abs_self (positiveEnergy d W G +
    (MediatorIteration.offset (family d (denominator d.edges G))
      (denominator d.edges G + W + 1) G : ℝ) - realSourceGroundEnergy d)
  simp only [lowerThreshold,Rat.cast_add,Rat.cast_sub,Rat.cast_div,
    Rat.cast_mul,Rat.cast_one,Rat.cast_ofNat,Rat.cast_natCast]
  linarith

theorem source_positive_no_margin (d : SquareLatticeHeisenberg) {W G : ℕ}
    (hG : 0 < G) (hW : ∀ e, |(d.coefficient e : ℝ)| ≤ W) {b : ℚ}
    (hno : (b : ℝ) ≤ realSourceGroundEnergy d) :
    (upperThreshold d W G b : ℝ) + 1 / (2048 * (G : ℝ)) ≤ positiveEnergy d W G := by
  have hm := source_positive_margin d hG hW
  have ha := neg_abs_le (positiveEnergy d W G +
    (MediatorIteration.offset (family d (denominator d.edges G))
      (denominator d.edges G + W + 1) G : ℝ) - realSourceGroundEnergy d)
  simp only [upperThreshold,Rat.cast_sub,Rat.cast_div,
    Rat.cast_mul,Rat.cast_one,Rat.cast_ofNat,Rat.cast_natCast]
  linarith

end ContinuumCoulomb.SourceNormalizedSpectrum

namespace ContinuumCoulomb.SourcePositiveProgram
open SourceMetadataProgram

theorem output_yes_margin (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid)
    (hp : d.PolynomialPromise k)
    (hyes : realSourceGroundEnergy (d.toSource h) ≤ d.lower.value) :
    energy (output k d) + 1 / (2048 * ((size d ^ k : ℕ) : ℝ)) ≤
      (output k d).lower := by
  rw [energy_eq k d h,lower_eq k d h]
  exact SourceNormalizedSpectrum.source_positive_yes_margin _ (pow_pos (size_pos d) k)
    (polynomialPromise_weight k d h hp) hyes

theorem output_no_margin (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid)
    (hp : d.PolynomialPromise k)
    (hno : (d.upper.value : ℝ) ≤ realSourceGroundEnergy (d.toSource h)) :
    ((output k d).upper : ℝ) + 1 / (2048 * ((size d ^ k : ℕ) : ℝ)) ≤
      energy (output k d) := by
  rw [energy_eq k d h,upper_eq k d h]
  exact SourceNormalizedSpectrum.source_positive_no_margin _ (pow_pos (size_pos d) k)
    (polynomialPromise_weight k d h hp) hno

end ContinuumCoulomb.SourcePositiveProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourcePhysicalPromise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Promise transfer for the literal physical thresholds. The retained
source margin absorbs the finite, continuum, and scalar-evaluation errors. -/

noncomputable section
namespace ContinuumCoulomb.SourcePhysicalThreshold

theorem exact_endpoint_differences (rho C : ℕ) (eps c : ℚ) (s p h k A B q : ℕ)
    (d : BinaryHeisenberg) (v : ℝ) :
    let x := input rho C eps c s p h k A B q d
    let a := (SourceNuclearProgram.amplification rho k d : ℝ) *
      (((SourceContactProgram.size d^(30*B) : ℕ) : ℝ)⁻¹)^2
    (AffinePhysicalThreshold.exactValue rho x v).1 - exactSourceEnergy rho C eps c s p h k A B q d v =
      a * ((SourcePositiveProgram.output s d).lower - SourcePositiveProgram.energy (SourcePositiveProgram.output s d)) ∧
    exactSourceEnergy rho C eps c s p h k A B q d v - (AffinePhysicalThreshold.exactValue rho x v).2 =
      a * (SourcePositiveProgram.energy (SourcePositiveProgram.output s d) - (SourcePositiveProgram.output s d).upper) := by
  dsimp only
  simp only [AffinePhysicalThreshold.exactValue,AffinePhysicalThreshold.exactFinite,
    exactSourceEnergy,input,SourceNuclearProgram.amplification,Rat.cast_inv,Rat.cast_natCast]
  constructor <;> ring

end ContinuumCoulomb.SourcePhysicalThreshold

namespace ContinuumCoulomb.SourceUnitCoulomb

theorem promise_transfer (rho C U F K : ℕ) (hrho : 0 < rho) (eps c : ℚ)
    (s p h k A B q ap : ℕ) (d : BinaryHeisenberg) (hd : d.Valid)
    (hp : d.PolynomialPromise s) {m : ℕ} (u : Fin m → CoulombPairSum.Point)
    (hu : Function.Injective u)
    (hsites : SourceNuclearProgram.sites rho C eps c s p h k A B d = List.ofFn u)
    (ho : (value rho C U F K eps c s p h k A B q ap d).Valid)
    (center continuumError finiteError : ℝ)
    (hground : ((center-continuumError : ℝ) : EReal) ≤
        unitGroundEnergy ((value rho C U F K eps c s p h k A B q ap d).toData ho) ∧
      unitGroundEnergy ((value rho C U F K eps c s p h k A B q ap d).toData ho) ≤
        ((center+continuumError : ℝ) : EReal))
    (hfinite : |center - SourcePhysicalThreshold.exactSourceEnergy rho C eps c s p h k A B q d
      (CoulombPairSum.exactTotal (GaussianFrequency.frequency rho) u)| ≤ finiteError)
    (hbudget : continuumError + finiteError + 1 / (((SourceContactProgram.size d^q : ℕ) : ℝ)+1) ≤
      (SourceNuclearProgram.amplification rho k d : ℝ) *
        (((SourceContactProgram.size d^(30*B) : ℕ) : ℝ)⁻¹)^2 *
        (1 / (2048 * ((SourceMetadataProgram.size d^s : ℕ) : ℝ)))) :
    (realSourceGroundEnergy (d.toSource hd) ≤ d.lower.value →
      unitGroundEnergy ((value rho C U F K eps c s p h k A B q ap d).toData ho) ≤
        (((value rho C U F K eps c s p h k A B q ap d).lower.value : ℝ) : EReal)) ∧
    ((d.upper.value : ℝ) ≤ realSourceGroundEnergy (d.toSource hd) →
      (((value rho C U F K eps c s p h k A B q ap d).upper.value : ℝ) : EReal) ≤
        unitGroundEnergy ((value rho C U F K eps c s p h k A B q ap d).toData ho)) := by
  let v := CoulombPairSum.exactTotal (GaussianFrequency.frequency rho) u
  let x := SourcePhysicalThreshold.input rho C eps c s p h k A B q d
  let a := (SourceNuclearProgram.amplification rho k d : ℝ) *
    (((SourceContactProgram.size d^(30*B) : ℕ) : ℝ)⁻¹)^2
  have ha : 0 ≤ a := by
    apply mul_nonneg _ (sq_nonneg _)
    exact (CenteredPhysicalThreshold.amplification_bound rho _ hrho).1
  have herr := actual_threshold_error rho C U F K hrho eps c s p h k A B q ap d u hu hsites
  have hdiff := SourcePhysicalThreshold.exact_endpoint_differences rho C eps c s p h k A B q d v
  change (AffinePhysicalThreshold.exactValue rho x v).1 -
      SourcePhysicalThreshold.exactSourceEnergy rho C eps c s p h k A B q d v =
      a * ((SourcePositiveProgram.output s d).lower - SourcePositiveProgram.energy (SourcePositiveProgram.output s d)) ∧
    SourcePhysicalThreshold.exactSourceEnergy rho C eps c s p h k A B q d v -
      (AffinePhysicalThreshold.exactValue rho x v).2 =
      a * (SourcePositiveProgram.energy (SourcePositiveProgram.output s d) - (SourcePositiveProgram.output s d).upper) at hdiff
  have hfe := abs_le.mp hfinite
  have hlow := abs_le.mp herr.1
  have hhigh := abs_le.mp herr.2
  constructor
  · intro hy
    have hm := mul_le_mul_of_nonneg_left (SourcePositiveProgram.output_yes_margin s d hd hp hy) ha
    have hl : center+continuumError ≤ (value rho C U F K eps c s p h k A B q ap d).lower.value := by
      dsimp only [a] at hm
      nlinarith only [hm,hdiff.1,hbudget,hfe.2,hlow.1]
    exact hground.2.trans (EReal.coe_le_coe_iff.mpr hl)
  · intro hn
    have hm := mul_le_mul_of_nonneg_left (SourcePositiveProgram.output_no_margin s d hd hp hn) ha
    have hh : ((value rho C U F K eps c s p h k A B q ap d).upper.value : ℝ) ≤ center-continuumError := by
      dsimp only [a] at hm
      nlinarith only [hm,hdiff.2,hbudget,hfe.1,hhigh.2]
    exact (EReal.coe_le_coe_iff.mpr hh).trans hground.1

end ContinuumCoulomb.SourceUnitCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceHubbardEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite-spin and scalar-offset identities for the literal source
bond list. These identify the Hubbard center with the computed threshold center. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open MediatorIteration HubbardGlobal

theorem source_graph_bottom {m r : ℕ} (s : ℕ) (d : BinaryHeisenberg)
    (F : Bonds (m+1) r)
    (hvertices : (SourcePositiveProgram.output s d).vertices = m+1)
    (hbonds : F.toList = (SourcePositiveProgram.output s d).bonds) (τ : ℝ) :
    graphSourceBottom m F.left F.right (fun e => τ^2*(F.weight e : ℝ)) =
      τ^2*(SourcePositiveProgram.energy (SourcePositiveProgram.output s d) -
        (((SourcePositiveProgram.output s d).bonds.map (fun e => e.2.2)).sum : ℝ)) := by
  rw [graphSourceBottom_bonds_smul F (sq_nonneg τ)]
  have hm : sourceMatrixBottom (m+1) F.matrix =
      SourcePositiveProgram.energy (SourcePositiveProgram.output s d) := by
    unfold SourcePositiveProgram.energy
    rw [hvertices,← hbonds,Bonds.matrix_toList]
  have hs : (∑ e, (F.weight e : ℝ)) =
      (((SourcePositiveProgram.output s d).bonds.map (fun e => e.2.2)).sum : ℝ) := by
    rw [← hbonds]
    simp only [Bonds.toList,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  rw [hm,hs]

namespace SourcePhysicalThreshold

theorem hubbard_center_error (rho C : ℕ) (hrho : 0 < rho) (eps c : ℚ)
    (s p h k A B q : ℕ) (d : BinaryHeisenberg) {m r : ℕ}
    (u : Fin (m+1) → CoulombPairSum.Point) (F : Bonds (m+1) r) (t : Fin r → ℝ)
    (hvertices : (SourcePositiveProgram.output s d).vertices = m+1)
    (hbonds : F.toList = (SourcePositiveProgram.output s d).bonds)
    {δ : ℝ}
    (hfinite : |hubbardFermionBottom m (localizedCoulombProfile (GaussianFrequency.frequency rho) 0)
        (localizedOffsiteCoulomb (GaussianFrequency.frequency rho)
          (fun i => PlanarForcingProgram.position (u i))) F.left F.right t -
      graphSourceBottom m F.left F.right (fun e =>
        ((((SourceContactProgram.size d^(30*B) : ℕ) : ℝ)⁻¹)^2)*(F.weight e : ℝ))| ≤ δ) :
    |exactHubbardEnergy rho C eps c s p h k A B q d u F t -
      exactSourceEnergy rho C eps c s p h k A B q d
        (CoulombPairSum.exactTotal (GaussianFrequency.frequency rho) u)| ≤
      (SourceNuclearProgram.amplification rho k d : ℝ)*δ := by
  have ha : 0 ≤ (SourceNuclearProgram.amplification rho k d : ℝ) :=
    (CenteredPhysicalThreshold.amplification_bound rho (SourcePhysicalThreshold.mesh k d) hrho).1
  rw [source_graph_bottom s d F hvertices hbonds] at hfinite
  have he : exactHubbardEnergy rho C eps c s p h k A B q d u F t -
      exactSourceEnergy rho C eps c s p h k A B q d
        (CoulombPairSum.exactTotal (GaussianFrequency.frequency rho) u) =
    (SourceNuclearProgram.amplification rho k d : ℝ) *
      (hubbardFermionBottom m (localizedCoulombProfile (GaussianFrequency.frequency rho) 0)
        (localizedOffsiteCoulomb (GaussianFrequency.frequency rho)
          (fun i => PlanarForcingProgram.position (u i))) F.left F.right t -
        (((SourceContactProgram.size d^(30*B) : ℕ) : ℝ)⁻¹)^2 *
          (SourcePositiveProgram.energy (SourcePositiveProgram.output s d) -
            (((SourcePositiveProgram.output s d).bonds.map (fun e => e.2.2)).sum : ℝ))) := by
    simp only [exactHubbardEnergy,exactSourceEnergy,input,SourceNuclearProgram.amplification,
      Rat.cast_inv,Rat.cast_natCast,Rat.cast_list_sum,List.map_map,Function.comp_def]
    ring
  rw [he,abs_mul,abs_of_nonneg ha]
  exact mul_le_mul_of_nonneg_left hfinite ha

end SourcePhysicalThreshold
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourcePromiseBudget
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed exponent choices absorb all three physical simulation errors
inside the margin retained by the positive-spin source program. -/

noncomputable section
namespace ContinuumCoulomb

theorem physical_promise_error_budget {N M scale : ℝ}
    (hN : 2 ≤ N) (hM : 1 ≤ M) (hMN : M ≤ N) (hscale : 1 ≤ scale)
    (s B p g q : ℕ) (hp : 60*B+s+14 ≤ p) (hg : s+14 ≤ g)
    (hq : 60*B+s+14 ≤ q) :
    scale*(N^p)⁻¹ + scale*(N^g)⁻¹*((N^(30*B))⁻¹)^2 + 1/(N^q+1) ≤
      scale*((N^(30*B))⁻¹)^2*(1/(2048*M^s)) := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hM0 : 0 < M := by linarith
  have hscale0 : 0 ≤ scale := by linarith
  have hi {a b : ℕ} (hab : b ≤ a) : (N^a)⁻¹ ≤ (N^b)⁻¹ := by
    exact inv_anti₀ (pow_pos hN0 b) (pow_le_pow_right₀ hN1 hab)
  have hid : (N^(60*B+s+14))⁻¹ = ((N^(30*B))⁻¹)^2*(N^(s+14))⁻¹ := by
    rw [show 60*B+s+14=(30*B)*2+(s+14) by omega,pow_add,pow_mul,mul_inv_rev,inv_pow]
    ring
  have hcont : scale*(N^p)⁻¹ ≤ scale*((N^(30*B))⁻¹)^2*(N^(s+14))⁻¹ := by
    have hh := mul_le_mul_of_nonneg_left (hi hp) hscale0
    simpa only [hid,mul_assoc] using hh
  have hfinite : scale*(N^g)⁻¹*((N^(30*B))⁻¹)^2 ≤
      scale*((N^(30*B))⁻¹)^2*(N^(s+14))⁻¹ := by
    have hh := mul_le_mul_of_nonneg_left (hi hg)
      (mul_nonneg hscale0 (sq_nonneg ((N^(30*B))⁻¹)))
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hh
  have hnum : 1/(N^q+1) ≤ scale*((N^(30*B))⁻¹)^2*(N^(s+14))⁻¹ := by
    have hfirst : 1/(N^q+1) ≤ (N^q)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (pow_pos hN0 q)
        (show N^q ≤ N^q+1 by linarith)
    have hsecond := (hi hq).trans (le_mul_of_one_le_left (by positivity) hscale)
    exact hfirst.trans (by simpa only [hid,mul_assoc] using hsecond)
  have htail : 3*(N^(s+14))⁻¹ ≤ 1/(2048*M^s) := by
    have hpow : (6144:ℝ) ≤ N^14 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hN 14
      norm_num at hh
      linarith
    have hproduct : 3*(2048*M^s) ≤ N^(s+14) := by
      rw [pow_add]
      calc
        _ = M^s*6144 := by ring
        _ ≤ N^s*N^14 := mul_le_mul (pow_le_pow_left₀ hM0.le hMN s) hpow
          (by norm_num) (pow_nonneg hN0.le s)
    exact (div_le_div_iff₀ (pow_pos hN0 (s+14)) (by positivity : 0 < 2048*M^s)).mpr
      (by simpa only [one_mul] using hproduct)
  have ht := mul_le_mul_of_nonneg_left htail
    (mul_nonneg hscale0 (sq_nonneg ((N^(30*B))⁻¹)))
  nlinarith only [hcont,hfinite,hnum,ht]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceHubbardPromise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! End-to-end promise accounting from a Hubbard interval for the literal
source output. All errors use the actual fixed-power precision schedules. -/

noncomputable section
namespace ContinuumCoulomb.SourceUnitCoulomb
open HubbardGlobal MediatorIteration

theorem promise_of_hubbard_interval_oai (rho C U F K : ℕ) (hrho : 0 < rho) (eps c : ℚ)
    (s pc h k A B q ap p g : ℕ) (d : BinaryHeisenberg) (hd : d.Valid)
    (hp : d.PolynomialPromise s) {m r : ℕ} (u : Fin (m+1) → CoulombPairSum.Point)
    (hu : Function.Injective u)
    (hsites : SourceNuclearProgram.sites rho C eps c s pc h k A B d = List.ofFn u)
    (graph : Bonds (m+1) r)
    (hvertices : (SourcePositiveProgram.output s d).vertices = m+1)
    (hbonds : graph.toList = (SourcePositiveProgram.output s d).bonds) (t : Fin r → ℝ)
    (ho : (value rho C U F K eps c s pc h k A B q ap d).Valid)
    (hscale : 1 ≤ (SourceNuclearProgram.amplification rho k d:ℝ))
    (hpowers : 60*B+s+14 ≤ p) (hgpowers : s+14 ≤ g) (hqpowers : 60*B+s+14 ≤ q)
    (hfinite : |hubbardFermionBottom m (localizedCoulombProfile (GaussianFrequency.frequency rho) 0)
        (localizedOffsiteCoulomb (GaussianFrequency.frequency rho)
          (fun i => PlanarForcingProgram.position (u i))) graph.left graph.right t -
      graphSourceBottom m graph.left graph.right (fun e =>
        (((SourceContactProgram.size d^(30*B):ℕ):ℝ)⁻¹)^2*(graph.weight e:ℝ))| ≤
      ((SourceContactProgram.size d:ℝ)^g)⁻¹*
        (((SourceContactProgram.size d^(30*B):ℕ):ℝ)⁻¹)^2)
    (hground :
      ((SourcePhysicalThreshold.exactHubbardEnergy rho C eps c s pc h k A B q d u graph t -
        (SourceNuclearProgram.amplification rho k d:ℝ)*((SourceContactProgram.size d:ℝ)^p)⁻¹:ℝ):EReal) ≤
        unitGroundEnergy ((value rho C U F K eps c s pc h k A B q ap d).toData ho) ∧
      unitGroundEnergy ((value rho C U F K eps c s pc h k A B q ap d).toData ho) ≤
        ((SourcePhysicalThreshold.exactHubbardEnergy rho C eps c s pc h k A B q d u graph t +
          (SourceNuclearProgram.amplification rho k d:ℝ)*((SourceContactProgram.size d:ℝ)^p)⁻¹:ℝ):EReal)) :
    (realSourceGroundEnergy (d.toSource hd) ≤ d.lower.value →
      value rho C U F K eps c s pc h k A B q ap d ∈ unitCoulombPromise.yes) ∧
    ((d.upper.value:ℝ) ≤ realSourceGroundEnergy (d.toSource hd) →
      value rho C U F K eps c s pc h k A B q ap d ∈ unitCoulombPromise.no) := by
  have hN : (2:ℝ) ≤ SourceContactProgram.size d := by
    exact_mod_cast SourceContactProgram.size_ge_two d
  have hM : (1:ℝ) ≤ SourceMetadataProgram.size d := by
    exact_mod_cast SourceMetadataProgram.size_pos d
  have hMN : (SourceMetadataProgram.size d:ℝ) ≤ SourceContactProgram.size d := by
    simp only [SourceContactProgram.size,Nat.cast_add,Nat.cast_one]
    linarith
  have hbudget := physical_promise_error_budget hN hM hMN hscale s B p g q hpowers hgpowers hqpowers
  have hcenter := SourcePhysicalThreshold.hubbard_center_error rho C hrho eps c s pc h k A B q d
    u graph t hvertices hbonds hfinite
  obtain ⟨hy,hn⟩ := promise_transfer rho C U F K hrho eps c s pc h k A B q ap d hd hp u hu hsites ho
    (SourcePhysicalThreshold.exactHubbardEnergy rho C eps c s pc h k A B q d u graph t)
    ((SourceNuclearProgram.amplification rho k d:ℝ)*((SourceContactProgram.size d:ℝ)^p)⁻¹)
    ((SourceNuclearProgram.amplification rho k d:ℝ)*((SourceContactProgram.size d:ℝ)^g)⁻¹*
      (((SourceContactProgram.size d^(30*B):ℕ):ℝ)⁻¹)^2)
    hground (by simpa only [mul_assoc] using hcenter)
    (by simpa only [Nat.cast_pow] using hbudget)
  exact ⟨fun h => ⟨ho,hy h⟩,fun h => ⟨ho,hn h⟩⟩

end ContinuumCoulomb.SourceUnitCoulomb

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.SourceUnitCoulomb.promise_of_hubbard_interval_oai := @OAI.ContinuumCoulomb.SourceUnitCoulomb.promise_of_hubbard_interval_oai
