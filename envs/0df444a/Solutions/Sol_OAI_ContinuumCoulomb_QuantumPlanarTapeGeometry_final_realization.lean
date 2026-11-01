-- Prove2me | solution 1 for OAI.ContinuumCoulomb.QuantumPlanarTapeGeometry.final_realization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:41:38.927263+00:00
-- url     : https://prove2.me/submissions/5b665b24-6a88-4ebe-a6ec-a30cda4d98f2

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.UpperLower.Basic
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
import Mathlib.Topology.Order.Compact
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_OAIQ092A010

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
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorBlocks
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

theorem spinMatrixOperator_add_norm_bound {α : Type*} [Fintype α] [DecidableEq α]
    (M N : Matrix α α ℂ) (K : ℝ) (hN : ‖spinMatrixOperator N‖ ≤ K) :
    ‖spinMatrixOperator (M + N)‖ ≤ ‖spinMatrixOperator M‖ + K := by
  rw [spinMatrixOperator_add]
  calc
    ‖spinMatrixOperator M + spinMatrixOperator N‖ ≤
        ‖spinMatrixOperator M‖ + ‖spinMatrixOperator N‖ := norm_add_le _ _
    _ ≤ ‖spinMatrixOperator M‖ + K := by linarith only [hN]

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

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorOffsets
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

end ContinuumCoulomb

end

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

end ContinuumCoulomb.MediatorGraph

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumExchangeRounding
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational coefficient rounding controls the full physical ground energy. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ : Type*} [Fintype κ]

theorem qmaExchangeMatrix_norm (left right : κ → Fin n) (hne : ∀ e, left e ≠ right e)
    (J : κ → ℝ) (constant : ℝ) :
    ‖spinMatrixOperator (qmaExchangeMatrix left right J constant)‖ ≤
      3*(∑ e, |J e|)+|constant| := by
  have hI : ‖spinMatrixOperator (1 : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)‖ ≤ 1 := by
    apply spinMatrixOperator_unitary_norm
    simp
  have hs : ‖spinMatrixOperator ((∑ e, (J e:ℂ) • sourceHeisenbergMatrix n (left e) (right e)))‖ ≤
      3*(∑ e, |J e|) := by
    rw [spinMatrixOperator_sum,Finset.mul_sum]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro e _
    rw [spinMatrixOperator_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_comm]
    exact mul_le_mul_of_nonneg_right (sourceHeisenbergMatrix_operator_norm n _ _ (hne e)) (abs_nonneg _)
  rw [qmaExchangeMatrix,spinMatrixOperator_add]
  apply (norm_add_le _ _).trans
  rw [spinMatrixOperator_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs]
  have hc := mul_le_mul_of_nonneg_left hI (abs_nonneg constant)
  linarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSingletStar
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.mediatorHighRestriction_apply _root_.OAI.ContinuumCoulomb.mediatorHighRestriction_inclusion _root_.OAI.ContinuumCoulomb.mediatorHighRestriction_low _root_.OAI.ContinuumCoulomb.mediatorLowRestriction_apply _root_.OAI.ContinuumCoulomb.mediatorLowRestriction_high _root_.OAI.ContinuumCoulomb.mediatorLowRestriction_inclusion _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted multi-terminal singlet stars for the lattice routing gadgets. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaPauliKernel_self (n : ℕ) (i : Fin n) : qmaPauliKernel n i i = (3:ℂ) • 1 := by
  simp only [qmaPauliKernel,sourceLocalPauli_sq]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  module

theorem qmaPauliKernel_eq (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    qmaPauliKernel n i j = sourceHeisenbergMatrix n i j := sourceLocalPauli_sum n i j hij

theorem qmaHeisenberg_symm (n : ℕ) (i j : Fin n) :
    sourceHeisenbergMatrix n i j = sourceHeisenbergMatrix n j i := by
  unfold sourceHeisenbergMatrix sourceSpinSwap
  rw [Equiv.swap_comm i j]

variable {κ : Type*} [Fintype κ]

theorem qmaSingletStar_compression (n r : ℕ) (Delta : ℝ) (e : Fin r)
    (site : κ → Fin n) (member : κ → Fin 2) (amplitude : κ → ℝ) :
    mediatorCompression n r (qmaSingletStar n r e site member amplitude *
      liftedMediatorInverse n r Delta * qmaSingletStar n r e site member amplitude) =
    ∑ a, ∑ b, (((amplitude a:ℂ)*(amplitude b:ℂ))*
      ((4*Delta)⁻¹:ℝ)*(if member a = member b then (1:ℂ) else -1)) •
        qmaPauliKernel n (site a) (site b) := by
  simp only [qmaSingletStar,Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm,
    map_sum,map_smul,mediatorAxisSpoke_compression,ite_true, if_true,qmaPauliKernel,smul_smul,Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  by_cases hm : member a = member b
  · simp only [hm,ite_true, if_true]
    ring_nf
  · simp only [hm,ite_false, if_false]
    ring_nf

/-- Separate singlet pairs have zero mixed second-order compression. -/
theorem qmaSingletStar_cross_zero (n r : ℕ) (Delta : ℝ) (e f : Fin r) (hef : e ≠ f)
    (site site' : κ → Fin n) (member member' : κ → Fin 2) (amplitude amplitude' : κ → ℝ) :
    mediatorCompression n r (qmaSingletStar n r e site member amplitude *
      liftedMediatorInverse n r Delta * qmaSingletStar n r f site' member' amplitude') = 0 := by
  simp only [qmaSingletStar,Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm,
    map_sum,map_smul,mediatorAxisSpoke_compression,hef,ite_false, if_false,smul_zero,Finset.sum_const_zero]

theorem qmaRoutingStars_compression (n r : ℕ) (Delta : ℝ)
    (site : Fin r → κ → Fin n) (member : Fin r → κ → Fin 2) (amplitude : Fin r → κ → ℝ) :
    mediatorCompression n r (qmaRoutingStars n r site member amplitude *
      liftedMediatorInverse n r Delta * qmaRoutingStars n r site member amplitude) =
    ∑ e, mediatorCompression n r (qmaSingletStar n r e (site e) (member e) (amplitude e) *
      liftedMediatorInverse n r Delta * qmaSingletStar n r e (site e) (member e) (amplitude e)) := by
  simp only [qmaRoutingStars,Finset.sum_mul,Finset.mul_sum,map_sum]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_eq_single e
  · intro f _ hfe
    exact qmaSingletStar_cross_zero n r Delta f e hfe _ _ _ _ _ _
  · simp

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingBlocks
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Low and high blocks for the finite singlet stars used in lattice routing. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

theorem routingCoupling_norm (n r : ℕ)
    (W : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ) :
    ‖routingCoupling n r W‖ ≤ ‖spinMatrixOperator W‖ := by
  unfold routingCoupling
  rw [ContinuousLinearMap.norm_restrictScalars]
  exact HubbardGlobal.coordinateCompression_norm _ _ _
    (mediatorHighRestriction_norm n r) (mediatorLowInclusion_norm n r)

theorem routingHighBlock_norm (n r : ℕ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (W : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ) :
    ‖routingHighBlock n r C W‖ ≤
      ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      ‖spinMatrixOperator W‖ := by
  unfold routingHighBlock
  rw [ContinuousLinearMap.norm_restrictScalars]
  exact (HubbardGlobal.coordinateCompression_norm _ _ _
    (mediatorHighRestriction_norm n r) (mediatorHighInclusion_norm n r)).trans
      (spinMatrixOperator_add_norm_bound _ _ _ le_rfl)

theorem routing_second_order (n r : ℕ) {Delta : ℝ} (hDelta : 0 < Delta)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (W : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1 / 4)
    (hbound : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      ‖spinMatrixOperator W‖ ≤ epsilon * (4 * Delta)) :
    |Perturbation.lowBlockBottom (actualMediatorLowBlock n r C)
        (diagonalPenalty (actualMediatorWeight n r Delta))
        (routingHighBlock n r C W) (routingCoupling n r W) -
      Perturbation.effectiveBottom (actualMediatorLowBlock n r C)
        (diagonalPenalty (fun s => (actualMediatorWeight n r Delta s)⁻¹))
        (routingCoupling n r W)| ≤ 16 * Delta * epsilon ^ 3 := by
  obtain ⟨hAT, hT, hgap⟩ := actualMediator_inverse_data n r hDelta
  have hg : 0 < 4 * Delta := by positivity
  have hB : ‖routingCoupling n r W‖ ≤ epsilon * (4 * Delta) :=
    (routingCoupling_norm n r W).trans
      ((le_add_of_nonneg_left (norm_nonneg _)).trans hbound)
  have hC : ‖actualMediatorLowBlock n r C‖ ≤ epsilon * (4 * Delta) :=
    (actualMediatorLowBlock_norm n r C).trans
      ((le_add_of_nonneg_right (norm_nonneg _)).trans hbound)
  have hD := (routingHighBlock_norm n r C W).trans hbound
  have hu : ‖(EuclideanSpace.single (fun _ : Fin n => (0 : Fin 2)) (1 : ℂ) :
      MediatorLowSpace n)‖ = 1 := by simp
  convert Perturbation.finite_lowBlockBottom_second_order
    (actualMediatorLowBlock n r C) (diagonalPenalty (actualMediatorWeight n r Delta))
    (diagonalPenalty (fun s => (actualMediatorWeight n r Delta s)⁻¹))
    (routingHighBlock n r C W) (routingCoupling n r W)
    hg hepsilon hsmall hAT (diagonalPenalty_symmetric _)
    (fun q => (mul_nonneg hg.le (sq_nonneg ‖q‖)).trans (hgap q)) hgap hT hB hC hD _ hu using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact quadratic forms for the finite singlet routing gadgets. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

theorem routingLowRestriction_low (n r : ℕ)
    (W : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ)
    (hWlow : mediatorCompression n r W = 0) (p : MediatorLowSpace n) :
    mediatorLowRestriction n r (spinMatrixOperator W
      (mediatorLowInclusion n r p)) = 0 := by
  have h := congrArg (fun T : MediatorLowSpace n →L[ℂ] MediatorLowSpace n => T p)
    (mediatorLow_operator_compression n r W)
  simpa only [ContinuousLinearMap.comp_apply, hWlow,
    spinMatrixOperator_zero, _root_.zero_apply] using h

/-- Hopping a singlet-sector state creates only actual mediator excitations. -/
theorem routingHighInclusion_coupling (n r : ℕ)
    (W : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ)
    (hWlow : mediatorCompression n r W = 0) (p : MediatorLowSpace n) :
    mediatorHighInclusion n r (routingCoupling n r W p) =
      spinMatrixOperator W
        (mediatorLowInclusion n r p) := by
  change mediatorHighInclusion n r (mediatorHighRestriction n r
    (spinMatrixOperator W
      (mediatorLowInclusion n r p))) = _
  have h := mediator_full_decomposition n r
    (spinMatrixOperator W
      (mediatorLowInclusion n r p))
  simpa only [routingLowRestriction_low n r W hWlow, map_zero, zero_add] using h

/-- Exact effective quadratic form for every entangled original-spin vector. -/
theorem routing_effectiveForm (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (W : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ)
    (hW : W.conjTranspose = W) (hWlow : mediatorCompression n r W = 0)
    (p : MediatorLowSpace n) :
    Perturbation.effectiveForm (actualMediatorLowBlock n r C)
      (diagonalPenalty (fun s => (actualMediatorWeight n r Delta s)⁻¹))
      (routingCoupling n r W) p =
      ⟪p, spinMatrixOperator (C - mediatorCompression n r
        (W * liftedMediatorInverse n r Delta *
          W)) p⟫_ℝ := by
  let B := routingCoupling n r W
  let T := diagonalPenalty (fun s => (actualMediatorWeight n r Delta s)⁻¹)
  have hB : mediatorHighInclusion n r (B p) = spinMatrixOperator W (mediatorLowInclusion n r p) :=
    routingHighInclusion_coupling n r W hWlow p
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
        (spinMatrixOperator_real_symmetric W hW _ _).symm
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


/-- Full-state quadratic-form equality for the concrete low/high blocks. -/
theorem routingHamiltonian_form_blocks (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    (W : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ)
    (hW : W.conjTranspose = W) (hWlow : mediatorCompression n r W = 0)
    (p : MediatorLowSpace n) (q : MediatorHighSpace n r) :
    ⟪assembleMediator n r p q,
      spinMatrixOperator (routingHamiltonian n r Delta C W)
        (assembleMediator n r p q)⟫_ℝ =
      Perturbation.lowBlockEnergy (actualMediatorLowBlock n r C)
        (diagonalPenalty (actualMediatorWeight n r Delta))
        (routingHighBlock n r C W)
        (routingCoupling n r W) p q := by
  let H := spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ) + W)
  let P := spinMatrixOperator (bellMediatorPenaltyMatrix n r Delta)
  let lp := mediatorLowInclusion n r p
  let hq := mediatorHighInclusion n r q
  have hHermitian : (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ) + W).conjTranspose =
      C ⊗ₖ 1 + W := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_kronecker, hC,
      Matrix.conjTranspose_one, hW]
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
      mediatorLow_real_inner, routingLowRestriction_low n r W hWlow, inner_zero_right, add_zero,
      actualMediatorLowBlock_eq]
    rfl
  have hCross : ⟪hq, H lp⟫_ℝ =
      ⟪q, routingCoupling n r W p⟫_ℝ := by
    rw [hHlow, inner_add_right, mediatorHigh_real_inner, mediatorHighRestriction_low,
      inner_zero_right, zero_add, mediatorHigh_real_inner]
    rfl
  have hReverse : ⟪lp, H hq⟫_ℝ =
      ⟪q, routingCoupling n r W p⟫_ℝ := by
    rw [spinMatrixOperator_real_symmetric _ hHermitian, real_inner_comm, hCross]
  have hHigh : ⟪hq, H hq⟫_ℝ =
      ⟪q, routingHighBlock n r C W q⟫_ℝ := by
    rw [mediatorHigh_real_inner]
    rfl
  have hform : ⟪assembleMediator n r p q,
      spinMatrixOperator (routingHamiltonian n r Delta C W)
        (assembleMediator n r p q)⟫_ℝ =
      ⟪lp + hq, P (lp + hq) + H (lp + hq)⟫_ℝ := by
    unfold routingHamiltonian assembleMediator
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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ground-energy comparison on the complete spin space for routing gadgets. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

theorem routingFullBottom_eq_lowBlockBottom (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    (W : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ)
    (hW : W.conjTranspose = W) (hWlow : mediatorCompression n r W = 0) :
    mediatorFullBottom n r (routingHamiltonian n r Delta C W) =
      Perturbation.lowBlockBottom (actualMediatorLowBlock n r C)
        (diagonalPenalty (actualMediatorWeight n r Delta))
        (routingHighBlock n r C W)
        (routingCoupling n r W) := by
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
    rw [← routingHamiltonian_form_blocks n r Delta C hC W hW hWlow,
      ← assembleMediator_norm_sq, hassemble]
  · rintro ⟨p, q, hpq, rfl⟩
    refine ⟨assembleMediator n r p q, ?_, ?_⟩
    · rw [assembleMediator_norm_sq]
      exact hpq
    · rw [routingHamiltonian_form_blocks n r Delta C hC W hW hWlow,
        assembleMediator_norm_sq]
      rfl

theorem routing_effectiveBottom_matrix (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (W : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ)
    (hW : W.conjTranspose = W) (hWlow : mediatorCompression n r W = 0) :
    Perturbation.effectiveBottom (actualMediatorLowBlock n r C)
      (diagonalPenalty (fun s => (actualMediatorWeight n r Delta s)⁻¹))
      (routingCoupling n r W) =
      sourceMatrixBottom n (C - mediatorCompression n r
        (W * liftedMediatorInverse n r Delta *
          W)) := by
  unfold Perturbation.effectiveBottom sourceMatrixBottom
  simp_rw [routing_effectiveForm n r Delta C W hW hWlow]

theorem routing_bottom (n r : ℕ) {Delta : ℝ} (hDelta : 0 < Delta)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    (W : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ)
    (hW : W.conjTranspose = W) (hWlow : mediatorCompression n r W = 0)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1 / 4)
    (hbound : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      ‖spinMatrixOperator W‖ ≤ epsilon * (4 * Delta)) :
    |mediatorFullBottom n r (routingHamiltonian n r Delta C W) -
      sourceMatrixBottom n (C - mediatorCompression n r
        (W * liftedMediatorInverse n r Delta * W))| ≤ 16 * Delta * epsilon ^ 3 := by
  have h := routing_second_order n r hDelta C W hepsilon hsmall hbound
  rw [← routingFullBottom_eq_lowBlockBottom n r Delta C hC W hW hWlow,
    routing_effectiveBottom_matrix n r Delta C W hW hWlow] at h
  exact h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSingletStarBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.mediatorHighRestriction_apply _root_.OAI.ContinuumCoulomb.mediatorHighRestriction_inclusion _root_.OAI.ContinuumCoulomb.mediatorHighRestriction_low _root_.OAI.ContinuumCoulomb.mediatorLowRestriction_apply _root_.OAI.ContinuumCoulomb.mediatorLowRestriction_high _root_.OAI.ContinuumCoulomb.mediatorLowRestriction_inclusion _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.ContinuumCoulomb.spinMatrixOperator_diagonal _root_.OAI.ContinuumCoulomb.spinMatrixOperator_sub _root_.OAI.ContinuumCoulomb.spinMatrixOperator_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full-space norm and low-sector facts for the routing singlet stars. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {κ : Type*} [Fintype κ]

theorem mediatorAxisSpoke_star (n r : ℕ) (e : Fin r) (i : Fin n) (member : Fin 2) :
    (mediatorAxisSpoke n r e i member).conjTranspose = mediatorAxisSpoke n r e i member := by
  simp only [mediatorAxisSpoke,Matrix.conjTranspose_sum,elementaryMediatorSpoke_star]

theorem mediatorAxisSpoke_norm (n r : ℕ) (e : Fin r) (i : Fin n) (member : Fin 2) :
    ‖spinMatrixOperator (mediatorAxisSpoke n r e i member)‖ ≤ 3 := by
  rw [mediatorAxisSpoke,spinMatrixOperator_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _μ : Fin 3, (1:ℝ) := Finset.sum_le_sum (fun μ _ =>
      elementaryMediatorSpoke_operator_norm n r e member μ i)
    _ = 3 := by norm_num

theorem qmaSingletStar_star (n r : ℕ) (e : Fin r) (site : κ → Fin n)
    (member : κ → Fin 2) (amplitude : κ → ℝ) :
    (qmaSingletStar n r e site member amplitude).conjTranspose =
      qmaSingletStar n r e site member amplitude := by
  simp only [qmaSingletStar,Matrix.conjTranspose_sum,Matrix.conjTranspose_smul,
    Complex.star_def,Complex.conj_ofReal,mediatorAxisSpoke_star]

theorem qmaSingletStar_norm (n r : ℕ) (e : Fin r) (site : κ → Fin n)
    (member : κ → Fin 2) (amplitude : κ → ℝ) :
    ‖spinMatrixOperator (qmaSingletStar n r e site member amplitude)‖ ≤
      3*∑ a, |amplitude a| := by
  rw [qmaSingletStar,spinMatrixOperator_sum,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  rw [spinMatrixOperator_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_comm]
  exact mul_le_mul_of_nonneg_right (mediatorAxisSpoke_norm n r e _ _) (abs_nonneg _)

theorem qmaSingletStar_low (n r : ℕ) (e : Fin r) (site : κ → Fin n)
    (member : κ → Fin 2) (amplitude : κ → ℝ) :
    mediatorCompression n r (qmaSingletStar n r e site member amplitude) = 0 := by
  simp only [qmaSingletStar,mediatorAxisSpoke,map_sum,map_smul,
    elementaryMediatorSpoke_low_compression,Finset.sum_const_zero,smul_zero]

theorem qmaRoutingStars_star (n r : ℕ) (site : Fin r → κ → Fin n)
    (member : Fin r → κ → Fin 2) (amplitude : Fin r → κ → ℝ) :
    (qmaRoutingStars n r site member amplitude).conjTranspose =
      qmaRoutingStars n r site member amplitude := by
  simp only [qmaRoutingStars,Matrix.conjTranspose_sum,qmaSingletStar_star]

theorem qmaRoutingStars_low (n r : ℕ) (site : Fin r → κ → Fin n)
    (member : Fin r → κ → Fin 2) (amplitude : Fin r → κ → ℝ) :
    mediatorCompression n r (qmaRoutingStars n r site member amplitude) = 0 := by
  simp only [qmaRoutingStars,map_sum,qmaSingletStar_low,Finset.sum_const_zero]

theorem qmaRoutingStars_norm (n r : ℕ) (site : Fin r → κ → Fin n)
    (member : Fin r → κ → Fin 2) (amplitude : Fin r → κ → ℝ) :
    ‖spinMatrixOperator (qmaRoutingStars n r site member amplitude)‖ ≤
      3*∑ e, ∑ a, |amplitude e a| := by
  rw [qmaRoutingStars,spinMatrixOperator_sum,Finset.mul_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun e _ =>
    qmaSingletStar_norm n r e (site e) (member e) (amplitude e)))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSingletStarSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ground-energy estimate for the finite singlet stars used in routing. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {κ : Type*} [Fintype κ]

theorem qmaRoutingStars_bottom (n r : ℕ) {Delta : ℝ} (hDelta : 0 < Delta)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    (site : Fin r → κ → Fin n) (member : Fin r → κ → Fin 2) (amplitude : Fin r → κ → ℝ)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1/4)
    (hbound : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      3*∑ e, ∑ a, |amplitude e a| ≤ epsilon * (4*Delta)) :
    |mediatorFullBottom n r (routingHamiltonian n r Delta C
        (qmaRoutingStars n r site member amplitude)) -
      sourceMatrixBottom n (C - mediatorCompression n r
        (qmaRoutingStars n r site member amplitude * liftedMediatorInverse n r Delta *
          qmaRoutingStars n r site member amplitude))| ≤ 16*Delta*epsilon^3 := by
  have hb : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      ‖spinMatrixOperator (qmaRoutingStars n r site member amplitude)‖ ≤ epsilon * (4*Delta) := by
    calc
      _ ≤ ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
          3*∑ e, ∑ a, |amplitude e a| := add_le_add le_rfl (qmaRoutingStars_norm n r site member amplitude)
      _ ≤ epsilon * (4*Delta) := hbound
  exact routing_bottom n r hDelta C hC (qmaRoutingStars n r site member amplitude)
    (qmaRoutingStars_star n r site member amplitude)
    (qmaRoutingStars_low n r site member amplitude) hepsilon hsmall hb

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingPhysical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual physical spin interactions for the singlet routing construction. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace
variable {κ : Type*} [Fintype κ]

theorem qmaPhysicalSingletStar_transform (n r : ℕ) (e : Fin r) (site : κ → Fin n)
    (member : κ → Fin 2) (amplitude : κ → ℝ) :
    (fullMediatorBellMatrix n r).conjTranspose *
      qmaPhysicalSingletStar n r e site member amplitude * fullMediatorBellMatrix n r =
      qmaSingletStar n r e site member amplitude := by
  simp only [qmaPhysicalSingletStar,qmaSingletStar,mediatorAxisSpoke,
    Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,physicalSpoke_bellTransform]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit ordinary-spin edges for a routing star, with the central offset. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix MediatorGraph
open scoped BigOperators Kronecker Classical
variable {ν κ : Type*} [Fintype ν] [Fintype κ]

theorem qmaExchangeMatrix_lift {n r : ℕ} (left right : ν → Fin n)
    (hneq : ∀ a, left a ≠ right a) (weight : ν → ℝ) (constant : ℝ) :
    (qmaExchangeMatrix (fun a => old n r (left a)) (fun a => old n r (right a))
      weight constant).submatrix (basisEquiv n r) (basisEquiv n r) =
        qmaExchangeMatrix left right weight constant ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ) := by
  simp only [qmaExchangeMatrix,submatrix_add_apply,submatrix_sum,submatrix_smul_apply,
    Matrix.submatrix_one_equiv,heisenberg_old n r _ _ (hneq _),Matrix.add_kronecker,
    Matrix.smul_kronecker,Matrix.one_kronecker_one,sum_kronecker]

theorem qmaExchangeMatrix_lift_norm {n r : ℕ} (left right : ν → Fin n)
    (hneq : ∀ a, left a ≠ right a) (weight : ν → ℝ) (constant : ℝ) :
    ‖spinMatrixOperator (qmaExchangeMatrix left right weight constant ⊗ₖ
      (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ ≤
      3*(∑ a, |weight a|)+|constant| := by
  rw [← qmaExchangeMatrix_lift left right hneq weight constant,reindex_operator_norm]
  exact qmaExchangeMatrix_norm _ _ (fun a h => hneq a (old_injective n r h)) weight constant

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingScale
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial penalty choice for the second-order routing gadgets. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Kronecker

theorem qmaRoutingScale_bounds {A B N : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hN : 0 < N) :
    let R := qmaRoutingScale A B N
    0 < R ∧ 0 ≤ (A+B+1)/R ∧ (A+B+1)/R ≤ 1/4 ∧
      B+A*R ≤ ((A+B+1)/R)*(4*R^2) ∧
      16*R^2*((A+B+1)/R)^3 ≤ 1/N := by
  let Q := A+B+1
  have hQ : 0 < Q := by dsimp [Q]; linarith
  have hq3 : 0 ≤ 16*Q^3*N := by positivity
  have hR : 0 < qmaRoutingScale A B N := by
    change 0 < 16*Q^3*N+4*Q+1
    positivity
  have hR1 : 1 ≤ qmaRoutingScale A B N := by
    change 1 ≤ 16*Q^3*N+4*Q+1
    nlinarith
  have hR4 : 4*Q ≤ qmaRoutingScale A B N := by
    change 4*Q ≤ 16*Q^3*N+4*Q+1
    linarith
  have hR16 : 16*Q^3*N ≤ qmaRoutingScale A B N := by
    change 16*Q^3*N ≤ 16*Q^3*N+4*Q+1
    linarith
  refine ⟨hR,div_nonneg hQ.le hR.le,?_,?_,?_⟩
  · apply (div_le_iff₀ hR).mpr
    change Q ≤ (1/4)*qmaRoutingScale A B N
    linarith
  · have heq : (Q/qmaRoutingScale A B N)*(4*qmaRoutingScale A B N^2) =
        4*Q*qmaRoutingScale A B N := by field_simp
    change B+A*qmaRoutingScale A B N ≤ (Q/qmaRoutingScale A B N)*(4*qmaRoutingScale A B N^2)
    rw [heq]
    have hbR := mul_le_mul_of_nonneg_left hR1 hB
    have hqR := mul_nonneg hQ.le hR.le
    dsimp [Q] at *
    nlinarith
  · change 16*qmaRoutingScale A B N^2*(Q/qmaRoutingScale A B N)^3 ≤ 1/N
    have heq : 16*qmaRoutingScale A B N^2*(Q/qmaRoutingScale A B N)^3 =
        16*Q^3/qmaRoutingScale A B N := by field_simp
    rw [heq]
    apply (div_le_iff₀ hR).mpr
    simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one] using (le_div_iff₀ hN).mpr hR16

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumParallelGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit ordinary-spin graph for an entire parallel singlet-routing layer. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix MediatorGraph
open scoped BigOperators Kronecker Classical
variable {ν κ : Type*} [Fintype ν] [Fintype κ]

theorem qmaParallelGraph_matrix {n r : ℕ} (left right : ν → Fin n)
    (hneq : ∀ a, left a ≠ right a) (weight : ν → ℝ) (constant Delta : ℝ)
    (site : Fin r → κ → Fin n) (member : Fin r → κ → Fin 2) (amplitude : Fin r → κ → ℝ) :
    (qmaExchangeMatrix (qmaParallelGraphLeft left site) (qmaParallelGraphRight right member)
      (qmaParallelGraphWeight weight Delta amplitude) (constant+3*r*Delta)).submatrix
        (basisEquiv n r) (basisEquiv n r) =
      qmaPhysicalParallelHamiltonian n r Delta (qmaExchangeMatrix left right weight constant)
        site member amplitude := by
  simp only [qmaExchangeMatrix,Fintype.sum_sum_type,Fintype.sum_prod_type,
    qmaParallelGraphLeft,qmaParallelGraphRight,qmaParallelGraphWeight,
    submatrix_add_apply,submatrix_sum,submatrix_smul_apply,
    Matrix.submatrix_one_equiv,heisenberg_old n r _ _ (hneq _),heisenberg_central,
    heisenberg_spoke]
  unfold qmaPhysicalParallelHamiltonian qmaPhysicalSingletStar
  rw [physicalMediatorPenalty_offset]
  simp only [Matrix.add_kronecker,Matrix.kronecker_add,Matrix.smul_kronecker,
    Matrix.kronecker_smul,Matrix.one_kronecker_one,sum_kronecker,kronecker_sum,
    Complex.ofReal_add,add_smul,Finset.smul_sum]
  abel

theorem qmaPhysicalParallel_transform (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (site : Fin r → κ → Fin n) (member : Fin r → κ → Fin 2) (amplitude : Fin r → κ → ℝ) :
    (fullMediatorBellMatrix n r).conjTranspose *
      qmaPhysicalParallelHamiltonian n r Delta C site member amplitude *
        fullMediatorBellMatrix n r =
      routingHamiltonian n r Delta C (qmaRoutingStars n r site member amplitude) := by
  simp only [qmaPhysicalParallelHamiltonian,routingHamiltonian,qmaRoutingStars,mul_add,
    add_mul,Finset.mul_sum,Finset.sum_mul,physicalMediatorPenalty_full_transform,
    liftedSource_full_transform,qmaPhysicalSingletStar_transform]

theorem qmaPhysicalParallel_bottom (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (site : Fin r → κ → Fin n) (member : Fin r → κ → Fin 2) (amplitude : Fin r → κ → ℝ) :
    mediatorFullBottom n r (qmaPhysicalParallelHamiltonian n r Delta C site member amplitude) =
      mediatorFullBottom n r (routingHamiltonian n r Delta C (qmaRoutingStars n r site member amplitude)) := by
  have h := mediatorFullBottom_unitary n r (fullMediatorBellMatrix n r)
    (qmaPhysicalParallelHamiltonian n r Delta C site member amplitude)
    (fullMediatorBellMatrix_gram n r) (fullMediatorBellMatrix_cogram n r)
  rw [qmaPhysicalParallel_transform] at h
  exact h.symm

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathSubdivision
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational two-edge and three-edge exchange subdivision, including the
pendant singlet partner needed by an even-length lattice path. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaPathSubdivision_effective {n r : ℕ} (e : Fin r) (site : Fin 2 → Fin n)
    (hsite : Function.Injective site) (even : Bool) (R J : ℝ) (hR : R ≠ 0) :
    qmaPathCorrection R J - mediatorCompression n r
      (qmaSingletStar n r e site (qmaPathMember even) (qmaPathAmplitude even R J) *
        liftedMediatorInverse n r (R^2) *
          qmaSingletStar n r e site (qmaPathMember even) (qmaPathAmplitude even R J)) =
      (J:ℂ) • sourceHeisenbergMatrix n (site 0) (site 1) := by
  have hk (a b : Fin 2) : qmaPauliKernel n (site a) (site b) =
      if a = b then (3:ℂ) • 1 else sourceHeisenbergMatrix n (site a) (site b) := by
    by_cases hab : a = b
    · subst b
      simp only [ite_true, if_true,qmaPauliKernel_self]
    · rw [ite_eq_right hab]
      exact qmaPauliKernel_eq n _ _ (fun h => hab (hsite h))
  rw [qmaSingletStar_compression]
  simp only [hk,qmaPathCorrection]
  cases even <;>
    simp [qmaPathMember,qmaPathAmplitude,Fin.sum_univ_succ] <;>
    rw [qmaHeisenberg_symm n (site 1) (site 0)] <;>
    ext s t <;>
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.neg_apply,Matrix.smul_apply,
      smul_eq_mul,RCLike.real_smul_eq_coe_smul (K := ℂ),RCLike.ofReal_eq_complex_ofReal] <;>
    have hRC : (R:ℂ) ≠ 0 := by exact_mod_cast hR
  all_goals field_simp [hRC]; ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathsParallel
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A whole layer of independently even or odd path subdivisions. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

theorem qmaPaths_effective {n r : ℕ} (site : Fin r → Fin 2 → Fin n)
    (hsite : ∀ e, Function.Injective (site e)) (even : Fin r → Bool)
    (R : ℝ) (hR : R ≠ 0) (J : Fin r → ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :
    (C + ∑ e, qmaPathCorrection (n := n) R (J e)) -
      mediatorCompression n r (qmaRoutingStars n r site (fun e => qmaPathMember (even e))
          (fun e => qmaPathAmplitude (even e) R (J e)) * liftedMediatorInverse n r (R^2) *
        qmaRoutingStars n r site (fun e => qmaPathMember (even e))
          (fun e => qmaPathAmplitude (even e) R (J e))) =
      C + ∑ e, (J e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 1) := by
  rw [qmaRoutingStars_compression,add_sub_assoc,← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  exact qmaPathSubdivision_effective e (site e) (hsite e) (even e) R (J e) hR

theorem qmaPaths_bottom {n r : ℕ} (site : Fin r → Fin 2 → Fin n)
    (hsite : ∀ e, Function.Injective (site e)) (even : Fin r → Bool)
    (R : ℝ) (hR : 0 < R) (J : Fin r → ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1/4)
    (hbound : ‖spinMatrixOperator ((C + ∑ e, qmaPathCorrection (n := n) R (J e)) ⊗ₖ
        (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      3*∑ e, ∑ a, |qmaPathAmplitude (even e) R (J e) a| ≤ epsilon*(4*R^2)) :
    |mediatorFullBottom n r (routingHamiltonian n r (R^2)
        (C + ∑ e, qmaPathCorrection (n := n) R (J e))
        (qmaRoutingStars n r site (fun e => qmaPathMember (even e))
          (fun e => qmaPathAmplitude (even e) R (J e)))) -
      sourceMatrixBottom n (C + ∑ e,
        (J e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 1))| ≤ 16*R^2*epsilon^3 := by
  have hCW : (C + ∑ e, qmaPathCorrection (n := n) R (J e)).conjTranspose =
      C + ∑ e, qmaPathCorrection (n := n) R (J e) := by
    simp only [qmaPathCorrection,Matrix.conjTranspose_add,Matrix.conjTranspose_sum,hC,
      Matrix.conjTranspose_smul,Matrix.conjTranspose_one,Complex.star_def,Complex.conj_ofReal]
  have h := qmaRoutingStars_bottom n r (sq_pos_of_pos hR) _ hCW site
    (fun e => qmaPathMember (even e)) (fun e => qmaPathAmplitude (even e) R (J e))
    hepsilon hsmall hbound
  rw [qmaPaths_effective site hsite even R hR.ne' J C] at h
  exact h

theorem qmaPathAmplitude_norm (even : Bool) (R J : ℝ) (hR : 0 ≤ R) :
    3*(∑ a, |qmaPathAmplitude even R J a|) = 3*R*(1+2*|J|) := by
  cases even <;> simp [qmaPathAmplitude,Fin.sum_univ_succ,abs_mul,abs_of_nonneg hR] <;> ring

theorem qmaPathCorrection_lift_norm (n r : ℕ) (R J : ℝ) :
    ‖spinMatrixOperator (qmaPathCorrection (n := n) R J ⊗ₖ
      (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ ≤ 4*(1+|J|)^2 := by
  have hI : ‖spinMatrixOperator (1 : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ)‖ ≤ 1 := by
    apply spinMatrixOperator_unitary_norm
    simp
  rw [qmaPathCorrection,Matrix.smul_kronecker,Matrix.one_kronecker_one,spinMatrixOperator_smul,
    norm_smul,Complex.norm_real,Real.norm_eq_abs]
  have hoff : 0 ≤ 3/4+3*J^2 := by positivity
  rw [abs_of_nonneg hoff]
  calc
    _ ≤ (3/4+3*J^2)*1 := mul_le_mul_of_nonneg_left hI hoff
    _ ≤ _ := by nlinarith [sq_abs J,abs_nonneg J]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathsCalibration
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial penalty for a simultaneous layer of arbitrary parity subdivisions. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

theorem qmaPaths_correction_norm (n r : ℕ) (R : ℝ) (J : Fin r → ℝ) :
    ‖spinMatrixOperator ((∑ e, qmaPathCorrection (n := n) R (J e)) ⊗ₖ
      (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ ≤
      4*∑ e, (1+|J e|)^2 := by
  rw [MediatorGraph.sum_kronecker,spinMatrixOperator_sum,Finset.mul_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun e _ =>
    qmaPathCorrection_lift_norm n r R (J e)))

theorem qmaPaths_amplitude (r : ℕ) (even : Fin r → Bool) (R : ℝ) (hR : 0 ≤ R) (J : Fin r → ℝ) :
    3*(∑ e, ∑ a, |qmaPathAmplitude (even e) R (J e) a|) =
      (3*∑ e, (1+2*|J e|))*R := by
  rw [Finset.mul_sum]
  simp_rw [qmaPathAmplitude_norm _ R _ hR]
  rw [← Finset.mul_sum]
  ring

theorem qmaPaths_accuracy {n r : ℕ} (site : Fin r → Fin 2 → Fin n)
    (hsite : ∀ e, Function.Injective (site e)) (even : Fin r → Bool) (J : Fin r → ℝ)
    {B N : ℝ} (hB : 0 ≤ B) (hN : 0 < N)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    (hCn : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ ≤ B) :
    let A := 3*∑ e, (1+2*|J e|)
    let D := B+4*∑ e, (1+|J e|)^2
    let R := qmaRoutingScale A D N
    |mediatorFullBottom n r (routingHamiltonian n r (R^2)
        (C + ∑ e, qmaPathCorrection (n := n) R (J e))
        (qmaRoutingStars n r site (fun e => qmaPathMember (even e))
          (fun e => qmaPathAmplitude (even e) R (J e)))) -
      sourceMatrixBottom n (C + ∑ e,
        (J e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 1))| ≤ 1/N := by
  let A := 3*∑ e, (1+2*|J e|)
  let D := B+4*∑ e, (1+|J e|)^2
  let R := qmaRoutingScale A D N
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨hR,he,hes,hbound,herr⟩ := qmaRoutingScale_bounds hA hD hN
  have hCC : ‖spinMatrixOperator ((C + ∑ e, qmaPathCorrection (n := n) R (J e)) ⊗ₖ
      (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ ≤ D := by
    rw [Matrix.add_kronecker,spinMatrixOperator_add]
    exact (norm_add_le _ _).trans (add_le_add hCn (qmaPaths_correction_norm n r R J))
  have hb : ‖spinMatrixOperator ((C + ∑ e, qmaPathCorrection (n := n) R (J e)) ⊗ₖ
        (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      3*∑ e, ∑ a, |qmaPathAmplitude (even e) R (J e) a| ≤ ((A+D+1)/R)*(4*R^2) := by
    rw [qmaPaths_amplitude r even R hR.le J]
    exact (add_le_add hCC (le_refl (A*R))).trans hbound
  exact (qmaPaths_bottom site hsite even R hR J C hC he hes hb).trans herr

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathsGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit ordinary-spin edges for simultaneous path subdivisions. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix MediatorGraph
open scoped BigOperators Kronecker Classical
variable {ν : Type*} [Fintype ν]

theorem qmaPathsBase_matrix {n r : ℕ} (left right : ν → Fin n) (weight : ν → ℝ)
    (constant R : ℝ) (J : Fin r → ℝ) :
    qmaExchangeMatrix left right weight (constant+∑ e, qmaPathOffset (J e)) =
      qmaExchangeMatrix left right weight constant +
        ∑ e, qmaPathCorrection (n := n) R (J e) := by
  simp only [qmaExchangeMatrix,qmaPathCorrection,qmaPathOffset,
    Complex.ofReal_add,Complex.ofReal_sum,add_smul,Finset.sum_smul]
  abel

theorem qmaPathsGraph_matrix {n r : ℕ} (left right : ν → Fin n)
    (hneq : ∀ a, left a ≠ right a) (weight : ν → ℝ) (constant R : ℝ)
    (site : Fin r → Fin 2 → Fin n) (even : Fin r → Bool) (J : Fin r → ℝ) :
    (qmaPathsGraph left right weight constant R site even J).submatrix
      (basisEquiv n r) (basisEquiv n r) =
      qmaPhysicalParallelHamiltonian n r (R^2)
        (qmaExchangeMatrix left right weight constant+∑ e, qmaPathCorrection (n := n) R (J e))
        site (fun e => qmaPathMember (even e)) (fun e => qmaPathAmplitude (even e) R (J e)) := by
  unfold qmaPathsGraph
  have h := qmaParallelGraph_matrix left right hneq weight
      (constant+∑ e, qmaPathOffset (J e)) (R^2)
      site (fun e => qmaPathMember (even e)) (fun e => qmaPathAmplitude (even e) R (J e))
  rw [qmaPathsBase_matrix left right weight constant R J] at h
  exact h

theorem qmaPathsGraph_accuracy {n r : ℕ} (left right : ν → Fin n)
    (hneq : ∀ a, left a ≠ right a) (weight : ν → ℝ) (constant : ℝ)
    (site : Fin r → Fin 2 → Fin n) (hsite : ∀ e, Function.Injective (site e))
    (even : Fin r → Bool) (J : Fin r → ℝ) {N : ℝ} (hN : 0 < N) :
    let B := 3*(∑ a, |weight a|)+|constant|
    let A := 3*∑ e, (1+2*|J e|)
    let D := B+4*∑ e, (1+|J e|)^2
    let R := qmaRoutingScale A D N
    |sourceMatrixBottom (n+r*2) (qmaPathsGraph left right weight constant R site even J) -
      sourceMatrixBottom n (qmaExchangeMatrix left right weight constant + ∑ e,
        (J e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 1))| ≤ 1/N := by
  dsimp only
  rw [sourceMatrixBottom_eq_mediator n r,qmaPathsGraph_matrix left right hneq weight constant,
    qmaPhysicalParallel_bottom]
  have hC : (qmaExchangeMatrix left right weight constant).conjTranspose =
      qmaExchangeMatrix left right weight constant := by
    simp only [qmaExchangeMatrix,Matrix.conjTranspose_add,Matrix.conjTranspose_sum,
      Matrix.conjTranspose_smul,sourceHeisenbergMatrix_star n _ _ (hneq _),
      Complex.star_def,Complex.conj_ofReal,Matrix.conjTranspose_one]
  exact qmaPaths_accuracy site hsite even J (by positivity) hN _ hC
    (qmaExchangeMatrix_lift_norm left right hneq weight constant)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial coefficient program for both parities of a path gadget. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPathCode
open ExactQuantumFactoring.BitStackProgram QuantumRoutingCode

theorem coefficients_offset (x : Input) :
    (coefficients x 3 : ℝ) = qmaPathOffset (x.2.2:ℝ)+3*(x.2.1:ℝ)^2 := by
  simp [coefficients,qmaPathOffset]

end ContinuumCoulomb.QuantumPathCode

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutedSubdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete odd-route realization with the actual rational Hamiltonian,
finite rectangle, degree bound and accumulated full-space spectral error. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped Classical
namespace QMAPathEmbedding
variable {W : QMAPathSchedule} {Γ : SimpleGraph (ℕ × ℕ)} (P : QMAPathEmbedding W Γ)

theorem next_bounded (N : ℚ) {X Y : ℕ} (h : P.Bounded X Y) : (P.next N).Bounded X Y := by
  constructor
  · change ∀ v : Fin (W.graph.n+W.active.card*2),
      (P.nextPosition v).1 < X ∧ (P.nextPosition v).2 < Y
    intro v
    obtain ⟨v,rfl⟩ := (vertexEquiv W.graph.n W.active.card).surjective v
    rcases v with v | ⟨i,b⟩
    · change (P.nextPosition (old _ _ v)).1 < X ∧ (P.nextPosition (old _ _ v)).2 < Y
      simpa only [nextPosition_old] using h.1 v
    · have hw := W.selected_work_pos i
      have hb := b.isLt
      change (P.nextPosition (fresh _ _ i b)).1 < X ∧ (P.nextPosition (fresh _ _ i b)).2 < Y
      simpa only [nextPosition_fresh,freshPosition] using
        h.2 (qmaSelectedIndex W.active i) (b.val+1) (by omega)
  · intro e k hk
    exact h.2 (W.nextParent e) (W.nextIndex e k) (W.nextIndex_bounds e hk)

end QMAPathEmbedding
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRouteEnumeration
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMACellRoute.reverse_body _root_.OAI.ContinuumCoulomb.QMACellRoute.reverse_source _root_.OAI.ContinuumCoulomb.QMACellRoute.reverse_target _root_.OAI.ContinuumCoulomb.QMACellRoute.reverse_valid _root_.OAI.ContinuumCoulomb.qmaPointCell_ancilla _root_.OAI.ContinuumCoulomb.qmaPointCell_inner _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Only 140 explicit catalog routes need be tested for a physical edge: the
seventy oriented routes in each endpoint cell. This supplies a fixed finite
search space for the literal planar-route compiler. -/

namespace ContinuumCoulomb

theorem qmaCellBodies_length (p : ℕ × ℕ) : (qmaCellBodies p).length = 35 := by
  simp [qmaCellBodies,List.length_flatMap]

theorem qmaCellRoutes_length (p : ℕ × ℕ) : (qmaCellRoutes p).length = 70 := by
  simp [qmaCellRoutes,List.length_flatMap,qmaCellBodies_length]

theorem qmaRouteCandidates_length (x y : ℕ × ℕ) : (qmaRouteCandidates x y).length = 140 := by
  simp [qmaRouteCandidates,qmaCellRoutes_length]

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCellRouteSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A catalog path stays in the cells of its two endpoints. This transfers
positivity and box bounds from physical spins to all subdivision sites. -/

namespace ContinuumCoulomb

namespace QMACellRoute

theorem path_bounded (R : QMACellRoute) {X Y : ℕ}
    (hs : R.source.1 < 32*X ∧ R.source.2 < 32*Y)
    (ht : R.target.1 < 32*X ∧ R.target.2 < 32*Y)
    {z : ℕ × ℕ} (hz : z ∈ R.path) : z.1 < 32*X ∧ z.2 < 32*Y := by
  have hp : (qmaPointCell z).1 < X ∧ (qmaPointCell z).2 < Y := by
    rcases R.path_cells hz with h | h
    · rw [h]
      change R.source.1/32 < X ∧ R.source.2/32 < Y
      omega
    · rw [h]
      change R.target.1/32 < X ∧ R.target.2/32 < Y
      omega
  change z.1/32 < X ∧ z.2/32 < Y at hp
  omega

end QMACellRoute
end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingTableCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite table is the data of the actual port routes. Its membership
tests agree exactly with the permissions used in the geometric proof. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
open QuantumRoutingTable
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem routingTable_source (p : ℕ × ℕ) :
    p ∈ P.routingTable.1 ↔ ∃ v, P.position v = p := by
  exact List.mem_ofFn

theorem routingTable_crossing (p : ℕ × ℕ) :
    p ∈ P.routingTable.2.2 ↔ P.IsCrossing p := by
  exact Finset.mem_toList.trans P.mem_crossingCells

theorem routingTable_allowed (R : QMACellRouteBody) :
    allowed P.routingTable R = true ↔ P.RoutingAllowed R := by
  cases R with
  | ray p a =>
    simp only [allowed,Bool.and_eq_true,Bool.not_eq_true_eq_eq_false,decide_eq_true_eq,
      decide_eq_false_iff_not,routingTable_source,routingTable_crossing,RoutingAllowed]
  | pair p e =>
    simp only [allowed,Bool.and_eq_true,Bool.not_eq_true_eq_eq_false,decide_eq_true_eq,
      decide_eq_false_iff_not,routingTable_pair,routingTable_crossing,RoutingAllowed]
  | patch p e =>
    simp only [allowed,decide_eq_true_eq,routingTable_crossing,RoutingAllowed]
  | corridor p a b c =>
    have h (q : ℕ × ℕ) : decide (q ∈ P.routingTable.2.2) = decide (P.IsCrossing q) := by
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq,P.routingTable_crossing]
    simp only [allowed,Bool.and_eq_true,decide_eq_true_eq,h,RoutingAllowed]

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRouteLeaf
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reserve one singlet leaf beside the initial step of every scaled route.
Four incident directions use four different quadrants. -/

namespace ContinuumCoulomb

theorem qmaRouteLeaf_bounds {X Y : ℕ} {p : ℕ × ℕ} (hx : p.1 < X) (hy : p.2 < Y)
    (a : Fin 4) : (qmaRouteLeaf p a).1 < 8*X ∧ (qmaRouteLeaf p a).2 < 8*Y := by
  fin_cases a <;> simp [qmaRouteLeaf] <;> omega

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListPathMatrix
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_old _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_fresh _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_old _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.ContinuumCoulomb.qmaSubdivisionCell_fresh _root_.OAI.ContinuumCoulomb.qmaSubdivisionCell_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix semantics of the literal path-subdivision block. Its fresh labels
are exactly the two ordinary-spin labels in the singlet gadget. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListPathProgram
open Matrix MediatorGraph MediatorListProgram
open scoped BigOperators

private theorem old_value (n r : ℕ) (i : Fin n) : (old n r i).val = i.val := rfl

private theorem fresh_value (n r : ℕ) (i : Fin r) (a : Fin 2) :
    (fresh n r i a).val = n+2*i.val+a.val := by
  change n+(a.val+2*i.val) = _
  omega

theorem bond_eq {n r : ℕ} (i : Fin r) (site : Fin 2 → Fin n) (even : Bool) (R J : ℚ)
    (k : Fin 3) :
    bond ((n,even,R),i.val,(site 0).val,(site 1).val,J) k =
      ((physicalLeft i site k).val,(physicalRight (n := n) i even k).val,
        QuantumPathCode.coefficients (even,R,J) k.castSucc) := by
  cases even <;> fin_cases k <;>
    simp [bond,left,right,coefficient,physicalLeft,physicalRight,qmaPathMember,fresh_value,old_value]

theorem block_matrix {n r : ℕ} (i : Fin r) (site : Fin 2 → Fin n) (even : Bool) (R J : ℚ) :
    SourceBondLists.matrix (n+r*2) (block ((n,even,R),i.val,(site 0).val,(site 1).val,J)) =
      ∑ k : Fin 3, (QuantumPathCode.coefficients (even,R,J) k.castSucc:ℂ) •
        sourceHeisenbergMatrix (n+r*2) (physicalLeft i site k) (physicalRight i even k) := by
  simp only [SourceBondLists.matrix,block,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [bond_eq,SourceBondLists.bondMatrix,dite_eq_left
    ⟨(physicalLeft i site k).isLt,(physicalRight i even k).isLt⟩]

theorem offset_cast (n i : ℕ) (site : Fin 2 → ℕ) (even : Bool) (R J : ℚ) :
    (offset ((n,even,R),i,site 0,site 1,J):ℝ) = qmaPathOffset (J:ℝ)+3*(R:ℝ)^2 :=
  QuantumPathCode.coefficients_offset (even,R,J)

theorem indexed_ofFn {m : ℕ} (p : Parameters) (f : Fin m → Bond) (i : Fin m) :
    indexed (i.val,(p,List.ofFn f)) = (p,i.val,f i) := by
  unfold indexed
  rw [List.headD_eq_head?_getD,List.head?_drop,
    List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using i.isLt)]
  simp only [List.getElem_ofFn,Option.getD_some]

theorem family_ofFn {m : ℕ} (p : Parameters) (f : Fin m → Bond) :
    family (p,List.ofFn f) = (List.ofFn fun i => block (p,i.val,f i)).flatten := by
  have hm (g : ℕ → List Bond) :
      (List.range m).map g = List.ofFn (fun i : Fin m => g i.val) := by
    simpa only [List.length_range,List.getElem_range,Fin.val_cast] using
      (List.ofFn_getElem_eq_map (List.range m) g).symm
  unfold family
  rw [List.length_ofFn,hm]
  apply congrArg List.flatten
  apply congrArg (fun g : Fin m → List Bond => List.ofFn g)
  funext i
  rw [indexed_ofFn]

theorem matrix_flatten (n : ℕ) (xss : List (List Bond)) :
    SourceBondLists.matrix n xss.flatten = (xss.map (SourceBondLists.matrix n)).sum := by
  simp only [SourceBondLists.matrix,List.map_flatten,List.sum_flatten,List.map_map,
    Function.comp_def]
  rfl

theorem family_matrix {n r : ℕ} (site : Fin r → Fin 2 → Fin n) (even : Bool)
    (R : ℚ) (J : Fin r → ℚ) :
    SourceBondLists.matrix (n+r*2)
      (family ((n,even,R),List.ofFn fun i => ((site i 0).val,(site i 1).val,J i))) =
      ∑ i : Fin r, ∑ k : Fin 3, (QuantumPathCode.coefficients (even,R,J i) k.castSucc:ℂ) •
        sourceHeisenbergMatrix (n+r*2) (physicalLeft i (site i) k) (physicalRight i even k) := by
  rw [family_ofFn,matrix_flatten]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  exact Finset.sum_congr rfl (fun i _ => block_matrix i (site i) even R (J i))

theorem physical_sum {n r : ℕ} (i : Fin r) (site : Fin 2 → Fin n) (even : Bool)
    (R J : ℚ) :
    (∑ k : Fin 3, (QuantumPathCode.coefficients (even,R,J) k.castSucc:ℂ) •
      sourceHeisenbergMatrix (n+r*2) (physicalLeft i site k) (physicalRight i even k)) =
      ((R:ℝ)^2:ℂ) • sourceHeisenbergMatrix (n+r*2) (fresh n r i 0) (fresh n r i 1)+
        ∑ a : Fin 2, (qmaPathAmplitude even (R:ℝ) (J:ℝ) a:ℂ) •
          sourceHeisenbergMatrix (n+r*2) (old n r (site a))
            (fresh n r i (qmaPathMember even a)) := by
  cases even <;> simp [Fin.sum_univ_succ,physicalLeft,physicalRight,
    QuantumPathCode.coefficients,qmaPathAmplitude,qmaPathMember,add_assoc,Complex.ofReal_ratCast] <;>
    ext s t <;>
    simp only [Matrix.add_apply,Matrix.neg_apply,Matrix.smul_apply,smul_eq_mul,
      Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_ratCast]

theorem familyOffset_cast {n r : ℕ} (site : Fin r → Fin 2 → Fin n) (even : Bool)
    (R : ℚ) (J : Fin r → ℚ) :
    (familyOffset ((n,even,R),List.ofFn fun i => ((site i 0).val,(site i 1).val,J i)):ℝ) =
      (∑ i : Fin r, qmaPathOffset (J i:ℝ))+3*r*(R:ℝ)^2 := by
  simp only [familyOffset,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  calc
    _ = ∑ i : Fin r, (offset ((n,even,R),0,(site i 0).val,(site i 1).val,J i):ℝ) := by
      push_cast
      rfl
    _ = ∑ i : Fin r, (qmaPathOffset (J i:ℝ)+3*(R:ℝ)^2) := by
      apply Finset.sum_congr rfl
      intro i _
      exact offset_cast n 0 (fun a => (site i a).val) even R (J i)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring

theorem matrix_ofFn {n m : ℕ} (left right : Fin m → Fin n) (w : Fin m → ℚ) :
    SourceBondLists.matrix n (List.ofFn fun i => ((left i).val,(right i).val,w i)) =
      ∑ i : Fin m, (w i:ℂ) • sourceHeisenbergMatrix n (left i) (right i) := by
  simp only [SourceBondLists.matrix,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [SourceBondLists.bondMatrix,dite_eq_left ⟨(left i).isLt,(right i).isLt⟩]

theorem retained_matrix {n m : ℕ} (left right : Fin m → Fin n) (w : Fin m → ℚ) (r : ℕ) :
    SourceBondLists.matrix (n+r*2) (List.ofFn fun i => ((left i).val,(right i).val,w i)) =
      ∑ i : Fin m, (w i:ℂ) • sourceHeisenbergMatrix (n+r*2)
        (old n r (left i)) (old n r (right i)) :=
  matrix_ofFn (fun i => old n r (left i)) (fun i => old n r (right i)) w

theorem fixed_step_matrix {n m r : ℕ} (left right : Fin m → Fin n) (w : Fin m → ℚ)
    (site : Fin r → Fin 2 → Fin n) (even : Bool) (R c : ℚ) (J : Fin r → ℚ) :
    let selected := List.ofFn fun i => ((site i 0).val,(site i 1).val,J i)
    SourceBondLists.matrix (n+r*2)
        ((List.ofFn fun i => ((left i).val,(right i).val,w i))++family ((n,even,R),selected))+
      ((c+familyOffset ((n,even,R),selected):ℚ):ℂ) • 1 =
        qmaPathsGraph left right (fun i => (w i:ℝ)) c R site (fun _ => even) (fun i => (J i:ℝ)) := by
  dsimp only
  have hoff :
      ((c+familyOffset ((n,even,R),List.ofFn fun i => ((site i 0).val,(site i 1).val,J i)):ℚ):ℂ) =
      ((((c:ℝ)+∑ i : Fin r, qmaPathOffset (J i:ℝ))+3*(r:ℝ)*(R:ℝ)^2:ℝ):ℂ) := by
    calc
      _ = ((c:ℝ)+(familyOffset ((n,even,R),List.ofFn fun i =>
        ((site i 0).val,(site i 1).val,J i)):ℝ):ℂ) := by simp
      _ = _ := by rw [familyOffset_cast]; push_cast; ring
  simp only [SourceBondLists.matrix,List.map_append,List.sum_append]
  change (SourceBondLists.matrix (n+r*2) (List.ofFn fun i =>
      ((left i).val,(right i).val,w i))+SourceBondLists.matrix (n+r*2)
        (family ((n,even,R),List.ofFn fun i => ((site i 0).val,(site i 1).val,J i))))+_ = _
  rw [retained_matrix,family_matrix,hoff]
  simp_rw [physical_sum]
  simp only [qmaPathsGraph,qmaExchangeMatrix,Fintype.sum_sum_type,Fintype.sum_prod_type,
    qmaParallelGraphLeft,qmaParallelGraphRight,qmaParallelGraphWeight,
    Finset.sum_add_distrib,Complex.ofReal_pow,Complex.ofReal_ratCast]

end ContinuumCoulomb.QuantumListPathProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListPathAccuracy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal bond-list subdivision has the same full-space ground-energy
estimate as the calibrated singlet construction. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListPathStep
open Matrix
open scoped BigOperators

theorem scale_cast {n m r : ℕ} (left right : Fin m → Fin n) (w : Fin m → ℚ)
    (site : Fin r → Fin 2 → Fin n) (J : Fin r → ℚ) (even : Bool) (N c : ℚ) :
    ((parameters (encodedInput left right w site J even N c)).2.2:ℝ) =
      qmaRoutingScale (3*∑ i, (1+2*|(J i:ℝ)|))
        ((3*(∑ i, |(w i:ℝ)|)+|(c:ℝ)|)+4*∑ i, (1+|(J i:ℝ)|)^2) N := by
  simp only [parameters,scaleInput,encodedInput,QuantumPathScaleProgram.value,
    QuantumPathScaleProgram.active,QuantumPathScaleProgram.correction,QuantumPathScaleProgram.base,
    List.map_ofFn,List.sum_ofFn,Function.comp_apply,QuantumPathScaleProgram.linearCost,
    QuantumPathScaleProgram.squareCost,qmaRoutingScale]
  push_cast
  rfl

theorem encoded_matrix {n m r : ℕ} (left right : Fin m → Fin n) (w : Fin m → ℚ)
    (site : Fin r → Fin 2 → Fin n) (J : Fin r → ℚ) (even : Bool) (N c : ℚ) :
    let x := encodedInput left right w site J even N c
    SourceBondLists.matrix (n+r*2) (bonds x)+(constant x:ℂ) • 1 =
      qmaPathsGraph left right (fun i => (w i:ℝ)) c (parameters x).2.2 site
        (fun _ => even) (fun i => (J i:ℝ)) := by
  simpa only [encodedInput,count,bonds,constant,parameters,List.length_ofFn] using
    QuantumListPathProgram.fixed_step_matrix left right w site even
      (parameters (encodedInput left right w site J even N c)).2.2 c J

theorem source_matrix {n m r : ℕ} (left right : Fin m → Fin n) (w : Fin m → ℚ)
    (site : Fin r → Fin 2 → Fin n) (J : Fin r → ℚ) (c : ℚ) :
    SourceBondLists.matrix n ((List.ofFn fun i => ((left i).val,(right i).val,w i))++
      List.ofFn fun i => ((site i 0).val,(site i 1).val,J i))+(c:ℂ) • 1 =
      qmaExchangeMatrix left right (fun i => (w i:ℝ)) c+
        ∑ i, (J i:ℂ) • sourceHeisenbergMatrix n (site i 0) (site i 1) := by
  simp only [SourceBondLists.matrix,List.map_append,List.sum_append]
  change SourceBondLists.matrix n (List.ofFn fun i => ((left i).val,(right i).val,w i))+
    SourceBondLists.matrix n (List.ofFn fun i => ((site i 0).val,(site i 1).val,J i))+
      (c:ℂ) • 1 = _
  rw [QuantumListPathProgram.matrix_ofFn,QuantumListPathProgram.matrix_ofFn]
  simp only [qmaExchangeMatrix,Complex.ofReal_ratCast]
  abel

theorem energy_error {n m r : ℕ} (left right : Fin m → Fin n)
    (hne : ∀ i, left i ≠ right i) (w : Fin m → ℚ)
    (site : Fin r → Fin 2 → Fin n) (hsite : ∀ i, Function.Injective (site i))
    (J : Fin r → ℚ) (even : Bool) {N : ℚ} (hN : 0 < N) (c : ℚ) :
    let x := encodedInput left right w site J even N c
    |sourceMatrixBottom (count x) (SourceBondLists.matrix (count x) (bonds x)+(constant x:ℂ) • 1)-
      sourceMatrixBottom n (SourceBondLists.matrix n (x.2.1++x.2.2)+(c:ℂ) • 1)| ≤ 1/(N:ℝ) := by
  dsimp only
  have hc : count (encodedInput left right w site J even N c) = n+r*2 := by
    simp only [count,encodedInput,List.length_ofFn]
  have hs : SourceBondLists.matrix n
      ((encodedInput left right w site J even N c).2.1++
        (encodedInput left right w site J even N c).2.2)+(c:ℂ) • 1 =
      qmaExchangeMatrix left right (fun i => (w i:ℝ)) c+
        ∑ i, (J i:ℂ) • sourceHeisenbergMatrix n (site i 0) (site i 1) :=
    source_matrix left right w site J c
  rw [hc,encoded_matrix,hs,scale_cast]
  exact qmaPathsGraph_accuracy left right hne (fun i => (w i:ℝ)) c site hsite
    (fun _ => even) (fun i => (J i:ℝ)) (by exact_mod_cast hN)

end ContinuumCoulomb.QuantumListPathStep

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListPathInput
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_left _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_right _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_toList _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_weight _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.toList_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The subdivision guarantee for arbitrary valid input tapes, with no
assumption that their bond lists came from a chosen abstract edge enumeration. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListPathStep
open MediatorListProgram

theorem bonds_list {n : ℕ} (xs : List Bond) (hb : SourceBondLists.bounded n xs) :
    (List.ofFn fun i => (((SourceBondLists.bonds n xs hb).left i).val,
      ((SourceBondLists.bonds n xs hb).right i).val,
      (SourceBondLists.bonds n xs hb).weight i)) = xs := by
  exact List.ofFn_get xs

theorem input_of_bonds (x : Input) (hk : SourceBondLists.bounded x.1.1 x.2.1)
    (hs : SourceBondLists.bounded x.1.1 x.2.2) :
    encodedInput (SourceBondLists.bonds x.1.1 x.2.1 hk).left
      (SourceBondLists.bonds x.1.1 x.2.1 hk).right
      (SourceBondLists.bonds x.1.1 x.2.1 hk).weight
      (fun i => ![(SourceBondLists.bonds x.1.1 x.2.2 hs).left i,
        (SourceBondLists.bonds x.1.1 x.2.2 hs).right i])
      (SourceBondLists.bonds x.1.1 x.2.2 hs).weight x.1.2.1 x.1.2.2.1 x.1.2.2.2 = x := by
  unfold encodedInput
  dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [bonds_list,bonds_list]

theorem energy_error_input (x : Input) (hk : SourceBondLists.bounded x.1.1 x.2.1)
    (hs : SourceBondLists.bounded x.1.1 x.2.2)
    (hnk : ∀ e ∈ x.2.1, e.1 ≠ e.2.1) (hns : ∀ e ∈ x.2.2, e.1 ≠ e.2.1)
    (hN : 0 < x.1.2.2.1) :
    |sourceMatrixBottom (count x) (SourceBondLists.matrix (count x) (bonds x)+(constant x:ℂ) • 1)-
      sourceMatrixBottom x.1.1 (SourceBondLists.matrix x.1.1 (x.2.1++x.2.2)+
        (x.1.2.2.2:ℂ) • 1)| ≤ 1/(x.1.2.2.1:ℝ) := by
  let k := SourceBondLists.bonds x.1.1 x.2.1 hk
  let s := SourceBondLists.bonds x.1.1 x.2.2 hs
  have hk' : ∀ i, k.left i ≠ k.right i := SourceBondLists.bonds_noLoops _ _ hk hnk
  have hs' : ∀ i, Function.Injective (![s.left i,s.right i] : Fin 2 → Fin x.1.1) := by
    intro i a b hab
    have hi : s.left i ≠ s.right i := SourceBondLists.bonds_noLoops _ _ hs hns i
    fin_cases a <;> fin_cases b <;> dsimp at hab ⊢
    all_goals simp_all
  have h := energy_error k.left k.right hk' k.weight (fun i => ![s.left i,s.right i]) hs'
    s.weight x.1.2.1 hN x.1.2.2.2
  rw [input_of_bonds x hk hs] at h
  exact h

end ContinuumCoulomb.QuantumListPathStep

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListRoutePieces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite route pieces used by one literal subdivision round. -/

namespace ContinuumCoulomb.QuantumListRouteProgram
open QuantumRouteCode

theorem lookup_range (f : ℕ → Pair) (n i : ℕ) (hi : i<n) :
    lookup ((List.range n).map f) i = f i := by
  unfold lookup
  rw [List.headD_eq_head?_getD,List.head?_drop,
    List.getElem?_eq_getElem (by simpa only [List.length_map,List.length_range] using hi)]
  simp only [List.getElem_map,List.getElem_range,Option.getD_some]

theorem tail_reverse (f : ℕ → Pair) (w : ℕ) :
    (((List.range (2*w+2)).map f).drop 2).reverse =
      (List.range (2*w)).map (fun k => f (2*w+1-k)) := by
  apply List.ext_getElem
  · simp only [List.length_reverse,List.length_drop,List.length_map,List.length_range]
    omega
  · intro i hi hj
    have hi' : i<2*w := by simpa only [List.length_map,List.length_range] using hj
    rw [List.getElem_reverse]
    simp only [List.getElem_drop,List.getElem_map,List.getElem_range,
      List.length_drop,List.length_map,List.length_range]
    congr 1
    omega

theorem freshPoints_range (e : QuantumListSchedule.Entry) (f : ℕ → Pair) (w : ℕ)
    (hw : 0<w) : freshPoints (e,(List.range (2*w+2)).map f) = [f 1,f 2] := by
  simp only [freshPoints,lookup_range f (2*w+2) 1 (by omega),
    lookup_range f (2*w+2) 2 (by omega)]

end ContinuumCoulomb.QuantumListRouteProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumInflatedListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The eightfold scaled route is an explicit list computation. Its loop
bound is eight times the input route length. -/

noncomputable section
namespace ContinuumCoulomb.QuantumInflatedListProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

theorem lookup_range (p : ℕ → Pair) (n k : ℕ) (hk : k<n) :
    QuantumForkGridProgram.lookup ((List.range n).map p) k=p k :=
  QuantumListRouteProgram.lookup_range p n k hk

theorem point_range (p : ℕ → Pair) (L k : ℕ) (hk : k≤8*L) :
    point (k,(List.range (L+1)).map p)=qmaInflatedPoint p k := by
  unfold point
  by_cases he : k=8*L
  · subst k
    rw [qmaInflatedPoint_last,qmaInflatedPoint_last,
      lookup_range p (L+1) L (by omega)]
  · have hd : k/8<L := by omega
    unfold qmaInflatedPoint
    rw [lookup_range p (L+1) (k/8) (by omega),
      lookup_range p (L+1) (k/8+1) (by omega)]

theorem value_range (p : ℕ → Pair) (L : ℕ) :
    value ((List.range (L+1)).map p)=
      (List.range (8*L+1)).map (qmaInflatedPoint p) := by
  unfold value
  simp only [List.length_map,List.length_range,Nat.add_sub_cancel]
  apply List.map_congr_left
  intro k hk
  exact point_range p L k (by have := List.mem_range.mp hk; omega)

end ContinuumCoulomb.QuantumInflatedListProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumEvenRouteRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full even-route realization from the reserved-leaf placement. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped Classical
namespace QMAEvenRouteData
variable {G : QMARationalExchangeGraph} (P : QMAEvenRouteData G)

theorem embedding_bounded (N : ℚ) {X Y : ℕ} (h : P.Bounded X Y) :
    (P.embedding N).Bounded X Y := by
  constructor
  · change ∀ v : Fin (G.n+(Finset.univ : Finset G.Edge).card*2),
      (P.nextPosition v).1 < X ∧ (P.nextPosition v).2 < Y
    intro v
    obtain ⟨v,rfl⟩ := (vertexEquiv G.n (Finset.univ : Finset G.Edge).card).surjective v
    rcases v with v | ⟨i,b⟩
    · change (P.nextPosition (old _ _ v)).1 < X ∧ (P.nextPosition (old _ _ v)).2 < Y
      simpa only [nextPosition_old] using h.1 v
    · change (P.nextPosition (fresh _ _ i b)).1 < X ∧ (P.nextPosition (fresh _ _ i b)).2 < Y
      rw [nextPosition_fresh]
      fin_cases b
      · exact h.2.1 (selected i) 1 (by omega)
      · exact h.2.2 (selected i)
  · intro e k hk
    change (P.nextPoint e k).1 < X ∧ (P.nextPoint e k).2 < Y
    rcases e with e | (i | ⟨i,a⟩)
    · exact (e.property (Finset.mem_univ _)).elim
    · change (if k = 0 then P.point (selected i) 1 else P.leaf (selected i)).1 < X ∧
        (if k = 0 then P.point (selected i) 1 else P.leaf (selected i)).2 < Y
      split
      · exact h.2.1 (selected i) 1 (by omega)
      · exact h.2.2 (selected i)
    · fin_cases a
      · have hk' : k ≤ 1 := hk
        exact h.2.1 (selected i) k (by omega)
      · exact h.2.1 (selected i) (2*P.work (selected i)+2-k) (Nat.sub_le _ _)

end QMAEvenRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumEvenListPieces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal reserved-leaf and tail arrays for an even route subdivision. -/

noncomputable section
namespace ContinuumCoulomb.QuantumEvenListPieces
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

theorem tail_reverse (p : ℕ → Pair) (n : ℕ) :
    (((List.range (n+1)).map p).drop 1).reverse=
      (List.range n).map (fun k => p (n-k)) := by
  apply List.ext_getElem
  · simp only [List.length_reverse,List.length_drop,List.length_map,List.length_range]
    omega
  · intro i hi hj
    have hi' : i<n := by simpa only [List.length_map,List.length_range] using hj
    rw [List.getElem_reverse]
    simp only [List.getElem_drop,List.getElem_map,List.getElem_range,
      List.length_drop,List.length_map,List.length_range]
    congr 1
    omega

theorem leaf_range (p : ℕ → Pair) (L : ℕ) (hL : 0<L) :
    leaf ((List.range (L+1)).map p)=qmaRouteLeaf (p 0) (qmaGridNeighborIndex (p 0) (p 1)) := by
  unfold leaf
  rw [QuantumInflatedListProgram.lookup_range p (L+1) 0 (by omega),
    QuantumInflatedListProgram.lookup_range p (L+1) 1 (by omega)]

theorem fresh_range (p : ℕ → Pair) (L : ℕ) (hL : 0<L) :
    fresh ((List.range (L+1)).map p)=
      [qmaInflatedPoint p 1,qmaRouteLeaf (p 0) (qmaGridNeighborIndex (p 0) (p 1))] := by
  unfold fresh
  rw [QuantumInflatedListProgram.point_range p L 1 (by omega),leaf_range p L hL]

theorem paths_range (p : ℕ → Pair) (L : ℕ) (hL : 0<L) :
    paths ((List.range (L+1)).map p)=
      [[qmaInflatedPoint p 1,qmaRouteLeaf (p 0) (qmaGridNeighborIndex (p 0) (p 1))],
       [qmaInflatedPoint p 0,qmaInflatedPoint p 1],
       (List.range (8*L)).map (fun k => qmaInflatedPoint p (8*L-k))] := by
  unfold paths
  rw [fresh_range p L hL,QuantumInflatedListProgram.point_range p L 0 (by omega),
    QuantumInflatedListProgram.point_range p L 1 (by omega),
    QuantumInflatedListProgram.value_range,tail_reverse]

end ContinuumCoulomb.QuantumEvenListPieces

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListSchedule
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Validity, fixed-round termination and full-space energy bounds for the
literal list-work routing compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open Matrix MediatorListProgram

theorem partition_matrix (n : ℕ) (xs : List Entry) :
    SourceBondLists.matrix n (erase (partition false xs)++erase (partition true xs)) =
      SourceBondLists.matrix n (erase xs) := by
  induction xs with
  | nil => rfl
  | cons e xs ih =>
    by_cases he : e.1=0
    · simpa [partition,selected,he,erase,SourceBondLists.matrix,add_assoc] using
        congrArg (fun x => SourceBondLists.bondMatrix n e.2+x) ih
    · simp [partition,selected,he,erase,SourceBondLists.matrix] at ih ⊢
      rw [← ih]
      abel

theorem value_energy_error (x : Input) (hx : Valid x.2) (hN : 0<x.1) :
    |energy (value x)-energy x.2| ≤ 1/(x.1:ℝ) := by
  have hk := partition_valid x.2 hx false
  have hs := partition_valid x.2 hx true
  have h := QuantumListPathStep.energy_error_input (stepInput x) hk.1 hs.1 hk.2 hs.2 hN
  change |sourceMatrixBottom (QuantumListPathStep.count (stepInput x))
    (SourceBondLists.matrix (QuantumListPathStep.count (stepInput x)) (erase (value x).2.2)+
      (QuantumListPathStep.constant (stepInput x):ℂ) • 1)-energy x.2| ≤ _
  rw [erase_value]
  have hp : SourceBondLists.matrix (stepInput x).1.1 ((stepInput x).2.1++(stepInput x).2.2) =
      SourceBondLists.matrix x.2.1 (erase x.2.2.2) := partition_matrix x.2.1 x.2.2.2
  rw [hp] at h
  exact h

theorem indexed_mem (x : Input) (i : ℕ) (hi : i<(partition true x.2.2.2).length) :
    (indexed (i,x)).2.2 ∈ x.2.2.2 := by
  have he : ((partition true x.2.2.2).drop i).headD zeroEntry = (partition true x.2.2.2)[i] := by
    rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem hi]
    rfl
  change ((partition true x.2.2.2).drop i).headD zeroEntry ∈ _
  rw [he]
  exact (List.mem_filter.mp (List.getElem_mem hi)).1

theorem value_work_le (x : Input) {D : ℕ} (hD : ∀ e ∈ x.2.2.2, e.1≤D) :
    ∀ e ∈ (value x).2.2, e.1≤D-1 := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · rw [partition_zero _ _ he]
    exact Nat.zero_le _
  · obtain ⟨bs,hbs,he⟩ := List.mem_flatten.mp he
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hbs
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp he
    change blockWork (indexed (i,x)) k ≤ _
    unfold blockWork
    split
    · exact Nat.sub_le_sub_right (hD _ (indexed_mem x i (List.mem_range.mp hi))) 1
    · exact Nat.zero_le _

theorem iterate_work_le (N : ℚ) (s : State) {D : ℕ} (hD : ∀ e ∈ s.2.2, e.1≤D) (k : ℕ) :
    ∀ e ∈ (iterate N k s).2.2, e.1≤D-k := by
  induction k with
  | zero => exact hD
  | succ k ih =>
    simpa only [iterate,Nat.sub_sub] using value_work_le (N,iterate N k s) ih

theorem iterate_complete (N : ℚ) (s : State) {D : ℕ} (hD : ∀ e ∈ s.2.2, e.1≤D) :
    ∀ e ∈ (iterate N D s).2.2, e.1=0 := by
  intro e he
  have h := iterate_work_le N s hD D e he
  omega

theorem iterate_energy_error {N : ℚ} (hN : 0<N) (s : State) (hs : Valid s) (k : ℕ) :
    |energy (iterate N k s)-energy s| ≤ (k:ℝ)/(N:ℝ) := by
  induction k with
  | zero => simp [iterate]
  | succ k ih =>
    calc
      _ ≤ |energy (value (N,iterate N k s))-energy (iterate N k s)|+
          |energy (iterate N k s)-energy s| := abs_sub_le _ _ _
      _ ≤ 1/(N:ℝ)+(k:ℝ)/(N:ℝ) :=
        add_le_add (value_energy_error (N,iterate N k s) (iterate_valid N s hs k) hN) ih
      _ = _ := by push_cast; ring

theorem partition_lengths (xs : List Entry) :
    (partition false xs).length+(partition true xs).length=xs.length := by
  induction xs with
  | nil => rfl
  | cons e xs ih =>
    by_cases he : e.1=0 <;> simp [partition,selected,he] at ih ⊢ <;> omega

theorem value_size (x : Input) :
    (value x).1+(value x).2.2.length ≤ 5*(x.2.1+x.2.2.2.length) := by
  change QuantumListPathStep.count (stepInput x)+(partition false x.2.2.2++family x).length ≤ _
  simp only [QuantumListPathStep.count,stepInput,erase,List.length_map,List.length_append,family_length]
  have h := partition_lengths x.2.2.2
  omega

theorem iterate_size (N : ℚ) (s : State) (k : ℕ) :
    (iterate N k s).1+(iterate N k s).2.2.length ≤ 5^k*(s.1+s.2.2.length) := by
  induction k with
  | zero => simp only [iterate,pow_zero,one_mul,le_refl]
  | succ k ih =>
    change (value (N,iterate N k s)).1+(value (N,iterate N k s)).2.2.length ≤ _
    exact (value_size (N,iterate N k s)).trans
      (by simpa only [pow_succ,Nat.mul_assoc,Nat.mul_comm 5] using Nat.mul_le_mul_left 5 ih)

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFiniteRouteSearch
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The 140-candidate route search uses a literal fixed-size scan. Its input
predicate can be supplied by the finite physical geometry table. -/

namespace ContinuumCoulomb.QuantumFiniteRouteSearch
open ExactQuantumFactoring.BitStackProgram

theorem firstTrue_eq_findIdx {k : ℕ} {bs : List Bool} (h : bs.length = k) :
    firstTrue k bs = bs.findIdx id := by
  induction bs generalizing k with
  | nil => subst k; rfl
  | cons b bs ih =>
    have hk : k ≠ 0 := by simp only [List.length_cons] at h; omega
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    have ht : bs.length = k := by simpa using h
    cases b <;> simp [firstTrue,List.findIdx_cons,ih ht,Nat.add_comm]

end ContinuumCoulomb.QuantumFiniteRouteSearch

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumParallelRouteSearch
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The predicate mask and the path list have the same 140-entry order.
Searching the mask therefore returns the path of the actual first permitted
catalog route, without encoding proof-carrying route objects. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFiniteRouteSearch
open ExactQuantumFactoring.BitStackProgram

private theorem mapped_drop_findIdx {α β : Type} (xs : List α) (p : α → Bool)
    (f : α → β) (default : β) :
    ((xs.map f).drop (xs.findIdx p)).headD default = (xs.find? p).elim default f := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases h : p a
    · simp [List.findIdx_cons,h]
    · simpa [List.findIdx_cons,List.find?_cons,h,Nat.add_comm] using ih

theorem selectParallelValue_eq {α β : Type} (default : β) (xs : List α)
    (p : α → Bool) (f : α → β) (hlen : xs.length = 140) {a : α}
    (hfind : xs.find? p = some a) :
    selectParallelValue default (xs.map f,xs.map p) = f a := by
  have hi : firstTrue 140 (xs.map p) = xs.findIdx p := by
    rw [firstTrue_eq_findIdx (by simpa using hlen),List.findIdx_map]
    rfl
  rw [selectParallelValue,hi,mapped_drop_findIdx,hfind]
  rfl

end ContinuumCoulomb.QuantumFiniteRouteSearch

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRouteSelectorCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite data program returns exactly the path used by the actual
merged physical graph, rather than merely a path with the same endpoints. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
open QuantumRoutingTable QuantumTaggedRouteProgram QuantumRouteSelectorProgram
open QuantumFiniteRouteSearch

namespace QMACellRoute

theorem headD_path (R : QMACellRoute) : R.path.headD (0,0) = R.source := by
  rw [List.headD_eq_head?_getD,R.endpoints.1]
  rfl

theorem reverse_headD_path (R : QMACellRoute) : R.path.reverse.headD (0,0) = R.target := by
  rw [List.headD_eq_head?_getD,List.head?_reverse,R.endpoints.2]
  rfl

end QMACellRoute

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem routing_accepts (ends : Ends) (R : QMACellRoute) :
    accepts ends (tagged P.routingTable R) =
      decide (P.RoutingAllowed R.body ∧ R.Valid ∧ R.source=ends.1 ∧ R.target=ends.2) := by
  apply Bool.eq_iff_iff.mpr
  simp only [accepts,tagged,Bool.and_eq_true,bodyPermitted_eq_true,decide_eq_true_eq,
    P.routingTable_allowed,R.headD_path,R.reverse_headD_path,QMACellRoute.Valid]
  constructor
  · rintro ⟨⟨⟨ha,hv⟩,hs⟩,ht⟩
    exact decide_eq_true ⟨ha,hv,hs,ht⟩
  · intro h
    obtain ⟨ha,hv,hs,ht⟩ := of_decide_eq_true h
    exact ⟨⟨⟨ha,hv⟩,hs⟩,ht⟩

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListRouteSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The route-array filter selects exactly the same source indices as the
literal work-list filter, preserving their order. -/

namespace ContinuumCoulomb.QuantumListRouteProgram
open QuantumListSchedule

theorem selectedRoutes_get (b : Bool) (x : Input) (i : Fin (partition b x.2.1.2.2).length) :
    (selectedRoutes b x).get (Fin.cast (selectedRoutes_length b x).symm i) =
      decoratedEntry x (indexEquiv b x.2.1.2.2 i).val := by
  change _ = decoratedEntry x ((indices b x.2.1.2.2).get
    (Fin.cast (indices_length b x.2.1.2.2).symm i))
  have hl : i.val<(selectedRoutes b x).length := by
    rw [selectedRoutes_length]
    exact i.isLt
  have hr : i.val<(indices b x.2.1.2.2).length := by
    rw [indices_length]
    exact i.isLt
  have h := congrArg (fun rs : List Routed => rs[i.val]?) (selectedRoutes_eq b x)
  simpa only [List.getElem?_map,List.getElem?_eq_getElem hl,List.getElem?_eq_getElem hr,
    Option.map_some,Option.some.injEq,List.get_eq_getElem,Fin.val_cast] using h

end ContinuumCoulomb.QuantumListRouteProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathRelabeling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport of the route invariant between different finite edge orders.
This is used when the emitted list order differs from a set's chosen order. -/

noncomputable section
namespace ContinuumCoulomb

namespace QMAPathRelabeling
variable {S T : QMAPathSchedule} (E : QMAPathRelabeling S T)

theorem transport_bounded {Γ : SimpleGraph (ℕ × ℕ)} (P : QMAPathEmbedding S Γ)
    {X Y : ℕ} (h : P.Bounded X Y) : (E.transport P).Bounded X Y := by
  constructor
  · intro v
    exact h.1 (E.vertex.symm v)
  · intro e k hk
    rw [← E.inverse_work] at hk
    exact h.2 (E.edge.symm e) k hk

end QMAPathRelabeling
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListScheduleGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact emitted edge order realizes the abstract scheduled subdivision.
This transfers the disjoint-route invariant to the literal list compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open MediatorGraph
open scoped Classical

theorem nextEdge_tag (x : Input) (hs : Valid x.2) (t : Tags x) :
    nextEdge x hs ((tagEquiv x).symm t) = tagEdge x hs t := by
  have h := nextEdge_eq x hs ((tagEquiv x).symm t)
  simpa only [Equiv.apply_symm_apply] using h

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListScheduleRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-list schedule: route preservation and nearest-neighbor
realization after the prescribed number of rounds. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open scoped Classical

variable {Γ : SimpleGraph (ℕ × ℕ)}

theorem nextEmbedding_bounded (x : Input) (hs : Valid x.2)
    (P : QMAPathEmbedding (schedule x.2 hs) Γ) {X Y : ℕ}
    (h : P.Bounded X Y) : (nextEmbedding x hs P).Bounded X Y :=
  (nextRelabel x hs).symm.transport_bounded (P.next x.1) (P.next_bounded x.1 h)

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListRouteRepresentation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.allRouted_length _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.value_length _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Representation of a scheduled embedding by finite position and route arrays. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListRouteProgram
open QuantumListSchedule QuantumRouteCode
open scoped Classical

variable {Γ : SimpleGraph Pair}

theorem decoratedEntry_represents (x : Input) (hx : Valid x.2.1)
    (P : QMAPathEmbedding (schedule x.2.1 hx) Γ) (hP : Represents x.2 hx P)
    (i : Fin x.2.1.2.2.length) : decoratedEntry x i=
      (x.2.1.2.2.get i,(List.range (2*(schedule x.2.1 hx).work i+2)).map (P.point i)) := by
  unfold decoratedEntry
  rw [hP.2,List.headD_eq_head?_getD,List.head?_drop,List.getElem?_ofFn]
  simp only [dite_eq_left i.isLt,Option.getD_some]

theorem map_selectedRoutes {α : Type} (b : Bool) (x : Input) (f : Routed → α) :
    (selectedRoutes b x).map f=List.ofFn
      (fun i : Fin (partition b x.2.1.2.2).length =>
        f (decoratedEntry x (indexEquiv b x.2.1.2.2 i).val)) := by
  apply List.ext_getElem
  · simp only [List.length_map,List.length_ofFn,selectedRoutes_length]
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_ofFn]
    have hb : i<(partition b x.2.1.2.2).length := by simpa using hj
    have h := selectedRoutes_get b x ⟨i,hb⟩
    exact congrArg f h

theorem selected_index (s : QuantumListSchedule.State) (hs : Valid s)
    (i : Fin (partition true s.2.2).length) :
    qmaSelectedIndex (schedule s hs).active (activePermutation s hs i)=
      (indexEquiv true s.2.2 i).val :=
  congrArg Subtype.val ((schedule s hs).active.equivFin.symm_apply_apply (activeEquiv s hs i))

theorem selected_freshPoints (x : Input) (hx : Valid x.2.1)
    (P : QMAPathEmbedding (schedule x.2.1 hx) Γ) (hP : Represents x.2 hx P)
    (i : Fin (partition true x.2.1.2.2).length) :
    freshPoints (decoratedEntry x (indexEquiv true x.2.1.2.2 i).val)=
      [P.point (qmaSelectedIndex (schedule x.2.1 hx).active (activePermutation x.2.1 hx i)) 1,
       P.point (qmaSelectedIndex (schedule x.2.1 hx).active (activePermutation x.2.1 hx i)) 2] := by
  rw [decoratedEntry_represents x hx P hP]
  have hw : 0<(schedule x.2.1 hx).work (indexEquiv true x.2.1.2.2 i).val :=
    (selected_true_iff _).mp (indexEquiv true x.2.1.2.2 i).property
  rw [freshPoints_range _ _ _ hw,selected_index]

end ContinuumCoulomb.QuantumListRouteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListRouteNextPosition
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.allRouted_length _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.value_length _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal new-coordinate list is exactly the placement of the
next scheduled embedding, in the emitted spin order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListRouteProgram
open QuantumListSchedule QuantumRouteCode MediatorGraph
open scoped Classical

private theorem ofFn_pairs {r : ℕ} (f : Fin r × Fin 2 → Pair) :
    List.ofFn (fun k : Fin (r*2) => f (finProdFinEquiv.symm k)) =
      (List.ofFn fun i : Fin r => [f (i,0),f (i,1)]).flatten := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg (fun g : Fin r → List Pair => List.ofFn g)
  funext i
  have hh : (fun k : Fin 2 => f (finProdFinEquiv.symm
      ⟨i.val*2+k.val,by omega⟩)) = fun k : Fin 2 => f (i,k) := by
    funext k
    have he : (⟨i.val*2+k.val,by omega⟩ : Fin (r*2))=finProdFinEquiv (i,k) := by
      apply Fin.ext
      change i.val*2+k.val=k.val+2*i.val
      omega
    rw [he,Equiv.symm_apply_apply]
  rw [hh]
  simp [List.ofFn_succ,List.ofFn_zero,Fin.succ]

private theorem ofFn_vertices {n r : ℕ} (f : Fin (n+r*2) → Pair) :
    List.ofFn f = List.ofFn (fun i => f (old n r i)) ++
      (List.ofFn fun i => [f (fresh n r i 0),f (fresh n r i 1)]).flatten := by
  rw [List.ofFn_add]
  apply congrArg₂ (fun a b : List Pair => a++b)
  · apply congrArg List.ofFn
    funext i
    apply congrArg f
    exact Fin.ext rfl
  · rw [← ofFn_pairs (fun p : Fin r × Fin 2 => f (fresh n r p.1 p.2))]
    apply congrArg List.ofFn
    funext k
    apply congrArg f
    apply Fin.ext
    change n+k.val=n+(finProdFinEquiv (finProdFinEquiv.symm k)).val
    rw [Equiv.apply_symm_apply]

private theorem ofFn_cast {n m : ℕ} (h : n=m) (f : Fin n → Pair) :
    List.ofFn (fun i : Fin m => f ((finCongr h).symm i))=List.ofFn f := by
  subst m
  rfl

variable {Γ : SimpleGraph Pair}

theorem next_position (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (P : QMAPathEmbedding (schedule s hs) Γ) (v : Fin (QuantumListSchedule.value (N,s)).1) :
    (nextEmbedding (N,s) hs P).position v =
      (P.next N).position (nextVertex (N,s) hs v) := rfl

theorem next_position_old (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (P : QMAPathEmbedding (schedule s hs) Γ) (v : Fin s.1) :
    (nextEmbedding (N,s) hs P).position
      ((finCongr (value_count (N,s))).symm (old s.1 (partition true s.2.2).length v)) =
      P.position v := by
  rw [next_position]
  change (P.next N).position (vertexRelabel s hs
    ((finCongr (value_count (N,s))) ((finCongr (value_count (N,s))).symm
      (old s.1 (partition true s.2.2).length v)))) = _
  rw [Equiv.apply_symm_apply,vertexRelabel_old]
  exact P.nextPosition_old v

theorem next_position_fresh (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (P : QMAPathEmbedding (schedule s hs) Γ) (i : Fin (partition true s.2.2).length) (a : Fin 2) :
    (nextEmbedding (N,s) hs P).position
      ((finCongr (value_count (N,s))).symm (fresh s.1 (partition true s.2.2).length i a)) =
      P.point (qmaSelectedIndex (schedule s hs).active (activePermutation s hs i)) (a.val+1) := by
  rw [next_position]
  change (P.next N).position (vertexRelabel s hs
    ((finCongr (value_count (N,s))) ((finCongr (value_count (N,s))).symm
      (fresh s.1 (partition true s.2.2).length i a)))) = _
  rw [Equiv.apply_symm_apply,vertexRelabel_fresh]
  exact P.nextPosition_fresh _ a

theorem positions_next (x : Input) (hx : Valid x.2.1)
    (P : QMAPathEmbedding (schedule x.2.1 hx) Γ) (hP : Represents x.2 hx P) :
    positions x=List.ofFn (nextEmbedding (x.1,x.2.1) hx P).position := by
  let Q := nextEmbedding (x.1,x.2.1) hx P
  calc
    positions x = List.ofFn (fun v => Q.position ((finCongr (value_count (x.1,x.2.1))).symm v)) := by
      rw [ofFn_vertices]
      change x.2.2.1++((selectedRoutes true x).map freshPoints).flatten = _
      apply congrArg₂ (fun a b : List Pair => a++b)
      · have he : (fun v => Q.position ((finCongr (value_count (x.1,x.2.1))).symm
            (old x.2.1.1 (partition true x.2.1.2.2).length v)))=P.position := by
          funext v
          exact next_position_old x.1 x.2.1 hx P v
        rw [he]
        exact hP.1
      · rw [map_selectedRoutes]
        apply congrArg List.flatten
        apply congrArg (fun f : Fin (partition true x.2.1.2.2).length → List Pair => List.ofFn f)
        funext i
        rw [next_position_fresh,next_position_fresh]
        exact selected_freshPoints x hx P hP i
    _ = List.ofFn Q.position := ofFn_cast _ _

end ContinuumCoulomb.QuantumListRouteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListRouteNextPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact route-index formulas for the three emitted edges of a selected
source edge and for every retained edge. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListRouteProgram
open QuantumListSchedule QuantumRouteCode
open scoped Classical

variable {Γ : SimpleGraph Pair}

theorem next_edge_retained (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (i : Fin (partition false s.2.2).length) :
    nextEdge (N,s) hs ((tagEquiv (N,s)).symm (.inl i)) = .inl (retainedEquiv s hs i) := by
  exact nextEdge_tag (N,s) hs (.inl i)

theorem next_edge_central (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (i : Fin (partition true s.2.2).length) :
    nextEdge (N,s) hs ((tagEquiv (N,s)).symm (.inr (i,0))) =
      .inr (.inl (activePermutation s hs i)) := by
  exact nextEdge_tag (N,s) hs (.inr (i,0))

theorem next_edge_left (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (i : Fin (partition true s.2.2).length) :
    nextEdge (N,s) hs ((tagEquiv (N,s)).symm (.inr (i,1))) =
      .inr (.inr (activePermutation s hs i,0)) := by
  exact nextEdge_tag (N,s) hs (.inr (i,1))

theorem next_edge_right (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (i : Fin (partition true s.2.2).length) :
    nextEdge (N,s) hs ((tagEquiv (N,s)).symm (.inr (i,2))) =
      .inr (.inr (activePermutation s hs i,1)) := by
  exact nextEdge_tag (N,s) hs (.inr (i,2))

theorem next_point (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (P : QMAPathEmbedding (schedule s hs) Γ) (e : Fin (QuantumListSchedule.value (N,s)).2.2.length)
    (k : ℕ) : (nextEmbedding (N,s) hs P).point e k =
      (P.next N).point (nextEdge (N,s) hs e) k := rfl

theorem next_point_retained (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (P : QMAPathEmbedding (schedule s hs) Γ) (i : Fin (partition false s.2.2).length) (k : ℕ) :
    (nextEmbedding (N,s) hs P).point ((tagEquiv (N,s)).symm (.inl i)) k =
      P.point (retainedEquiv s hs i).val k := by
  rw [next_point,next_edge_retained]
  rfl

theorem next_point_central (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (P : QMAPathEmbedding (schedule s hs) Γ) (i : Fin (partition true s.2.2).length) (k : ℕ) :
    (nextEmbedding (N,s) hs P).point ((tagEquiv (N,s)).symm (.inr (i,0))) k =
      P.point (qmaSelectedIndex (schedule s hs).active (activePermutation s hs i)) (k+1) := by
  rw [next_point,next_edge_central]
  rfl

theorem next_point_left (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (P : QMAPathEmbedding (schedule s hs) Γ) (i : Fin (partition true s.2.2).length) (k : ℕ) :
    (nextEmbedding (N,s) hs P).point ((tagEquiv (N,s)).symm (.inr (i,1))) k =
      P.point (qmaSelectedIndex (schedule s hs).active (activePermutation s hs i)) k := by
  rw [next_point,next_edge_left]
  rfl

theorem next_point_right (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (P : QMAPathEmbedding (schedule s hs) Γ) (i : Fin (partition true s.2.2).length) (k : ℕ) :
    (nextEmbedding (N,s) hs P).point ((tagEquiv (N,s)).symm (.inr (i,2))) k =
      P.point (qmaSelectedIndex (schedule s hs).active (activePermutation s hs i))
        (2*(schedule s hs).work
          (qmaSelectedIndex (schedule s hs).active (activePermutation s hs i))+1-k) := by
  rw [next_point,next_edge_right]
  rfl

end ContinuumCoulomb.QuantumListRouteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListRouteNextWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact remaining-work values in the finite output edge order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListRouteProgram
open QuantumListSchedule QuantumRouteCode
open scoped Classical

private theorem work_map (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (e : Fin (QuantumListSchedule.value (N,s)).2.2.length) :
    (schedule (QuantumListSchedule.value (N,s)) (value_valid (N,s) hs)).work e =
      ((schedule s hs).next N).work (nextEdge (N,s) hs e) :=
  (nextRelabel (N,s) hs).work e

theorem next_work_retained (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (i : Fin (partition false s.2.2).length) :
    (schedule (QuantumListSchedule.value (N,s)) (value_valid (N,s) hs)).work
      ((tagEquiv (N,s)).symm (.inl i))=0 := by
  exact (work_map N s hs _).trans
    (congrArg ((schedule s hs).next N).work (next_edge_retained N s hs i))

theorem next_work_central (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (i : Fin (partition true s.2.2).length) :
    (schedule (QuantumListSchedule.value (N,s)) (value_valid (N,s) hs)).work
      ((tagEquiv (N,s)).symm (.inr (i,0)))=0 := by
  exact (work_map N s hs _).trans
    (congrArg ((schedule s hs).next N).work (next_edge_central N s hs i))

theorem next_work_left (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (i : Fin (partition true s.2.2).length) :
    (schedule (QuantumListSchedule.value (N,s)) (value_valid (N,s) hs)).work
      ((tagEquiv (N,s)).symm (.inr (i,1)))=0 := by
  exact (work_map N s hs _).trans
    (congrArg ((schedule s hs).next N).work (next_edge_left N s hs i))

theorem next_work_right (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (i : Fin (partition true s.2.2).length) :
    (schedule (QuantumListSchedule.value (N,s)) (value_valid (N,s) hs)).work
      ((tagEquiv (N,s)).symm (.inr (i,2))) =
      (schedule s hs).work (qmaSelectedIndex (schedule s hs).active (activePermutation s hs i))-1 := by
  exact (work_map N s hs _).trans
    (congrArg ((schedule s hs).next N).work (next_edge_right N s hs i))

end ContinuumCoulomb.QuantumListRouteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListRoutePathOrder
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.allRouted_length _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.value_length _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The output path array has exactly the output bond array's tag order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListRouteProgram
open QuantumListSchedule QuantumRouteCode

theorem pathBlock_ofFn (r : Routed) : pathBlock r=List.ofFn (pathPiece r) := by
  simp [pathBlock,pathPiece,List.ofFn_succ,List.ofFn_zero]

private theorem ofFn_triples {m : ℕ} (f : Fin m × Fin 3 → List Pair) :
    List.ofFn (fun k : Fin (m*3) => f (finProdFinEquiv.symm k)) =
      (List.ofFn fun i : Fin m => List.ofFn fun k : Fin 3 => f (i,k)).flatten := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg (fun g : Fin m → List (List Pair) => List.ofFn g)
  funext i
  apply congrArg (fun g : Fin 3 → List Pair => List.ofFn g)
  funext k
  have he : (⟨i.val*3+k.val,by omega⟩ : Fin (m*3))=finProdFinEquiv (i,k) := by
    apply Fin.ext
    change i.val*3+k.val=k.val+3*i.val
    omega
  rw [he,Equiv.symm_apply_apply]

theorem paths_flat (x : Input) : paths x=List.ofFn
    (fun i => tagPath x (flatTagEquiv (x.1,x.2.1) i)) := by
  rw [List.ofFn_add]
  change _ = (List.ofFn (fun i : Fin (partition false x.2.1.2.2).length =>
    tagPath x (flatTagEquiv (x.1,x.2.1) (Fin.castAdd ((partition true x.2.1.2.2).length*3) i))))++
    List.ofFn (fun i : Fin ((partition true x.2.1.2.2).length*3) =>
      tagPath x (flatTagEquiv (x.1,x.2.1) (Fin.natAdd (partition false x.2.1.2.2).length i)))
  simp only [flatTagEquiv,Equiv.trans_apply,finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd,Equiv.sumCongr_apply,Equiv.refl_apply,
    Sum.map_inl,Sum.map_inr,tagPath]
  have h3 := ofFn_triples (fun p : Fin (partition true x.2.1.2.2).length × Fin 3 =>
    pathPiece (decoratedEntry x (indexEquiv true x.2.1.2.2 p.1).val) p.2)
  rw [h3]
  change (selectedRoutes false x).map Prod.snd++((selectedRoutes true x).map pathBlock).flatten = _
  rw [map_selectedRoutes,map_selectedRoutes]
  simp_rw [pathBlock_ofFn]

theorem paths_tagged (x : Input) : paths x=List.ofFn
    (fun i => tagPath x (tagEquiv (x.1,x.2.1) i)) := by
  rw [paths_flat]
  apply List.ext_getElem
  · simp only [List.length_ofFn,value_length]
  · intro i hi hj
    simp only [List.getElem_ofFn,tagEquiv,Equiv.trans_apply,finCongr_apply]
    apply congrArg (tagPath x)
    apply congrArg (flatTagEquiv (x.1,x.2.1))
    exact Fin.ext rfl

end ContinuumCoulomb.QuantumListRouteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListRoutePreservation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Preservation of the exact finite coordinate/route representation by one
round, and hence by the fixed number of rounds of the literal compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListRouteProgram
open QuantumListSchedule QuantumRouteCode
open scoped Classical

variable {Γ : SimpleGraph Pair}

private theorem range_map_congr {a b : ℕ} {f g : ℕ → Pair}
    (h : a=b) (hf : ∀ k, f k=g k) :
    (List.range (2*a+2)).map f=(List.range (2*b+2)).map g :=
  congrArg₂ List.map (funext hf) (congrArg (fun k => List.range (2*k+2)) h)

theorem tagPath_next (x : Input) (hx : Valid x.2.1)
    (P : QMAPathEmbedding (schedule x.2.1 hx) Γ) (hP : Represents x.2 hx P)
    (t : Tags (x.1,x.2.1)) :
    tagPath x t = (List.range (2*(schedule (QuantumListSchedule.value (x.1,x.2.1))
      (value_valid (x.1,x.2.1) hx)).work ((tagEquiv (x.1,x.2.1)).symm t)+2)).map
        ((nextEmbedding (x.1,x.2.1) hx P).point ((tagEquiv (x.1,x.2.1)).symm t)) := by
  rcases t with i | ⟨i,k⟩
  · change (decoratedEntry x (indexEquiv false x.2.1.2.2 i).val).2 = _
    rw [decoratedEntry_represents x hx P hP]
    change (List.range (2*(schedule x.2.1 hx).work (retainedEquiv x.2.1 hx i).val+2)).map
      (P.point (retainedEquiv x.2.1 hx i).val) = _
    exact (range_map_congr
      ((schedule x.2.1 hx).retained_work_zero (retainedEquiv x.2.1 hx i))
      (fun _ => rfl)).trans
      (range_map_congr (next_work_retained x.1 x.2.1 hx i)
        (next_point_retained x.1 x.2.1 hx P i)).symm
  · change pathPiece (decoratedEntry x (indexEquiv true x.2.1.2.2 i).val) k = _
    rw [decoratedEntry_represents x hx P hP,← selected_index x.2.1 hx i]
    let e := qmaSelectedIndex (schedule x.2.1 hx).active (activePermutation x.2.1 hx i)
    let w := (schedule x.2.1 hx).work e
    let f := P.point e
    have hw : 0<w := (schedule x.2.1 hx).selected_work_pos (activePermutation x.2.1 hx i)
    have h0 : 0<2*w+2 := by omega
    have h1 : 1<2*w+2 := by omega
    have h2 : 2<2*w+2 := by omega
    have hn : 2*(w-1)+2=2*w := by omega
    fin_cases k
    · change [lookup ((List.range (2*w+2)).map f) 1,
        lookup ((List.range (2*w+2)).map f) 2] = _
      have hl : [lookup ((List.range (2*w+2)).map f) 1,
        lookup ((List.range (2*w+2)).map f) 2] =
        (List.range 2).map (fun k => f (k+1)) := by
        rw [lookup_range f _ _ h1,lookup_range f _ _ h2]
        rfl
      exact hl.trans (range_map_congr (next_work_central x.1 x.2.1 hx i)
        (next_point_central x.1 x.2.1 hx P i)).symm
    · change [lookup ((List.range (2*w+2)).map f) 0,
        lookup ((List.range (2*w+2)).map f) 1] = _
      have hl : [lookup ((List.range (2*w+2)).map f) 0,
        lookup ((List.range (2*w+2)).map f) 1] = (List.range 2).map f := by
        rw [lookup_range f _ _ h0,lookup_range f _ _ h1]
        rfl
      exact hl.trans (range_map_congr (next_work_left x.1 x.2.1 hx i)
        (next_point_left x.1 x.2.1 hx P i)).symm
    · change (((List.range (2*w+2)).map f).drop 2).reverse = _
      have hl : (((List.range (2*w+2)).map f).drop 2).reverse =
        (List.range (2*(w-1)+2)).map (fun k => f (2*w+1-k)) := by
        rw [tail_reverse,hn]
      exact hl.trans (range_map_congr (next_work_right x.1 x.2.1 hx i)
        (next_point_right x.1 x.2.1 hx P i)).symm

theorem paths_next (x : Input) (hx : Valid x.2.1)
    (P : QMAPathEmbedding (schedule x.2.1 hx) Γ) (hP : Represents x.2 hx P) :
    paths x=List.ofFn (fun e => (List.range (2*(schedule
      (QuantumListSchedule.value (x.1,x.2.1)) (value_valid (x.1,x.2.1) hx)).work e+2)).map
        ((nextEmbedding (x.1,x.2.1) hx P).point e)) := by
  rw [paths_tagged]
  apply congrArg List.ofFn
  funext e
  have h := tagPath_next x hx P hP (tagEquiv (x.1,x.2.1) e)
  simpa only [Equiv.symm_apply_apply] using h

theorem value_represents (x : Input) (hx : Valid x.2.1)
    (P : QMAPathEmbedding (schedule x.2.1 hx) Γ) (hP : Represents x.2 hx P) :
    Represents (value x) (value_valid (x.1,x.2.1) hx) (nextEmbedding (x.1,x.2.1) hx P) :=
  ⟨positions_next x hx P hP,paths_next x hx P hP⟩

theorem iterate_state (N : ℚ) (s : State) (k : ℕ) :
    (iterate N k s).1=QuantumListSchedule.iterate N k s.1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change QuantumListSchedule.value (N,(iterate N k s).1)=_
    rw [ih]
    rfl

theorem iterate_represents (N : ℚ) (s : State) (hs : Valid s.1)
    (P : QMAPathEmbedding (schedule s.1 hs) Γ) (hP : Represents s hs P)
    {X Y : ℕ} (hbox : P.Bounded X Y) (k : ℕ) :
    ∃ (hs' : Valid (iterate N k s).1)
      (P' : QMAPathEmbedding (schedule (iterate N k s).1 hs') Γ),
      Represents (iterate N k s) hs' P' ∧ P'.Bounded X Y := by
  induction k with
  | zero => exact ⟨hs,P,hP,hbox⟩
  | succ k ih =>
    obtain ⟨hk,Q,hQ,hQbox⟩ := ih
    exact ⟨value_valid (N,(iterate N k s).1) hk,
      nextEmbedding (N,(iterate N k s).1) hk Q,
      value_represents (N,iterate N k s) hk Q hQ,
      nextEmbedding_bounded (N,(iterate N k s).1) hk Q hQbox⟩

theorem compile_realization {N : ℚ} (hN : 0<N) (s : State) (hs : Valid s.1)
    (P : QMAPathEmbedding (schedule s.1 hs) Γ) (hP : Represents s hs P)
    {D X Y : ℕ} (hD : ∀ e ∈ s.1.2.2, e.1≤D) (hbox : P.Bounded X Y) :
    ∃ (hs' : Valid (iterate N D s).1)
      (P' : QMAPathEmbedding (schedule (iterate N D s).1 hs') Γ),
      Represents (iterate N D s) hs' P' ∧ P'.Bounded X Y ∧
      (∀ e, Γ.Adj (P'.position ((schedule (iterate N D s).1 hs').graph.left e))
        (P'.position ((schedule (iterate N D s).1 hs').graph.right e))) ∧
      (iterate N D s).1.1+(iterate N D s).1.2.2.length≤5^D*(s.1.1+s.1.2.2.length) ∧
      |QuantumListSchedule.energy (iterate N D s).1-QuantumListSchedule.energy s.1|≤(D:ℝ)/(N:ℝ) := by
  obtain ⟨hs',Q,hQ,hQbox⟩ := iterate_represents N s hs P hP hbox D
  refine ⟨hs',Q,hQ,hQbox,?_,?_,?_⟩
  · have hc : ∀ e ∈ (iterate N D s).1.2.2, e.1=0 := by
      rw [iterate_state]
      exact QuantumListSchedule.iterate_complete N s.1 hD
    exact Q.adjacent_of_complete (fun e => hc _ (List.get_mem _ e))
  · rw [iterate_state]
    exact QuantumListSchedule.iterate_size N s.1 D
  · rw [iterate_state]
    exact QuantumListSchedule.iterate_energy_error hN s.1 hs D

end ContinuumCoulomb.QuantumListRouteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumEvenRouteLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit vertex and edge labels for the even subdivision of a planar route family. -/

noncomputable section
namespace ContinuumCoulomb.QuantumEvenRouteLabels
open MediatorGraph QuantumRouteCode
open scoped Classical

variable {G : QMARationalExchangeGraph} (P : QMAPlanarRouteData G)
    {m : ℕ} (labels : G.Edge ≃ Fin m)

theorem fresh_eq (i : Fin m) : QuantumEvenListPieces.fresh (originalPath P labels i)=
    [P.toEven.freshPosition (activeIndex labels i) 0,
     P.toEven.freshPosition (activeIndex labels i) 1] := by
  rw [originalPath,QuantumEvenListPieces.fresh_range _ _ (P.length_pos _)]
  simp only [QMAEvenRouteData.freshPosition,ite_true, if_true,show (1:Fin 2)≠0 from by decide,ite_false, if_false,
    selected_index labels i,QMAPlanarRouteData.toEven,QMAPlanarRouteData.leaf,QMAPlanarRouteData.direction]

theorem paths_eq (i : Fin m) : QuantumEvenListPieces.paths (originalPath P labels i)=
    List.ofFn (fun k : Fin 3 => (List.range (2*work P labels (i,k)+2)).map
      (P.toEven.nextPoint (edge labels (i,k)))) := by
  rw [originalPath,QuantumEvenListPieces.paths_range _ _ (P.length_pos _)]
  have he : 2*(4*P.length (labels.symm i)-1)+2=8*P.length (labels.symm i) :=
    P.even_length _
  have h0 : (List.range (2*work P labels (i,0)+2)).map
      (P.toEven.nextPoint (edge labels (i,0)))=
        [qmaInflatedPoint (P.point (labels.symm i)) 1,
          qmaRouteLeaf (P.point (labels.symm i) 0)
            (qmaGridNeighborIndex (P.point (labels.symm i) 0) (P.point (labels.symm i) 1))] := by
    change (List.range 2).map (fun k => if k=0 then
      qmaInflatedPoint (P.point (QMAEvenRouteData.selected (activeIndex labels i))) 1 else
      qmaRouteLeaf (P.point (QMAEvenRouteData.selected (activeIndex labels i)) 0)
        (qmaGridNeighborIndex (P.point (QMAEvenRouteData.selected (activeIndex labels i)) 0)
          (P.point (QMAEvenRouteData.selected (activeIndex labels i)) 1)))=_
    rw [selected_index labels i]
    rfl
  have h1 : (List.range (2*work P labels (i,1)+2)).map
      (P.toEven.nextPoint (edge labels (i,1)))=
        [qmaInflatedPoint (P.point (labels.symm i)) 0,qmaInflatedPoint (P.point (labels.symm i)) 1] := by
    change (List.range 2).map (qmaInflatedPoint
      (P.point (QMAEvenRouteData.selected (activeIndex labels i))))=_
    rw [selected_index labels i]
    rfl
  have h2 : (List.range (2*work P labels (i,2)+2)).map
      (P.toEven.nextPoint (edge labels (i,2)))=
        (List.range (8*P.length (labels.symm i))).map
          (fun k => qmaInflatedPoint (P.point (labels.symm i)) (8*P.length (labels.symm i)-k)) := by
    change (List.range (2*(4*P.length (labels.symm i)-1)+2)).map
      (fun k => qmaInflatedPoint (P.point (QMAEvenRouteData.selected (activeIndex labels i)))
        (2*(4*P.length (QMAEvenRouteData.selected (activeIndex labels i))-1)+2-k))=_
    rw [selected_index labels i,he]
  change _=[_,_,_]
  exact congrArg₂ List.cons h0.symm
    (congrArg₂ List.cons h1.symm (congrArg₂ List.cons h2.symm rfl))

theorem positions_eq :
    (List.ofFn (fun v => qmaLeafCenter (P.position v)))++
      ((List.ofFn (originalPath P labels)).map QuantumEvenListPieces.fresh).flatten=
        List.ofFn (fun v => P.toEven.nextPosition (vertex labels v)) := by
  rw [List.ofFn_add]
  apply congrArg₂ (· ++ ·)
  · apply congrArg List.ofFn
    funext v
    change qmaLeafCenter (P.position v)=P.toEven.nextPosition (vertex labels (old G.n m v))
    rw [vertex_old,QMAEvenRouteData.nextPosition_old]
    rfl
  · rw [List.map_ofFn,List.ofFn_mul]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    dsimp only [Function.comp_apply]
    rw [fresh_eq]
    have hf (a : Fin 2) : P.toEven.nextPosition (vertex labels
        ((⟨i.val*2+a.val,by omega⟩ : Fin (m*2)).natAdd G.n))=
          P.toEven.freshPosition (activeIndex labels i) a := by
      have he : ((⟨i.val*2+a.val,by omega⟩ : Fin (m*2)).natAdd G.n)=fresh G.n m i a := by
        apply Fin.ext
        change G.n+(i.val*2+a.val)=G.n+(a.val+2*i.val)
        omega
      rw [he,vertex_fresh,QMAEvenRouteData.nextPosition_fresh]
    simp only [hf,List.ofFn_succ,List.ofFn_zero,Fin.succ_zero_eq_one]

theorem allPaths_eq :
    ((List.ofFn (originalPath P labels)).map QuantumEvenListPieces.paths).flatten=
      List.ofFn (fun k : Fin (m*3) =>
        (List.range (2*work P labels (finProdFinEquiv.symm k)+2)).map
          (P.toEven.nextPoint (edge labels (finProdFinEquiv.symm k)))) := by
  rw [List.map_ofFn,List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply]
  rw [paths_eq]
  apply congrArg List.ofFn
  funext k
  have he : (⟨i.val*3+k.val,by omega⟩ : Fin (m*3))=finProdFinEquiv (i,k) := by
    apply Fin.ext
    change i.val*3+k.val=k.val+3*i.val
    omega
  rw [he,Equiv.symm_apply_apply]

end ContinuumCoulomb.QuantumEvenRouteLabels

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPhysicalCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every physical spin retains the coarse cell of an original route point.
This transfers the original positive-coordinate and rectangle bounds. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped Classical

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem crossingPosition_bounded {X Y : ℕ}
    (hsource : ∀ v, (P.position v).1 < X ∧ (P.position v).2 < Y)
    (hpath : ∀ e k, k ≤ P.length e → (P.point e k).1 < X ∧ (P.point e k).2 < Y)
    (N : ℚ) (D : ℕ) (v : Fin ((P.finishedGraph N D).n+P.crossingCells.card*2)) :
    (P.crossingPosition N D v).1 < 32*X ∧ (P.crossingPosition N D v).2 < 32*Y := by
  have h := P.crossingPosition_cell_property (fun p => p.1 < X ∧ p.2 < Y) hsource hpath N D v
  change (P.crossingPosition N D v).1/32 < X ∧ (P.crossingPosition N D v).2/32 < Y at h
  omega

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPlanarRouteRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded planar route family produces the actual nearest-neighbor rational
Hamiltonian with a fixed number of perturbative layers. -/

namespace ContinuumCoulomb

theorem qmaInflatedPoint_bounded (p : ℕ → ℕ × ℕ) {L X Y : ℕ}
    (hp : ∀ i < L, qmaSquareGrid.Adj (p i) (p (i+1)))
    (hb : ∀ i ≤ L, (p i).1 < X ∧ (p i).2 < Y) {k : ℕ} (hk : k ≤ 8*L) :
    (qmaInflatedPoint p k).1 < 8*X ∧ (qmaInflatedPoint p k).2 < 8*Y := by
  by_cases hz : k%8 = 0
  · rw [qmaInflatedPoint_boundary p hz]
    obtain ⟨hx,hy⟩ := hb (k/8) (by omega)
    simp only [qmaLeafCenter]
    omega
  · have hd : k/8 < L := by omega
    have hl := qmaLeafCenter_adj_length (hp _ hd)
    have hi : k%8 ≤ qmaManhattanLength (qmaLeafCenter (p (k/8)))
        (qmaLeafCenter (p (k/8+1))) := by omega
    have hh := qmaManhattanPoint_bounds _ _ _ hi
    obtain ⟨hx,hy⟩ := hb (k/8) hd.le
    obtain ⟨hx',hy'⟩ := hb (k/8+1) (by omega)
    change (qmaManhattanPoint _ _ _).1 < _ ∧ (qmaManhattanPoint _ _ _).2 < _
    simp only [qmaLeafCenter] at hh
    constructor
    · exact hh.2.1.trans_lt (max_lt (by omega) (by omega))
    · exact hh.2.2.2.trans_lt (max_lt (by omega) (by omega))

noncomputable section
open scoped Classical
namespace QMAPlanarRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPlanarRouteData G)

theorem toEven_bounded {X Y : ℕ} (hb : P.Bounded X Y) : P.toEven.Bounded (8*X) (8*Y) := by
  refine ⟨?_,?_,?_⟩
  · intro v
    obtain ⟨hx,hy⟩ := hb.1 v
    change 8*(P.position v).1+4 < 8*X ∧ 8*(P.position v).2+4 < 8*Y
    omega
  · intro e k hk
    change k ≤ 2*(4*P.length e-1)+2 at hk
    rw [P.even_length] at hk
    exact qmaInflatedPoint_bounded (P.point e) (P.step e) (hb.2 e) hk
  · intro e
    exact qmaRouteLeaf_bounds (hb.2 e 0 (Nat.zero_le _)).1 (hb.2 e 0 (Nat.zero_le _)).2 _

end QMAPlanarRouteData
end
end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFinalRoutingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal fixed-round routing to the serialized square-lattice source. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFinalRoutingProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode MediatorListProgram

theorem rounds_eq : rounds=80 := roundsValue.property

end ContinuumCoulomb.QuantumFinalRoutingProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumEvenTapeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal even tape has the canonical reserved-leaf geometry, up to
its explicit vertex and triple-edge ordering. -/

noncomputable section
namespace ContinuumCoulomb.QuantumEvenTapeGeometry
open QuantumRouteCode QuantumListSchedule MediatorGraph
open scoped Classical

variable {G : QMARationalExchangeGraph} (P : QMAPlanarRouteData G)
    {m : ℕ} (labels : G.Edge ≃ Fin m) (N : ℚ)

private theorem ofFn_cast {α : Type} {a b : ℕ} (h : a=b) (f : Fin b → α) :
    List.ofFn (fun i => f (finCongr h i))=List.ofFn f := by
  subst b
  rfl

theorem triple_cast (i : Fin (QuantumEvenTapeProgram.entries (input P labels N)).length) :
    tripleEquiv P labels N i=finProdFinEquiv.symm (finCongr (entry_count P labels N) i) := by
  apply Prod.ext <;> apply Fin.ext <;> rfl

theorem represents : QuantumListRouteProgram.Represents
    (QuantumEvenTapeProgram.value (input P labels N)) (input_valid P labels N)
      (embedding P labels N) := by
  constructor
  · change QuantumEvenTapeProgram.positions (input P labels N)=
      List.ofFn (fun i => P.toEven.nextPosition
        (QuantumEvenRouteLabels.vertex labels (finCongr (count_eq P labels N) i)))
    have hp : QuantumEvenTapeProgram.positions (input P labels N)=
        List.ofFn (fun i => P.toEven.nextPosition (QuantumEvenRouteLabels.vertex labels i)) := by
      simpa only [QuantumEvenTapeProgram.positions,input,List.map_ofFn,Function.comp_def] using
        QuantumEvenRouteLabels.positions_eq P labels
    exact hp.trans (ofFn_cast (count_eq P labels N)
      (fun i => P.toEven.nextPosition (QuantumEvenRouteLabels.vertex labels i))).symm
  · change QuantumEvenTapeProgram.paths (input P labels N)=
      List.ofFn (fun e : Fin (QuantumEvenTapeProgram.entries (input P labels N)).length =>
        (List.range (2*(schedule (QuantumEvenTapeProgram.value (input P labels N)).1
          (input_valid P labels N)).work e+2)).map
            (P.toEven.nextPoint (QuantumEvenRouteLabels.edge labels (tripleEquiv P labels N e))))
    simp_rw [literal_work,triple_cast]
    have hp : QuantumEvenTapeProgram.paths (input P labels N)=
        List.ofFn (fun k : Fin (m*3) =>
          (List.range (2*QuantumEvenRouteLabels.work P labels (finProdFinEquiv.symm k)+2)).map
            (P.toEven.nextPoint (QuantumEvenRouteLabels.edge labels (finProdFinEquiv.symm k)))) :=
      QuantumEvenRouteLabels.allPaths_eq P labels
    exact hp.trans (ofFn_cast (entry_count P labels N)
      (fun k : Fin (m*3) =>
        (List.range (2*QuantumEvenRouteLabels.work P labels (finProdFinEquiv.symm k)+2)).map
          (P.toEven.nextPoint (QuantumEvenRouteLabels.edge labels (finProdFinEquiv.symm k))))).symm

theorem work_le (hL : ∀ e, P.length e≤20) :
    ∀ e ∈ (QuantumEvenTapeProgram.value (input P labels N)).1.2.2, e.1≤80 := by
  intro e he
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp he
  let j : Fin (QuantumEvenTapeProgram.entries (input P labels N)).length := ⟨i.val,i.isLt⟩
  change (schedule (QuantumEvenTapeProgram.value (input P labels N)).1
    (input_valid P labels N)).work j≤80
  rw [literal_work P labels N j]
  unfold QuantumEvenRouteLabels.work
  split
  · have h := hL (labels.symm (tripleEquiv P labels N j).1)
    omega
  · omega

theorem embedding_bounded {X Y : ℕ} (hbox : P.Bounded X Y) :
    (embedding P labels N).Bounded (8*X) (8*Y) :=
  (relabel P labels N).symm.transport_bounded (P.toEven.embedding N)
    (P.toEven.embedding_bounded N (P.toEven_bounded hbox))

theorem realizes (hN : 0<N) (hL : ∀ e, P.length e≤20) {X Y : ℕ}
    (hbox : P.Bounded X Y) :
    ∃ (hs : Valid (QuantumListRouteProgram.iterate N QuantumFinalRoutingProgram.rounds
        (QuantumEvenTapeProgram.value (input P labels N))).1)
      (Q : QMAPathEmbedding (schedule (QuantumListRouteProgram.iterate N QuantumFinalRoutingProgram.rounds
        (QuantumEvenTapeProgram.value (input P labels N))).1 hs)),
      QuantumListRouteProgram.Represents (QuantumListRouteProgram.iterate N QuantumFinalRoutingProgram.rounds
        (QuantumEvenTapeProgram.value (input P labels N))) hs Q ∧
      Q.Bounded (8*X) (8*Y) ∧
      (∀ e, qmaSquareGrid.Adj (Q.position ((schedule _ hs).graph.left e))
        (Q.position ((schedule _ hs).graph.right e))) ∧
      (QuantumListRouteProgram.iterate N QuantumFinalRoutingProgram.rounds (QuantumEvenTapeProgram.value (input P labels N))).1.1+
        (QuantumListRouteProgram.iterate N QuantumFinalRoutingProgram.rounds (QuantumEvenTapeProgram.value (input P labels N))).1.2.2.length≤
          5^QuantumFinalRoutingProgram.rounds*((QuantumEvenTapeProgram.value (input P labels N)).1.1+
            (QuantumEvenTapeProgram.value (input P labels N)).1.2.2.length) ∧
      |QuantumListSchedule.energy
          (QuantumListRouteProgram.iterate N QuantumFinalRoutingProgram.rounds (QuantumEvenTapeProgram.value (input P labels N))).1-
        QuantumListSchedule.energy (QuantumEvenTapeProgram.value (input P labels N)).1|≤(QuantumFinalRoutingProgram.rounds:ℝ)/(N:ℝ) := by
  exact QuantumListRouteProgram.compile_realization hN _ (input_valid P labels N)
    (embedding P labels N) (represents P labels N)
    (by rw [QuantumFinalRoutingProgram.rounds_eq]; exact work_le P labels N hL)
    (embedding_bounded P labels N hbox)

end ContinuumCoulomb.QuantumEvenTapeGeometry

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSelectedRoute
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal route selector returns a permitted catalog path for any
oriented pair of endpoints for which such a path exists. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
open QuantumRouteSelectorProgram QuantumTaggedRouteProgram QuantumFiniteRouteSearch

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem selectedAllowedRoute_path (x y : ℕ × ℕ) (h : P.HasAllowedRoute x y) :
    QuantumRouteSelectorProgram.value (P.routingTable,(x,y)) =
      (P.selectedAllowedRoute x y h).path := by
  have hf : (qmaRouteCandidates x y).find?
      (fun R => accepts (x,y) (tagged P.routingTable R)) =
        some (P.selectedAllowedRoute x y h) := by
    simp only [P.routing_accepts]
    exact (Option.some_get (P.findAllowedRoute_isSome h)).symm
  have hs := selectParallelValue_eq (false,[]) (qmaRouteCandidates x y)
    (fun R => accepts (x,y) (tagged P.routingTable R)) (tagged P.routingTable)
    (qmaRouteCandidates_length x y) hf
  simpa only [value,choose,candidates,List.map_map,Function.comp_def,tagged]
    using congrArg (fun v : Tagged => v.2) hs

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPlanarSelectorTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite selector gives a planar family after arbitrary vertex
and edge permutations, including independent edge orientation changes. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

namespace QMAPlanarListData

theorem range_toRoute_point {G : QMARationalExchangeGraph} (L : QMAPlanarListData G)
    (e : G.Edge) :
    (List.range (L.toRoute.length e+1)).map (L.toRoute.point e) = L.path e := by
  have hn : L.toRoute.length e+1 = (L.path e).length := by
    change (L.path e).length-1+1 = (L.path e).length
    have h := L.length e
    omega
  rw [hn]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range]
  · intro i hi hj
    rw [List.getElem_map,List.getElem_range]
    exact L.point_get e hj

end QMAPlanarListData

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

section Transport
variable (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    {H : QMARationalExchangeGraph}
    (vertex : Fin H.n ≃ Fin (P.crossingOutput N hD).merge.n)
    (edge : H.Edge ≃ (P.crossingOutput N hD).merge.Edge)
    (ends : ∀ e, s(vertex (H.left e),vertex (H.right e)) =
      s((P.crossingOutput N hD).merge.left (edge e),
        (P.crossingOutput N hD).merge.right (edge e)))

theorem selectorTransportRoute_path (e : H.Edge) :
    (P.selectorTransportRoute N hD havoid vertex edge ends e).path =
      QuantumRouteSelectorProgram.value (P.routingTable,
        P.crossingPosition N D (vertex (H.left e)),
        P.crossingPosition N D (vertex (H.right e))) :=
  (P.selectedAllowedRoute_path _ _ _).symm

theorem selectorPlanarList_path
    (hpositive : ∀ v, 0 < (P.position v).1 ∧ 0 < (P.position v).2) (e : H.Edge) :
    (P.selectorPlanarList N hD havoid vertex edge ends hpositive).path e =
      QuantumRouteSelectorProgram.value (P.routingTable,
        P.crossingPosition N D (vertex (H.left e)),
        P.crossingPosition N D (vertex (H.right e))) :=
  P.selectorTransportRoute_path N hD havoid vertex edge ends e

theorem selectorPlanarRoute_path
    (hpositive : ∀ v, 0 < (P.position v).1 ∧ 0 < (P.position v).2) (e : H.Edge) :
    (List.range ((P.selectorPlanarRoute N hD havoid vertex edge ends hpositive).length e+1)).map
      ((P.selectorPlanarRoute N hD havoid vertex edge ends hpositive).point e) =
      QuantumRouteSelectorProgram.value (P.routingTable,
        P.crossingPosition N D (vertex (H.left e)),
        P.crossingPosition N D (vertex (H.right e))) :=
  ((P.selectorPlanarList N hD havoid vertex edge ends hpositive).range_toRoute_point e).trans
    (P.selectorPlanarList_path N hD havoid vertex edge ends hpositive e)

theorem selectorPlanarRoute_length
    (hpositive : ∀ v, 0 < (P.position v).1 ∧ 0 < (P.position v).2) (e : H.Edge) :
    (P.selectorPlanarRoute N hD havoid vertex edge ends hpositive).length e ≤ 20 := by
  change (P.selectorTransportRoute N hD havoid vertex edge ends e).path.length-1 ≤ 20
  have h := (P.selectorTransportRoute N hD havoid vertex edge ends e).length_bounds.2
  omega

theorem selectorTransportRoute_path_bounded {X Y : ℕ}
    (hsource : ∀ v, (P.position v).1 < X ∧ (P.position v).2 < Y)
    (hpath : ∀ e k, k ≤ P.length e → (P.point e k).1 < X ∧ (P.point e k).2 < Y)
    (e : H.Edge) {z : ℕ × ℕ}
    (hz : z ∈ (P.selectorTransportRoute N hD havoid vertex edge ends e).path) :
    z.1 < 32*X ∧ z.2 < 32*Y := by
  have hs := P.selectorTransportRoute_spec N hD havoid vertex edge ends e
  apply (P.selectorTransportRoute N hD havoid vertex edge ends e).path_bounded ?_ ?_ hz
  · rw [hs.2.2.1]
    exact P.crossingPosition_bounded hsource hpath N D _
  · rw [hs.2.2.2]
    exact P.crossingPosition_bounded hsource hpath N D _

theorem selectorPlanarRoute_bounded {X Y : ℕ}
    (hpositive : ∀ v, 0 < (P.position v).1 ∧ 0 < (P.position v).2)
    (hsource : ∀ v, (P.position v).1 < X ∧ (P.position v).2 < Y)
    (hpath : ∀ e k, k ≤ P.length e → (P.point e k).1 < X ∧ (P.point e k).2 < Y) :
    (P.selectorPlanarRoute N hD havoid vertex edge ends hpositive).Bounded (32*X) (32*Y) := by
  refine ⟨fun v => P.crossingPosition_bounded hsource hpath N D (vertex v),?_⟩
  intro e k hk
  let L := P.selectorPlanarList N hD havoid vertex edge ends hpositive
  change (L.point e k).1 < 32*X ∧ (L.point e k).2 < 32*Y
  apply P.selectorTransportRoute_path_bounded N hD havoid vertex edge ends hsource hpath e
  exact L.point_mem e (by
    have hlen := L.length e
    change k ≤ (L.path e).length-1 at hk
    omega)

end Transport
end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPlanarTapeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The emitted planar tape is the exact coordinate and path array of a
bounded planar family, in its literal merged-edge order. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

namespace QuantumRouteSelectorProgram

theorem value_eq_of_allowed (t u : QuantumRoutingTable.Table)
    (h : ∀ B, QuantumRoutingTable.allowed t B = QuantumRoutingTable.allowed u B)
    (ends : Ends) : value (t,ends) = value (u,ends) := by
  have ht : QuantumTaggedRouteProgram.tagged t = QuantumTaggedRouteProgram.tagged u := by
    funext R
    simp only [QuantumTaggedRouteProgram.tagged,QuantumTaggedRouteProgram.bodyPermitted,h]
  simp only [value,candidates,ht]

end QuantumRouteSelectorProgram

namespace QuantumPlanarTapeGeometry
open QuantumPlanarTapeProgram QuantumRouteCode

private theorem map_eq_ofFn {α β : Type*} (xs : List α) (f : α → β) :
    xs.map f = List.ofFn (fun i => f (xs.get i)) := by
  have h := congrArg (List.map f) (List.ofFn_get xs)
  rw [List.map_ofFn] at h
  exact h.symm

theorem graph_packed (x : Input) (hn : ∀ e ∈ x.1.1.2.1, e.1 ≠ e.2.1) :
    QuantumListGraph.packed (graph x hn) (Equiv.refl _) = merged x := by
  change List.ofFn (fun i : Fin (merged x).length => (merged x).get i) = merged x
  exact List.ofFn_get _

section Geometry
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D) (x : Input)
    (hb : SourceBondLists.bounded x.1.1.1 x.1.1.2.1)
    (hn : ∀ e ∈ x.1.1.2.1, e.1 ≠ e.2.1)
    (vertex : Fin x.1.1.1 ≃ Fin (P.crossingOutput N hD).n)
    (forward : ∀ e : (rawGraph x hb hn).Edge, ∃ f : (P.crossingOutput N hD).Edge,
      s(vertex ((rawGraph x hb hn).left e),vertex ((rawGraph x hb hn).right e)) =
        s((P.crossingOutput N hD).left f,(P.crossingOutput N hD).right f))
    (backward : ∀ f : (P.crossingOutput N hD).Edge, ∃ e : (rawGraph x hb hn).Edge,
      s(vertex ((rawGraph x hb hn).left e),vertex ((rawGraph x hb hn).right e)) =
        s((P.crossingOutput N hD).left f,(P.crossingOutput N hD).right f))
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (hpositive : ∀ v, 0 < (P.position v).1 ∧ 0 < (P.position v).2)

theorem route_length (e : (graph x hn).Edge) :
    (route P N hD x hb hn vertex forward backward havoid hpositive).length e ≤ 20 :=
  P.selectorPlanarRoute_length (H := graph x hn) N hD havoid vertex (edge P N hD x hb hn vertex forward backward)
    (edge_endpoints P N hD x hb hn vertex forward backward) hpositive e

theorem route_bounded {X Y : ℕ}
    (hsource : ∀ v, (P.position v).1 < X ∧ (P.position v).2 < Y)
    (hpath : ∀ e k, k ≤ P.length e → (P.point e k).1 < X ∧ (P.point e k).2 < Y) :
    (route P N hD x hb hn vertex forward backward havoid hpositive).Bounded (32*X) (32*Y) :=
  P.selectorPlanarRoute_bounded (H := graph x hn) N hD havoid vertex (edge P N hD x hb hn vertex forward backward)
    (edge_endpoints P N hD x hb hn vertex forward backward) hpositive hsource hpath

variable
    (hpositions : x.1.2 = List.ofFn (fun v => P.crossingPosition N D (vertex v)))
    (hallowed : ∀ B, QuantumRoutingTable.allowed x.2 B =
      QuantumRoutingTable.allowed P.routingTable B)

include hpositions in
theorem lookup_position (v : Fin x.1.1.1) :
    QuantumForkGridProgram.lookup x.1.2 v.val = P.crossingPosition N D (vertex v) := by
  rw [hpositions]
  unfold QuantumForkGridProgram.lookup
  rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_ofFn]
  simp only [dite_eq_left v.isLt,Option.getD_some]

include hpositions hallowed in
theorem selected_path (e : (graph x hn).Edge) :
    QuantumRouteSelectorProgram.value (routeInput x ((merged x).get e)) =
      QuantumRouteSelectorProgram.value (P.routingTable,
        P.crossingPosition N D (vertex ((graph x hn).left e)),
        P.crossingPosition N D (vertex ((graph x hn).right e))) := by
  let a : Fin x.1.1.1 := (graph x hn).left e
  let b : Fin x.1.1.1 := (graph x hn).right e
  change QuantumRouteSelectorProgram.value (x.2,
    QuantumForkGridProgram.lookup x.1.2 a.val,
    QuantumForkGridProgram.lookup x.1.2 b.val) =
      QuantumRouteSelectorProgram.value (P.routingTable,
        P.crossingPosition N D (vertex a),P.crossingPosition N D (vertex b))
  rw [lookup_position P N hD x vertex hpositions a,lookup_position P N hD x vertex hpositions b]
  exact QuantumRouteSelectorProgram.value_eq_of_allowed x.2 P.routingTable hallowed _

include hpositions hallowed in
theorem path_eq (e : (graph x hn).Edge) :
    QuantumRouteSelectorProgram.value (routeInput x ((merged x).get e)) =
      (List.range ((route P N hD x hb hn vertex forward backward havoid hpositive).length e+1)).map
        ((route P N hD x hb hn vertex forward backward havoid hpositive).point e) := by
  exact (selected_path P N hD x hn vertex hpositions hallowed e).trans
    (P.selectorPlanarRoute_path (H := graph x hn) N hD havoid vertex (edge P N hD x hb hn vertex forward backward)
      (edge_endpoints P N hD x hb hn vertex forward backward) hpositive e).symm

include hpositions in
theorem positions_eq : (value x).2.1 =
    List.ofFn (route P N hD x hb hn vertex forward backward havoid hpositive).position :=
  hpositions

include hpositions hallowed in
theorem paths_eq : (value x).2.2 =
    List.ofFn (fun e =>
      (List.range ((route P N hD x hb hn vertex forward backward havoid hpositive).length e+1)).map
        ((route P N hD x hb hn vertex forward backward havoid hpositive).point e)) := by
  change (merged x).map (fun e => QuantumRouteSelectorProgram.value (routeInput x e)) = _
  rw [map_eq_ofFn]
  apply congrArg List.ofFn
  funext e
  exact path_eq P N hD x hb hn vertex forward backward havoid hpositive hpositions hallowed e

include hpositions hallowed in
theorem value_eq : value x =
    (((graph x hn).n,QuantumListGraph.packed (graph x hn) (Equiv.refl _),(graph x hn).constant),
      List.ofFn (route P N hD x hb hn vertex forward backward havoid hpositive).position,
      List.ofFn (fun e =>
        (List.range ((route P N hD x hb hn vertex forward backward havoid hpositive).length e+1)).map
          ((route P N hD x hb hn vertex forward backward havoid hpositive).point e))) := by
  apply Prod.ext
  · rw [graph_packed]
    rfl
  · exact Prod.ext
      (positions_eq P N hD x hb hn vertex forward backward havoid hpositive hpositions)
      (paths_eq P N hD x hb hn vertex forward backward havoid hpositive hpositions hallowed)

include hpositions hallowed in
theorem even_input_eq (M : ℚ) :
    (M,value x) = QuantumEvenTapeGeometry.input
      (route P N hD x hb hn vertex forward backward havoid hpositive) (Equiv.refl _) M := by
  exact congrArg (fun t : Output => (M,t))
    (value_eq P N hD x hb hn vertex forward backward havoid hpositive hpositions hallowed)

end Geometry
end QuantumPlanarTapeGeometry
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPacketRoutingGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Packet support and the finite permission table suffice to recover the
actual emitted planar family and its final nearest-neighbor embedding. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPlanarTapeGeometry
open QuantumPlanarTapeProgram
open scoped Classical

variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D) (x : Input)
    (hg : QMAPacketGeometry (P.crossingOutput N hD) (P.crossingPosition N D) x.1.1 x.1.2)
    (hallowed : ∀ B, QuantumRoutingTable.allowed x.2 B =
      QuantumRoutingTable.allowed P.routingTable B)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (hpositive : ∀ v, 0 < (P.position v).1 ∧ 0 < (P.position v).2)
    {X Y : ℕ}
    (hsource : ∀ v, (P.position v).1 < X ∧ (P.position v).2 < Y)
    (hpath : ∀ e k, k ≤ P.length e → (P.point e k).1 < X ∧ (P.point e k).2 < Y)

include hD hg hallowed havoid hpositive hsource hpath in
theorem planar_family :
    ∃ R : QMAPlanarRouteData (graph x hg.noLoops),
      (N,value x) = QuantumEvenTapeGeometry.input R (Equiv.refl _) N ∧
      (∀ e, R.length e ≤ 20) ∧ R.Bounded (32*X) (32*Y) := by
  obtain ⟨v,hpos,hforward,hbackward⟩ := hg.matching
  exact ⟨route P N hD x hg.bounded hg.noLoops v hforward hbackward havoid hpositive,
    even_input_eq P N hD x hg.bounded hg.noLoops v hforward hbackward havoid hpositive
      hpos hallowed N,
    route_length P N hD x hg.bounded hg.noLoops v hforward hbackward havoid hpositive,
    route_bounded P N hD x hg.bounded hg.noLoops v hforward hbackward havoid hpositive
      hsource hpath⟩

include hD hg hallowed havoid hpositive hsource hpath in
theorem final_realization_oai (hN : 0 < N) :
    let s := QuantumListRouteProgram.iterate N QuantumFinalRoutingProgram.rounds
      (QuantumEvenTapeProgram.value (N,value x))
    ∃ (hs : QuantumListSchedule.Valid s.1)
      (Q : QMAPathEmbedding (QuantumListSchedule.schedule s.1 hs)),
      QuantumListRouteProgram.Represents s hs Q ∧ Q.Bounded (256*X) (256*Y) ∧
      (∀ e, qmaSquareGrid.Adj (Q.position ((QuantumListSchedule.schedule s.1 hs).graph.left e))
        (Q.position ((QuantumListSchedule.schedule s.1 hs).graph.right e))) := by
  obtain ⟨R,hinput,hL,hbox⟩ := planar_family P N hD x hg hallowed havoid hpositive hsource hpath
  have h := QuantumEvenTapeGeometry.realizes R (Equiv.refl _) N hN hL hbox
  rw [← hinput] at h
  obtain ⟨hs,Q,hQ,hbox',hgrid,_,_⟩ := h
  exact ⟨hs,Q,hQ,by simpa only [← Nat.mul_assoc,show 8*32=256 by decide] using hbox',hgrid⟩

end ContinuumCoulomb.QuantumPlanarTapeGeometry

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.QuantumPlanarTapeGeometry.final_realization_oai := @OAI.ContinuumCoulomb.QuantumPlanarTapeGeometry.final_realization_oai
