-- Prove2me | solution 1 for OAI.ContinuumCoulomb.QuantumHistorySourceProgram.history_error
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:38:03.02433+00:00
-- url     : https://prove2.me/submissions/6e82e58c-f660-45e1-8f92-86f3f1a723cc

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
import Mathlib.NumberTheory.Real.Irrational
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
import Theorems.Thm_OAI_ContinuumCoulomb_QuantumFinalRoutingProgram_spatial_energy_error
import Theorems.Thm_OAI_ContinuumCoulomb_QuantumPaddedLabelProgram_history_accuracy

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFixedPauli
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_conj _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_imaginary _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_neg _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_rat _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-arity Pauli traces evaluated entirely in rational registers.
The interpretation is the actual complex Pauli coefficient, not an
assumed list of Hamiltonian coefficients. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFixedPauli
open QuantumAlgebraicScalar Matrix
open scoped BigOperators Classical

theorem value_finiteProduct {α : Type} [Fintype α] (f : α → Scalar) :
    value (finiteProduct f) = ∏ a, value (f a) := by
  simp only [finiteProduct,value_product,enumerate,List.map_ofFn,List.prod_ofFn]
  exact (Fintype.equivFin α).symm.prod_comp (fun a => value (f a))

theorem value_pauli (μ : Fin 4) (a b : Fin 2) :
    value (pauli μ a b) = qmaPauli μ a b := by
  fin_cases μ <;> fin_cases a <;> fin_cases b <;>
    norm_num [pauli,qmaPauli,pauliX,pauliY,pauliZ]

end ContinuumCoulomb.QuantumFixedPauli

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAlgebraicHistory
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_conj _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_neg _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_rat _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual ordered history cores have exact four-rational entries.  The
propagation Gram is formed on its at-most-five-site core; the construction
does not sum over spectator configurations. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli Matrix
open scoped BigOperators Classical

theorem value_identity {α : Type} [DecidableEq α] (s t : α) :
    value (identity s t) = (1 : Matrix α α ℂ) s t := by
  by_cases h : s = t <;> simp [identity,Matrix.one_apply,h]

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal short support lists for the time-ordered history compiler.
The list order, duplicate removal, and local-coordinate equivalence are
explicit; no arbitrary finite-type enumeration enters the input algorithm. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedSupport
open scoped Classical

theorem supportEquiv_apply (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) (i : Fin (sites c hT a).length) :
    (supportEquiv c hT a i).val = (sites c hT a).get i := rfl

theorem siteNumber_injective (c : QMACircuit) : Function.Injective (siteNumber c) := by
  intro i j h
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    simp only [siteNumber] at h
  all_goals have hi := i.isLt
  all_goals have hj := j.isLt
  · exact congrArg Sum.inl (Fin.ext h)
  · omega
  · omega
  · omega
  · exact congrArg (fun x => Sum.inr (Sum.inl x)) (Fin.ext (by omega))
  · omega
  · omega
  · omega
  · exact congrArg (fun x => Sum.inr (Sum.inr x)) (Fin.ext (by omega))

end ContinuumCoulomb.QuantumOrderedSupport

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistorySiteProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal ordered gate and propagation support lists. The values agree
with the exact support order used by the local history matrix tables. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySiteProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

theorem gateLabels_actual (work : ℕ) (g : QMAGate) :
    gateLabels (work,g)=(QuantumOrderedSupport.gateSites work g).map Fin.val := by
  cases g <;> rfl

theorem propagationLabels_actual (c : QMACircuit) (t : Fin c.gates.length) :
    propagationLabels (c,t.val)=
      (QuantumOrderedSupport.propagationSites c t).map (distributedNumber c) := by
  simp only [propagationLabels,gateAt,gateLabels_actual,
    QuantumOrderedSupport.propagationSites,List.map_append,List.map_cons,List.map_nil,
    List.map_map,Function.comp_def,distributedNumber,qmaClockLeft,qmaClockMiddle,qmaClockRight]
  rfl

end ContinuumCoulomb.QuantumHistorySiteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedDescriptors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numeric time grouping agrees with the exact ordered reference family.
The first-use time is computed from the actual gate list. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDescriptors
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

theorem ordered_get (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) :
    (ordered c)[i.val]'(by rw [ordered_length c hT]; exact i.isLt) =
      encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i) := by
  simp only [ordered_actual c hT,List.getElem_map,qmaOrderedTermEquiv_get]

end ContinuumCoulomb.QuantumHistoryDescriptors

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkEffective
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational asymmetric fork gadget for reducing the degree of an old spin. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFork_effective {n r : ℕ} (e : Fin r) (site : Fin 3 → Fin n)
    (hsite : Function.Injective site) (R J K : ℝ) (hR : R ≠ 0) :
    qmaForkCorrection site J K - mediatorCompression n r
      (qmaSingletStar n r e site qmaForkMember (qmaForkAmplitude R J K) *
        liftedMediatorInverse n r (R^2) *
          qmaSingletStar n r e site qmaForkMember (qmaForkAmplitude R J K)) =
      (J:ℂ) • sourceHeisenbergMatrix n (site 0) (site 1) +
        (K:ℂ) • sourceHeisenbergMatrix n (site 0) (site 2) := by
  have hk (a b : Fin 3) : qmaPauliKernel n (site a) (site b) =
      if a = b then (3:ℂ) • 1 else sourceHeisenbergMatrix n (site a) (site b) := by
    by_cases hab : a = b
    · subst b
      simp only [ite_true, if_true,qmaPauliKernel_self]
    · rw [ite_eq_right hab]
      exact qmaPauliKernel_eq n _ _ (fun h => hab (hsite h))
  rw [qmaSingletStar_compression]
  simp only [hk,qmaForkCorrection]
  simp [qmaForkMember,qmaForkAmplitude,Fin.sum_univ_succ]
  rw [qmaHeisenberg_symm n (site 1) (site 0),qmaHeisenberg_symm n (site 2) (site 0),
    qmaHeisenberg_symm n (site 2) (site 1)]
  ext s t
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.neg_apply,Matrix.smul_apply,
    smul_eq_mul,RCLike.real_smul_eq_coe_smul (K := ℂ),RCLike.ofReal_eq_complex_ofReal]
  have hRC : (R:ℂ) ≠ 0 := by exact_mod_cast hR
  field_simp [hRC]
  ring

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full-space energy comparison for the rational fork gadget. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker

theorem qmaForkCorrection_star {n : ℕ} (site : Fin 3 → Fin n)
    (hsite : Function.Injective site) (J K : ℝ) :
    (qmaForkCorrection site J K).conjTranspose = qmaForkCorrection site J K := by
  have hne : site 1 ≠ site 2 := fun h => (by decide : (1:Fin 3) ≠ 2) (hsite h)
  simp only [qmaForkCorrection,Matrix.conjTranspose_add,Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one,sourceHeisenbergMatrix_star n _ _ hne,
    Complex.star_def,Complex.conj_ofReal]

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial coefficient and operator bounds for parallel degree reduction. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

theorem qmaForkCorrection_exchange {n : ℕ} (site : Fin 3 → Fin n) (J K : ℝ) :
    qmaForkCorrection site J K =
      qmaExchangeMatrix (fun _ : Fin 1 => site 1)
        (fun _ : Fin 1 => site 2) (fun _ => 2*J*K) (qmaForkOffset J K) := by
  simp [qmaForkCorrection,qmaExchangeMatrix,qmaForkOffset,add_comm]

theorem qmaForkCorrection_lift_norm {n r : ℕ} (site : Fin 3 → Fin n)
    (hsite : Function.Injective site) (J K : ℝ) :
    ‖spinMatrixOperator (qmaForkCorrection site J K ⊗ₖ
      (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ ≤ 12*(1+|J|+|K|)^2 := by
  have hneq (_a : Fin 1) : site 1 ≠ site 2 :=
    fun h => (by decide : (1 : Fin 3) ≠ 2) (hsite h)
  rw [qmaForkCorrection_exchange]
  apply (qmaExchangeMatrix_lift_norm _ _ hneq _ _).trans
  have hoff : 0 ≤ qmaForkOffset J K := by unfold qmaForkOffset; positivity
  rw [abs_of_nonneg hoff]
  simp [qmaForkOffset,abs_mul]
  nlinarith [sq_abs J,sq_abs K,abs_nonneg J,abs_nonneg K,mul_nonneg (abs_nonneg J) (abs_nonneg K)]

theorem qmaForkAmplitude_norm (R J K : ℝ) (hR : 0 ≤ R) :
    3*(∑ a, |qmaForkAmplitude R J K a|) = 3*R*(1+2*|J|+2*|K|) := by
  simp [qmaForkAmplitude,Fin.sum_univ_succ,abs_mul,abs_of_nonneg hR]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkParallel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous fork elimination, with no mixed error between distinct singlets. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

theorem qmaForks_effective {n r : ℕ} (site : Fin r → Fin 3 → Fin n)
    (hsite : ∀ e, Function.Injective (site e)) (R : ℝ) (hR : R ≠ 0) (J K : Fin r → ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :
    (C + ∑ e, qmaForkCorrection (site e) (J e) (K e)) -
      mediatorCompression n r (qmaRoutingStars n r site (fun _ => qmaForkMember)
          (fun e => qmaForkAmplitude R (J e) (K e)) * liftedMediatorInverse n r (R^2) *
        qmaRoutingStars n r site (fun _ => qmaForkMember)
          (fun e => qmaForkAmplitude R (J e) (K e))) =
      C + ∑ e, ((J e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 1) +
        (K e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 2)) := by
  rw [qmaRoutingStars_compression,add_sub_assoc,← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  exact qmaFork_effective e (site e) (hsite e) R (J e) (K e) hR

theorem qmaForks_bottom {n r : ℕ} (site : Fin r → Fin 3 → Fin n)
    (hsite : ∀ e, Function.Injective (site e)) (R : ℝ) (hR : 0 < R) (J K : Fin r → ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1/4)
    (hbound : ‖spinMatrixOperator ((C + ∑ e, qmaForkCorrection (site e) (J e) (K e)) ⊗ₖ
        (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      3*∑ e, ∑ a, |qmaForkAmplitude R (J e) (K e) a| ≤ epsilon * (4*R^2)) :
    |mediatorFullBottom n r (routingHamiltonian n r (R^2)
        (C + ∑ e, qmaForkCorrection (site e) (J e) (K e))
        (qmaRoutingStars n r site (fun _ => qmaForkMember)
          (fun e => qmaForkAmplitude R (J e) (K e)))) -
      sourceMatrixBottom n (C + ∑ e,
        ((J e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 1) +
          (K e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 2)))| ≤
      16*R^2*epsilon^3 := by
  have hCW : (C + ∑ e, qmaForkCorrection (site e) (J e) (K e)).conjTranspose =
      C + ∑ e, qmaForkCorrection (site e) (J e) (K e) := by
    simp only [Matrix.conjTranspose_add,Matrix.conjTranspose_sum,hC,
      qmaForkCorrection_star _ (hsite _)]
  have h := qmaRoutingStars_bottom n r (sq_pos_of_pos hR) _ hCW site
    (fun _ => qmaForkMember) (fun e => qmaForkAmplitude R (J e) (K e))
    hepsilon hsmall hbound
  rw [qmaForks_effective site hsite R hR.ne' J K C] at h
  exact h

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkCalibration
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial calibration for a simultaneous fork stage. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

theorem qmaForks_correction_norm {n r : ℕ} (site : Fin r → Fin 3 → Fin n)
    (hsite : ∀ e, Function.Injective (site e)) (J K : Fin r → ℝ) :
    ‖spinMatrixOperator ((∑ e, qmaForkCorrection (site e) (J e) (K e)) ⊗ₖ
      (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ ≤
      12*∑ e, (1+|J e|+|K e|)^2 := by
  rw [MediatorGraph.sum_kronecker,spinMatrixOperator_sum,Finset.mul_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun e _ =>
    qmaForkCorrection_lift_norm (site e) (hsite e) (J e) (K e)))

theorem qmaForks_amplitude (r : ℕ) (R : ℝ) (hR : 0 ≤ R) (J K : Fin r → ℝ) :
    3*(∑ e, ∑ a, |qmaForkAmplitude R (J e) (K e) a|) =
      (3*∑ e, (1+2*|J e|+2*|K e|))*R := by
  rw [Finset.mul_sum]
  simp_rw [qmaForkAmplitude_norm R _ _ hR]
  rw [← Finset.mul_sum]
  ring

theorem qmaForks_accuracy {n r : ℕ} (site : Fin r → Fin 3 → Fin n)
    (hsite : ∀ e, Function.Injective (site e)) (J K : Fin r → ℝ)
    {B N : ℝ} (hB : 0 ≤ B) (hN : 0 < N)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    (hCn : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ ≤ B) :
    let A := 3*∑ e, (1+2*|J e|+2*|K e|)
    let D := B+12*∑ e, (1+|J e|+|K e|)^2
    let R := qmaRoutingScale A D N
    |mediatorFullBottom n r (routingHamiltonian n r (R^2)
        (C + ∑ e, qmaForkCorrection (site e) (J e) (K e))
        (qmaRoutingStars n r site (fun _ => qmaForkMember)
          (fun e => qmaForkAmplitude R (J e) (K e)))) -
      sourceMatrixBottom n (C + ∑ e,
        ((J e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 1) +
          (K e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 2)))| ≤ 1/N := by
  let A := 3*∑ e, (1+2*|J e|+2*|K e|)
  let D := B+12*∑ e, (1+|J e|+|K e|)^2
  let R := qmaRoutingScale A D N
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨hR,he,hes,hbound,herr⟩ := qmaRoutingScale_bounds hA hD hN
  have hCC : ‖spinMatrixOperator ((C + ∑ e, qmaForkCorrection (site e) (J e) (K e)) ⊗ₖ
      (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ ≤ D := by
    rw [Matrix.add_kronecker,spinMatrixOperator_add]
    exact (norm_add_le _ _).trans (add_le_add hCn (qmaForks_correction_norm site hsite J K))
  have hb : ‖spinMatrixOperator ((C + ∑ e, qmaForkCorrection (site e) (J e) (K e)) ⊗ₖ
        (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      3*∑ e, ∑ a, |qmaForkAmplitude R (J e) (K e) a| ≤ ((A+D+1)/R)*(4*R^2) := by
    rw [qmaForks_amplitude r R hR.le J K]
    exact (add_le_add hCC (le_refl (A*R))).trans hbound
  exact (qmaForks_bottom site hsite R hR J K C hC he hes hb).trans herr

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational-register tables for every actual ordered history term.
Only the propagation core is multiplied, so its summation has at most
32 states regardless of the number of spectator qubits. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli Matrix
open scoped BigOperators Classical

theorem value_localY (n : ℕ) (i : Fin n) (s t : SourceSpinBasis n) :
    value (localY n i s t) = sourceLocalPauli n i 1 s t := by
  rw [localY,value_finiteProduct]
  unfold sourceLocalPauli sourceTensor
  apply Finset.prod_congr rfl
  intro k _
  by_cases h : k = i
  · simp only [h,ite_true, if_true,value_pauli]
    rfl
  · simp only [h,ite_false, if_false,value_identity]

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedSourceIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit finite sum/product indices for the history qubits and padded
terms. Their natural values are the literal support-list site numbers. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedSourceIndex
open scoped Classical

theorem qubits_index (c : QMACircuit) :
    QuantumOrderedLabelTable.index (qubits c)=QuantumOrderedSupport.siteNumber c := by
  funext i
  rcases i with i | (i | i)
  · rfl
  · rfl
  · change qmaHistoryReferenceWork c+1+((c.gates.length+2)+i.val) =
      qmaHistoryReferenceWork c+1+(c.gates.length+2)+i.val
    omega

end ContinuumCoulomb.QuantumOrderedSourceIndex

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDescriptorSites
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The descriptor compiler computes the very same ordered support labels
as the mathematical local-history construction. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDescriptors
open QuantumHistorySiteProgram

theorem distributedLabels_actual (c : QMACircuit) (a : QMACircuitTerm c) :
    distributedLabels c (encode c a) =
      (QuantumOrderedSupport.distributedSites c (qmaFirstUseTime c) a).map
        (distributedNumber c) := by
  rcases a with i | (b | (i | (u | t)))
  · rfl
  · fin_cases b <;>
      simp [distributedLabels,encode,QuantumOrderedSupport.distributedSites,distributedNumber]
  · simp only [distributedLabels,encode]
    norm_num only
    rw [QuantumFirstUseProgram.value_eq]
    rfl
  · cases u
    rfl
  · simp only [distributedLabels,encode]
    norm_num only
    exact propagationLabels_actual c t

theorem referenceWork_eq (c : QMACircuit) : referenceWork c=qmaHistoryReferenceWork c := rfl

theorem orderedAt_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) :
    orderedAt c i.val = encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i) := by
  unfold orderedAt
  rw [List.headD_eq_head?_getD,List.head?_drop]
  rw [List.getElem?_eq_getElem (by rw [ordered_length c hT]; exact i.isLt)]
  exact ordered_get c hT i

theorem number_inr (c : QMACircuit) (q : QMACircuitQubit c) :
    QuantumOrderedSupport.siteNumber c (.inr q)=
      referenceWork c+1+distributedNumber c q := by
  cases q <;> simp [QuantumOrderedSupport.siteNumber,distributedNumber,referenceWork_eq,
    Nat.add_assoc]

theorem rebitLabels_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) :
    rebitLabels c i.val =
      (QuantumOrderedSupport.rawSites c hT (.inl i)).map
        (QuantumOrderedSupport.siteNumber c) := by
  rw [rebitLabels,orderedAt_actual c hT i,distributedLabels_actual]
  simp only [QuantumOrderedSupport.rawSites,List.map_cons,List.map_map,Function.comp_def,
    QuantumOrderedSupport.siteNumber]
  congr 1
  apply List.map_congr_left
  intro q _
  exact (number_inr c q).symm

theorem referenceLabels_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    referenceLabels c ((QuantumOrderedSourceIndex.reference c).symm a).val =
      (QuantumOrderedSupport.rawSites c hT a).map
        (QuantumOrderedSupport.siteNumber c) := by
  cases a with
  | inl i =>
    change (if i.val < referenceWork c+1 then rebitLabels c i.val else _) = _
    rw [ite_eq_left (by simpa only [referenceWork_eq] using i.isLt)]
    exact rebitLabels_actual c hT i
  | inr i =>
    change referenceLabels c (qmaHistoryReferenceWork c+1+i.val) = _
    rw [referenceLabels,ite_eq_right (by rw [referenceWork_eq]; omega)]
    simp only [referenceWork_eq,Nat.add_sub_cancel_left,QuantumOrderedSupport.rawSites,
      List.map_cons,List.map_nil,QuantumOrderedSupport.siteNumber,Fin.val_castSucc,Fin.val_succ]

theorem supportLabels_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    supportLabels c ((QuantumOrderedSourceIndex.reference c).symm a).val =
      QuantumOrderedSupport.encodedSites c hT a := by
  rw [supportLabels,referenceLabels_actual c hT a,
    List.dedup_map_of_injective (QuantumOrderedSupport.siteNumber_injective c)]
  rfl

end ContinuumCoulomb.QuantumHistoryDescriptors

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSupportLookup
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual local support coordinates are read by literal label lookup.
This identifies a small matrix input with its zero extension on spectator
qubits, without enumerating the ambient spin basis. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSupportLookup
open ExactQuantumFactoring.BitStackProgram

theorem value_map_get {α : Type} (xs : List α) (hx : xs.Nodup)
    (f : α → ℕ) (hf : Function.Injective f) (s : Fin xs.length → ℕ)
    (i : Fin xs.length) :
    value (f (xs.get i),xs.map f,List.ofFn s)=s i := by
  have hi : i.val < (xs.map f).length := by simpa only [List.length_map] using i.isLt
  have he : (xs.map f)[i.val]'hi = f (xs.get i) := by
    simp only [List.getElem_map,List.get_eq_getElem]
  have hind := (hx.map hf).idxOf_getElem i.val hi
  rw [he] at hind
  unfold value
  rw [hind,List.headD_eq_head?_getD,List.head?_drop]
  simp

theorem value_not_mem (xs ys : List ℕ) (q : ℕ)
    (hq : q ∉ xs) (hy : ys.length ≤ xs.length) : value (q,xs,ys)=0 := by
  unfold value
  rw [List.idxOf_of_notMem hq,List.drop_eq_nil_of_le hy]
  rfl

open QuantumOrderedSupport
open scoped Classical

private theorem extend_mem {α : Type} [Fintype α] [DecidableEq α]
    (S : Finset α) (u : QMASupportBasis S) (q : α) (hq : q ∈ S) :
    qmaSupportExtend S u q = u ⟨q,hq⟩ :=
  dite_eq_left hq

private theorem extend_not_mem {α : Type} [Fintype α] [DecidableEq α]
    (S : Finset α) (u : QMASupportBasis S) (q : α) (hq : q ∉ S) :
    qmaSupportExtend S u q = 0 :=
  dite_eq_right hq

theorem support_value (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s : Fin (sites c hT a).length → Fin 2) (q : Qubit c) :
    value (siteNumber c q,encodedSites c hT a,supportBits c hT a s) =
      (qmaSupportExtend ((qmaOrderedHistoryModel c hT).sites a)
        (fun i => s ((supportEquiv c hT a).symm i)) q).val := by
  by_cases hq : q ∈ (qmaOrderedHistoryModel c hT).sites a
  · let i := (supportEquiv c hT a).symm ⟨q,hq⟩
    have hi : (sites c hT a).get i=q := by
      have h := congrArg Subtype.val ((supportEquiv c hT a).apply_symm_apply ⟨q,hq⟩)
      exact h
    have hlookup := value_map_get (sites c hT a) (sites_nodup c hT a)
      (siteNumber c) (siteNumber_injective c) (fun j => (s j).val) i
    have hv : value (siteNumber c q,encodedSites c hT a,supportBits c hT a s) =
        (s i).val := by
      simpa only [encodedSites,supportBits,hi] using hlookup
    exact hv.trans (congrArg Fin.val (extend_mem
      ((qmaOrderedHistoryModel c hT).sites a)
      (fun j => s ((supportEquiv c hT a).symm j)) q hq)).symm
  · have hn : siteNumber c q ∉ encodedSites c hT a := by
      intro h
      obtain ⟨p,hp,he⟩ := List.mem_map.mp h
      have hpq := siteNumber_injective c he
      subst p
      apply hq
      rw [← sites_finset c hT a]
      exact List.mem_toFinset.mpr hp
    have hzero := value_not_mem (encodedSites c hT a) (supportBits c hT a s)
      (siteNumber c q) hn (by simp only [supportBits,List.length_ofFn,
        encodedSites,List.length_map,le_refl])
    have hv : value (siteNumber c q,encodedSites c hT a,supportBits c hT a s) = 0 := by
      exact hzero
    exact hv.trans (congrArg Fin.val (extend_not_mem
      ((qmaOrderedHistoryModel c hT).sites a)
      (fun j => s ((supportEquiv c hT a).symm j)) q hq)).symm

theorem support_readBit (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s : Fin (sites c hT a).length → Fin 2) (q : Qubit c) :
    readBit (siteNumber c q,encodedSites c hT a,supportBits c hT a s) =
      qmaSupportExtend ((qmaOrderedHistoryModel c hT).sites a)
        (fun i => s ((supportEquiv c hT a).symm i)) q := by
  apply Fin.ext
  change value _ % 2 = _
  rw [support_value]
  exact Nat.mod_eq_of_lt (Fin.isLt _)

end ContinuumCoulomb.QuantumSupportLookup

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryBitProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal bit reads for the small history tables, and a bounded Boolean
scan.  The register bound is unary; this scan has no spin-configuration loop. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryBitProgram
open ExactQuantumFactoring.BitStackProgram QuantumAlgebraicScalar

theorem row_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s t : Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2)
    (q : QuantumOrderedSupport.Qubit c) :
    row (QuantumOrderedSupport.encodedSites c hT a,
      QuantumSupportLookup.supportBits c hT a s,
      QuantumSupportLookup.supportBits c hT a t)
      (QuantumOrderedSupport.siteNumber c q) =
    qmaSupportExtend ((qmaOrderedHistoryModel c hT).sites a)
      (fun i => s ((QuantumOrderedSupport.supportEquiv c hT a).symm i)) q :=
  QuantumSupportLookup.support_readBit c hT a s q

theorem column_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s t : Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2)
    (q : QuantumOrderedSupport.Qubit c) :
    column (QuantumOrderedSupport.encodedSites c hT a,
      QuantumSupportLookup.supportBits c hT a s,
      QuantumSupportLookup.supportBits c hT a t)
      (QuantumOrderedSupport.siteNumber c q) =
    qmaSupportExtend ((qmaOrderedHistoryModel c hT).sites a)
      (fun i => t ((QuantumOrderedSupport.supportEquiv c hT a).symm i)) q :=
  QuantumSupportLookup.support_readBit c hT a t q

end ContinuumCoulomb.QuantumHistoryBitProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryDiagonal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_conj _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_neg _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_rat _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The four diagonal descriptor cases are evaluated directly from their
clock/work bits.  Their values are exact rational entries of the actual
distributed history operator, before the rebit construction. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDiagonal
open QuantumHistoryDescriptors QuantumHistorySiteProgram QuantumHistoryBitProgram
open QuantumAlgebraicScalar
open scoped Classical

theorem distributed_entry (c : QMACircuit) (a : QMACircuitTerm c)
    (ha : (encode c a).1<4) (d : Data) :
    QuantumAlgebraicHistory.distributed c (qmaFirstUseTime c) a
      (readRow c d) (readColumn c d) =
    if readRow c d=readColumn c d then rat (weight c (encode c a) d) else rat 0 := by
  rcases a with i | (b | (i | (u | t)))
  · rfl
  · fin_cases b <;> rfl
  · change (if readRow c d=readColumn c d then rat
        (if qmaClockAt c.gates.length (qmaFirstUseTime c i) (readRow c d ∘ Sum.inl) ∧
          qmaInputCheck c i (readRow c d ∘ Sum.inr) then 14 else 0) else rat 0) =
      if readRow c d=readColumn c d then rat
        (if clockRow c d (QuantumFirstUseProgram.value (c,i.val))=1 ∧
          clockRow c d (QuantumFirstUseProgram.value (c,i.val)+1)=0 ∧
          c.witness ≤ i.val ∧ workRow c d i.val≠0 then 14 else 0) else rat 0
    simp only [QuantumFirstUseProgram.value_eq]
    unfold qmaClockAt qmaInputCheck
    have he : (clockRow c d (qmaFirstUse c i)=1 ∧
        clockRow c d (qmaFirstUse c i+1)=0) ∧
        (c.witness ≤ i.val ∧ workRow c d i.val≠0) ↔
      clockRow c d (qmaFirstUse c i)=1 ∧
        clockRow c d (qmaFirstUse c i+1)=0 ∧
        c.witness ≤ i.val ∧ workRow c d i.val≠0 := by tauto
    simp only [readRow,clockRow,workRow,referenceWork_eq,
      QuantumOrderedSupport.siteNumber,Function.comp_apply,Fin.val_castSucc,Fin.val_succ] at *
    simp only [he]
    rfl
  · cases u
    rfl
  · norm_num [encode] at ha

theorem readRow_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s t : Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2) :
    readRow c (supportData c hT a s t) = fun q =>
      qmaSupportExtend ((qmaOrderedHistoryModel c hT).sites a)
        (fun j => s ((QuantumOrderedSupport.supportEquiv c hT a).symm j)) (.inr q) := by
  funext q
  exact QuantumHistoryBitProgram.row_actual c hT a s t (.inr q)

theorem readColumn_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s t : Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2) :
    readColumn c (supportData c hT a s t) = fun q =>
      qmaSupportExtend ((qmaOrderedHistoryModel c hT).sites a)
        (fun j => t ((QuantumOrderedSupport.supportEquiv c hT a).symm j)) (.inr q) := by
  funext q
  exact QuantumHistoryBitProgram.column_actual c hT a s t (.inr q)

end ContinuumCoulomb.QuantumHistoryDiagonal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRebitDiagonal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_conj _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_imaginary _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_neg _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_rat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.realHeight_neg _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.realHeight_rat _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A real diagonal term remains diagonal under the reference-spin rebit
construction.  These entry identities avoid any sum over spectators. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDiagonal
open QuantumAlgebraicHistory QuantumAlgebraicScalar
open scoped Classical

theorem rebit_rat_entry {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (i : Fin n) (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar)
    (s t : Fin n ⊕ ι → Fin 2) (q : ℚ)
    (hA : A (s ∘ Sum.inr) (t ∘ Sum.inr)=rat q) :
    rebit n i A s t = if s ∘ Sum.inl=t ∘ Sum.inl then rat q else rat 0 := by
  by_cases h : s ∘ Sum.inl=t ∘ Sum.inl
  · simp [rebit,hA,identity,h,rat,realRat,QuantumAlgebraicScalar.realPart,imagPart,mul,add,neg,
      realAdd,realSub,realNeg,realMul,imaginary]
  · simp [rebit,hA,identity,h,rat,realRat,QuantumAlgebraicScalar.realPart,imagPart,mul,add,neg,
      realAdd,realSub,realNeg,realMul,imaginary]

theorem rebit_diagonal_entry {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (i : Fin n) (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar)
    (s t : Fin n ⊕ ι → Fin 2) (q : ℚ)
    (hA : A (s ∘ Sum.inr) (t ∘ Sum.inr)=
      if s ∘ Sum.inr=t ∘ Sum.inr then rat q else rat 0) :
    rebit n i A s t = if s=t then rat q else rat 0 := by
  by_cases hb : s ∘ Sum.inr=t ∘ Sum.inr
  · rw [ite_eq_left hb] at hA
    rw [rebit_rat_entry n i A s t q hA]
    have he : (s ∘ Sum.inl=t ∘ Sum.inl) ↔ s=t := by
      constructor
      · intro hr
        funext a
        cases a with
        | inl a => exact congrFun hr a
        | inr a => exact congrFun hb a
      · intro h
        exact congrArg (fun f => f ∘ Sum.inl) h
    simp only [he]
  · rw [ite_eq_right hb] at hA
    rw [rebit_rat_entry n i A s t 0 hA]
    have hne : s≠t := fun h => hb (congrArg (fun f => f ∘ Sum.inr) h)
    simp [hne]

theorem orderedExtend_at (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s : Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2)
    (i : Fin (QuantumOrderedSupport.sites c hT a).length) :
    orderedExtend c hT a s ((QuantumOrderedSupport.supportEquiv c hT a i).val)=s i := by
  calc
    orderedExtend c hT a s ((QuantumOrderedSupport.supportEquiv c hT a i).val) =
      s ((QuantumOrderedSupport.supportEquiv c hT a).symm
        (QuantumOrderedSupport.supportEquiv c hT a i)) :=
      dite_eq_left (QuantumOrderedSupport.supportEquiv c hT a i).property
    _ = s i := congrArg s ((QuantumOrderedSupport.supportEquiv c hT a).symm_apply_apply i)

theorem orderedExtend_injective (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    Function.Injective (orderedExtend c hT a) := by
  intro s t h
  funext i
  have he := congrFun h (QuantumOrderedSupport.supportEquiv c hT a i).val
  simpa only [orderedExtend_at] using he

theorem ordered_diagonal_entry (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1))
    (ha : (QuantumHistoryDescriptors.encode c
      (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i)).1<4)
    (s t : Fin (QuantumOrderedSupport.sites c hT (.inl i)).length → Fin 2) :
    orderedTable c hT (.inl i) s t = if s=t then rat (weight c
      (QuantumHistoryDescriptors.encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i))
      (supportData c hT (.inl i) s t)) else rat 0 := by
  let S := orderedExtend c hT (.inl i) s
  let T := orderedExtend c hT (.inl i) t
  let a := qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i
  have hd := distributed_entry c a ha (supportData c hT (.inl i) s t)
  rw [readRow_actual,readColumn_actual] at hd
  have he := rebit_diagonal_entry (qmaHistoryReferenceWork c+1) i
    (distributed c (qmaFirstUseTime c) a) S T
    (weight c (QuantumHistoryDescriptors.encode c a) (supportData c hT (.inl i) s t)) hd
  have hs : S=T ↔ s=t := (orderedExtend_injective c hT (.inl i)).eq_iff
  change rebit (qmaHistoryReferenceWork c+1) i (distributed c (qmaFirstUseTime c) a) S T = _
  rw [he]
  simp only [hs]
  rfl

end ContinuumCoulomb.QuantumHistoryDiagonal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDiagonalTableProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-arity scalar tables for the actual diagonal history terms.
Only the local support bits are tabulated; the arity is at most six. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDiagonal
open ExactQuantumFactoring.BitStackProgram QuantumAlgebraicScalar QuantumFixedPauli
open QuantumCircuitCode QuantumHistoryDescriptors
open scoped Classical

theorem table_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1))
    (ha : (encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i)).1<4) :
    table (QuantumOrderedSupport.sites c hT (.inl i)).length
      (c,encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i),
        QuantumOrderedSupport.encodedSites c hT (.inl i)) =
      QuantumAlgebraicHistory.orderedTable c hT (.inl i) := by
  funext s t
  exact (ordered_diagonal_entry c hT i ha s t).symm

theorem tableList_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1))
    (ha : (encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i)).1<4) :
    tableList (QuantumOrderedSupport.sites c hT (.inl i)).length
      (c,encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i),
        QuantumOrderedSupport.encodedSites c hT (.inl i)) =
      matrixData (QuantumAlgebraicHistory.orderedTable c hT (.inl i)) :=
  congrArg matrixData (table_actual c hT i ha)

end ContinuumCoulomb.QuantumHistoryDiagonal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceBondLists
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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact exchange-graph semantics for the finite bond lists manipulated by
the routing compiler. The scalar offset stays part of the full Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListGraph
open Matrix MediatorListProgram
open scoped BigOperators Classical

theorem ofBonds_matrix (n : ℕ) (xs : List Bond) (c : ℚ)
    (hb : SourceBondLists.bounded n xs) (hn : ∀ e ∈ xs, e.1 ≠ e.2.1) :
    qmaExchangeMatrix (n := n) (ofBonds n xs c hb hn).left (ofBonds n xs c hb hn).right
      (fun e => ((ofBonds n xs c hb hn).weight e:ℝ)) c =
      SourceBondLists.matrix n xs+(c:ℂ) • 1 := by
  rw [SourceBondLists.matrix_bonds n xs hb]
  simp only [ofBonds,qmaExchangeMatrix,MediatorIteration.Bonds.matrix,sourceGraphMatrix,
    Complex.ofReal_ratCast]
  rfl

end ContinuumCoulomb.QuantumListGraph

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFinalPrecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Precision for all nine early simulation errors and the subsequent
routing errors, retaining the exact final inverse-polynomial promise gap. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open ExactQuantumFactoring.BitStackProgram

theorem finalPrecision_pos (rounds : ℕ) (c : QMACircuit) :
    0 < finalPrecision rounds c := by
  unfold finalPrecision
  positivity

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordinary spin edges and polynomial full-space error for a parallel fork round. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix MediatorGraph
open scoped BigOperators Kronecker Classical
variable {ν : Type*} [Fintype ν]

omit [Fintype ν] in
theorem qmaForksBase_distinct {n r : ℕ} (left right : ν → Fin n)
    (hneq : ∀ a, left a ≠ right a) (site : Fin r → Fin 3 → Fin n)
    (hsite : ∀ e, Function.Injective (site e)) :
    ∀ a, qmaForksBaseLeft left site a ≠ qmaForksBaseRight right site a := by
  intro a
  cases a with
  | inl a => exact hneq a
  | inr e => exact fun h => (by decide : (1 : Fin 3) ≠ 2) (hsite e h)

theorem qmaForksBase_matrix {n r : ℕ} (left right : ν → Fin n) (weight : ν → ℝ)
    (constant : ℝ) (site : Fin r → Fin 3 → Fin n) (J K : Fin r → ℝ) :
    qmaExchangeMatrix (qmaForksBaseLeft left site) (qmaForksBaseRight right site)
      (qmaForksBaseWeight weight J K) (constant+∑ e, qmaForkOffset (J e) (K e)) =
      qmaExchangeMatrix left right weight constant +
        ∑ e, qmaForkCorrection (site e) (J e) (K e) := by
  simp only [qmaExchangeMatrix,Fintype.sum_sum_type,qmaForksBaseLeft,qmaForksBaseRight,
    qmaForksBaseWeight,Sum.elim_inl,Sum.elim_inr,qmaForkCorrection,qmaForkOffset,
    Complex.ofReal_add,Complex.ofReal_sum,add_smul,Finset.sum_add_distrib,Finset.sum_smul]
  abel

theorem qmaForksGraph_matrix {n r : ℕ} (left right : ν → Fin n)
    (hneq : ∀ a, left a ≠ right a) (weight : ν → ℝ) (constant R : ℝ)
    (site : Fin r → Fin 3 → Fin n) (hsite : ∀ e, Function.Injective (site e)) (J K : Fin r → ℝ) :
    (qmaForksGraph left right weight constant R site J K).submatrix
      (basisEquiv n r) (basisEquiv n r) =
      qmaPhysicalParallelHamiltonian n r (R^2)
        (qmaExchangeMatrix left right weight constant+∑ e, qmaForkCorrection (site e) (J e) (K e))
        site (fun _ => qmaForkMember) (fun e => qmaForkAmplitude R (J e) (K e)) := by
  unfold qmaForksGraph
  simpa only [qmaForksBase_matrix] using
    qmaParallelGraph_matrix _ _ (qmaForksBase_distinct left right hneq site hsite)
      (qmaForksBaseWeight weight J K) (constant+∑ e, qmaForkOffset (J e) (K e)) (R^2)
      site (fun _ => qmaForkMember) (fun e => qmaForkAmplitude R (J e) (K e))

theorem qmaForksGraph_accuracy {n r : ℕ} (left right : ν → Fin n)
    (hneq : ∀ a, left a ≠ right a) (weight : ν → ℝ) (constant : ℝ)
    (site : Fin r → Fin 3 → Fin n) (hsite : ∀ e, Function.Injective (site e))
    (J K : Fin r → ℝ) {N : ℝ} (hN : 0 < N) :
    let B := 3*(∑ a, |weight a|)+|constant|
    let A := 3*∑ e, (1+2*|J e|+2*|K e|)
    let D := B+12*∑ e, (1+|J e|+|K e|)^2
    let R := qmaRoutingScale A D N
    |sourceMatrixBottom (n+r*2) (qmaForksGraph left right weight constant R site J K) -
      sourceMatrixBottom n (qmaExchangeMatrix left right weight constant + ∑ e,
        ((J e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 1) +
          (K e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 2)))| ≤ 1/N := by
  dsimp only
  rw [sourceMatrixBottom_eq_mediator n r,qmaForksGraph_matrix left right hneq weight constant _ site hsite,
    qmaPhysicalParallel_bottom]
  have hC : (qmaExchangeMatrix left right weight constant).conjTranspose =
      qmaExchangeMatrix left right weight constant := by
    simp only [qmaExchangeMatrix,Matrix.conjTranspose_add,Matrix.conjTranspose_sum,
      Matrix.conjTranspose_smul,sourceHeisenbergMatrix_star n _ _ (hneq _),
      Complex.star_def,Complex.conj_ofReal,Matrix.conjTranspose_one]
  exact qmaForks_accuracy site hsite J K (by positivity) hN _ hC
    (qmaExchangeMatrix_lift_norm left right hneq weight constant)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkInitialMatrix
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The private-port initial state is the physical odd-subdivision Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix MediatorGraph
open scoped BigOperators Classical

theorem qmaOriginalSite_injective {n m : ℕ} (left right : Fin m → Fin n)
    (hneq : ∀ e, left e ≠ right e) (e : Fin m) : Function.Injective (qmaOriginalSite left right e) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [qmaOriginalSite] at h ⊢
  · exact (hneq e h).elim
  · exact (hneq e h.symm).elim

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRationalDegreeReduction
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full degree-three reduction has exact rational output coefficients. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaRationalInitialScale_cast {m : ℕ} (J : Fin m → ℚ) (constant N : ℚ) :
    (qmaRationalInitialScale J constant N:ℝ) =
      qmaRoutingScale (3*∑ e, (1+2*|(J e:ℝ)|))
        (|(constant:ℝ)|+4*∑ e, (1+|(J e:ℝ)|)^2) N := by
  simp [qmaRationalInitialScale,qmaRoutingScale]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRawCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial raw four-spin compiler with its full-space spectral guarantee. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawExchange
open QuantumAxisSample MediatorListProgram
open Matrix
open scoped BigOperators Classical

theorem rawBondMatrix_erase {n : ℕ} (b : TypedBond n) :
    rawBondMatrix n (erase b) = typedBondMatrix b := by
  simp only [rawBondMatrix,erase,b.1.isLt,b.2.1.isLt,↓reduceDIte,typedBondMatrix]

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListMatrix
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_old _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_fresh _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_old _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.ContinuumCoulomb.qmaSubdivisionCell_fresh _root_.OAI.ContinuumCoulomb.qmaSubdivisionCell_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The four literal bonds emitted for one port pair are exactly its
correction, singlet penalty and two outer couplings in the fork Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorGraph QuantumRawExchange QuantumAxisSample

theorem pairBonds_eq (n r : ℕ) (e : Fin r) (a b : Fin n) (J K R : ℚ) :
    pairBonds n e.val R ((a.val,J),(b.val,K))=
      (typedPairBonds n r e a b J K R).map erase := by
  simp [pairBonds,typedPairBonds,erase,MediatorIteration.old_val,
    MediatorIteration.fresh_val]

theorem pairBonds_matrix (n r : ℕ) (e : Fin r) (a b : Fin n) (J K R : ℚ) :
    ((pairBonds n e.val R ((a.val,J),(b.val,K))).map (rawBondMatrix (n+r*2))).sum =
      ((2*J*K:ℚ):ℂ) • sourceHeisenbergMatrix (n+r*2) (old n r a) (old n r b) +
      (((R^2:ℚ):ℂ) • sourceHeisenbergMatrix (n+r*2) (fresh n r e 0) (fresh n r e 1) +
      (((2*R*J:ℚ):ℂ) • sourceHeisenbergMatrix (n+r*2) (old n r a) (fresh n r e 1) +
      ((2*R*K:ℚ):ℂ) • sourceHeisenbergMatrix (n+r*2) (old n r b) (fresh n r e 1))) := by
  rw [pairBonds_eq,List.map_map]
  simp only [Function.comp_def,rawBondMatrix_erase,typedPairBonds,List.map_cons,
    List.map_nil,List.sum_cons,List.sum_nil,typedBondMatrix,add_zero]

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListPartition
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Adjacent pairing partitions the actual port lists without reordering or
dropping the odd final port. These identities connect the list compiler to the
full active-star Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList

theorem pairs_cons_cons (a b : Port) (ps : List Port) :
    pairs (a::b::ps) = (a,b)::pairs ps := by
  have hl : (a::b::ps).length/2=ps.length/2+1 := by simp only [List.length_cons]; omega
  unfold pairs
  rw [hl,List.range_succ_eq_map,List.map_cons,List.map_map]
  congr 1

theorem unpaired_cons_cons (a b : Port) (ps : List Port) :
    unpaired (a::b::ps)=unpaired ps := by
  have hl : (a::b::ps).length/2=ps.length/2+1 := by simp only [List.length_cons]; omega
  unfold unpaired
  rw [hl]
  have he : 2*(ps.length/2+1)=2*(ps.length/2)+2 := by omega
  rw [he]
  rfl

theorem pairs_partition (ps : List Port) :
    (pairs ps).flatMap (fun p => [p.1,p.2]) ++ unpaired ps=ps := by
  induction ps using List.twoStepInduction with
  | nil => rfl
  | singleton a => simp [pairs,unpaired]
  | cons_cons a b ps ih _ =>
    rw [pairs_cons_cons,unpaired_cons_cons]
    simpa only [List.flatMap_cons,List.append_assoc,List.cons_append,List.nil_append] using
      congrArg (fun xs => a::b::xs) ih

theorem paired_sum {M : Type*} [AddCommMonoid M] (f : Port → M) (ps : List Port) :
    (ps.map f).sum = ((pairs ps).map (fun p => f p.1+f p.2)).sum +
      ((unpaired ps).map f).sum := by
  conv_lhs => rw [← pairs_partition ps]
  simp only [List.map_append,List.sum_append,List.flatMap_def,List.map_flatten,
    List.sum_flatten,List.map_map,Function.comp_def,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero]

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListActive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact active-star matrices of the ordered compiler state. The pairing
identity applies to every matrix entry, including the retained odd port. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram QuantumRawExchange

theorem catalog_sum {M : Type*} [AddCommMonoid M] (gs : Groups) (f : TaggedPair → M) :
    ((catalog gs).map f).sum =
      ((List.range gs.length).map (fun i =>
        ((pairs (groupAt gs i)).map (fun p => f (i,p))).sum)).sum := by
  simp only [catalog,List.map_flatten,List.sum_flatten,List.map_map,Function.comp_def]

theorem active_pairing {M : Type*} [AddCommMonoid M] (gs : Groups) (f : Bond → M) :
    ((activeBonds gs).map f).sum =
      ((pairedBonds gs).map f).sum+((unpairedBonds gs).map f).sum := by
  have hp : ((List.range gs.length).map (fun i =>
      ((groupAt gs i).map (fun p => f (i,p.1,p.2))).sum)) =
      (List.range gs.length).map (fun i =>
        ((pairs (groupAt gs i)).map (fun p => f (i,p.1.1,p.1.2)+f (i,p.2.1,p.2.2))).sum+
        ((unpaired (groupAt gs i)).map (fun p => f (i,p.1,p.2))).sum) := by
    apply List.map_congr_left
    intro i _
    exact paired_sum (fun p => f (i,p.1,p.2)) (groupAt gs i)
  simp only [activeBonds,starBonds,List.map_flatten,List.sum_flatten,List.map_map,
    Function.comp_def]
  rw [hp,List.sum_map_add]
  congr 1
  · symm
    simp only [pairedBonds,List.flatMap_def,List.map_flatten,List.sum_flatten,
      List.map_map,Function.comp_def,List.map_cons,List.map_nil,List.sum_cons,
      List.sum_nil,add_zero]
    exact catalog_sum gs (fun p => f (p.1,p.2.1.1,p.2.1.2)+f (p.1,p.2.2.1,p.2.2.2))
  · simp only [unpairedBonds,starBonds,List.map_flatten,List.sum_flatten,List.map_map,
      Function.comp_def]

theorem matrix_pairing (s : State) : matrix s =
    rawMatrix s.1 (s.2.1++unpairedBonds s.2.2.2,s.2.2.1)+
      ((pairedBonds s.2.2.2).map (rawBondMatrix s.1)).sum := by
  simp only [matrix,rawMatrix,List.map_append,List.sum_append,
    active_pairing s.2.2.2 (rawBondMatrix s.1)]
  abel

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListBackground
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained part of a literal fork state has exactly the coefficient
budget and finite exchange matrix used by the parallel-fork estimate. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram QuantumRawExchange
open scoped BigOperators Classical

theorem background_weights (s : State) : (background s).map (fun b => b.2.2)=retained s := by
  simp only [background,retained,List.map_append]
  congr 1
  simp only [unpairedBonds,starBonds,List.map_flatten,List.map_map,Function.comp_def]
  have h := ExactQuantumFactoring.BitStackProgram.map_range_getD s.2.2.2 []
    (fun ps => (unpaired ps).map Prod.snd)
  simpa only [groupAt,List.map_flatten,List.map_map,Function.comp_def] using
    congrArg List.flatten h

theorem rawBondMatrix_eq_bondMatrix (n : ℕ) (b : Bond) :
    rawBondMatrix n b=SourceBondLists.bondMatrix n b := by
  by_cases hi : b.1<n <;> by_cases hj : b.2.1<n <;>
    simp [rawBondMatrix,SourceBondLists.bondMatrix,hi,hj]

theorem rawMatrix_eq_matrix (n : ℕ) (bs : List Bond) (c : ℚ) :
    rawMatrix n (bs,c)=SourceBondLists.matrix n bs+(c:ℂ) • 1 := by
  have h : rawBondMatrix n=SourceBondLists.bondMatrix n :=
    funext (rawBondMatrix_eq_bondMatrix n)
  simp only [rawMatrix,h,SourceBondLists.matrix,Rat.cast_smul_eq_qsmul]

theorem background_matrix (s : State) (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) :
    qmaExchangeMatrix (backgroundGraph s hb hn).left (backgroundGraph s hb hn).right
      (fun e => ((backgroundGraph s hb hn).weight e:ℝ)) s.2.2.1 =
      rawMatrix s.1 (background s,s.2.2.1) := by
  rw [rawMatrix_eq_matrix]
  exact QuantumListGraph.ofBonds_matrix s.1 (background s) s.2.2.1 hb hn

theorem background_sum (s : State) (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) (f : ℚ → ℚ) :
    (∑ e, f ((backgroundGraph s hb hn).weight e))=((retained s).map f).sum := by
  change (∑ e : Fin (background s).length, f ((background s).get e).2.2)=_
  rw [← List.sum_ofFn]
  have hl := List.ofFn_getElem_eq_map (background s) (fun b => f b.2.2)
  simp only [List.get_eq_getElem] at hl ⊢
  rw [hl]
  simpa only [List.map_map,Function.comp_def] using
    congrArg (fun xs => (xs.map f).sum) (background_weights s)

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListGraph
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_old _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_fresh _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_old _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.ContinuumCoulomb.qmaSubdivisionCell_fresh _root_.OAI.ContinuumCoulomb.qmaSubdivisionCell_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite bond packet emitted for parallel forks has the exact full-space
Hamiltonian used in the calibrated perturbation estimate. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorGraph QuantumRawExchange QuantumAxisSample
open scoped BigOperators Classical

theorem packetBonds_matrix {n r : ℕ} (e : Fin r) (site : Fin 3 → Fin n) (J K R : ℚ) :
    ((packetBonds e site J K R).map (rawBondMatrix (n+r*2))).sum =
      ((2*J*K:ℚ):ℂ) • sourceHeisenbergMatrix (n+r*2) (old n r (site 1)) (old n r (site 2)) +
      (((R^2:ℚ):ℂ) • sourceHeisenbergMatrix (n+r*2) (fresh n r e 0) (fresh n r e 1) +
      (((2*R*J:ℚ):ℂ) • sourceHeisenbergMatrix (n+r*2) (old n r (site 1)) (fresh n r e 1) +
      ((2*R*K:ℚ):ℂ) • sourceHeisenbergMatrix (n+r*2) (old n r (site 2)) (fresh n r e 1))) +
      (R:ℂ) • sourceHeisenbergMatrix (n+r*2) (old n r (site 0)) (fresh n r e 0) := by
  have h : ((site 0).val,n+2*e.val,R) =
      erase (old n r (site 0),fresh n r e 0,R) := by
    simp [erase,MediatorIteration.old_val,MediatorIteration.fresh_val]
  simp only [packetBonds,List.map_append,List.sum_append,pairBonds_matrix,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,h,
    rawBondMatrix_erase,typedBondMatrix]

theorem graph_matrix {n r m : ℕ} (left right : Fin m → Fin n) (w : Fin m → ℚ)
    (site : Fin r → Fin 3 → Fin n) (J K : Fin r → ℚ) (c R : ℚ) :
    rawMatrix (n+r*2) (graphBonds left right w site J K R,graphConstant c R J K) =
      qmaForksGraph left right (fun a => (w a:ℝ)) (c:ℝ) (R:ℝ) site
        (fun e => (J e:ℝ)) (fun e => (K e:ℝ)) := by
  simp only [rawMatrix,← Rat.cast_smul_eq_qsmul ℂ,graphBonds,List.map_append,List.sum_append,List.map_ofFn,
    List.sum_ofFn,List.map_flatten,List.sum_flatten,Function.comp_def,
    rawBondMatrix_erase,typedBondMatrix,packetBonds_matrix]
  simp only [qmaForksGraph,qmaExchangeMatrix,Fintype.sum_sum_type,Fintype.sum_prod_type,
    Fin.sum_univ_three,qmaParallelGraphLeft,qmaParallelGraphRight,
    qmaParallelGraphWeight,qmaForksBaseLeft,qmaForksBaseRight,qmaForksBaseWeight,
    Sum.elim_inl,Sum.elim_inr,qmaForkAmplitude,qmaForkMember,qmaForkOffset,
    graphConstant]
  push_cast
  simp only [Finset.sum_add_distrib]
  abel

theorem graphScale_cast {r m : ℕ} (w : Fin m → ℚ) (J K : Fin r → ℚ) (c N : ℚ) :
    (graphScale w J K c N : ℝ) =
      qmaRoutingScale (3*∑ e, (1+2*|(J e:ℝ)|+2*|(K e:ℝ)|))
        (3*(∑ a, |(w a:ℝ)|)+|(c:ℝ)|+
          12*∑ e, (1+|(J e:ℝ)|+|(K e:ℝ)|)^2) (N:ℝ) := by
  unfold graphScale qmaRoutingScale
  push_cast
  rfl

theorem graph_accuracy {n r m : ℕ} (left right : Fin m → Fin n)
    (hneq : ∀ a, left a ≠ right a) (w : Fin m → ℚ)
    (site : Fin r → Fin 3 → Fin n) (hsite : ∀ e, Function.Injective (site e))
    (J K : Fin r → ℚ) (c N : ℚ) (hN : 0 < N) :
    let R := graphScale w J K c N
    |sourceMatrixBottom (n+r*2)
        (rawMatrix (n+r*2) (graphBonds left right w site J K R,graphConstant c R J K)) -
      sourceMatrixBottom n (qmaExchangeMatrix left right (fun a => (w a:ℝ)) (c:ℝ) +
        ∑ e, ((J e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 1) +
          (K e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 2)))| ≤ 1/(N:ℝ) := by
  dsimp only
  rw [graph_matrix,graphScale_cast]
  have hJ : ∀ e, ((J e:ℝ):ℂ)=(J e:ℂ) := by intro e; norm_cast
  have hK : ∀ e, ((K e:ℝ):ℂ)=(K e:ℂ) := by intro e; norm_cast
  have h := qmaForksGraph_accuracy left right hneq (fun a => (w a:ℝ)) (c:ℝ)
    site hsite (fun e => (J e:ℝ)) (fun e => (K e:ℝ)) (show (0:ℝ) < N by exact_mod_cast hN)
  dsimp only at h
  simpa only [hJ,hK] using h

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reindexing the actual fresh-port list by its consecutive mediator number. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped BigOperators Classical

theorem fresh_sum {M : Type*} [AddCommMonoid M] (gs : Groups) (f : ℕ → ℕ → M) :
    ((List.range gs.length).map (fun i =>
      ((List.range ((groupAt gs i).length/2)).map (fun j =>
        f i (pairStart gs i+j))).sum)).sum =
      ∑ e : Fin (pairCount gs),
        f (((catalog gs).drop e.val).headD (0,((0,0),(0,0)))).1 e.val := by
  simp only [range_sum]
  have h := (pairEquiv gs).sum_comp (fun e =>
    f (((catalog gs).drop e.val).headD (0,((0,0),(0,0)))).1 e.val)
  simp only [catalog_pairEquiv] at h
  simpa only [LocalPair,Fintype.sum_sigma,pairEquiv_val] using h

theorem next_active_sum {M : Type*} [AddCommMonoid M] (n : ℕ) (R : ℚ)
    (gs : Groups) (f : Bond → M) :
    ((activeBonds ((List.range gs.length).map (nextGroup n R gs))).map f).sum =
      ((List.range (pairCount gs)).map (fun e =>
        f ((((catalog gs).drop e).headD (0,((0,0),(0,0)))).1,n+2*e,R))).sum+
      ((unpairedBonds gs).map f).sum := by
  have h : ((List.range gs.length).map (fun i =>
      ((groupAt ((List.range gs.length).map (nextGroup n R gs)) i).map
        (fun p => f (i,p.1,p.2))).sum)) =
      (List.range gs.length).map (fun i =>
        ((List.range ((groupAt gs i).length/2)).map (fun j =>
          f (i,n+2*(pairStart gs i+j),R))).sum+
        ((unpaired (groupAt gs i)).map (fun p => f (i,p.1,p.2))).sum) := by
    apply List.map_congr_left
    intro i hi
    rw [next_groupAt n R gs i (List.mem_range.mp hi)]
    simp only [nextGroup,List.map_append,List.sum_append,List.map_map,Function.comp_def]
  simp only [activeBonds,starBonds,List.map_flatten,List.sum_flatten,List.map_map,
    Function.comp_def,List.length_map,List.length_range]
  rw [h,List.sum_map_add]
  congr 1
  · simpa only [range_sum] using fresh_sum gs (fun i e => f (i,n+2*e,R))
  · simp only [unpairedBonds,starBonds,List.map_flatten,List.sum_flatten,List.map_map,
      Function.comp_def]

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal rational scale is exactly the scale appearing in the checked
parallel-fork theorem, including all retained odd-port coefficients. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open scoped BigOperators Classical

theorem catalog_weights_sum (gs : Groups) (f : ℚ → ℚ → ℚ) :
    (((catalog gs).map Prod.snd).map (fun p => f p.1.2 p.2.2)).sum =
      ∑ e : Fin (pairCount gs), f (actualJ gs e) (actualK gs e) := by
  rw [List.map_map]
  change ((catalog gs).map (fun p => f p.2.1.2 p.2.2.2)).sum=_
  rw [← ExactQuantumFactoring.BitStackProgram.map_range_getD (catalog gs)
    (0,((0,0),(0,0))) (fun p => f p.2.1.2 p.2.2.2),catalog_length,range_sum]
  apply Finset.sum_congr rfl
  intro e _
  have hc := catalog_pairEquiv gs (localPair gs e)
  rw [show pairEquiv gs (localPair gs e)=e from (pairEquiv gs).apply_symm_apply e] at hc
  rw [hc]
  rfl

theorem scale_eq_graphScale (s : State)
    (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) (N : ℚ) :
    scale N s = graphScale (backgroundGraph s hb hn).weight
      (actualJ s.2.2.2) (actualK s.2.2.2) s.2.2.1 N := by
  have hL : (((catalog s.2.2.2).map Prod.snd).map pairLinear).sum =
      ∑ e, (1+2*|actualJ s.2.2.2 e|+2*|actualK s.2.2.2 e|) :=
    catalog_weights_sum s.2.2.2 (fun J K => 1+2*|J|+2*|K|)
  have hS : (((catalog s.2.2.2).map Prod.snd).map pairSquare).sum =
      ∑ e, (1+|actualJ s.2.2.2 e|+|actualK s.2.2.2 e|)^2 :=
    catalog_weights_sum s.2.2.2 (fun J K => (1+|J|+|K|)^2)
  have hw : (∑ e : Fin (background s).length, |((background s).get e).2.2|) =
      ((retained s).map abs).sum := background_sum s hb hn abs
  change scale N s = graphScale (fun e : Fin (background s).length => ((background s).get e).2.2)
    (actualJ s.2.2.2) (actualK s.2.2.2) s.2.2.1 N
  dsimp only [scale,graphScale]
  rw [hL,hS,hw]

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete literal round is the retained matrix plus the calibrated
five-bond packets, including the newly active center-to-mediator edges. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram QuantumRawExchange

theorem packets_sum {M : Type*} [AddCommMonoid M] (s : State) (R : ℚ) (f : Bond → M) :
    ((packets s R).map f).sum =
      ((addedBonds s R).map f).sum+((freshBonds s R).map f).sum := by
  simp only [packets,addedBonds,freshBonds,List.map_flatten,List.sum_flatten,List.map_map,
    Function.comp_def,List.map_append,List.sum_append,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,catalog_length,List.sum_map_add]

theorem next_matrix_packets (N : ℚ) (s : State) :
    matrix (next N s) =
      rawMatrix (s.1+2*pairCount s.2.2.2)
        (background s++packets s (scale N s),(next N s).2.2.1) := by
  dsimp only [matrix,next]
  simp only [rawMatrix,List.map_append,List.sum_append,
    next_active_sum,background,packets_sum,freshBonds,List.map_map,Function.comp_def]
  abel

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListRealization
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact correspondence between the emitted ordered state and the finite
parallel-fork Hamiltonian. The mediator numbering is the proved prefix index. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorGraph QuantumAxisSample QuantumRawExchange
open scoped BigOperators Classical

theorem retained_graph_list (s : State)
    (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) :
    List.ofFn (fun a => erase
      (old s.1 (pairCount s.2.2.2) ((backgroundGraph s hb hn).left a),
       old s.1 (pairCount s.2.2.2) ((backgroundGraph s hb hn).right a),
       (backgroundGraph s hb hn).weight a)) = background s := by
  simpa only [backgroundGraph,QuantumListGraph.ofBonds,SourceBondLists.bonds,
    erase,MediatorIteration.old_val] using List.ofFn_get (background s)

theorem packet_graph_list (s : State) (hs : ValidPorts s.1 s.2.2.2) (R : ℚ) :
    (List.ofFn (fun e => packetBonds e (actualSite hs e)
      (actualJ s.2.2.2 e) (actualK s.2.2.2 e) R)).flatten=packets s R := by
  unfold packets
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hi' : i < pairCount s.2.2.2 := by simpa only [List.length_ofFn] using hi
    simp only [List.getElem_ofFn,List.getElem_map,List.getElem_range]
    rw [catalog_actualSite hs ⟨i,hi'⟩]
    rfl

theorem graph_bonds_eq (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) (R : ℚ) :
    graphBonds (backgroundGraph s hb hn).left (backgroundGraph s hb hn).right
      (backgroundGraph s hb hn).weight (actualSite hs) (actualJ s.2.2.2)
      (actualK s.2.2.2) R = background s++packets s R := by
  unfold graphBonds
  exact congrArg₂ List.append (retained_graph_list s hb hn) (packet_graph_list s hs R)

theorem next_constant (s : State) (N : ℚ) :
    (next N s).2.2.1 = graphConstant s.2.2.1 (scale N s)
      (actualJ s.2.2.2) (actualK s.2.2.2) := by
  have h : (((catalog s.2.2.2).map Prod.snd).map pairOffset).sum =
      ∑ e, (3/4+3*(actualJ s.2.2.2 e)^2+3*(actualK s.2.2.2 e)^2) :=
    catalog_weights_sum s.2.2.2 (fun J K => 3/4+3*J^2+3*K^2)
  dsimp only [next,graphConstant]
  rw [h]

theorem next_bottom_graph (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) (N : ℚ) :
    normalizedBottom (matrix (next N s)) =
      normalizedBottom (qmaForksGraph (backgroundGraph s hb hn).left (backgroundGraph s hb hn).right
        (fun e => ((backgroundGraph s hb hn).weight e:ℝ)) (s.2.2.1:ℝ) (scale N s:ℝ)
        (actualSite hs) (fun e => (actualJ s.2.2.2 e:ℝ)) (fun e => (actualK s.2.2.2 e:ℝ))) := by
  rw [next_matrix_packets,next_constant]
  change rawBottom (s.1+2*pairCount s.2.2.2)
    (background s++packets s (scale N s),
      graphConstant s.2.2.1 (scale N s) (actualJ s.2.2.2) (actualK s.2.2.2)) = _
  rw [show s.1+2*pairCount s.2.2.2=s.1+pairCount s.2.2.2*2 by omega]
  unfold rawBottom
  rw [← graph_bonds_eq s hs hb hn]
  exact congrArg normalizedBottom (graph_matrix _ _ _ _ _ _ _ _)

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListAccuracy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full-space error for one actual literal fork round. Both sides are the
matrices defined by the emitted bond/port lists, with their scalar offsets. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorGraph QuantumRawExchange QuantumAxisSample
open scoped BigOperators Classical

theorem catalog_index_sum {M : Type} [AddCommMonoid M] (gs : Groups)
    (f : TaggedPair → M) : ((catalog gs).map f).sum =
      ∑ e : Fin (pairCount gs), f (((catalog gs).drop e.val).headD (0,((0,0),(0,0)))) := by
  rw [← ExactQuantumFactoring.BitStackProgram.map_range_getD (catalog gs)
    (0,((0,0),(0,0))) f,catalog_length,range_sum]

theorem rawBondMatrix_fin {n : ℕ} (a b : Fin n) (J : ℚ) :
    rawBondMatrix n (a.val,b.val,J)=(J:ℂ) • sourceHeisenbergMatrix n a b :=
  rawBondMatrix_erase (a,b,J)

theorem paired_matrix {n : ℕ} {gs : Groups} (hs : ValidPorts n gs) :
    ((pairedBonds gs).map (rawBondMatrix n)).sum =
      ∑ e : Fin (pairCount gs),
        ((actualJ gs e:ℂ) • sourceHeisenbergMatrix n (actualSite hs e 0) (actualSite hs e 1) +
         (actualK gs e:ℂ) • sourceHeisenbergMatrix n (actualSite hs e 0) (actualSite hs e 2)) := by
  simp only [pairedBonds,List.flatMap_def,List.map_flatten,List.sum_flatten,List.map_map,
    Function.comp_def,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  rw [catalog_index_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [catalog_actualSite hs e]
  simp only [rawBondMatrix_fin]

theorem input_matrix_graph (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) :
    matrix s = qmaExchangeMatrix (n := s.1) (backgroundGraph s hb hn).left (backgroundGraph s hb hn).right
      (fun e => ((backgroundGraph s hb hn).weight e:ℝ)) (s.2.2.1:ℝ) +
      ∑ e : Fin (pairCount s.2.2.2),
        ((actualJ s.2.2.2 e:ℂ) • sourceHeisenbergMatrix s.1 (actualSite hs e 0) (actualSite hs e 1) +
         (actualK s.2.2.2 e:ℂ) • sourceHeisenbergMatrix s.1 (actualSite hs e 0) (actualSite hs e 2)) := by
  have h := matrix_pairing s
  change matrix s=rawMatrix s.1 (background s,s.2.2.1)+_ at h
  rw [← background_matrix s hb hn,paired_matrix hs] at h
  exact h

theorem next_accuracy (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) (N : ℚ) (hN : 0 < N) :
    |normalizedBottom (matrix (next N s))-normalizedBottom (matrix s)| ≤ 1/(N:ℝ) := by
  let left : Fin (background s).length → Fin s.1 := (backgroundGraph s hb hn).left
  let right : Fin (background s).length → Fin s.1 := (backgroundGraph s hb hn).right
  let w : Fin (background s).length → ℚ := (backgroundGraph s hb hn).weight
  have hneq : ∀ a, left a ≠ right a := (backgroundGraph s hb hn).distinct
  have h := graph_accuracy left right hneq w
    (actualSite hs) (actualSite_injective hs) (actualJ s.2.2.2) (actualK s.2.2.2) s.2.2.1 N hN
  dsimp only at h
  have hscale : graphScale w (actualJ s.2.2.2) (actualK s.2.2.2) s.2.2.1 N=scale N s :=
    (scale_eq_graphScale s hb hn N).symm
  rw [graph_matrix,hscale] at h
  change |normalizedBottom _-normalizedBottom _| ≤ 1/(N:ℝ) at h
  have hout : normalizedBottom (matrix (next N s)) =
      normalizedBottom (qmaForksGraph left right (fun e => (w e:ℝ)) (s.2.2.1:ℝ)
        (scale N s:ℝ) (actualSite hs) (fun e => (actualJ s.2.2.2 e:ℝ))
          (fun e => (actualK s.2.2.2 e:ℝ))) := next_bottom_graph s hs hb hn N
  have hin : matrix s = qmaExchangeMatrix left right (fun e => (w e:ℝ)) (s.2.2.1:ℝ)+
      ∑ e, ((actualJ s.2.2.2 e:ℂ) • sourceHeisenbergMatrix s.1 (actualSite hs e 0) (actualSite hs e 1)+
        (actualK s.2.2.2 e:ℂ) • sourceHeisenbergMatrix s.1 (actualSite hs e 0) (actualSite hs e 2)) :=
    input_matrix_graph s hs hb hn
  rw [← hout,← hin] at h
  exact h

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListNextBackground
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded, loop-free ordinary bonds survive the actual list transformation.
Together with port separation this supplies every hypothesis of the next
full-space fork comparison. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram

theorem unpairedBonds_valid {n : ℕ} {gs : Groups} (h : ValidPorts n gs)
    (b : Bond) (hb : b ∈ unpairedBonds gs) : b.1 < n ∧ b.2.1 < n ∧ b.1 ≠ b.2.1 := by
  obtain ⟨bs,hbs,hb⟩ := List.mem_flatten.mp hb
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hbs
  have hi' := List.mem_range.mp hi
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hb
  have hp' : p ∈ groupAt gs i := List.mem_of_mem_drop hp
  obtain ⟨j,hj,hp⟩ := List.getElem_of_mem hp'
  have he : portAt (groupAt gs i) j=p := (portAt_eq_getElem _ _ hj).trans hp
  have hbound := h.bounded ⟨i,hi'⟩ ⟨j,hj⟩
  have hne := h.disjoint ⟨i,hi'⟩ ⟨i,hi'⟩ ⟨j,hj⟩
  rw [he] at hbound hne
  exact ⟨lt_of_lt_of_le hi' h.centers,hbound,hne⟩

theorem next_background_valid (s : State) (h : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) (N : ℚ) :
    SourceBondLists.bounded (next N s).1 (background (next N s)) ∧
      ∀ b ∈ background (next N s), b.1 ≠ b.2.1 := by
  have hv : ∀ b ∈ background (next N s),
      b.1 < (next N s).1 ∧ b.2.1 < (next N s).1 ∧ b.1 ≠ b.2.1 := by
    intro b hmem
    change b ∈ (s.2.1++addedBonds s (scale N s))++unpairedBonds (next N s).2.2.2 at hmem
    rcases List.mem_append.mp hmem with hold | hport
    · rcases List.mem_append.mp hold with hold | hnew
      · have hm : b ∈ background s := List.mem_append_left _ hold
        have hbb := hb b hm
        have hnn := hn b hm
        rw [next_count]
        exact ⟨lt_of_lt_of_le hbb.1 (Nat.le_add_right _ _),
          lt_of_lt_of_le hbb.2 (Nat.le_add_right _ _),hnn⟩
      · exact addedBonds_valid s h (scale N s) b hnew
    · exact unpairedBonds_valid (next_validPorts N s h) b hport
  exact ⟨fun b hm => ⟨(hv b hm).1,(hv b hm).2.1⟩,fun b hm => (hv b hm).2.2⟩

theorem iterate_background_valid (s : State) (h : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) (N : ℚ) (k : ℕ) :
    SourceBondLists.bounded (iterate N k s).1 (background (iterate N k s)) ∧
      ∀ b ∈ background (iterate N k s), b.1 ≠ b.2.1 := by
  induction k with
  | zero => exact ⟨hb,hn⟩
  | succ k ih =>
    exact next_background_valid _ (iterate_validPorts N s h k) ih.1 ih.2 N

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full-space accuracy of the repeated literal fork compiler. All port and
ordinary-bond hypotheses are propagated from its actual input lists. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorGraph QuantumAxisSample
open scoped Classical

theorem iterate_accuracy (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) (N : ℚ) (hN : 0 < N) (k : ℕ) :
    |normalizedBottom (matrix (iterate N k s))-normalizedBottom (matrix s)| ≤
      (k:ℝ)/(N:ℝ) := by
  induction k with
  | zero =>
    rw [iterate]
    rw [sub_self,abs_zero,Nat.cast_zero,zero_div]
  | succ k ih =>
    have hv := iterate_background_valid s hs hb hn N k
    have he := next_accuracy (iterate N k s) (iterate_validPorts N s hs k)
      hv.1 hv.2 N hN
    calc
      _ ≤ |normalizedBottom (matrix (next N (iterate N k s)))-
          normalizedBottom (matrix (iterate N k s))|+
          |normalizedBottom (matrix (iterate N k s))-normalizedBottom (matrix s)| :=
        abs_sub_le _ _ _
      _ ≤ 1/(N:ℝ)+(k:ℝ)/(N:ℝ) := add_le_add he ih
      _ = ((k+1:ℕ):ℝ)/(N:ℝ) := by push_cast; ring

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal odd subdivision satisfies all hypotheses needed to iterate
the full-space fork estimate. Its fresh singlets have distinct endpoints. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram

theorem initial_background_valid (n : ℕ) (bs : List Bond) (c N : ℚ) :
    SourceBondLists.bounded (initial n bs c N).1 (background (initial n bs c N)) ∧
      ∀ b ∈ background (initial n bs c N), b.1 ≠ b.2.1 := by
  have hv : ∀ b ∈ background (initial n bs c N),
      b.1 < (initial n bs c N).1 ∧ b.2.1 < (initial n bs c N).1 ∧ b.1 ≠ b.2.1 := by
    intro b hb
    rcases List.mem_append.mp hb with hs | hp
    · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hs
      have he' := List.mem_range.mp he
      dsimp only [initial]
      omega
    · exact unpairedBonds_valid (initial_validPorts n bs c N) b hp
  exact ⟨fun b hm => ⟨(hv b hm).1,(hv b hm).2.1⟩,fun b hm => (hv b hm).2.2⟩

theorem initial_iterate_accuracy (n : ℕ) (bs : List Bond) (c N : ℚ) (hN : 0 < N)
    (k : ℕ) :
    |MediatorGraph.normalizedBottom (matrix (iterate N k (initial n bs c N)))-
      MediatorGraph.normalizedBottom (matrix (initial n bs c N))| ≤ (k:ℝ)/(N:ℝ) := by
  have h := initial_background_valid n bs c N
  exact iterate_accuracy _ (initial_validPorts n bs c N) h.1 h.2 N hN k

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Regrouping the literal initial ports recovers the two physical end
couplings of each input edge. The regrouping uses its actual endpoint table. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped BigOperators Classical

theorem initialBond_mem (bs : List Bond) (j : ℕ) (hj : j < 2*bs.length) :
    initialBond bs j ∈ bs := by
  have hi : j/2 < bs.length := by omega
  simp only [initialBond,List.headD_eq_head?_getD,List.head?_drop,
    List.getElem?_eq_getElem hi,Option.getD_some]
  exact List.getElem_mem hi

theorem initialEndpoint_bound (n : ℕ) (bs : List Bond) (hb : SourceBondLists.bounded n bs)
    (j : ℕ) (hj : j < 2*bs.length) : initialEndpoint bs j < n := by
  have h := hb _ (initialBond_mem bs j hj)
  unfold initialEndpoint
  split
  · exact h.1
  · exact h.2

theorem initial_center_sum {M : Type*} [AddCommMonoid M] (n : ℕ) (bs : List Bond)
    (hb : SourceBondLists.bounded n bs) (j : Fin (2*bs.length)) (f : ℕ → ℕ → M) :
    (∑ i : Fin n, if initialEndpoint bs j.val=i.val then f i.val j.val else 0) =
      f (initialEndpoint bs j.val) j.val := by
  let e : Fin n := ⟨initialEndpoint bs j.val,initialEndpoint_bound n bs hb j.val j.isLt⟩
  rw [Finset.sum_eq_single e]
  · simp only [e,ite_true, if_true]
  · intro i _ hi
    exact ite_eq_right (fun h => hi (Fin.ext h.symm))
  · intro h
    exact (h (Finset.mem_univ e)).elim

theorem initial_group_sum {M : Type*} [AddCommMonoid M] (n : ℕ) (bs : List Bond)
    (hb : SourceBondLists.bounded n bs) (R : ℚ) (f : ℕ → Port → M) :
    ((List.range n).map (fun i => ((initialGroup n bs R i).map (f i)).sum)).sum =
      ((List.range (2*bs.length)).map (fun j =>
        f (initialEndpoint bs j) (n+j,initialWeight bs R j))).sum := by
  simp only [initialGroup,List.map_map,Function.comp_def,initialIndices_sum,range_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ =>
    initial_center_sum n bs hb j (fun i k => f i (n+k,initialWeight bs R k)))

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The even and odd entries in the initial endpoint table are precisely
the two couplings belonging to each physical singlet. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped BigOperators Classical

theorem initialWeight_even (bs : List Bond) (R : ℚ) (e : Fin bs.length) :
    initialWeight bs R (2*e.val)=R := by
  have hm : (2*e.val)%2=0 := by omega
  simp only [initialWeight,hm,ite_true, if_true]

theorem initialWeight_odd (bs : List Bond) (R : ℚ) (e : Fin bs.length) :
    initialWeight bs R (2*e.val+1)=2*R*bs[e.val].2.2 := by
  have hm : (2*e.val+1)%2≠0 := by omega
  simp only [initialWeight,hm,ite_false, if_false]
  simpa only [Fin.val_one] using
    congrArg (fun b : Bond => 2*R*b.2.2) (initialBond_pair bs e 1)

theorem initial_group_pair_sum {M : Type*} [AddCommMonoid M] (n : ℕ) (bs : List Bond)
    (hb : SourceBondLists.bounded n bs) (R : ℚ) (f : ℕ → Port → M) :
    ((List.range n).map (fun i => ((initialGroup n bs R i).map (f i)).sum)).sum =
      ∑ e : Fin bs.length,
        (f bs[e.val].1 (n+2*e.val,R)+
          f bs[e.val].2.1 (n+(2*e.val+1),2*R*bs[e.val].2.2)) := by
  rw [initial_group_sum n bs hb,initial_evenodd_sum]
  simp only [initialEndpoint_even,initialEndpoint_odd,initialWeight_even,initialWeight_odd]

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact matrix semantics of the emitted initial singlet/port lists. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram QuantumRawExchange
open scoped BigOperators Classical

theorem initial_active_sum {M : Type*} [AddCommMonoid M] (n : ℕ) (bs : List Bond)
    (hb : SourceBondLists.bounded n bs) (R : ℚ) (f : Bond → M) :
    ((activeBonds ((List.range n).map (initialGroup n bs R))).map f).sum =
      ∑ e : Fin bs.length,
        (f (bs[e.val].1,n+2*e.val,R)+
          f (bs[e.val].2.1,n+(2*e.val+1),2*R*bs[e.val].2.2)) := by
  have hg : (List.range n).map (fun i =>
      ((groupAt ((List.range n).map (initialGroup n bs R)) i).map
        (fun p => f (i,p.1,p.2))).sum) =
      (List.range n).map (fun i => ((initialGroup n bs R i).map
        (fun p => f (i,p.1,p.2))).sum) := by
    apply List.map_congr_left
    intro i hi
    rw [initial_groupAt n bs R i (List.mem_range.mp hi)]
  simp only [activeBonds,starBonds,List.map_flatten,List.sum_flatten,List.map_map,
    Function.comp_def,List.length_map,List.length_range]
  rw [hg]
  exact initial_group_pair_sum n bs hb R (fun i p => f (i,p.1,p.2))

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialPhysical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The initial emitted couplings are the simultaneous odd-path singlet
Hamiltonian used by the already proved full-space perturbation estimate. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorGraph QuantumRawExchange QuantumAxisSample
open scoped BigOperators Classical

theorem initialPhysical_matrix {n m : ℕ} (left right : Fin m → Fin n)
    (J : Fin m → ℚ) (c R : ℚ) :
    rawMatrix (n+m*2) (initialPhysicalBonds left right J R,initialConstant J c R) =
      qmaPathsGraph (fun a : Fin 0 => Fin.elim0 a) (fun a : Fin 0 => Fin.elim0 a)
        (fun _ => 0) (c:ℝ) (R:ℝ) (qmaOriginalSite left right) (fun _ => false)
          (fun e => (J e:ℝ)) := by
  simp only [rawMatrix,← Rat.cast_smul_eq_qsmul ℂ,initialPhysicalBonds,List.map_append,
    List.sum_append,List.map_ofFn,List.sum_ofFn,List.map_flatten,List.sum_flatten,
    Function.comp_def,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
    rawBondMatrix_erase,typedBondMatrix]
  simp only [qmaPathsGraph,qmaExchangeMatrix,Fintype.sum_sum_type,Fintype.sum_prod_type,
    Fin.sum_univ_two,qmaParallelGraphLeft,qmaParallelGraphRight,qmaParallelGraphWeight,
    qmaPathAmplitude,qmaPathMember,qmaOriginalSite,qmaPathOffset,
    Finset.univ_eq_empty,Finset.sum_empty,zero_add,
    initialConstant]
  push_cast
  simp only [Finset.sum_add_distrib]

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reordering the actual initial bond list gives exactly the typed physical
singlet Hamiltonian, including its scalar offset. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorGraph QuantumRawExchange QuantumAxisSample MediatorListProgram
open scoped BigOperators Classical

theorem initialPhysical_sum {M : Type*} [AddCommMonoid M] {n m : ℕ}
    (left right : Fin m → Fin n) (J : Fin m → ℚ) (R : ℚ) (f : Bond → M) :
    ((initialPhysicalBonds left right J R).map f).sum =
      (∑ e : Fin m, f (n+2*e.val,n+2*e.val+1,R^2))+
      ∑ e : Fin m,
        (f ((left e).val,n+2*e.val,R)+f ((right e).val,n+2*e.val+1,2*R*J e)) := by
  simp only [initialPhysicalBonds,List.map_append,List.sum_append,List.map_ofFn,
    List.sum_ofFn,List.map_flatten,List.sum_flatten,Function.comp_def,List.map_cons,
    List.map_nil,List.sum_cons,List.sum_nil,add_zero,erase,MediatorIteration.old_val,
    MediatorIteration.fresh_val,Fin.val_zero,Fin.val_one]

theorem initialSource_sum {M : Type*} [AddCommMonoid M] (n : ℕ) (bs : List Bond)
    (hb : SourceBondLists.bounded n bs) (R : ℚ) (f : Bond → M) :
    ((initialSourceBonds n bs R).map f).sum =
      ((initialPhysicalBonds (SourceBondLists.bonds n bs hb).left
        (SourceBondLists.bonds n bs hb).right (fun e => (bs.get e).2.2) R).map f).sum := by
  simp only [initialSourceBonds,List.map_append,List.sum_append,List.map_map,
    Function.comp_def,range_sum,initial_active_sum n bs hb,initialPhysical_sum,
    SourceBondLists.bonds,List.get_eq_getElem]
  congr 1

theorem initial_constant_eq (n : ℕ) (bs : List Bond) (c N : ℚ) :
    (initial n bs c N).2.2.1 =
      initialConstant (fun e : Fin bs.length => (bs.get e).2.2) c (initialScale N bs c) := by
  have hh : (bs.map (fun b => (3/4+3*b.2.2^2:ℚ))).sum =
      ∑ e : Fin bs.length, (3/4+3*(bs.get e).2.2^2) := by
    rw [← List.sum_ofFn]
    exact congrArg List.sum (List.ofFn_getElem_eq_map bs
      (fun b => (3/4+3*b.2.2^2:ℚ))).symm
  change c+(bs.map (fun b => (3/4+3*b.2.2^2:ℚ))).sum+
    3*(bs.length:ℚ)*(initialScale N bs c)^2 = _
  rw [hh]
  rfl

theorem initial_bottom_physical (n : ℕ) (bs : List Bond)
    (hb : SourceBondLists.bounded n bs) (c N : ℚ) :
    normalizedBottom (matrix (initial n bs c N)) =
      rawBottom (n+bs.length*2)
        (initialPhysicalBonds (SourceBondLists.bonds n bs hb).left
          (SourceBondLists.bonds n bs hb).right (fun e => (bs.get e).2.2) (initialScale N bs c),
        initialConstant (fun e : Fin bs.length => (bs.get e).2.2) c (initialScale N bs c)) := by
  have hh : rawMatrix (n+2*bs.length)
      (initialSourceBonds n bs (initialScale N bs c),(initial n bs c N).2.2.1) =
      rawMatrix (n+2*bs.length)
        (initialPhysicalBonds (SourceBondLists.bonds n bs hb).left
          (SourceBondLists.bonds n bs hb).right (fun e => (bs.get e).2.2) (initialScale N bs c),
        initialConstant (fun e : Fin bs.length => (bs.get e).2.2) c (initialScale N bs c)) := by
    unfold rawMatrix
    rw [initialSource_sum n bs hb,initial_constant_eq]
  change rawBottom (n+2*bs.length)
    (initialSourceBonds n bs (initialScale N bs c),(initial n bs c N).2.2.1)=_
  calc
    _ = rawBottom (n+2*bs.length)
        (initialPhysicalBonds (SourceBondLists.bonds n bs hb).left
          (SourceBondLists.bonds n bs hb).right (fun e => (bs.get e).2.2) (initialScale N bs c),
        initialConstant (fun e : Fin bs.length => (bs.get e).2.2) c (initialScale N bs c)) :=
      congrArg normalizedBottom hh
    _ = _ := by rw [Nat.mul_comm 2 bs.length]

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal initial scale has exactly the coefficient budget used in
the rational simultaneous path estimate. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped BigOperators Classical

theorem initialScale_eq (N : ℚ) (bs : List Bond) (c : ℚ) :
    initialScale N bs c=qmaRationalInitialScale (fun e : Fin bs.length => (bs.get e).2.2) c N := by
  unfold initialScale qmaRationalInitialScale
  rw [initial_list_sum,initial_list_sum]

theorem initialScale_cast (N : ℚ) (bs : List Bond) (c : ℚ) :
    (initialScale N bs c:ℝ)=
      qmaRoutingScale (3*∑ e : Fin bs.length, (1+2*|((bs.get e).2.2:ℝ)|))
        (|(c:ℝ)|+4*∑ e : Fin bs.length, (1+|((bs.get e).2.2:ℝ)|)^2) (N:ℝ) := by
  rw [initialScale_eq,qmaRationalInitialScale_cast]

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialAccuracy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual initial odd subdivision changes the full-space ground energy
by at most 1/N. Together with the literal fork iteration this is (k+1)/N. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorGraph QuantumRawExchange QuantumAxisSample MediatorListProgram
open scoped BigOperators Classical

theorem initial_accuracy (n : ℕ) (bs : List Bond) (hb : SourceBondLists.bounded n bs)
    (hn : ∀ b ∈ bs, b.1 ≠ b.2.1) (c N : ℚ) (hN : 0 < N) :
    |normalizedBottom (matrix (initial n bs c N))-normalizedBottom (rawMatrix n (bs,c))| ≤
      1/(N:ℝ) := by
  let left : Fin bs.length → Fin n := (SourceBondLists.bonds n bs hb).left
  let right : Fin bs.length → Fin n := (SourceBondLists.bonds n bs hb).right
  let J : Fin bs.length → ℚ := fun e => (bs.get e).2.2
  have hneq : ∀ e, left e ≠ right e := SourceBondLists.bonds_noLoops n bs hb hn
  have h := qmaPathsGraph_accuracy (fun a : Fin 0 => Fin.elim0 a)
    (fun a : Fin 0 => Fin.elim0 a) (fun a => Fin.elim0 a) (fun _ => 0) (c:ℝ)
    (qmaOriginalSite left right) (qmaOriginalSite_injective left right hneq)
    (fun _ => false) (fun e => (J e:ℝ)) (show (0:ℝ) < N by exact_mod_cast hN)
  dsimp only at h
  have hscale : (initialScale N bs c:ℝ)=
      qmaRoutingScale (3*∑ e, (1+2*|(J e:ℝ)|))
        (|(c:ℝ)|+4*∑ e, (1+|(J e:ℝ)|)^2) (N:ℝ) := initialScale_cast N bs c
  simp only [Finset.univ_eq_empty,Finset.sum_empty,mul_zero,zero_add] at h
  rw [← hscale] at h
  have hout : normalizedBottom (matrix (initial n bs c N))=
      normalizedBottom (qmaPathsGraph (fun a : Fin 0 => Fin.elim0 a)
        (fun a : Fin 0 => Fin.elim0 a) (fun _ => 0) (c:ℝ) (initialScale N bs c:ℝ)
        (qmaOriginalSite left right) (fun _ => false) (fun e => (J e:ℝ))) := by
    rw [initial_bottom_physical n bs hb c N]
    unfold rawBottom
    exact congrArg normalizedBottom (initialPhysical_matrix left right J c (initialScale N bs c))
  have hin : rawMatrix n (bs,c)=qmaExchangeMatrix left right (fun e => (J e:ℝ)) (c:ℝ) := by
    rw [rawMatrix_eq_matrix]
    exact (QuantumListGraph.ofBonds_matrix n bs c hb hn).symm
  have hJ : ∀ e, ((J e:ℝ):ℂ)=(J e:ℂ) := by intro e; norm_cast
  have hc : ((c:ℝ):ℂ)=(c:ℂ) := by norm_cast
  simp only [qmaExchangeMatrix,Finset.univ_eq_empty,Finset.sum_empty,zero_add] at h
  have hin' : rawMatrix n (bs,c)=
      ∑ e, (J e:ℂ) • sourceHeisenbergMatrix n (left e) (right e)+(c:ℂ) • 1 := by
    simpa only [qmaExchangeMatrix,hJ,hc] using hin
  change |normalizedBottom _-normalizedBottom _| ≤ 1/(N:ℝ) at h
  rw [← hout] at h
  have heq : (c:ℂ) • (1 : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)+
      ∑ e, (J e:ℂ) • sourceHeisenbergMatrix n (left e) (right e)=rawMatrix n (bs,c) := by
    rw [hin']
    exact add_comm _ _
  simpa only [qmaOriginalSite,Matrix.cons_val_zero,Matrix.cons_val_one,hJ,hc,heq] using h

theorem initial_iterated_accuracy (n : ℕ) (bs : List Bond) (hb : SourceBondLists.bounded n bs)
    (hn : ∀ b ∈ bs, b.1 ≠ b.2.1) (c N : ℚ) (hN : 0 < N) (k : ℕ) :
    |normalizedBottom (matrix (iterate N k (initial n bs c N)))-
      normalizedBottom (rawMatrix n (bs,c))| ≤ ((k:ℝ)+1)/(N:ℝ) := by
  calc
    _ ≤ |normalizedBottom (matrix (iterate N k (initial n bs c N)))-
        normalizedBottom (matrix (initial n bs c N))|+
        |normalizedBottom (matrix (initial n bs c N))-normalizedBottom (rawMatrix n (bs,c))| :=
      abs_sub_le _ _ _
    _ ≤ (k:ℝ)/(N:ℝ)+1/(N:ℝ) :=
      add_le_add (initial_iterate_accuracy n bs c N hN k) (initial_accuracy n bs hb hn c N hN)
    _ = ((k:ℝ)+1)/(N:ℝ) := by ring

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListSpatialPackage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Package the literal full fork graph with deterministic midpoint anchors.
The package keeps its actual spin indices, coefficients and scalar offset. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped Classical

theorem fullGraph_matrix (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 s.2.1) (hn : ∀ b ∈ s.2.1, b.1≠b.2.1) :
    qmaExchangeMatrix (fullGraph s hs hb hn).left (fullGraph s hs hb hn).right
      (fun e => ((fullGraph s hs hb hn).weight e:ℝ)) s.2.2.1 = matrix s := by
  change _ = QuantumRawExchange.rawMatrix s.1 (fullList s,s.2.2.1)
  rw [rawMatrix_eq_matrix]
  exact QuantumListGraph.ofBonds_matrix _ _ _ _ _

theorem spatialModel_matrix {rows width : ℕ} (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 s.2.1) (hn : ∀ b ∈ s.2.1, b.1≠b.2.1)
    (cell : ℕ → QMAGridCell rows width) (A : ℕ)
    (hc : ∀ p, qmaCellMass (fun v : Fin s.1 => cell v.val) p ≤ A)
    (hd : ∀ v : Fin s.1, degree (fullList s) v.val ≤ 3)
    (hl : BondLocal (fullList s) cell CommonCell) :
    let M := spatialModel s hs hb hn cell A hc hd hl
    qmaExchangeMatrix M.left M.right (fun e => (M.weight e:ℝ)) M.constant = matrix s :=
  fullGraph_matrix s hs hb hn

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialSpatial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded-density local input list yields the actual degree-three
spatial output, with its full Hamiltonian and fixed density constant. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped Classical

namespace SpatialInput
variable {rows width A D : ℕ} (I : SpatialInput rows width A D)

theorem model_energy : I.model.energy=MediatorGraph.normalizedBottom (matrix I.state) :=
  congrArg MediatorGraph.normalizedBottom
    (spatialModel_matrix I.state I.validPorts I.state_bounded I.state_noLoops I.cells
      (spatialDensity A D) I.state_density I.state_degree I.state_locality)

end SpatialInput
end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGateScalarReduction
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_conj _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_neg _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_rat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scalar reduction of a one-site gate tensor to its active entry
and spectator equality test. This avoids an ambient spin-basis sum in the
literal history-matrix evaluator. -/

noncomputable section
namespace ContinuumCoulomb.QuantumGateScalarReduction
open QuantumAlgebraicScalar QuantumFixedPauli QuantumAlgebraicHistory
open scoped Classical

theorem listProduct_single {α : Type} [DecidableEq α] (i : α) (z : Scalar)
    (xs : List α) (hx : xs.Nodup) :
    product (xs.map (fun j => if j=i then z else rat 1)) =
      if i ∈ xs then z else rat 1 := by
  induction xs with
  | nil => simp [product]
  | cons a xs ih =>
    by_cases ha : a=i
    · subst a
      have hn : i ∉ xs := (List.nodup_cons.mp hx).1
      simp [product,ih (List.nodup_cons.mp hx).2,hn]
    · simp [product,ha,ih (List.nodup_cons.mp hx).2,Ne.symm ha]

theorem listProduct_zero (xs : List Scalar) (h : rat 0 ∈ xs) : product xs=rat 0 := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    rcases List.mem_cons.mp h with ha | hx
    · subst a
      simp [product]
    · simp [product,ih hx]

theorem finiteProduct_single {α : Type} [Fintype α] [DecidableEq α]
    (i : α) (z : Scalar) :
    finiteProduct (fun j => if j=i then z else rat 1)=z := by
  have hn : (enumerate α).Nodup :=
    List.nodup_ofFn.mpr (Fintype.equivFin α).symm.injective
  have hi : i ∈ enumerate α :=
    List.mem_ofFn.mpr ⟨(Fintype.equivFin α) i,(Fintype.equivFin α).symm_apply_apply i⟩
  rw [finiteProduct,listProduct_single i z _ hn,ite_eq_left hi]

theorem finiteProduct_zero {α : Type} [Fintype α] (f : α → Scalar)
    (i : α) (hi : f i=rat 0) : finiteProduct f=rat 0 := by
  apply listProduct_zero
  apply List.mem_map.mpr
  refine ⟨i,?_,hi⟩
  exact List.mem_ofFn.mpr
    ⟨(Fintype.equivFin α) i,(Fintype.equivFin α).symm_apply_apply i⟩

theorem finiteProduct_sparse {α : Type} [Fintype α] [DecidableEq α]
    (i : α) (A : Fin 2 → Fin 2 → Scalar) (s t : α → Fin 2) :
    finiteProduct (fun j => if j=i then A (s j) (t j) else identity (s j) (t j)) =
      sparseEntry i A s t := by
  by_cases h : ∀ j, j ≠ i → s j=t j
  · have he : (fun j => if j=i then A (s j) (t j) else identity (s j) (t j)) =
        (fun j => if j=i then A (s i) (t i) else rat 1) := by
      funext j
      by_cases hj : j=i
      · simp [hj]
      · simp [hj,identity,h j hj]
    rw [he,finiteProduct_single]
    exact (ite_eq_left h).symm
  · obtain ⟨j,hj⟩ := not_forall.mp h
    have hji : j ≠ i := fun he => hj (by simp [he])
    have hst : s j ≠ t j := fun he => hj (fun _ => he)
    rw [finiteProduct_zero _ j (by simp [hji,identity,hst])]
    exact (ite_eq_right h).symm

theorem hadamard_entry (work j : ℕ) (s t : SourceSpinBasis (work+1)) :
    gate work (.hadamard j) s t=sparseEntry (qmaQubit work j) hadamard s t :=
  finiteProduct_sparse _ _ _ _

theorem phaseT_entry (work j : ℕ) (s t : SourceSpinBasis (work+1)) :
    gate work (.phaseT j) s t=sparseEntry (qmaQubit work j) phaseT s t :=
  finiteProduct_sparse _ _ _ _

end ContinuumCoulomb.QuantumGateScalarReduction

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGateEntryProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_conj _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_neg _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_rat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact gate entries from a bounded register scan.  Work is unary, addresses
and support labels are binary, and each quantum bit is read from the supplied
small support table.  No sum over ambient configurations occurs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumGateEntryProgram
open ExactQuantumFactoring.BitStackProgram QuantumAlgebraicScalar QuantumCircuitCode
open scoped Classical

theorem allWork_iff (x : Input) : allWork x = true ↔
    ∀ i : Fin (x.1+1), point x i.val = true := by
  simp only [allWork,List.all_map,List.all_eq_true,List.mem_range,Function.comp_apply,id_eq]
  exact ⟨fun h i => h i.val i.isLt,fun h i hi => h ⟨i,hi⟩⟩

theorem allWork_single (x : Input) (hg : gateTag x.2.2.1 ≠ 2) :
    allWork x = true ↔ ∀ i : Fin (x.1+1),
      i ≠ qmaQubit x.1 (gateLeft x.2.2.1) → row x i.val=column x i.val := by
  rw [allWork_iff]
  simp only [point,ite_eq_right hg,Bool.or_eq_true,decide_eq_true_eq]
  constructor
  · intro h i hi
    rcases h i with he | he
    · exact False.elim (hi (Fin.ext he))
    · exact Fin.ext he
  · intro h i
    by_cases hi : i=qmaQubit x.1 (gateLeft x.2.2.1)
    · exact Or.inl (congrArg Fin.val hi)
    · exact Or.inr (congrArg Fin.val (h i hi))

private theorem swap_val (b : Fin 2) : (Equiv.swap (0 : Fin 2) 1 b).val = 1-b.val := by
  fin_cases b <;> decide

theorem allWork_cnot (work base a b : ℕ) (d : QuantumHistoryBitProgram.Data) :
    allWork (work,base,.controlledNot a b,d) = true ↔
      (fun i : Fin (work+1) => row (work,base,.controlledNot a b,d) i.val) =
      qmaControlledNot work (qmaQubit work a) (qmaQubit work b)
        (fun i => column (work,base,.controlledNot a b,d) i.val) := by
  rw [allWork_iff,funext_iff]
  apply forall_congr'
  intro i
  change decide ((row (work,base,.controlledNot a b,d) i.val).val =
    if i.val=b%(work+1) ∧ (column (work,base,.controlledNot a b,d) (a%(work+1))).val=1 then
      1-(column (work,base,.controlledNot a b,d) i.val).val
    else (column (work,base,.controlledNot a b,d) i.val).val)=true ↔ _
  rw [decide_eq_true_eq]
  have ht : (i.val=b%(work+1)) ↔ i=qmaQubit work b :=
    ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
  have hc : (column (work,base,.controlledNot a b,d) (a%(work+1))).val=1 ↔
      column (work,base,.controlledNot a b,d) (a%(work+1))=1 :=
    ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
  have he : (i.val=b%(work+1) ∧
      (column (work,base,.controlledNot a b,d) (a%(work+1))).val=1) ↔
      (i=qmaQubit work b ∧
        column (work,base,.controlledNot a b,d) (a%(work+1))=1) := and_congr ht hc
  by_cases h : i=qmaQubit work b ∧
      column (work,base,.controlledNot a b,d) (a%(work+1))=1
  · have hr : qmaControlledNot work (qmaQubit work a) (qmaQubit work b)
        (fun j => column (work,base,.controlledNot a b,d) j.val) i =
        Equiv.swap (0:Fin 2) 1 (column (work,base,.controlledNot a b,d) i.val) :=
      ite_eq_left h
    rw [ite_eq_left (he.mpr h),hr,Fin.ext_iff,swap_val]
  · have hr : qmaControlledNot work (qmaQubit work a) (qmaQubit work b)
        (fun j => column (work,base,.controlledNot a b,d) j.val) i =
        column (work,base,.controlledNot a b,d) i.val := ite_eq_right h
    rw [ite_eq_right (mt he.mp h),hr,Fin.ext_iff]

theorem entry_eq (work base : ℕ) (g : QMAGate) (d : QuantumHistoryBitProgram.Data) :
    entry (work,base,g,d) = QuantumAlgebraicHistory.gate work g
      (fun i => row (work,base,g,d) i.val) (fun i => column (work,base,g,d) i.val) := by
  cases g with
  | hadamard j =>
    rw [QuantumGateScalarReduction.hadamard_entry]
    have hh := allWork_single (work,base,.hadamard j,d) (by change (0 : ℕ) ≠ 2; decide)
    by_cases h : allWork (work,base,.hadamard j,d)=true
    · have hv : entry (work,base,.hadamard j,d) = QuantumAlgebraicHistory.hadamard
          (row (work,base,.hadamard j,d) (left (work,base,.hadamard j,d)))
          (column (work,base,.hadamard j,d) (left (work,base,.hadamard j,d))) := by
        unfold entry
        rw [ite_eq_left h]
        exact ite_eq_left rfl
      refine hv.trans ?_
      symm
      exact ite_eq_left (hh.mp h)
    · have hv : entry (work,base,.hadamard j,d)=rat 0 := ite_eq_right h
      refine hv.trans ?_
      symm
      exact ite_eq_right (mt hh.mpr h)
  | phaseT j =>
    rw [QuantumGateScalarReduction.phaseT_entry]
    have hh := allWork_single (work,base,.phaseT j,d) (by change (1 : ℕ) ≠ 2; decide)
    by_cases h : allWork (work,base,.phaseT j,d)=true
    · have hv : entry (work,base,.phaseT j,d) = QuantumAlgebraicHistory.phaseT
          (row (work,base,.phaseT j,d) (left (work,base,.phaseT j,d)))
          (column (work,base,.phaseT j,d) (left (work,base,.phaseT j,d))) := by
        unfold entry
        rw [ite_eq_left h]
        rw [ite_eq_right (by change (1 : ℕ) ≠ 0; decide)]
        exact ite_eq_left rfl
      refine hv.trans ?_
      symm
      exact ite_eq_left (hh.mp h)
    · have hv : entry (work,base,.phaseT j,d)=rat 0 := ite_eq_right h
      refine hv.trans ?_
      symm
      exact ite_eq_right (mt hh.mpr h)
  | controlledNot a b =>
    have hh := allWork_cnot work base a b d
    unfold entry QuantumAlgebraicHistory.gate
    simp only [gateTag]
    by_cases h : allWork (work,base,.controlledNot a b,d)=true
    · simp [h,hh.mp h]
    · have hn := mt hh.mpr h
      simp [h,hn]

end ContinuumCoulomb.QuantumGateEntryProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedCellProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cell arrays follow the same term-major order as the literal local-word
compiler. Each new mediator inherits its term's cell; each output word retains
that cell as its anchor. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedCellProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

theorem cells_ofFn {n m : ℕ} (d : ℕ) (cell : Fin n → Pair) (anchor : Fin m → Pair) :
    (value d (List.ofFn cell,List.ofFn anchor)).1=List.ofFn (Fin.append cell anchor) :=
  (List.ofFn_fin_append cell anchor).symm

theorem anchors_ofFn {m : ℕ} (d : ℕ) (anchor : Fin m → Pair) :
    anchors d (List.ofFn anchor)=
      (List.ofFn (fun i : Fin m => List.ofFn (fun _ : Fin d => anchor i))).flatten := by
  simp only [anchors,List.map_ofFn,List.ofFn_const,Function.comp_def]

end ContinuumCoulomb.QuantumOrderedCellProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedCellTable
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.allRouted_length _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.value_length _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The computed spatial arrays use exactly the same sum/product enumeration
as the actual ordered Hamiltonian compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedCellTable
open QuantumOrderedCellProgram QuantumOrderedLabelTable QuantumOrderedSpatialComplete
open ExactQuantumFactoring.BitStackProgram
open QuantumRouteCode
variable {ι κ : Type} {n m : ℕ}

theorem value_table (d : ℕ) (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (cell : ι → Pair) (anchor : κ → Pair) :
    value d (table q e cell anchor)=
      table (nextQubit q e) (nextTerm e d) (extendCell cell anchor) (extendAnchor d anchor) := by
  apply Prod.ext
  · rw [show (value d (table q e cell anchor)).1=
        List.ofFn (Fin.append (fun i => cell (q i)) (fun i => anchor (e i))) from cells_ofFn d _ _]
    apply congrArg List.ofFn
    funext i
    obtain ⟨i,rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n+m)).surjective i
    cases i <;> simp [nextQubit,extendCell,Fin.append]
  · change anchors d (List.ofFn (fun i => anchor (e i)))=List.ofFn _
    rw [anchors_ofFn]
    rw [← product_table (fun p : Fin m × Fin d => anchor (e p.1))]
    apply congrArg List.ofFn
    funext i
    rfl

theorem complete_table (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (cell : ι → Pair) (anchor : κ → Pair) :
    complete (table q e cell anchor)=
      table (QuantumOrderedLabelTable.qubits6 q e) (QuantumOrderedLabelTable.terms6 e)
        (cell6 cell anchor) (anchor6 anchor) := by
  unfold complete
  rw [value_table,value_table,value_table,value_table,value_table,value_table]
  rfl

end ContinuumCoulomb.QuantumOrderedCellTable

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedLabelData
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual padded history word is obtained by zipping its literal
site-number list with a fixed local pattern. No spectator basis occurs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedHistory
open scoped Classical

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
private theorem local_word_at {n : ℕ} (S : Finset ι) (e : Fin n ≃ {i // i ∈ S})
    (m : ℕ) (w : Fin (n+m) → Fin 4) (i : Fin n) :
    QuantumPaddedLocal.word S e m w (e i).val=QuantumPaddedPauli.paddedWord n m w i := by
  simp only [QuantumPaddedLocal.word,qmaPauliExtend,dite_eq_left (e i).property]
  apply congrArg (QuantumPaddedPauli.paddedWord n m w)
  apply e.injective
  rw [Equiv.apply_symm_apply]

private theorem map_get_zip {α β γ : Type} (xs : List α) (g : α → β)
    (f : Fin xs.length → γ) :
    (List.ofFn (fun i => (g (xs.get i),f i)))= (xs.map g).zip (List.ofFn f) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem source_tag (c : QMACircuit) (hT : 0 < c.gates.length) (p : Term c) :
    QuantumOrderedLabelData.tag (QuantumOrderedSupport.siteNumber c)
      (QuantumOrderedSupport.sites c hT p.1) (word c hT p) =
      (QuantumOrderedSupport.encodedSites c hT p.1).zip
        (localLabels (QuantumOrderedSupport.sites c hT p.1).length
          (6-(QuantumOrderedSupport.sites c hT p.1).length)
          (widthIndex _ (QuantumOrderedSupport.sites_length c hT p.1) p.2)) := by
  let xs := QuantumOrderedSupport.sites c hT p.1
  let e := QuantumOrderedSupport.supportEquiv c hT p.1
  let v : QuantumOrderedSupport.Qubit c → Fin 4 := word c hT p
  let w := widthIndex _ (QuantumOrderedSupport.sites_length c hT p.1) p.2
  have hw (i : Fin xs.length) :
      v (xs.get i)=
        QuantumPaddedPauli.paddedWord xs.length (6-xs.length) w i := by
    have hi := QuantumOrderedSupport.supportEquiv_apply c hT p.1 i
    change (e i).val=xs.get i at hi
    rw [← hi]
    exact local_word_at _ e _ w i
  change xs.map (fun i => (QuantumOrderedSupport.siteNumber c i,(v i).val)) = _
  calc
    _ = List.ofFn (fun i : Fin xs.length =>
        (QuantumOrderedSupport.siteNumber c (xs.get i),(v (xs.get i)).val)) :=
      (List.ofFn_getElem_eq_map xs
        (fun i => (QuantumOrderedSupport.siteNumber c i,(v i).val))).symm
    _ = List.ofFn (fun i : Fin xs.length =>
        (QuantumOrderedSupport.siteNumber c (xs.get i),
          (QuantumPaddedPauli.paddedWord xs.length (6-xs.length) w i).val)) := by
      apply congrArg List.ofFn
      funext i
      rw [hw]
    _ = _ := map_get_zip xs (QuantumOrderedSupport.siteNumber c)
      (fun i => (QuantumPaddedPauli.paddedWord xs.length (6-xs.length) w i).val)

end ContinuumCoulomb.QuantumPaddedHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedLabelProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-arity local history packets: sparse numeric labels and sampled
algebraic coefficients share exactly the same fixed Pauli-word order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedLabelProgram
open QuantumAlgebraicScalar QuantumFixedPauli QuantumPaddedHistory
open QuantumOrderedLabelData
open ExactQuantumFactoring.BitStackProgram
open scoped Classical

theorem uniformPacket_eq (x : Input) (h : x.2.1.length ≤ 6) :
    uniformPacket x=packet x.2.1.length (6-x.2.1.length) x := by
  generalize hn : x.2.1.length=n at *
  interval_cases n <;> simp only [uniformPacket,hn] <;> norm_num

end ContinuumCoulomb.QuantumPaddedLabelProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedLabelMeaning
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every emitted local packet entry is the actual padded history word
and its sampled coefficient, in the supplied support-list order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedLabelProgram
open QuantumAlgebraicScalar QuantumFixedPauli QuantumPaddedHistory
open scoped Classical

attribute [local instance] OAI.ContinuumCoulomb.QuantumPaddedLabelProgram.finDecision
private theorem labels_eq_zip (n m : ℕ) (w : Fin (n+m) → Fin 4)
    (xs : List ℕ) (hlen : xs.length=n) :
    labels n m w xs = xs.zip (localLabels n m w) := by
  apply List.ext_getElem
  · simp [labels,localLabels,hlen]
  · intro i hi hj
    have hi' : i < xs.length := by simpa only [labels,List.length_ofFn,← hlen] using hi
    simp only [labels,localLabels,List.getElem_ofFn,List.getElem_zip]
    rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem hi',Option.getD_some]

theorem entry_source (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (w : Fin ((QuantumOrderedSupport.sites c hT a).length+
      (6-(QuantumOrderedSupport.sites c hT a).length)) → Fin 4) :
    entry (QuantumOrderedSupport.sites c hT a).length
      (6-(QuantumOrderedSupport.sites c hT a).length) w
      (k,QuantumOrderedSupport.encodedSites c hT a,
        matrixData (QuantumAlgebraicHistory.orderedTable c hT a)) =
    let p : Term c := (a,(widthIndex _ (QuantumOrderedSupport.sites_length c hT a)).symm w)
    (QuantumOrderedLabelData.tag (QuantumOrderedSupport.siteNumber c)
      (QuantumOrderedSupport.sites c hT a) (word c hT p),sampledWeight k c hT p) := by
  let p : Term c := (a,(widthIndex _ (QuantumOrderedSupport.sites_length c hT a)).symm w)
  have hw : widthIndex _ (QuantumOrderedSupport.sites_length c hT a) p.2 = w :=
    (widthIndex _ (QuantumOrderedSupport.sites_length c hT a)).apply_symm_apply w
  apply Prod.ext
  · change labels _ _ w (QuantumOrderedSupport.encodedSites c hT a) = _
    rw [labels_eq_zip _ _ w _ (by simp only [QuantumOrderedSupport.encodedSites,List.length_map])]
    have hs := source_tag c hT p
    change QuantumOrderedLabelData.tag (QuantumOrderedSupport.siteNumber c)
      (QuantumOrderedSupport.sites c hT a) (word c hT p) =
      (QuantumOrderedSupport.encodedSites c hT a).zip (localLabels _ _
        (widthIndex _ (QuantumOrderedSupport.sites_length c hT a) p.2)) at hs
    rw [hw] at hs
    exact hs.symm
  · change sample k (QuantumPaddedTable.coefficient _ _ _ w) = _
    unfold sampledWeight
    apply congrArg (sample k)
    unfold scalar
    rw [hw]

end ContinuumCoulomb.QuantumPaddedLabelProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedLabelTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal concatenation of fixed-width history packets is an exact
enumeration of the actual padded history family.  The local pattern order is
allowed to depend on the support width; its explicit bijection is retained. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedLabelProgram
open QuantumAlgebraicScalar QuantumFixedPauli QuantumPaddedHistory
open scoped Classical

theorem packet_reindex (n : ℕ) (hn : n ≤ 6) (x : Input) :
    packet n (6-n) x = List.ofFn (fun j => entry n (6-n) (packetPatterns n hn j) x) := by
  simp only [packet,enumerate,List.map_ofFn,Function.comp_def]
  rw [List.ofFn_congr (pattern_card n hn)]
  rfl

attribute [local instance] OAI.ContinuumCoulomb.QuantumPaddedLabelProgram.tableFinDecision
theorem sourceEntries_table (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length) :
    sourceEntries k c hT =
      QuantumOrderedLabelTable.table (sourceTerms c hT)
        (QuantumOrderedLabelTable.index (QuantumOrderedSourceIndex.qubits c))
        (fun p => QuantumOrderedSupport.sites c hT p.1)
        (sourceWord c hT) (sampledWeight k c hT) := by
  unfold sourceEntries QuantumOrderedLabelTable.table sourceTerms
  simp only [Equiv.trans_apply]
  let entryAt (j : Fin (QuantumOrderedSourceIndex.referenceCount c) ×
      Fin QuantumOrderedSourceIndex.patternCount) :=
    let p := Equiv.prodShear (QuantumOrderedSourceIndex.reference c)
      (fun i => (packetPatterns _ (QuantumOrderedSupport.sites_length c hT
        (QuantumOrderedSourceIndex.reference c i))).trans
          (widthIndex _ (QuantumOrderedSupport.sites_length c hT
            (QuantumOrderedSourceIndex.reference c i))).symm) j
    (QuantumOrderedLabelData.tag
      (QuantumOrderedLabelTable.index (QuantumOrderedSourceIndex.qubits c))
      (QuantumOrderedSupport.sites c hT p.1) (sourceWord c hT p),sampledWeight k c hT p)
  change _ = List.ofFn (fun i => entryAt (finProdFinEquiv.symm i))
  rw [QuantumOrderedLabelTable.product_table entryAt]
  dsimp only [entryAt]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  let a := QuantumOrderedSourceIndex.reference c i
  have hn := QuantumOrderedSupport.sites_length c hT a
  rw [uniformPacket_eq _ (by
    simpa only [sourceInput,QuantumOrderedSupport.encodedSites,List.length_map] using hn)]
  rw [show (sourceInput k c hT (QuantumOrderedSourceIndex.reference c i)).2.1.length =
    (QuantumOrderedSupport.sites c hT a).length by
      simp only [sourceInput,QuantumOrderedSupport.encodedSites,List.length_map,a]]
  change packet (QuantumOrderedSupport.sites c hT a).length
    (6-(QuantumOrderedSupport.sites c hT a).length) (sourceInput k c hT a) = _
  rw [packet_reindex _ hn]
  apply congrArg List.ofFn
  funext j
  have h := entry_source k c hT a (packetPatterns _ hn j)
  simpa only [sourceInput,sourceWord,Equiv.trans_apply,Equiv.prodShear_apply,
    Equiv.symm_apply_apply,
    QuantumOrderedSourceIndex.qubits_index] using h

theorem sourceEntries_length (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length) :
    (sourceEntries k c hT).length = QuantumOrderedSourceIndex.termCount c := by
  rw [sourceEntries_table]
  simp only [QuantumOrderedLabelTable.table,List.length_ofFn,
    QuantumOrderedSourceIndex.termCount]

end ContinuumCoulomb.QuantumPaddedLabelProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSweepCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal natural row/column tags for the sparse sweep.  The
three gates of each wire transfer carry the same column; the original gate
keeps its proved arrival column. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSweepCells
open QuantumCircuitCode

theorem transfer_columns {width work : ℕ}
    (l r : Fin (width+1) → Fin (work+1)) (xs : List (Fin (width+1))) :
    (qmaColumnTransfer l r xs).map (fun p => p.2.val)=
      repeatColumns (xs.map Fin.val) := by
  induction xs with
  | nil => rfl
  | cons j xs ih =>
    simp only [qmaColumnTransfer,List.flatMap_cons,List.map_append,
      qmaWireSwapGates,List.map_cons,List.map_nil,repeatColumns]
    simpa only [repeatColumns,qmaColumnTransfer,qmaWireSwapGates,List.map_cons,List.map_nil]
      using congrArg (fun ys => [j.val,j.val,j.val]++ys) ih

theorem columns_actual (width order : ℕ) :
    (List.ofFn (qmaSweepOrder width order)).map Fin.val=columns width order := by
  apply List.ext_getElem
  · simp only [List.length_map,List.length_ofFn,columns,List.length_range]
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_ofFn,columns,List.getElem_range,
      sweepIndex_value]

theorem arrival_actual (width order : ℕ) (g : QMAGate) :
    (qmaGateArrivalColumn width (qmaSweepOrder width order) g).val=
      sweepIndex width order (rowCut width order g-1) := by
  rw [qmaGateArrivalColumn,sweepIndex_value]
  simp only [qmaGateArrivalIndex,rowCut_eq]

theorem rowColumns_actual (width work order : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (g : QMAGate) :
    (qmaTaggedRowStage width work l r (qmaSweepOrder width order) g).map
        (fun p => p.2.val)=rowColumns width order g := by
  simp only [qmaTaggedRowStage,List.map_append,List.map_cons,List.map_nil,
    transfer_columns,List.map_take,List.map_drop,columns_actual,rowCut_eq,
    arrival_actual,rowColumns]

theorem rowCells_actual (rows width start : ℕ) (hs : start < rows) (g : QMAGate) :
    ((qmaTaggedRowStage width (qmaGridWork rows width)
      (qmaGridQubit rows width ⟨start,by omega⟩)
      (qmaGridQubit rows width ⟨start+1,by omega⟩)
      (qmaSweepOrder width (rows-1-start)) g).map
        (fun p => (p.1,((⟨start,by omega⟩ : Fin (rows+1)),p.2)))).map
        (fun p => (p.2.1.val,p.2.2.val))=rowCells rows width start g := by
  simpa only [List.map_map,Function.comp_def,rowCells] using
    congrArg (List.map (fun j => (start,j)))
      (rowColumns_actual width (qmaGridWork rows width) (rows-1-start)
        (qmaGridQubit rows width ⟨start,by omega⟩)
        (qmaGridQubit rows width ⟨start+1,by omega⟩) g)

theorem sweepCells_cons (rows width start : ℕ) (g : QMAGate) (gs : List QMAGate) :
    sweepCells rows width start (g::gs)=
      rowCells rows width start g++sweepCells rows width (start+1) gs := by
  simp only [sweepCells,List.length_cons,List.range_succ_eq_map,List.flatMap_cons,
    List.flatMap_map,readGate,List.drop_zero,List.headD_cons,Nat.add_zero,List.drop_succ_cons]
  congr 1
  have h : (fun i => rowCells rows width (start+Nat.succ i)
      ((gs.drop i).headD (.hadamard 0)))=
      (fun i => rowCells rows width (start+1+i) ((gs.drop i).headD (.hadamard 0))) := by
    funext i
    congr 1
    omega
  rw [h]

theorem sweepCells_actual (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows) :
    (qmaTaggedSweepFrom rows width start gs h).map
      (fun p => (p.2.1.val,p.2.2.val))=sweepCells rows width start gs := by
  induction gs generalizing start with
  | nil => rfl
  | cons g gs ih =>
    have hs : start < rows := by simp only [List.length_cons] at h; omega
    rw [sweepCells_cons]
    simp only [qmaTaggedSweepFrom,List.map_append]
    rw [rowCells_actual rows width start hs g,ih]

theorem value_actual (c : QMACircuit) :
    value c=(qmaSparseTags c).map (fun p => (p.2.1.val,p.2.2.val)) :=
  (sweepCells_actual _ _ _ _ _).symm

theorem value_length (c : QMACircuit) :
    (value c).length=(qmaSparseCircuit c).gates.length := by
  rw [value_actual,List.length_map,qmaSparseTags_length]

end ContinuumCoulomb.QuantumSweepCells

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Natural cell lookups for the actual sparse history.  The reference
lookup uses the same time-grouped descriptors as the sampled Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryCells
open QuantumHistoryDescriptors QuantumOrderedSourceIndex

theorem gateCell_actual (c : QMACircuit) (t : Fin (qmaSparseCircuit c).gates.length) :
    gateCell c t.val=encodeCell (qmaSparseGateCell c t) := by
  unfold gateCell
  rw [List.headD_eq_head?_getD,List.head?_drop]
  rw [List.getElem?_eq_getElem (by rw [QuantumSweepCells.value_length]; exact t.isLt)]
  simp only [QuantumSweepCells.value_actual,List.getElem_map,encodeCell,
    qmaSparseGateCell,qmaSparseCell,Fin.val_cast,Option.getD_some]

theorem referenceCell_actual (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (i : Fin (qmaHistoryReferenceWork (qmaSparseCircuit c)+1)) :
    referenceCell c i.val=encodeCell (qmaOrderedSparseReferenceCell c hT i) := by
  unfold referenceCell
  rw [orderedAt_actual _ hT i,time_encode _ hT]
  exact gateCell_actual c _

theorem qubitCell_actual (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (q : QuantumOrderedSupport.Qubit (qmaSparseCircuit c)) :
    qubitCell c (QuantumOrderedSupport.siteNumber (qmaSparseCircuit c) q)=
      encodeCell (qmaOrderedQubitCell c hT q) := by
  rcases q with i | (b | w)
  · have hi : i.val < referenceWork (qmaSparseCircuit c)+1 := by
      simpa only [referenceWork_eq] using i.isLt
    simp only [qubitCell,QuantumOrderedSupport.siteNumber,hi,ite_true, if_true,
      qmaOrderedQubitCell,Sum.elim_inl]
    exact referenceCell_actual c hT i
  · change (if qmaHistoryReferenceWork (qmaSparseCircuit c)+1+b.val<
        qmaHistoryReferenceWork (qmaSparseCircuit c)+1 then _ else _)=_
    rw [ite_eq_right (by omega)]
    simp only [QuantumOrderedSupport.siteNumber,referenceWork_eq,Nat.add_sub_cancel_left]
    change (if b.val<(qmaSparseCircuit c).gates.length+2 then _ else _)=_
    rw [ite_eq_left b.isLt]
    exact gateCell_actual c (qmaClockAnchorIndex _ hT b)
  · have hnot : ¬qmaHistoryReferenceWork (qmaSparseCircuit c)+1+
        ((qmaSparseCircuit c).gates.length+2)+w.val<
        referenceWork (qmaSparseCircuit c)+1 := by rw [referenceWork_eq]; omega
    have hd : qmaHistoryReferenceWork (qmaSparseCircuit c)+1+
        ((qmaSparseCircuit c).gates.length+2)+w.val-
        (referenceWork (qmaSparseCircuit c)+1)=
        (qmaSparseCircuit c).gates.length+2+w.val := by rw [referenceWork_eq]; omega
    simp only [qubitCell,QuantumOrderedSupport.siteNumber,hnot,ite_false, if_false,hd]
    rw [ite_eq_right (by omega),Nat.add_sub_cancel_left]
    rfl

theorem termCell_actual (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork (qmaSparseCircuit c))) :
    termCell c ((reference (qmaSparseCircuit c)).symm a).val=
      encodeCell (qmaOrderedTermCell c hT a) := by
  cases a with
  | inl i =>
    change referenceCell c (if i.val < referenceWork (qmaSparseCircuit c)+1
      then i.val else _)=_
    rw [ite_eq_left (by simpa only [referenceWork_eq] using i.isLt)]
    exact referenceCell_actual c hT i
  | inr i =>
    change referenceCell c (if qmaHistoryReferenceWork (qmaSparseCircuit c)+1+i.val<
      qmaHistoryReferenceWork (qmaSparseCircuit c)+1
      then qmaHistoryReferenceWork (qmaSparseCircuit c)+1+i.val
      else qmaHistoryReferenceWork (qmaSparseCircuit c)+1+i.val-
        (qmaHistoryReferenceWork (qmaSparseCircuit c)+1))=_
    rw [ite_eq_right (by omega),Nat.add_sub_cancel_left]
    exact referenceCell_actual c hT i.castSucc

theorem qubitCells_actual (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length) :
    qubitCells c=List.ofFn (fun i : Fin (qubitCount (qmaSparseCircuit c)) =>
      encodeCell (qmaOrderedQubitCell c hT (qubits (qmaSparseCircuit c) i))) := by
  apply List.ext_getElem
  · simp only [qubitCells,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hj
    simp only [qubitCells,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    let j : Fin (qubitCount (qmaSparseCircuit c)) := ⟨i,by
      simpa only [List.length_ofFn] using hj⟩
    have he := congrFun (qubits_index (qmaSparseCircuit c)) (qubits (qmaSparseCircuit c) j)
    simp only [QuantumOrderedLabelTable.index,Equiv.symm_apply_apply] at he
    simpa only [←he] using qubitCell_actual c hT (qubits (qmaSparseCircuit c) j)

theorem referenceCells_actual (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length) :
    referenceCells c=List.ofFn (fun i : Fin (referenceCount (qmaSparseCircuit c)) =>
      encodeCell (qmaOrderedTermCell c hT (reference (qmaSparseCircuit c) i))) := by
  apply List.ext_getElem
  · simp only [referenceCells,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hj
    simp only [referenceCells,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    let j : Fin (referenceCount (qmaSparseCircuit c)) := ⟨i,by
      simpa only [List.length_ofFn] using hj⟩
    simpa only [Equiv.symm_apply_apply] using
      termCell_actual c hT (reference (qmaSparseCircuit c) j)

private theorem sourceTerms_first (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (referenceCount c*patternCount)) :
    (QuantumPaddedLabelProgram.sourceTerms c hT i).1=
      reference c (finProdFinEquiv.symm i).1 := by
  simp only [QuantumPaddedLabelProgram.sourceTerms,Equiv.trans_apply,
    Equiv.prodShear_apply]

private theorem anchors_source (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c) → ℕ × ℕ) :
    QuantumOrderedCellProgram.anchors patternCount
      (List.ofFn (fun i : Fin (referenceCount c) => a (reference c i)))=
      List.ofFn (fun i : Fin (referenceCount c*patternCount) =>
        a (QuantumPaddedLabelProgram.sourceTerms c hT i).1) := by
  rw [QuantumOrderedCellProgram.anchors_ofFn]
  rw [←QuantumOrderedLabelTable.product_table (fun p :
    Fin (referenceCount c) × Fin patternCount => a (reference c p.1))]
  apply congrArg List.ofFn
  funext i
  rw [sourceTerms_first]

theorem value_actual (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length) :
    value c=QuantumOrderedCellTable.table (qubits (qmaSparseCircuit c))
      (QuantumPaddedLabelProgram.sourceTerms (qmaSparseCircuit c) hT)
      (fun q => encodeCell (qmaOrderedQubitCell c hT q))
      (fun a => encodeCell (qmaOrderedTermCell c hT a.1)) := by
  apply Prod.ext
  · exact qubitCells_actual c hT
  · change QuantumOrderedCellProgram.anchors patternCount (referenceCells c)=_
    rw [referenceCells_actual c hT]
    dsimp only [QuantumOrderedCellTable.table]
    exact anchors_source (qmaSparseCircuit c) hT (fun a => encodeCell (qmaOrderedTermCell c hT a))

end ContinuumCoulomb.QuantumHistoryCells

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryComparison
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unary-bounded equality checks for the clock/work registers. A single
specified bit may be flipped, as required by the propagation delta. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryComparison
open ExactQuantumFactoring.BitStackProgram QuantumHistoryBitProgram

theorem value_iff (x : Input) : value x=true ↔
    ∀ i : Fin x.1, row x.2.2.2.2 (x.2.1+i.val) =
      if x.2.2.1=true ∧ x.2.1+i.val=x.2.2.2.1 then
        Equiv.swap (0:Fin 2) 1 (column x.2.2.2.2 (x.2.1+i.val))
      else column x.2.2.2.2 (x.2.1+i.val) := by
  simp only [value,List.all_map,List.all_eq_true,List.mem_range,
    Function.comp_apply,id_eq,point,decide_eq_true_eq]
  exact ⟨fun h i => h i.val i.isLt,fun h i hi => h ⟨i,hi⟩⟩

theorem no_flip_iff (count base target : ℕ) (d : Data) :
    value (count,base,false,target,d)=true ↔
      ∀ i : Fin count, row d (base+i.val)=column d (base+i.val) := by
  rw [value_iff]
  simp only [Bool.false_eq_true,false_and,ite_false, if_false]

theorem value_equiv_iff {ι : Type} {count : ℕ} (e : ι ≃ Fin count)
    (base target : ℕ) (d : Data) :
    value (count,base,false,target,d)=true ↔
      (fun i => row d (base+(e i).val))=(fun i => column d (base+(e i).val)) := by
  rw [no_flip_iff,funext_iff]
  constructor
  · intro h i
    exact h (e i)
  · intro h i
    obtain ⟨j,rfl⟩ := e.surjective i
    exact h j

theorem value_flip_iff {ι : Type} [DecidableEq ι] {count : ℕ} (e : ι ≃ Fin count)
    (base : ℕ) (q : ι) (d : Data) :
    value (count,base,true,base+(e q).val,d)=true ↔
      (fun i => row d (base+(e i).val))=
        qmaBitFlip q (fun i => column d (base+(e i).val)) := by
  rw [value_iff,funext_iff]
  have hv (i : ι) (hi : i≠q) : (e i).val≠(e q).val :=
    fun h => hi (e.injective (Fin.ext h))
  constructor
  · intro h i
    by_cases hi : i=q
    · subst i
      simpa [qmaBitFlip] using h (e q)
    · simpa [qmaBitFlip,hi,hv i hi] using h (e i)
  · intro h i
    obtain ⟨j,rfl⟩ := e.surjective i
    by_cases hj : j=q
    · subst j
      simpa [qmaBitFlip] using h q
    · simpa [qmaBitFlip,hj,hv j hj] using h j

end ContinuumCoulomb.QuantumHistoryComparison

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryDelta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact register evaluation of the propagation delta.  The equality scans
are bounded by the unary circuit size; every bit is read from the supplied
local support table. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDelta
open QuantumAlgebraicScalar QuantumHistoryDescriptors QuantumHistoryBitProgram
open QuantumHistoryDiagonal QuantumHistorySiteProgram

theorem qubitEquiv_val (c : QMACircuit) (q : QMACircuitQubit c) :
    (qubitEquiv c q).val=distributedNumber c q := by
  cases q <;> rfl

theorem readRow_eq (c : QMACircuit) (d : Data) (q : QMACircuitQubit c) :
    readRow c d q=row d (referenceWork c+1+(qubitEquiv c q).val) := by
  rw [qubitEquiv_val]
  exact congrArg (row d) (number_inr c q)

theorem readColumn_eq (c : QMACircuit) (d : Data) (q : QMACircuitQubit c) :
    readColumn c d q=column d (referenceWork c+1+(qubitEquiv c q).val) := by
  rw [qubitEquiv_val]
  exact congrArg (column d) (number_inr c q)

theorem guard_iff (c : QMACircuit) (t : Fin c.gates.length) (d : Data) :
    guard c t.val d=true ↔
      QMAClockGuard c.gates.length t (readRow c d ∘ Sum.inl) ∧
        readRow c d (.inl (qmaClockMiddle c.gates.length t))=0 := by
  have he : (clockRow c d t.val=1 ∧ clockRow c d (t.val+2)=0 ∧
      clockRow c d (t.val+1)=0) ↔
      QMAClockGuard c.gates.length t (readRow c d ∘ Sum.inl) ∧
        readRow c d (.inl (qmaClockMiddle c.gates.length t))=0 := by
    simp only [QMAClockGuard,Function.comp_apply,readRow,QuantumOrderedSupport.siteNumber,
      clockRow,referenceWork_eq,qmaClockLeft,qmaClockRight,qmaClockMiddle,and_assoc]
  exact ⟨fun h => he.mp (of_decide_eq_true h),fun h => decide_eq_true (he.mpr h)⟩

theorem flipped_iff (c : QMACircuit) (t : Fin c.gates.length) (d : Data) :
    flipped c t.val d=true ↔ readRow c d=
      qmaBitFlip (.inl (qmaClockMiddle c.gates.length t)) (readColumn c d) := by
  have h := QuantumHistoryComparison.value_flip_iff (qubitEquiv c)
    (referenceWork c+1) (.inl (qmaClockMiddle c.gates.length t)) d
  have he : (qubitEquiv c (.inl (qmaClockMiddle c.gates.length t))).val=t.val+1 := rfl
  change QuantumHistoryComparison.value
    (c.gates.length+2+(c.work+1),referenceWork c+1,true,referenceWork c+1+(t.val+1),d)=true ↔ _
  simpa only [he,← readRow_eq,← readColumn_eq] using h

theorem sameClock_iff (c : QMACircuit) (d : Data) :
    sameClock c d=true ↔ readRow c d ∘ Sum.inl=readColumn c d ∘ Sum.inl := by
  have h := QuantumHistoryComparison.value_equiv_iff
    (Equiv.refl (Fin (c.gates.length+2))) (referenceWork c+1) 0 d
  simpa only [sameClock,Equiv.refl_apply,readRow,readColumn,
    QuantumOrderedSupport.siteNumber,referenceWork_eq,Function.comp_def] using h

theorem gate_entry (c : QMACircuit) (t : ℕ) (d : Data) :
    QuantumGateEntryProgram.entry
      (c.work,referenceWork c+1+(c.gates.length+2),gateAt (c,t),d)=
      QuantumAlgebraicHistory.gate c.work (gateAt (c,t))
        (readRow c d ∘ Sum.inr) (readColumn c d ∘ Sum.inr) := by
  rw [QuantumGateEntryProgram.entry_eq]
  rfl

theorem entry_actual (c : QMACircuit) (t : Fin c.gates.length) (d : Data) :
    entry c t.val d=QuantumAlgebraicHistory.delta c t (readRow c d) (readColumn c d) := by
  unfold entry QuantumAlgebraicHistory.delta QuantumAlgebraicHistory.identity
  rw [gate_entry]
  simp only [flipped_iff c t d,sameClock_iff c d,gateAt]
  by_cases hg : guard c t.val d=true
  · have hh := (guard_iff c t d).mp hg
    simp only [hg,hh,and_self,ite_true, if_true]
  · have hh := mt (guard_iff c t d).mpr hg
    simp only [hg,hh,Bool.false_eq_true,ite_false, if_false]

end ContinuumCoulomb.QuantumHistoryDelta

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedLabelEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual padded history packets, followed by the literal local and
four-spin compiler, have total full-space error at most nine over N. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedLabelProgram
open QuantumPaddedHistory QuantumOrderedSourceIndex
open scoped Classical

theorem historyQubits_eq (c : QMACircuit) (hT : 0 < c.gates.length) (N : ℕ) :
    historyQubits c hT N=4*(qubitCount c+3717*termCount c) := by
  unfold historyQubits historyInput QuantumOrderedLabelCompile.qubitCount
  rw [QuantumOrderedLabelPipeline.output_qubits,sourceEntries_length]

end ContinuumCoulomb.QuantumPaddedLabelProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryFork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual history compiler produces a bounded loop-free exchange list.
Its initial subdivision and ordered fork rounds preserve the full-space
ground energy with the accumulated explicit error. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph QuantumRawExchange
open scoped BigOperators Classical

namespace QuantumPaddedLabelProgram
open QuantumPaddedHistory QuantumOrderedSourceIndex QuantumForkList

theorem history_valid (c : QMACircuit) (hT : 0 < c.gates.length) (N : ℕ)
    (b : MediatorListProgram.Bond) (hb : b ∈ (historyOutput c hT N).1) :
    b.1 < historyQubits c hT N ∧ b.2.1 < historyQubits c hT N ∧ b.1 ≠ b.2.1 := by
  let k := QuantumAlgebraicHistory.samplePrecision c N
  have hi : historyInput c hT N =
      (N,qubitCount c,QuantumOrderedLabelTable.table (sourceTerms c hT)
        (QuantumOrderedLabelTable.index (qubits c))
        (fun p : Term c => QuantumOrderedSupport.sites c hT p.1)
        (sourceWord c hT) (sampledWeight k c hT)) := by
    unfold historyInput
    rw [sourceEntries_table]
  unfold historyOutput at hb
  rw [hi] at hb
  have hv := QuantumOrderedLabelCompile.output_valid (qubits c) (sourceTerms c hT)
    (fun p : Term c => QuantumOrderedSupport.sites c hT p.1)
    (sourceWord c hT) (sampledWeight k c hT)
    (fun p => QuantumOrderedSupport.sites_length c hT p.1)
    (fun p => QuantumOrderedSupport.sites_nodup c hT p.1) N b hb
  simpa only [historyQubits,hi] using hv

theorem fork_accuracy (c : QMACircuit) (hT : 0 < c.gates.length)
    (N : ℕ) (hN : 0 < N) (D : ℕ) :
    |normalizedBottom (matrix (forkState c hT N D))-(qmaOrderedHistoryModel c hT).energy| ≤
      ((D:ℝ)+10)/(N:ℝ) := by
  have hb : SourceBondLists.bounded (historyQubits c hT N) (historyOutput c hT N).1 :=
    fun b hb => ⟨(history_valid c hT N b hb).1,(history_valid c hT N b hb).2.1⟩
  have hn : ∀ b ∈ (historyOutput c hT N).1, b.1 ≠ b.2.1 :=
    fun b hb => (history_valid c hT N b hb).2.2
  have he := initial_iterated_accuracy (historyQubits c hT N) (historyOutput c hT N).1
    hb hn (historyOutput c hT N).2 (N:ℚ) (by exact_mod_cast hN) D
  have hh := history_accuracy c hT N hN
  have he' : |normalizedBottom (matrix (forkState c hT N D))-
      normalizedBottom (rawMatrix (historyQubits c hT N) (historyOutput c hT N))| ≤
        ((D:ℝ)+1)/(N:ℝ) := by
    have hcast : ((N:ℚ):ℝ)=(N:ℝ) := by norm_cast
    rw [hcast] at he
    exact he
  exact (abs_sub_le _ _ _).trans ((add_le_add he' hh).trans_eq (by ring))

end QuantumPaddedLabelProgram
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistorySpatial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual sparse verifier history has a fixed-density, degree-three
spatial exchange output. Its energy is that of the literal fork compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatial
open QuantumPaddedHistory QuantumOrderedSourceIndex QuantumPaddedLabelProgram
open QuantumForkList
open scoped Classical

theorem input_state (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    (input c hc hT hne N).state=forkState (qmaSparseCircuit c) hT N historyDegree := by
  unfold SpatialInput.state forkState historyQubits historyOutput historyInput
  rw [sourceEntries_table]
  rfl

theorem model_energy (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    (model c hc hT hne N).energy =
      MediatorGraph.normalizedBottom (matrix (forkState (qmaSparseCircuit c) hT N historyDegree)) := by
  rw [model,SpatialInput.model_energy,input_state]

theorem model_history_error (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) (hN : 0 < N) :
    |(model c hc hT hne N).energy-(qmaOrderedHistoryModel (qmaSparseCircuit c) hT).energy| ≤
      ((historyDegree:ℝ)+10)/(N:ℝ) := by
  rw [model_energy]
  exact fork_accuracy (qmaSparseCircuit c) hT N hN historyDegree

end ContinuumCoulomb.QuantumHistorySpatial

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual sparse verifier compiler, through the specified planar lattice.
The final precision pays for every early and routing error; the scalar offset
is removed from both thresholds exactly. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatial
open QuantumPaddedLabelProgram QuantumForkList QuantumAlgebraicHistory
open scoped Classical

-- Keep the fixed density symbolic; expanding it as a numeral is unnecessary.
attribute [local irreducible] spatialDensity

theorem routeRounds_eq : QMASpatialExchangeModel.routeLengthBound
    (spatialDensity rawDensity historyDegree) (27*spatialDensity rawDensity historyDegree) =
      routeRounds := routeRoundValue.property

end ContinuumCoulomb.QuantumHistorySpatial

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryOutputBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coefficient envelopes for the actual sparse-history and degree-three
spatial output, preserving the exact numeric output order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatial
open QuantumPaddedLabelProgram QuantumPaddedHistory QuantumOrderedSourceIndex
open QuantumForkList
open scoped Classical

theorem input_bonds (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    (input c hc hT hne N).bonds=(historyOutput (qmaSparseCircuit c) hT N).1 := by
  unfold historyOutput historyInput
  rw [sourceEntries_table]
  rfl

theorem input_constant (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    (input c hc hT hne N).constant=(historyOutput (qmaSparseCircuit c) hT N).2 := by
  unfold historyOutput historyInput
  rw [sourceEntries_table]
  rfl

theorem input_n (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    (input c hc hT hne N).n=historyQubits (qmaSparseCircuit c) hT N := by
  unfold historyQubits historyInput
  rw [sourceEntries_table]
  rfl

end ContinuumCoulomb.QuantumHistorySpatial

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumScalarReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact reindexing of the four-rational local-core sums.  This lets the
literal support-list coordinates evaluate the propagation Gram matrix. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli
open scoped BigOperators

private theorem scalar_add_eq (x y : Scalar) : add x y=x+y := rfl
theorem scalar_sum_eq (xs : List Scalar) : QuantumAlgebraicScalar.sum xs=xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [QuantumAlgebraicScalar.sum,ih,List.sum_cons,scalar_add_eq]

theorem scalar_finiteSum_eq {α : Type} [Fintype α] (f : α → Scalar) :
    finiteSum f=∑ a,f a := by
  rw [finiteSum,scalar_sum_eq]
  simp only [enumerate,List.map_ofFn,List.sum_ofFn]
  exact (Fintype.equivFin α).symm.sum_comp f

theorem scalar_finiteSum_reindex {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → Scalar) :
    finiteSum (fun a => f (e a))=finiteSum f := by
  rw [scalar_finiteSum_eq,scalar_finiteSum_eq]
  exact e.sum_comp f

theorem matMul_reindex {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (A B : Matrix β β Scalar) :
    matMul (reindex e A) (reindex e B)=reindex e (matMul A B) := by
  funext s t
  exact scalar_finiteSum_reindex e (fun u => mul (A (e s) u) (B u (e t)))

theorem adjoint_reindex {α β : Type} (e : α ≃ β) (A : Matrix β β Scalar) :
    adjoint (reindex e A)=reindex e (adjoint A) := rfl

theorem gram_reindex {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (A : Matrix β β Scalar) :
    matMul (adjoint (reindex e A)) (reindex e A)=
      reindex e (matMul (adjoint A) A) := by
  rw [adjoint_reindex,matMul_reindex]

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPropagationSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal, duplicate-free five-site propagation support.  Lookup in its
encoded labels agrees with the zero extension used by the actual local core. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPropagationSupport
open QuantumHistoryBitProgram QuantumHistoryDiagonal QuantumOrderedSupport
open scoped Classical

theorem supportEquiv_apply (c : QMACircuit) (t : Fin c.gates.length)
    (i : Fin (sites c t).length) : (supportEquiv c t i).val=(sites c t).get i := rfl

theorem lookup_actual (c : QMACircuit) (t : Fin c.gates.length)
    (s : Fin (sites c t).length → Fin 2) (q : QMACircuitQubit c) :
    QuantumSupportLookup.value (siteNumber c (.inr q),labels c t,
      List.ofFn (fun i => (s i).val))=
      (qmaSupportExtend (qmaPropagationSites c t)
        (fun j => s ((supportEquiv c t).symm j)) q).val := by
  have hf : Function.Injective (fun q : QMACircuitQubit c => siteNumber c (.inr q)) := by
    intro a b h
    exact Sum.inr_injective (siteNumber_injective c h)
  by_cases hq : q∈qmaPropagationSites c t
  · let i := (supportEquiv c t).symm ⟨q,hq⟩
    have hi : (sites c t).get i=q :=
      congrArg Subtype.val ((supportEquiv c t).apply_symm_apply ⟨q,hq⟩)
    have he := QuantumSupportLookup.value_map_get (sites c t) (sites_nodup c t)
      (fun q => siteNumber c (.inr q)) hf (fun j => (s j).val) i
    have hv : QuantumSupportLookup.value (siteNumber c (.inr q),labels c t,
        List.ofFn (fun j => (s j).val))=(s i).val := by
      simpa only [hi,labels] using he
    exact hv.trans (congrArg Fin.val (show
      qmaSupportExtend (qmaPropagationSites c t)
        (fun j => s ((supportEquiv c t).symm j)) q=s i from dite_eq_left hq)).symm
  · have hn : siteNumber c (.inr q)∉labels c t := by
      intro h
      obtain ⟨p,hp,he⟩ := List.mem_map.mp h
      have hpq := hf he
      subst p
      exact hq (by rw [← sites_finset]; exact List.mem_toFinset.mpr hp)
    have he := QuantumSupportLookup.value_not_mem (labels c t)
      (List.ofFn (fun i => (s i).val)) (siteNumber c (.inr q)) hn
      (by simp only [List.length_ofFn,labels,List.length_map,le_refl])
    exact he.trans (congrArg Fin.val (show
      qmaSupportExtend (qmaPropagationSites c t)
        (fun j => s ((supportEquiv c t).symm j)) q=0 from dite_eq_right hq)).symm

theorem readRow_actual (c : QMACircuit) (t : Fin c.gates.length)
    (s r : Fin (sites c t).length → Fin 2) :
    readRow c (data c t s r)=qmaSupportExtend (qmaPropagationSites c t)
      (fun j => s ((supportEquiv c t).symm j)) := by
  funext q
  apply Fin.ext
  change QuantumSupportLookup.value _ % 2 = _
  dsimp only [data]
  rw [lookup_actual]
  exact Nat.mod_eq_of_lt (Fin.isLt _)

theorem readColumn_actual (c : QMACircuit) (t : Fin c.gates.length)
    (s r : Fin (sites c t).length → Fin 2) :
    readColumn c (data c t s r)=qmaSupportExtend (qmaPropagationSites c t)
      (fun j => r ((supportEquiv c t).symm j)) := by
  funext q
  apply Fin.ext
  change QuantumSupportLookup.value _ % 2 = _
  dsimp only [data]
  rw [lookup_actual]
  exact Nat.mod_eq_of_lt (Fin.isLt _)

end ContinuumCoulomb.QuantumPropagationSupport

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPropagationTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact fixed-size propagation tables and their adjoint-product.  The
largest table has five qubits, independently of the circuit work register. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPropagationTable
open ExactQuantumFactoring.BitStackProgram QuantumAlgebraicScalar QuantumFixedPauli
open QuantumAlgebraicHistory QuantumCircuitCode
open scoped Classical

theorem table_actual (c : QMACircuit) (t : Fin c.gates.length) :
    table (QuantumPropagationSupport.sites c t).length
      (c,t.val,QuantumPropagationSupport.labels c t)=
      reindex (supportBasisEquiv c t) (deltaCore c t) := by
  funext s r
  change QuantumHistoryDelta.entry c t.val (QuantumPropagationSupport.data c t s r)=_
  rw [QuantumHistoryDelta.entry_actual,QuantumPropagationSupport.readRow_actual,
    QuantumPropagationSupport.readColumn_actual]
  rfl

theorem gram_actual (c : QMACircuit) (t : Fin c.gates.length) :
    matMul (adjoint (table (QuantumPropagationSupport.sites c t).length
      (c,t.val,QuantumPropagationSupport.labels c t)))
      (table (QuantumPropagationSupport.sites c t).length
        (c,t.val,QuantumPropagationSupport.labels c t))=
      reindex (supportBasisEquiv c t) (propagationCore c t) := by
  rw [table_actual,gram_reindex]
  rfl

end ContinuumCoulomb.QuantumPropagationTable

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumScalarFaithful
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The four rational registers faithfully represent their complex value.
This permits exact local-table identities to reuse the established complex
matrix identities, without changing the arithmetic program. -/

namespace ContinuumCoulomb.QuantumAlgebraicScalar

theorem sqrtHalf_irrational : Irrational (Real.sqrt (1/2 : ℝ)) := by
  rw [Real.sqrt_div (by norm_num : (0:ℝ)≤1),Real.sqrt_one,one_div]
  exact irrational_sqrt_two.inv

theorem realValue_injective : Function.Injective realValue := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have hb : b=d := by
    by_contra hbd
    have hi := (sqrtHalf_irrational.ratCast_mul (sub_ne_zero.mpr hbd)).ratCast_add (a-c)
    have hz : ((a-c : ℚ) : ℝ)+((b-d : ℚ) : ℝ)*Real.sqrt (1/2 : ℝ)=0 := by
      dsimp only [realValue] at h
      push_cast
      nlinarith [h]
    rw [hz] at hi
    exact not_irrational_zero hi
  have ha : a=c := by
    subst d
    have he : (a:ℝ)=(c:ℝ) := by
      dsimp only [realValue] at h
      linarith
    exact_mod_cast he
  exact Prod.ext ha hb

theorem value_injective : Function.Injective value := by
  intro x y h
  apply Prod.ext
  · apply realValue_injective
    simpa only [value_re] using congrArg Complex.re h
  · apply realValue_injective
    simpa only [value_im] using congrArg Complex.im h

end ContinuumCoulomb.QuantumAlgebraicScalar

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRebitLocal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_conj _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_neg _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact scalar core of a lifted term with one active reference qubit.
Spectator reference bits are zero in the local core and contribute identities. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli
open scoped Classical BigOperators

theorem referenceState_eq_iff (n : ℕ) (i : Fin n) (a b : Fin 2) :
    referenceState n i a=referenceState n i b ↔ a=b := by
  constructor
  · intro h
    simpa only [referenceState,ite_true, if_true] using congrFun h i
  · rintro rfl
    rfl

theorem reference_identity (n : ℕ) (i : Fin n) (a b : Fin 2) :
    identity (referenceState n i a) (referenceState n i b)=identity a b := by
  simp only [identity,referenceState_eq_iff]

theorem localY_referenceState (n : ℕ) (i : Fin n) (a b : Fin 2) :
    localY n i (referenceState n i a) (referenceState n i b)=
      QuantumFixedPauli.pauli 2 a b := by
  apply value_injective
  rw [value_localY,value_pauli]
  change sourceLocalPauli n i 1 (referenceState n i a) (referenceState n i b)=
    ContinuumCoulomb.pauli 1 a b
  unfold sourceLocalPauli sourceTensor
  rw [Finset.prod_eq_single i]
  · simp only [ite_true, if_true,referenceState,ite_true]
  · intro j _ hji
    simp only [hji,ite_false, if_false,referenceState,Matrix.one_apply,ite_true, if_true]
  · simp

theorem lift_extend {ι : Type} [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (A : Matrix (QMASupportBasis S) (QMASupportBasis S) Scalar)
    (u v : QMASupportBasis S) :
    lift S A (qmaSupportExtend S u) (qmaSupportExtend S v)=A u v := by
  have hu : (fun j : {j // j∈S} => qmaSupportExtend S u j.val)=u := by
    funext j
    exact dite_eq_left j.property
  have hv : (fun j : {j // j∈S} => qmaSupportExtend S v j.val)=v := by
    funext j
    exact dite_eq_left j.property
  have he : (fun j : {j // j∉S} => qmaSupportExtend S u j.val)=
      (fun j : {j // j∉S} => qmaSupportExtend S v j.val) := by
    funext j
    have hu0 : qmaSupportExtend S u j.val=0 := dite_eq_right j.property
    have hv0 : qmaSupportExtend S v j.val=0 := dite_eq_right j.property
    exact hu0.trans hv0.symm
  simp only [lift,hu,hv,identity,ite_eq_left he]
  apply value_injective
  simp only [value_mul,value_rat,Rat.cast_one,mul_one]

theorem rebit_entry_of_references {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (i : Fin n) (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar)
    (s t : Fin n ⊕ ι → Fin 2) (a b : Fin 2)
    (hs : s ∘ Sum.inl=referenceState n i a)
    (ht : t ∘ Sum.inl=referenceState n i b) :
    rebit n i A s t=oneReference a b (A (s ∘ Sum.inr) (t ∘ Sum.inr)) := by
  simp only [rebit,hs,ht,reference_identity,localY_referenceState,oneReference]

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPropagationOrder
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual ordered support has its reference bit first, followed by
the duplicate-free propagation support in its literal source order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPropagationOrder
open QuantumOrderedSupport
open scoped Classical

theorem firstIndex_site (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t) :
    (supportEquiv c hT (.inl i) (firstIndex c hT i t ht)).val=.inl i := by
  rw [supportEquiv_apply]
  change (sites c hT (.inl i))[0]'(firstIndex c hT i t ht).isLt=_
  simp only [sites_eq c hT i t ht,List.getElem_cons_zero]

theorem nextIndex_site (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t)
    (j : Fin (QuantumPropagationSupport.sites c t).length) :
    (supportEquiv c hT (.inl i) (nextIndex c hT i t ht j)).val=
      .inr (QuantumPropagationSupport.supportEquiv c t j).val := by
  rw [supportEquiv_apply,QuantumPropagationSupport.supportEquiv_apply]
  change (sites c hT (.inl i))[j.val+1]'(nextIndex c hT i t ht j).isLt=_
  simp only [sites_eq c hT i t ht,List.getElem_cons_succ,List.getElem_map,
    List.get_eq_getElem]

theorem extend_reference (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t)
    (s : Fin (sites c hT (.inl i)).length → Fin 2) :
    QuantumHistoryDiagonal.orderedExtend c hT (.inl i) s ∘ Sum.inl=
      QuantumAlgebraicHistory.referenceState (qmaHistoryReferenceWork c+1) i
        (referenceBit c hT i t ht s) := by
  funext j
  by_cases hj : j=i
  · subst j
    have he := QuantumHistoryDiagonal.orderedExtend_at c hT (.inl i) s
      (firstIndex c hT i t ht)
    rw [firstIndex_site c hT i t ht] at he
    simpa [QuantumAlgebraicHistory.referenceState,referenceBit] using he
  · have hn : Sum.inl j ∉ (qmaOrderedHistoryModel c hT).sites (.inl i) := by
      intro hm
      rw [← rawSites_finset] at hm
      have hl := List.mem_toFinset.mp hm
      change Sum.inl j ∈ Sum.inl i :: _ at hl
      rcases List.mem_cons.mp hl with he | he
      · exact hj (Sum.inl_injective he)
      · obtain ⟨q,_,he⟩ := List.mem_map.mp he
        cases he
    have hz : QuantumHistoryDiagonal.orderedExtend c hT (.inl i) s (.inl j)=0 :=
      dite_eq_right hn
    simpa only [Function.comp_apply,QuantumAlgebraicHistory.referenceState,
      ite_eq_right hj] using hz

theorem extend_data (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t)
    (s : Fin (sites c hT (.inl i)).length → Fin 2) :
    QuantumHistoryDiagonal.orderedExtend c hT (.inl i) s ∘ Sum.inr=
      qmaSupportExtend (qmaPropagationSites c t)
        (fun q => localBits c hT i t ht s ((QuantumPropagationSupport.supportEquiv c t).symm q)) := by
  funext q
  by_cases hq : q∈qmaPropagationSites c t
  · let j := (QuantumPropagationSupport.supportEquiv c t).symm ⟨q,hq⟩
    have hj : (QuantumPropagationSupport.supportEquiv c t j).val=q :=
      congrArg Subtype.val ((QuantumPropagationSupport.supportEquiv c t).apply_symm_apply ⟨q,hq⟩)
    have he := QuantumHistoryDiagonal.orderedExtend_at c hT (.inl i) s
      (nextIndex c hT i t ht j)
    rw [nextIndex_site c hT i t ht,hj] at he
    exact he.trans (show qmaSupportExtend (qmaPropagationSites c t)
      (fun q => localBits c hT i t ht s ((QuantumPropagationSupport.supportEquiv c t).symm q)) q=
      s (nextIndex c hT i t ht j) from dite_eq_left hq).symm
  · have hn : Sum.inr q ∉ (qmaOrderedHistoryModel c hT).sites (.inl i) := by
      intro hm
      have hl : Sum.inr q ∈ (sites c hT (.inl i)).toFinset := by
        rw [sites_finset]
        exact hm
      have hx := List.mem_toFinset.mp hl
      rw [sites_eq c hT i t ht] at hx
      rcases List.mem_cons.mp hx with he | he
      · cases he
      · obtain ⟨r,hr,he⟩ := List.mem_map.mp he
        have hrq : r=q := Sum.inr_injective he
        subst r
        apply hq
        rw [← QuantumPropagationSupport.sites_finset]
        exact List.mem_toFinset.mpr hr
    have hz : qmaSupportExtend (qmaPropagationSites c t)
        (fun q => localBits c hT i t ht s ((QuantumPropagationSupport.supportEquiv c t).symm q)) q=0 :=
      dite_eq_right hq
    exact (show QuantumHistoryDiagonal.orderedExtend c hT (.inl i) s (.inr q)=0 from
      dite_eq_right hn).trans hz.symm

theorem ordered_entry (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t)
    (s r : Fin (sites c hT (.inl i)).length → Fin 2) :
    QuantumAlgebraicHistory.orderedTable c hT (.inl i) s r=
      QuantumAlgebraicHistory.oneReference
        (referenceBit c hT i t ht s) (referenceBit c hT i t ht r)
        (QuantumAlgebraicScalar.mul
          (QuantumAlgebraicScalar.rat ((14*(c.work+1)+8)*c.gates.length : ℚ))
          (QuantumAlgebraicHistory.propagationCore c t
            (fun q => localBits c hT i t ht s ((QuantumPropagationSupport.supportEquiv c t).symm q))
            (fun q => localBits c hT i t ht r ((QuantumPropagationSupport.supportEquiv c t).symm q)))) := by
  let S := QuantumHistoryDiagonal.orderedExtend c hT (.inl i) s
  let R := QuantumHistoryDiagonal.orderedExtend c hT (.inl i) r
  change QuantumAlgebraicHistory.rebit (qmaHistoryReferenceWork c+1) i
    (QuantumAlgebraicHistory.distributed c (qmaFirstUseTime c)
      (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i)) S R=_
  rw [QuantumAlgebraicHistory.rebit_entry_of_references _ _ _ _ _ _ _
    (extend_reference c hT i t ht s) (extend_reference c hT i t ht r)]
  rw [ht]
  change QuantumAlgebraicHistory.oneReference _ _
    (QuantumAlgebraicScalar.mul _ (QuantumAlgebraicHistory.lift _ _
      (S ∘ Sum.inr) (R ∘ Sum.inr)))=_
  have hs := extend_data c hT i t ht s
  have hr := extend_data c hT i t ht r
  change S ∘ Sum.inr=_ at hs
  change R ∘ Sum.inr=_ at hr
  rw [hs,hr,QuantumAlgebraicHistory.lift_extend]

theorem ordered_gram_entry (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t)
    (s r : Fin (sites c hT (.inl i)).length → Fin 2) :
    QuantumAlgebraicHistory.orderedTable c hT (.inl i) s r=
      QuantumAlgebraicHistory.oneReference
        (referenceBit c hT i t ht s) (referenceBit c hT i t ht r)
        (QuantumAlgebraicScalar.mul
          (QuantumAlgebraicScalar.rat ((14*(c.work+1)+8)*c.gates.length : ℚ))
          (QuantumAlgebraicHistory.matMul
            (QuantumAlgebraicHistory.adjoint
              (QuantumPropagationTable.table (QuantumPropagationSupport.sites c t).length
                (c,t.val,QuantumPropagationSupport.labels c t)))
            (QuantumPropagationTable.table (QuantumPropagationSupport.sites c t).length
              (c,t.val,QuantumPropagationSupport.labels c t))
            (localBits c hT i t ht s) (localBits c hT i t ht r))) := by
  rw [ordered_entry c hT i t ht]
  have hg := congrFun (congrFun (QuantumPropagationTable.gram_actual c t)
    (localBits c hT i t ht s)) (localBits c hT i t ht r)
  exact congrArg (fun z => QuantumAlgebraicHistory.oneReference
    (referenceBit c hT i t ht s) (referenceBit c hT i t ht r)
    (QuantumAlgebraicScalar.mul
      (QuantumAlgebraicScalar.rat ((14*(c.work+1)+8)*c.gates.length : ℚ)) z)) hg.symm

end ContinuumCoulomb.QuantumPropagationOrder

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPropagationSampler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal local propagation tables after adding the single reference bit.
The arity is fixed in each program; no ambient spin configurations are scanned. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPropagationSampler
open QuantumAlgebraicScalar QuantumAlgebraicHistory QuantumFixedPauli
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode
open scoped Classical

theorem matrixData_cast {n m : ℕ} (h : n=m)
    (A : Matrix (Fin m → Fin 2) (Fin m → Fin 2) Scalar) :
    matrixData (reindex ((finCongr h).arrowCongr (Equiv.refl (Fin 2))) A)=matrixData A := by
  subst m
  rfl

theorem basisEquiv_zero (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=QuantumPropagationOrder.term c t)
    (s : Fin (QuantumOrderedSupport.sites c hT (.inl i)).length → Fin 2) :
    basisEquiv c hT i t ht s 0=QuantumPropagationOrder.referenceBit c hT i t ht s := by
  rfl

theorem basisEquiv_succ (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=QuantumPropagationOrder.term c t)
    (s : Fin (QuantumOrderedSupport.sites c hT (.inl i)).length → Fin 2) :
    (fun j => basisEquiv c hT i t ht s j.succ)=
      QuantumPropagationOrder.localBits c hT i t ht s := by
  rfl

theorem table_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=QuantumPropagationOrder.term c t) :
    QuantumAlgebraicHistory.orderedTable c hT (.inl i)=
      reindex (basisEquiv c hT i t ht)
        (table (QuantumPropagationSupport.sites c t).length
          (c,t.val,QuantumPropagationSupport.labels c t)) := by
  funext s r
  rw [QuantumPropagationOrder.ordered_gram_entry c hT i t ht]
  simp only [reindex,table,basisEquiv_zero,basisEquiv_succ,coefficient]

theorem tableList_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=QuantumPropagationOrder.term c t) :
    tableList (QuantumOrderedSupport.sites c hT (.inl i)).length
        (c,t.val,QuantumPropagationSupport.labels c t)=
      matrixData (QuantumAlgebraicHistory.orderedTable c hT (.inl i)) := by
  calc
    _ = tableList ((QuantumPropagationSupport.sites c t).length+1)
        (c,t.val,QuantumPropagationSupport.labels c t) :=
      congrArg (fun n => tableList n (c,t.val,QuantumPropagationSupport.labels c t))
        (QuantumPropagationOrder.length_eq c hT i t ht)
    _ = matrixData (table (QuantumPropagationSupport.sites c t).length
        (c,t.val,QuantumPropagationSupport.labels c t)) := rfl
    _ = _ := (matrixData_cast (QuantumPropagationOrder.length_eq c hT i t ht) _).symm.trans
      (congrArg matrixData (table_actual c hT i t ht).symm)

end ContinuumCoulomb.QuantumPropagationSampler

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceEdgeTable
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_conj _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_neg _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_rat _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact local tables for the reference-chain edges.  Their only nontrivial
entry is the fixed two-spin expression (I-Y tensor Y)/2. -/

noncomputable section
namespace ContinuumCoulomb.QuantumReferenceEdgeTable
open QuantumAlgebraicScalar QuantumAlgebraicHistory QuantumHistoryDiagonal
open QuantumHistoryBitProgram QuantumFixedPauli
open ExactQuantumFactoring.BitStackProgram
open scoped Classical

theorem inactive (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c))
    (s : Fin (QuantumOrderedSupport.sites c hT (.inr i)).length → Fin 2)
    (q : QuantumOrderedSupport.Qubit c)
    (hq : q≠.inl i.castSucc ∧ q≠.inl i.succ) :
    orderedExtend c hT (.inr i) s q=0 := by
  have hn : q∉(qmaOrderedHistoryModel c hT).sites (.inr i) := by
    change q∉{Sum.inl i.castSucc,Sum.inl i.succ}
    intro hm
    rcases Finset.mem_insert.mp hm with h | h
    · exact hq.1 h
    · exact hq.2 (Finset.mem_singleton.mp h)
  exact dite_eq_right hn

theorem ordered_entry (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c))
    (s t : Fin (QuantumOrderedSupport.sites c hT (.inr i)).length → Fin 2) :
    orderedTable c hT (.inr i) s t=
      table (QuantumOrderedSupport.sites c hT (.inr i)).length
        (i.val,QuantumOrderedSupport.encodedSites c hT (.inr i)) s t := by
  let S := orderedExtend c hT (.inr i) s
  let T := orderedExtend c hT (.inr i) t
  have hd : S ∘ Sum.inr=T ∘ Sum.inr := by
    funext q
    exact (inactive c hT i s (.inr q) (by simp)).trans
      (inactive c hT i t (.inr q) (by simp)).symm
  have hr : S ∘ Sum.inl=T ∘ Sum.inl ↔ s=t := by
    constructor
    · intro h
      apply orderedExtend_injective c hT (.inr i)
      funext q
      cases q with
      | inl j => exact congrFun h j
      | inr j => exact congrFun hd j
    · rintro rfl
      rfl
  have hs : ∀ k, k≠i.castSucc → k≠i.succ → S (.inl k)=T (.inl k) := by
    intro k hk hl
    exact (inactive c hT i s (.inl k) (by simpa only [ne_eq,Sum.inl.injEq] using And.intro hk hl)).trans
      (inactive c hT i t (.inl k) (by simpa only [ne_eq,Sum.inl.injEq] using And.intro hk hl)).symm
  have hb (u : Fin (QuantumOrderedSupport.sites c hT (.inr i)).length → Fin 2)
      (v : Fin (QuantumOrderedSupport.sites c hT (.inr i)).length → Fin 2)
      (j : Fin (qmaHistoryReferenceWork c+1)) :
      row (data _ u v (i.val,QuantumOrderedSupport.encodedSites c hT (.inr i))) j.val=
        orderedExtend c hT (.inr i) u (.inl j) :=
    QuantumHistoryBitProgram.row_actual c hT (.inr i) u v (.inl j)
  have hc (j : Fin (qmaHistoryReferenceWork c+1)) :
      column (data _ s t (i.val,QuantumOrderedSupport.encodedSites c hT (.inr i))) j.val=
        T (.inl j) :=
    QuantumHistoryBitProgram.column_actual c hT (.inr i) s t (.inl j)
  change referenceEdge (qmaHistoryReferenceWork c) i S T=_
  unfold referenceEdge pairY
  simp only [identity,hd,hr,Function.comp_apply,ite_true, if_true]
  rw [ite_eq_left hs]
  unfold table
  have hbl := hb s t i.castSucc
  have hbr := hb s t i.succ
  have hcl := hc i.castSucc
  have hcr := hc i.succ
  simp only [Fin.val_castSucc,Fin.val_succ] at hbl hbr hcl hcr
  dsimp only [Prod.fst]
  rw [hbl,hcl,hbr,hcr]
  apply value_injective
  simp only [identity,value_mul,value_sub,value_rat,Rat.cast_one,mul_one]
  rfl

theorem table_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c)) :
    table (QuantumOrderedSupport.sites c hT (.inr i)).length
        (i.val,QuantumOrderedSupport.encodedSites c hT (.inr i))=
      orderedTable c hT (.inr i) := by
  funext s t
  exact (ordered_entry c hT i s t).symm

end ContinuumCoulomb.QuantumReferenceEdgeTable

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryTableProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_conj _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_neg _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Total local-table dispatcher for the literal history order.  Its seven
arity templates are fixed; only descriptor and short-label reads vary. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryTableProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode QuantumHistoryDescriptors
open QuantumAlgebraicScalar QuantumFixedPauli
open scoped Classical

theorem table_eq (x : Input) (h : x.2.2.length≤6) : table x=localTable x.2.2.length x := by
  generalize hn : x.2.2.length=n at *
  interval_cases n <;> simp only [table,hn] <;> norm_num

end ContinuumCoulomb.QuantumHistoryTableProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryTableCorrectness
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The total table dispatcher agrees with the actual ordered history core,
including its canonical finite enumeration. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryTableProgram
open QuantumHistoryDescriptors QuantumAlgebraicScalar QuantumFixedPauli
open scoped Classical

theorem nondiagonal_term (c : QMACircuit) (a : QMACircuitTerm c)
    (ha : ¬(encode c a).1<4) :
    ∃ t : Fin c.gates.length, a=QuantumPropagationOrder.term c t := by
  rcases a with i | (b | (i | (u | t)))
  · norm_num [encode] at ha
  · norm_num [encode] at ha
  · norm_num [encode] at ha
  · norm_num [encode] at ha
  · exact ⟨t,rfl⟩

theorem propagationLabels_tail (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=QuantumPropagationOrder.term c t) :
    (QuantumOrderedSupport.encodedSites c hT (.inl i)).tail=
      QuantumPropagationSupport.labels c t := by
  simp only [QuantumOrderedSupport.encodedSites,QuantumPropagationOrder.sites_eq c hT i t ht,
    List.map_cons,List.tail_cons,List.map_map,Function.comp_def,QuantumPropagationSupport.labels]

theorem localTable_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    localTable (QuantumOrderedSupport.sites c hT a).length
      (c,((QuantumOrderedSourceIndex.reference c).symm a).val,
        QuantumOrderedSupport.encodedSites c hT a)=
      matrixData (QuantumAlgebraicHistory.orderedTable c hT a) := by
  cases a with
  | inl i =>
    change localTable (QuantumOrderedSupport.sites c hT (.inl i)).length
      (c,i.val,QuantumOrderedSupport.encodedSites c hT (.inl i))=_
    have hi : i.val < referenceWork c+1 := i.isLt
    simp only [localTable,hi,ite_true, if_true,orderedAt_actual c hT i]
    by_cases ha : (encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i)).1<4
    · rw [ite_eq_left ha]
      exact QuantumHistoryDiagonal.tableList_actual c hT i ha
    · rw [ite_eq_right ha]
      obtain ⟨t,ht⟩ := nondiagonal_term c
        (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i) ha
      rw [ht,propagationLabels_tail c hT i t ht]
      exact QuantumPropagationSampler.tableList_actual c hT i t ht
  | inr i =>
    change localTable (QuantumOrderedSupport.sites c hT (.inr i)).length
      (c,qmaHistoryReferenceWork c+1+i.val,QuantumOrderedSupport.encodedSites c hT (.inr i))=_
    have hi : ¬qmaHistoryReferenceWork c+1+i.val<qmaHistoryReferenceWork c+1 := by
      omega
    simp only [localTable,referenceWork_eq,hi,ite_false, if_false,Nat.add_sub_cancel_left]
    exact congrArg matrixData (QuantumReferenceEdgeTable.table_actual c hT i)

theorem table_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    table (c,((QuantumOrderedSourceIndex.reference c).symm a).val,
        QuantumOrderedSupport.encodedSites c hT a)=
      matrixData (QuantumAlgebraicHistory.orderedTable c hT a) := by
  rw [table_eq _ (by
    simpa only [QuantumOrderedSupport.encodedSites,List.length_map] using
      QuantumOrderedSupport.sites_length c hT a)]
  simpa only [QuantumOrderedSupport.encodedSites,List.length_map] using localTable_actual c hT a

end ContinuumCoulomb.QuantumHistoryTableProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistorySamplerProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial generation of all sampled history packets.  The
runtime list is indexed by the unary number of source terms, not Hilbert-space
dimension; each local matrix uses one of seven fixed arity programs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySamplerProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode QuantumHistoryDescriptors
open QuantumAlgebraicScalar QuantumFixedPauli
open scoped Classical

attribute [local instance] OAI.ContinuumCoulomb.QuantumHistorySamplerProgram.finDecision
private theorem matrixData_instances {β : Type} (F G : Fintype β)
    (A : Matrix β β Scalar) : @matrixData β F A=@matrixData β G A := by
  cases Subsingleton.elim F G
  rfl

private theorem pair_matrixData_instances {β : Type} (F G : Fintype β)
    (A : Matrix β β Scalar) (xs : List ℕ) :
    (xs,@matrixData β F A)=(xs,@matrixData β G A) :=
  congrArg (fun ys : List Scalar => (xs,ys)) (matrixData_instances F G A)

theorem packet_actual (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (QuantumOrderedSourceIndex.referenceCount c)) :
    packet (k,c) i.val=QuantumPaddedLabelProgram.uniformPacket
      (QuantumPaddedLabelProgram.sourceInput k c hT (QuantumOrderedSourceIndex.reference c i)) := by
  let a := QuantumOrderedSourceIndex.reference c i
  have hi : ((QuantumOrderedSourceIndex.reference c).symm a).val=i.val :=
    congrArg Fin.val ((QuantumOrderedSourceIndex.reference c).symm_apply_apply i)
  have hl := supportLabels_actual c hT a
  rw [hi] at hl
  have hm := QuantumHistoryTableProgram.table_actual c hT a
  rw [hi] at hm
  have hp : (supportLabels c i.val,
      QuantumHistoryTableProgram.table (c,i.val,supportLabels c i.val))=
      (QuantumOrderedSupport.encodedSites c hT a,
        matrixData (QuantumAlgebraicHistory.orderedTable c hT a)) := by
    rw [hl,hm]
    exact pair_matrixData_instances
      (β := Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2) _ _
      (QuantumAlgebraicHistory.orderedTable c hT a) (QuantumOrderedSupport.encodedSites c hT a)
  change QuantumPaddedLabelProgram.uniformPacket (k,
      (supportLabels c i.val,QuantumHistoryTableProgram.table (c,i.val,supportLabels c i.val)))=
    QuantumPaddedLabelProgram.uniformPacket (k,
      (QuantumOrderedSupport.encodedSites c hT a,
        matrixData (QuantumAlgebraicHistory.orderedTable c hT a)))
  exact congrArg (fun p => QuantumPaddedLabelProgram.uniformPacket (k,p)) hp

theorem entries_actual (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length) :
    entries (k,c)=QuantumPaddedLabelProgram.sourceEntries k c hT := by
  unfold entries QuantumPaddedLabelProgram.sourceEntries
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  exact packet_actual k c hT i

end ContinuumCoulomb.QuantumHistorySamplerProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryPrecisionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prescribed sampling precision is computed in unary.  Composition
with the checked local sampler yields the actual early raw exchange compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryPrecisionProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode QuantumAlgebraicHistory

theorem prepare_actual (N : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length) :
    prepare (N,c)=QuantumPaddedLabelProgram.historyInput c hT N := by
  change (N,QuantumOrderedSourceIndex.qubitCount c,
      QuantumHistorySamplerProgram.entries (samplePrecision c N,c))=
    (N,QuantumOrderedSourceIndex.qubitCount c,
      QuantumPaddedLabelProgram.sourceEntries (samplePrecision c N) c hT)
  rw [QuantumHistorySamplerProgram.entries_actual _ c hT]

theorem output_actual (N : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length) :
    output (N,c)=QuantumPaddedLabelProgram.historyOutput c hT N :=
  congrArg QuantumOrderedLabelCompile.output (prepare_actual N c hT)

theorem physicalQubits_actual (N : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length) :
    physicalQubits (N,c)=QuantumPaddedLabelProgram.historyQubits c hT N :=
  congrArg QuantumOrderedLabelCompile.qubitCount (prepare_actual N c hT)

end ContinuumCoulomb.QuantumHistoryPrecisionProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedRawCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The raw four-spin compiler repeats each computed logical cell four times,
in exactly the order of its physical spin indices. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedRawCells
open QuantumOrderedCellProgram QuantumOrderedCellTable QuantumOrderedSpatialComplete
open QuantumOrderedLabelTable QuantumRouteCode
open ExactQuantumFactoring.BitStackProgram

theorem four_ofFn {n : ℕ} (cell : Fin n → Pair) :
    anchors 4 (List.ofFn cell)=
      List.ofFn (fun i : Fin (n*4) => cell (finProdFinEquiv.symm i).1) := by
  rw [anchors_ofFn,← product_table (fun p : Fin n × Fin 4 => cell p.1)]

theorem value_table {ι κ : Type} {n m : ℕ} (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (cell : ι → Pair) (anchor : κ → Pair) :
    value (table q e cell anchor)=
      List.ofFn (fun i : Fin (finalCount n m*4) =>
        cell6 cell anchor (qubits6 q e (finProdFinEquiv.symm i).1)) := by
  unfold value
  rw [complete_table]
  exact four_ofFn _

end ContinuumCoulomb.QuantumOrderedRawCells

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryRawCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The computed cell array has the exact physical-spin order of the raw
history compiler, including all six mediator layers and the four-spin blocks. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryCells
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode QuantumOrderedSourceIndex
open QuantumOrderedLabelTable QuantumOrderedSpatialComplete

theorem map_cell6 {ι κ C D : Type} (f : C → D) (cell : ι → C) (anchor : κ → C) :
    cell6 (f ∘ cell) (f ∘ anchor)=f ∘ cell6 cell anchor := by
  funext q
  rcases q with q | q
  · rcases q with q | q
    · rcases q with q | q
      · rcases q with q | q
        · rcases q with q | q
          · rcases q with q | q <;> rfl
          · rfl
        · rfl
      · rfl
    · rfl
  · rfl

theorem rawCells_actual (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length) :
    rawCells c=List.ofFn (fun i : Fin
      (finalCount (qubitCount (qmaSparseCircuit c))
        (referenceCount (qmaSparseCircuit c)*patternCount)*4) =>
      encodeCell (QuantumOrderedOutputSpatial.physicalCell
        (qubits (qmaSparseCircuit c))
        (QuantumPaddedLabelProgram.sourceTerms (qmaSparseCircuit c) hT)
        (qmaOrderedQubitCell c hT) (fun p => qmaOrderedTermCell c hT p.1) i.val)) := by
  rw [rawCells,value_actual c hT,QuantumOrderedRawCells.value_table]
  apply congrArg List.ofFn
  funext i
  rw [QuantumOrderedOutputSpatial.physicalCell,
    QuantumRawCellLocality.blockCell_fin]
  change cell6 (encodeCell ∘ qmaOrderedQubitCell c hT)
      (encodeCell ∘ (fun p => qmaOrderedTermCell c hT p.1))
      (qubits6 (qubits (qmaSparseCircuit c))
        (QuantumPaddedLabelProgram.sourceTerms (qmaSparseCircuit c) hT)
        (finProdFinEquiv.symm i).1)=_
  rw [map_cell6]
  simp only [Function.comp_apply,QuantumOrderedOutputSpatial.logicalCell,qmaFourBlockCell]

theorem rawCells_length (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length) (N : ℕ) :
    (rawCells c).length=QuantumPaddedLabelProgram.historyQubits
      (qmaSparseCircuit c) hT N := by
  rw [rawCells_actual c hT,List.length_ofFn,
    QuantumPaddedLabelProgram.historyQubits_eq,finalCount_eq]
  simp only [termCount]
  omega

theorem rawCells_get (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length) (j : ℕ)
    (hj : j<(rawCells c).length) :
    (rawCells c)[j]=encodeCell (QuantumOrderedOutputSpatial.physicalCell
      (qubits (qmaSparseCircuit c))
      (QuantumPaddedLabelProgram.sourceTerms (qmaSparseCircuit c) hT)
      (qmaOrderedQubitCell c hT) (fun p => qmaOrderedTermCell c hT p.1) j) := by
  simp only [rawCells_actual c hT,List.getElem_ofFn]

theorem input_cell (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates≠[]) (N j : ℕ) :
    (QuantumHistorySpatial.input c hc hT hne N).cell j=
      QuantumOrderedOutputSpatial.physicalCell (qubits (qmaSparseCircuit c))
        (QuantumPaddedLabelProgram.sourceTerms (qmaSparseCircuit c) hT)
        (qmaOrderedQubitCell c hT) (fun p => qmaOrderedTermCell c hT p.1) j := by
  simp only [QuantumHistorySpatial.input,QuantumOrderedOutputSpatial.input,id]

theorem rawCells_input_length (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates≠[]) (N : ℕ) :
    (rawCells c).length=(QuantumHistorySpatial.input c hc hT hne N).n := by
  rw [QuantumHistorySpatial.input_n]
  exact rawCells_length c hT N

theorem rawCells_input_get (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates≠[]) (N j : ℕ)
    (hj : j<(rawCells c).length) :
    (rawCells c)[j]=encodeCell ((QuantumHistorySpatial.input c hc hT hne N).cell j) := by
  rw [input_cell]
  exact rawCells_get c hT j hj

end ContinuumCoulomb.QuantumHistoryCells

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistorySpatialProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal sampled history and its row/column labels are combined into
the exact prepared input of the fixed-round fork compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatialProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode
open QuantumHistoryPrecisionProgram

theorem rawCells_input (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates≠[]) (N : ℕ) :
    QuantumHistoryCells.rawCells c=List.ofFn
      (fun i : Fin (QuantumHistorySpatial.input c hc hT hne N).n =>
        QuantumSpatialInputTape.coordinates
          ((QuantumHistorySpatial.input c hc hT hne N).cell i.val)) := by
  apply List.ext_getElem
  · rw [List.length_ofFn]
    exact QuantumHistoryCells.rawCells_input_length c hc hT hne N
  · intro j hj _
    rw [List.getElem_ofFn]
    simpa only [QuantumSpatialInputTape.coordinates,QuantumHistoryCells.encodeCell] using
      QuantumHistoryCells.rawCells_input_get c hc hT hne N j hj

theorem initialInput_actual (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates≠[]) (N : ℕ) :
    initialInput (N,c)=
      ((QuantumHistorySpatial.input c hc hT hne N).precision,
        (QuantumHistorySpatial.input c hc hT hne N).n,
        (QuantumHistorySpatial.input c hc hT hne N).bonds,
        (QuantumHistorySpatial.input c hc hT hne N).constant) := by
  rw [initialInput,sparseInput,physicalQubits_actual N (qmaSparseCircuit c) hT,
    output_actual N (qmaSparseCircuit c) hT,QuantumHistorySpatial.input_n,
    QuantumHistorySpatial.input_bonds,QuantumHistorySpatial.input_constant]
  rfl

theorem prepared_actual (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates≠[]) (N : ℕ) :
    prepared (N,c)=QuantumSpatialInputTape.input
      (QuantumHistorySpatial.input c hc hT hne N) := by
  unfold prepared QuantumSpatialInputTape.input
  rw [initialInput_actual c hc hT hne N,rawCells_input c hc hT hne N]

end ContinuumCoulomb.QuantumHistorySpatialProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryPreparedProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nonempty circuit, final unary precision, exact history cells and
rational promise thresholds are assembled without semantic input oracles. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryPreparedProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

theorem precision_pos (c : QMACircuit) : 0<precision c :=
  QuantumAlgebraicHistory.finalPrecision_pos _ _

theorem prepared_actual (c : QMACircuit) (hc : c.WellFormed) :
    prepared c=QuantumSpatialInputTape.input
      (QuantumHistorySpatial.input (qmaNonemptyCircuit c) (qmaNonemptyCircuit_wellFormed c hc)
        (qmaNonemptyCircuit_sparse_pos c) (qmaNonemptyCircuit_nearest c) (precision c)) :=
  QuantumHistorySpatialProgram.prepared_actual _ (qmaNonemptyCircuit_wellFormed c hc)
    (qmaNonemptyCircuit_sparse_pos c) (qmaNonemptyCircuit_nearest c) (precision c)

theorem finalInput_actual (c : QMACircuit) (hc : c.WellFormed) :
    finalInput c=
      (((precision c:ℚ),QuantumSpatialInputTape.input
        (QuantumHistorySpatial.input (qmaNonemptyCircuit c) (qmaNonemptyCircuit_wellFormed c hc)
          (qmaNonemptyCircuit_sparse_pos c) (qmaNonemptyCircuit_nearest c) (precision c))),
        (QuantumAlgebraicHistory.xzYesThreshold (qmaPreparedCircuit c),
          QuantumAlgebraicHistory.xzNoThreshold (qmaPreparedCircuit c))) := by
  rw [finalInput,prepared_actual c hc]
  rfl

end ContinuumCoulomb.QuantumHistoryPreparedProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryRoutedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full-space history comparison and verifier implications for the
literal circuit-to-lattice output, including empty-circuit preparation. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySourceProgram
open QuantumHistorySpatial QuantumHistoryPreparedProgram QuantumPaddedLabelProgram
open QuantumAlgebraicHistory

theorem routedState_actual (c : QMACircuit) (hc : c.WellFormed) :
    routedState c = QuantumFinalRoutingProgram.routed rawDensity historyDegree
      (((precision c:ℚ),QuantumSpatialInputTape.input
        (QuantumHistorySpatial.input (qmaNonemptyCircuit c) (qmaNonemptyCircuit_wellFormed c hc)
          (qmaNonemptyCircuit_sparse_pos c) (qmaNonemptyCircuit_nearest c) (precision c))),
        thresholds c) :=
  congrArg (QuantumFinalRoutingProgram.routed rawDensity historyDegree) (finalInput_actual c hc)

theorem route_rounds_eq : QuantumSpatialPortProgram.rounds rawDensity historyDegree = routeRounds :=
  (QuantumSpatialPortProgram.rounds_eq rawDensity historyDegree).symm.trans routeRounds_eq

theorem history_error_oai (c : QMACircuit) (hc : c.WellFormed) :
    |QuantumListSchedule.energy (routedState c).1-
      (qmaOrderedHistoryModel (qmaPreparedCircuit c) (qmaNonemptyCircuit_sparse_pos c)).energy| ≤
      ((totalRounds:ℝ)+9)/(precision c:ℝ) := by
  let d := qmaNonemptyCircuit c
  let hd := qmaNonemptyCircuit_wellFormed c hc
  let ht := qmaNonemptyCircuit_sparse_pos c
  let he := qmaNonemptyCircuit_nearest c
  have hr := QuantumFinalRoutingProgram.spatial_energy_error
    (QuantumHistorySpatial.input d hd ht he (precision c)) finalDensity_pos
    (N := (precision c:ℚ)) (by exact_mod_cast precision_pos c)
    (thresholds c).1 (thresholds c).2
  have hh := model_history_error d hd ht he (precision c) (precision_pos c)
  rw [route_rounds_eq] at hr
  rw [routedState_actual c hc]
  have hn : ((precision c:ℚ):ℝ) = (precision c:ℝ) := Rat.cast_natCast _
  rw [hn] at hr
  calc
    _ ≤ |QuantumListSchedule.energy
          (QuantumFinalRoutingProgram.routed rawDensity historyDegree
            (((precision c:ℚ),QuantumSpatialInputTape.input
              (QuantumHistorySpatial.input d hd ht he (precision c))),thresholds c)).1-
            (model d hd ht he (precision c)).energy|+
        |(model d hd ht he (precision c)).energy-
          (qmaOrderedHistoryModel (qmaPreparedCircuit c) ht).energy| := abs_sub_le _ _ _
    _ ≤ ((routeRounds:ℝ)+82)/(precision c:ℝ)+((historyDegree:ℝ)+10)/(precision c:ℝ) :=
      add_le_add hr hh
    _ = _ := by simp only [totalRounds,Nat.cast_add,Nat.cast_ofNat]; ring

end ContinuumCoulomb.QuantumHistorySourceProgram

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.QuantumHistorySourceProgram.history_error_oai := @OAI.ContinuumCoulomb.QuantumHistorySourceProgram.history_error_oai
