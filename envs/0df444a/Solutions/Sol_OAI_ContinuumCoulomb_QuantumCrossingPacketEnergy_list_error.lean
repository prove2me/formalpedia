-- Prove2me | solution 1 for OAI.ContinuumCoulomb.QuantumCrossingPacketEnergy.list_error
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:19:51.43728+00:00
-- url     : https://prove2.me/submissions/d8f0f19a-d827-4d4d-85e2-42589f957c48

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
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.NodupEquivFin
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
import Definitions.Def_OAIQ092A008
import Definitions.Def_OAIQ092A009

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingEffective
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.mediatorHighRestriction_apply _root_.OAI.ContinuumCoulomb.mediatorHighRestriction_inclusion _root_.OAI.ContinuumCoulomb.mediatorHighRestriction_low _root_.OAI.ContinuumCoulomb.mediatorLowRestriction_apply _root_.OAI.ContinuumCoulomb.mediatorLowRestriction_high _root_.OAI.ContinuumCoulomb.mediatorLowRestriction_inclusion _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact four-terminal crossing gadget and its perimeter counterterms. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaCrossing_effective {n r : ℕ} (e : Fin r) (site : Fin 4 → Fin n)
    (hsite : Function.Injective site) (R J K : ℝ) (hR : R ≠ 0) :
    qmaCrossingCorrection site J K -
      mediatorCompression n r
        (qmaSingletStar n r e site qmaCrossingMember (qmaCrossingAmplitude R J K) *
          liftedMediatorInverse n r (R^2) *
            qmaSingletStar n r e site qmaCrossingMember (qmaCrossingAmplitude R J K)) =
      (J:ℂ) • sourceHeisenbergMatrix n (site 0) (site 2) +
        (K:ℂ) • sourceHeisenbergMatrix n (site 1) (site 3) := by
  have hk (a b : Fin 4) : qmaPauliKernel n (site a) (site b) =
      if a = b then (3:ℂ) • 1 else sourceHeisenbergMatrix n (site a) (site b) := by
    by_cases hab : a = b
    · subst b
      simp only [ite_true, if_true,qmaPauliKernel_self]
    · rw [ite_eq_right hab]
      exact qmaPauliKernel_eq n _ _ (fun h => hab (hsite h))
  rw [qmaSingletStar_compression]
  simp only [hk,qmaCrossingCorrection]
  simp [qmaCrossingMember,qmaCrossingAmplitude,Fin.sum_univ_succ]
  rw [qmaHeisenberg_symm n (site 1) (site 0),qmaHeisenberg_symm n (site 2) (site 0),
    qmaHeisenberg_symm n (site 2) (site 1),qmaHeisenberg_symm n (site 3) (site 0),
    qmaHeisenberg_symm n (site 3) (site 1),qmaHeisenberg_symm n (site 3) (site 2)]
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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingSpectrum
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The crossing construction compared on the complete spin Hilbert space. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

theorem qmaCrossingCorrection_star {n : ℕ} (site : Fin 4 → Fin n)
    (hsite : Function.Injective site) (J K : ℝ) :
    (qmaCrossingCorrection site J K).conjTranspose = qmaCrossingCorrection site J K := by
  have hij (a b : Fin 4) (hab : a ≠ b) : site a ≠ site b := fun h => hab (hsite h)
  simp only [qmaCrossingCorrection,Matrix.conjTranspose_add,Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul,Matrix.conjTranspose_one,
    sourceHeisenbergMatrix_star n _ _ (hij 0 1 (by decide)),
    sourceHeisenbergMatrix_star n _ _ (hij 0 3 (by decide)),
    sourceHeisenbergMatrix_star n _ _ (hij 1 2 (by decide)),
    sourceHeisenbergMatrix_star n _ _ (hij 2 3 (by decide)),
    Complex.star_def,Complex.conj_ofReal]
  norm_num [starRingEnd_apply,Complex.star_def]

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial coefficient and operator bounds for the crossing construction. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

theorem qmaCrossingCorrection_exchange {n : ℕ} (site : Fin 4 → Fin n) (J K : ℝ) :
    qmaCrossingCorrection site J K =
      qmaExchangeMatrix (fun a => site (qmaCrossingLeft a))
        (fun a => site (qmaCrossingRight a)) (qmaCrossingWeight J K) (qmaCrossingOffset J K) := by
  simp [qmaCrossingCorrection,qmaExchangeMatrix,qmaCrossingLeft,qmaCrossingRight,
    qmaCrossingWeight,qmaCrossingOffset,Fin.sum_univ_succ]
  module

theorem qmaCrossingCorrection_lift_norm {n r : ℕ} (site : Fin 4 → Fin n)
    (hsite : Function.Injective site) (J K : ℝ) :
    ‖spinMatrixOperator (qmaCrossingCorrection site J K ⊗ₖ
      (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ ≤ 12*(1+|J|+|K|)^2 := by
  have hneq (a : Fin 4) : site (qmaCrossingLeft a) ≠ site (qmaCrossingRight a) := by
    intro h
    have hh := hsite h
    fin_cases a <;> norm_num [qmaCrossingLeft,qmaCrossingRight, Fin.ext_iff] at hh
  rw [qmaCrossingCorrection_exchange]
  apply (qmaExchangeMatrix_lift_norm _ _ hneq _ _).trans
  have hoff : 0 ≤ qmaCrossingOffset J K := by unfold qmaCrossingOffset; positivity
  rw [abs_of_nonneg hoff]
  simp [qmaCrossingWeight,qmaCrossingOffset,Fin.sum_univ_succ,abs_mul,abs_neg]
  nlinarith [sq_abs J,sq_abs K,abs_nonneg J,abs_nonneg K,mul_nonneg (abs_nonneg J) (abs_nonneg K)]

theorem qmaCrossingAmplitude_norm (R J K : ℝ) (hR : 0 ≤ R) :
    3*(∑ a, |qmaCrossingAmplitude R J K a|) = 6*R*(1+|J|+|K|) := by
  simp [qmaCrossingAmplitude,Fin.sum_univ_succ,abs_mul,abs_of_nonneg hR]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingParallel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous crossing elimination, with no mixed error between distinct singlets. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

theorem qmaCrossings_effective {n r : ℕ} (site : Fin r → Fin 4 → Fin n)
    (hsite : ∀ e, Function.Injective (site e)) (R : ℝ) (hR : R ≠ 0) (J K : Fin r → ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :
    (C + ∑ e, qmaCrossingCorrection (site e) (J e) (K e)) -
      mediatorCompression n r (qmaRoutingStars n r site (fun _ => qmaCrossingMember)
          (fun e => qmaCrossingAmplitude R (J e) (K e)) * liftedMediatorInverse n r (R^2) *
        qmaRoutingStars n r site (fun _ => qmaCrossingMember)
          (fun e => qmaCrossingAmplitude R (J e) (K e))) =
      C + ∑ e, ((J e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 2) +
        (K e:ℂ) • sourceHeisenbergMatrix n (site e 1) (site e 3)) := by
  rw [qmaRoutingStars_compression,add_sub_assoc,← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  exact qmaCrossing_effective e (site e) (hsite e) R (J e) (K e) hR

theorem qmaCrossings_bottom {n r : ℕ} (site : Fin r → Fin 4 → Fin n)
    (hsite : ∀ e, Function.Injective (site e)) (R : ℝ) (hR : 0 < R) (J K : Fin r → ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1/4)
    (hbound : ‖spinMatrixOperator ((C + ∑ e, qmaCrossingCorrection (site e) (J e) (K e)) ⊗ₖ
        (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      3*∑ e, ∑ a, |qmaCrossingAmplitude R (J e) (K e) a| ≤ epsilon * (4*R^2)) :
    |mediatorFullBottom n r (routingHamiltonian n r (R^2)
        (C + ∑ e, qmaCrossingCorrection (site e) (J e) (K e))
        (qmaRoutingStars n r site (fun _ => qmaCrossingMember)
          (fun e => qmaCrossingAmplitude R (J e) (K e)))) -
      sourceMatrixBottom n (C + ∑ e,
        ((J e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 2) +
          (K e:ℂ) • sourceHeisenbergMatrix n (site e 1) (site e 3)))| ≤
      16*R^2*epsilon^3 := by
  have hCW : (C + ∑ e, qmaCrossingCorrection (site e) (J e) (K e)).conjTranspose =
      C + ∑ e, qmaCrossingCorrection (site e) (J e) (K e) := by
    simp only [Matrix.conjTranspose_add,Matrix.conjTranspose_sum,hC,
      qmaCrossingCorrection_star _ (hsite _)]
  have h := qmaRoutingStars_bottom n r (sq_pos_of_pos hR) _ hCW site
    (fun _ => qmaCrossingMember) (fun e => qmaCrossingAmplitude R (J e) (K e))
    hepsilon hsmall hbound
  rw [qmaCrossings_effective site hsite R hR.ne' J K C] at h
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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingCalibration
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial calibration for a simultaneous crossing stage. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

theorem qmaCrossings_correction_norm {n r : ℕ} (site : Fin r → Fin 4 → Fin n)
    (hsite : ∀ e, Function.Injective (site e)) (J K : Fin r → ℝ) :
    ‖spinMatrixOperator ((∑ e, qmaCrossingCorrection (site e) (J e) (K e)) ⊗ₖ
      (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ ≤
      12*∑ e, (1+|J e|+|K e|)^2 := by
  rw [MediatorGraph.sum_kronecker,spinMatrixOperator_sum,Finset.mul_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun e _ =>
    qmaCrossingCorrection_lift_norm (site e) (hsite e) (J e) (K e)))

theorem qmaCrossings_amplitude (r : ℕ) (R : ℝ) (hR : 0 ≤ R) (J K : Fin r → ℝ) :
    3*(∑ e, ∑ a, |qmaCrossingAmplitude R (J e) (K e) a|) =
      (6*∑ e, (1+|J e|+|K e|))*R := by
  rw [Finset.mul_sum]
  simp_rw [qmaCrossingAmplitude_norm R _ _ hR]
  rw [← Finset.mul_sum]
  ring

theorem qmaCrossings_accuracy {n r : ℕ} (site : Fin r → Fin 4 → Fin n)
    (hsite : ∀ e, Function.Injective (site e)) (J K : Fin r → ℝ)
    {B N : ℝ} (hB : 0 ≤ B) (hN : 0 < N)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    (hCn : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ ≤ B) :
    let A := 6*∑ e, (1+|J e|+|K e|)
    let D := B+12*∑ e, (1+|J e|+|K e|)^2
    let R := qmaRoutingScale A D N
    |mediatorFullBottom n r (routingHamiltonian n r (R^2)
        (C + ∑ e, qmaCrossingCorrection (site e) (J e) (K e))
        (qmaRoutingStars n r site (fun _ => qmaCrossingMember)
          (fun e => qmaCrossingAmplitude R (J e) (K e)))) -
      sourceMatrixBottom n (C + ∑ e,
        ((J e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 2) +
          (K e:ℂ) • sourceHeisenbergMatrix n (site e 1) (site e 3)))| ≤ 1/N := by
  let A := 6*∑ e, (1+|J e|+|K e|)
  let D := B+12*∑ e, (1+|J e|+|K e|)^2
  let R := qmaRoutingScale A D N
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨hR,he,hes,hbound,herr⟩ := qmaRoutingScale_bounds hA hD hN
  have hCC : ‖spinMatrixOperator ((C + ∑ e, qmaCrossingCorrection (site e) (J e) (K e)) ⊗ₖ
      (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ ≤ D := by
    rw [Matrix.add_kronecker,spinMatrixOperator_add]
    exact (norm_add_le _ _).trans (add_le_add hCn (qmaCrossings_correction_norm site hsite J K))
  have hb : ‖spinMatrixOperator ((C + ∑ e, qmaCrossingCorrection (site e) (J e) (K e)) ⊗ₖ
        (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      3*∑ e, ∑ a, |qmaCrossingAmplitude R (J e) (K e) a| ≤ ((A+D+1)/R)*(4*R^2) := by
    rw [qmaCrossings_amplitude r R hR.le J K]
    exact (add_le_add hCC (le_refl (A*R))).trans hbound
  exact (qmaCrossings_bottom site hsite R hR J K C hC he hes hb).trans herr

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingsGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordinary spin edges and polynomial full-space error for a parallel crossing-elimination round. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix MediatorGraph
open scoped BigOperators Kronecker Classical
variable {ν : Type*} [Fintype ν]

theorem qmaCrossingsBase_matrix {n r : ℕ} (left right : ν → Fin n) (weight : ν → ℝ)
    (constant : ℝ) (site : Fin r → Fin 4 → Fin n) (J K : Fin r → ℝ) :
    qmaExchangeMatrix (qmaCrossingsBaseLeft left site) (qmaCrossingsBaseRight right site)
      (qmaCrossingsBaseWeight weight J K) (constant+∑ e, qmaCrossingOffset (J e) (K e)) =
      qmaExchangeMatrix left right weight constant +
        ∑ e, qmaCrossingCorrection (site e) (J e) (K e) := by
  simp only [qmaCrossingCorrection_exchange,qmaExchangeMatrix,Fintype.sum_sum_type,
    Fintype.sum_prod_type,qmaCrossingsBaseLeft,qmaCrossingsBaseRight,qmaCrossingsBaseWeight,
    Sum.elim_inl,Sum.elim_inr,Complex.ofReal_add,Complex.ofReal_sum,add_smul,
    Finset.sum_add_distrib,Finset.sum_smul]
  abel

theorem qmaCrossingsGraph_matrix {n r : ℕ} (left right : ν → Fin n)
    (hneq : ∀ a, left a ≠ right a) (weight : ν → ℝ) (constant R : ℝ)
    (site : Fin r → Fin 4 → Fin n) (hsite : ∀ e, Function.Injective (site e)) (J K : Fin r → ℝ) :
    (qmaCrossingsGraph left right weight constant R site J K).submatrix
      (basisEquiv n r) (basisEquiv n r) =
      qmaPhysicalParallelHamiltonian n r (R^2)
        (qmaExchangeMatrix left right weight constant+∑ e, qmaCrossingCorrection (site e) (J e) (K e))
        site (fun _ => qmaCrossingMember) (fun e => qmaCrossingAmplitude R (J e) (K e)) := by
  unfold qmaCrossingsGraph
  simpa only [qmaCrossingsBase_matrix] using
    qmaParallelGraph_matrix _ _ (qmaCrossingsBase_distinct left right hneq site hsite)
      (qmaCrossingsBaseWeight weight J K) (constant+∑ e, qmaCrossingOffset (J e) (K e)) (R^2)
      site (fun _ => qmaCrossingMember) (fun e => qmaCrossingAmplitude R (J e) (K e))

theorem qmaCrossingsGraph_accuracy {n r : ℕ} (left right : ν → Fin n)
    (hneq : ∀ a, left a ≠ right a) (weight : ν → ℝ) (constant : ℝ)
    (site : Fin r → Fin 4 → Fin n) (hsite : ∀ e, Function.Injective (site e))
    (J K : Fin r → ℝ) {N : ℝ} (hN : 0 < N) :
    let B := 3*(∑ a, |weight a|)+|constant|
    let A := 6*∑ e, (1+|J e|+|K e|)
    let D := B+12*∑ e, (1+|J e|+|K e|)^2
    let R := qmaRoutingScale A D N
    |sourceMatrixBottom (n+r*2) (qmaCrossingsGraph left right weight constant R site J K) -
      sourceMatrixBottom n (qmaExchangeMatrix left right weight constant + ∑ e,
        ((J e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 2) +
          (K e:ℂ) • sourceHeisenbergMatrix n (site e 1) (site e 3)))| ≤ 1/N := by
  dsimp only
  rw [sourceMatrixBottom_eq_mediator n r,qmaCrossingsGraph_matrix left right hneq weight constant _ site hsite,
    qmaPhysicalParallel_bottom]
  have hC : (qmaExchangeMatrix left right weight constant).conjTranspose =
      qmaExchangeMatrix left right weight constant := by
    simp only [qmaExchangeMatrix,Matrix.conjTranspose_add,Matrix.conjTranspose_sum,
      Matrix.conjTranspose_smul,sourceHeisenbergMatrix_star n _ _ (hneq _),
      Complex.star_def,Complex.conj_ofReal,Matrix.conjTranspose_one]
  exact qmaCrossings_accuracy site hsite J K (by positivity) hN _ hC
    (qmaExchangeMatrix_lift_norm left right hneq weight constant)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial rational programs for the crossing coefficients and penalty. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRoutingCode
open ExactQuantumFactoring.BitStackProgram

theorem coefficients_spoke (x : Triple) (a : Fin 4) :
    (coefficients x ⟨a.val+1,by omega⟩ : ℝ) =
      qmaCrossingAmplitude (x.1:ℝ) (x.2.1:ℝ) (x.2.2:ℝ) a := by
  fin_cases a <;> simp [coefficients,qmaCrossingAmplitude]

theorem coefficients_perimeter (x : Triple) (a : Fin 4) :
    (coefficients x ⟨a.val+5,by omega⟩ : ℝ) = qmaCrossingWeight (x.2.1:ℝ) (x.2.2:ℝ) a := by
  fin_cases a <;> simp [coefficients,qmaCrossingWeight]

end ContinuumCoulomb.QuantumRoutingCode

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

theorem ofBonds_energy (n : ℕ) (xs : List Bond) (c : ℚ)
    (hb : SourceBondLists.bounded n xs) (hn : ∀ e ∈ xs, e.1 ≠ e.2.1) :
    (ofBonds n xs c hb hn).energy =
      sourceMatrixBottom n (SourceBondLists.matrix n xs+(c:ℂ) • 1) := by
  exact congrArg (sourceMatrixBottom n) (ofBonds_matrix n xs c hb hn)

end ContinuumCoulomb.QuantumListGraph

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRationalCrossing
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPathSchedule.mem_active _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_old _root_.OAI.ContinuumCoulomb.QMAPortRouteData.mem_crossingCells _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_fresh _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A simultaneous crossing-removal layer as exact rational ordinary-spin data. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph Matrix
open scoped BigOperators Classical

namespace QMARationalCrossingLayer
variable {r : ℕ}

theorem source_matrix (C : QMARationalCrossingLayer r) :
    qmaExchangeMatrix C.source.left C.source.right (fun e => (C.source.weight e:ℝ)) C.source.constant =
      qmaExchangeMatrix C.base.left C.base.right (fun e => (C.base.weight e:ℝ)) C.base.constant +
        ∑ i, ((C.J i:ℂ) • sourceHeisenbergMatrix C.base.n (C.site i 0) (C.site i 2) +
          (C.K i:ℂ) • sourceHeisenbergMatrix C.base.n (C.site i 1) (C.site i 3)) := by
  let f : C.source.Edge → Matrix (SourceSpinBasis C.base.n) (SourceSpinBasis C.base.n) ℂ :=
    fun e => (C.source.weight e:ℂ) • sourceHeisenbergMatrix C.base.n (C.source.left e) (C.source.right e)
  let g : C.base.Edge ⊕ (Fin r × Fin 2) →
      Matrix (SourceSpinBasis C.base.n) (SourceSpinBasis C.base.n) ℂ := fun e =>
    ((Sum.elim C.base.weight (fun p => if p.2 = 0 then C.J p.1 else C.K p.1)) e:ℂ) •
      sourceHeisenbergMatrix C.base.n
        ((Sum.elim C.base.left (fun p => C.site p.1 (if p.2 = 0 then 0 else 1))) e)
        ((Sum.elim C.base.right (fun p => C.site p.1 (if p.2 = 0 then 2 else 3))) e)
  let E : C.source.Edge ≃ C.base.Edge ⊕ (Fin r × Fin 2) := Equiv.refl _
  have hs : (∑ e, f e) = ∑ e, g e := Fintype.sum_equiv E f g (by intro e; rfl)
  simp only [qmaExchangeMatrix]
  change (∑ e, f e)+(C.base.constant:ℂ) • 1 = _
  rw [hs]
  simp only [g,Fintype.sum_sum_type,Fintype.sum_prod_type,Sum.elim_inl,Sum.elim_inr,Fin.sum_univ_two]
  simp
  ac_rfl

theorem scale_cast (C : QMARationalCrossingLayer r) (N : ℚ) :
    (C.scale N:ℝ) =
      qmaRoutingScale (6*∑ i, (1+|(C.J i:ℝ)|+|(C.K i:ℝ)|))
        (3*(∑ e, |(C.base.weight e:ℝ)|)+|(C.base.constant:ℝ)|+
          12*∑ i, (1+|(C.J i:ℝ)|+|(C.K i:ℝ)|)^2) N := by
  simp only [scale,qmaRoutingScale]
  push_cast
  rfl

theorem output_matrix (C : QMARationalCrossingLayer r) (N : ℚ) :
    qmaExchangeMatrix (C.output N).left (C.output N).right (fun e => ((C.output N).weight e:ℝ))
      (C.output N).constant =
      qmaCrossingsGraph C.base.left C.base.right (fun e => (C.base.weight e:ℝ)) C.base.constant
        (C.scale N) C.site (fun i => (C.J i:ℝ)) (fun i => (C.K i:ℝ)) := by
  dsimp only [output,qmaCrossingsGraph]
  congr 1
  · funext e
    rcases e with (e | ⟨i,a⟩) | (i | ⟨i,a⟩)
    · rfl
    · exact QuantumRoutingCode.coefficients_perimeter (C.scale N,C.J i,C.K i) a
    · simp [qmaParallelGraphWeight]
    · exact QuantumRoutingCode.coefficients_spoke (C.scale N,C.J i,C.K i) a
  · simp [qmaCrossingOffset]

theorem output_energy_error (C : QMARationalCrossingLayer r) {N : ℚ} (hN : 0 < N) :
    |(C.output N).energy-C.source.energy| ≤ 1/(N:ℝ) := by
  unfold QMARationalExchangeGraph.energy
  rw [C.output_matrix,C.source_matrix,C.scale_cast]
  exact qmaCrossingsGraph_accuracy C.base.left C.base.right C.base.distinct
    (fun e => (C.base.weight e:ℝ)) C.base.constant C.site C.injective
    (fun i => (C.J i:ℝ)) (fun i => (C.K i:ℝ)) (by exact_mod_cast hN)

end QMARationalCrossingLayer
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingScaleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational scale for a simultaneous crossing layer, computed from
its retained coefficients and the two crossing coefficients at each cell. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingScaleProgram
open ExactQuantumFactoring.BitStackProgram
open scoped BigOperators Classical

theorem value_actual {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) {m : ℕ}
    (labels : C.base.Edge ≃ Fin m) : value (actualInput C N labels)=C.scale N := by
  simp only [value,base,active,correction,actualInput,List.map_ofFn,List.sum_ofFn,
    Function.comp_apply,linearCost,squareCost,QMARationalCrossingLayer.scale]
  rw [labels.symm.sum_comp (fun e => |C.base.weight e|)]

end ContinuumCoulomb.QuantumCrossingScaleProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListPathMatrix
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

theorem matrix_flatten (n : ℕ) (xss : List (List Bond)) :
    SourceBondLists.matrix n xss.flatten = (xss.map (SourceBondLists.matrix n)).sum := by
  simp only [SourceBondLists.matrix,List.map_flatten,List.sum_flatten,List.map_map,
    Function.comp_def]
  rfl

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

end ContinuumCoulomb.QuantumListPathProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingListActual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal crossing packet has exactly the sites, scale and scalar
shift of the rational crossing layer used by the spectral comparison. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingListLayer
open QuantumCrossingListBlock
open scoped BigOperators Classical

theorem scaleInput_actual {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) {m : ℕ}
    (labels : C.base.Edge ≃ Fin m) :
    scaleInput (actualInput C N labels)=QuantumCrossingScaleProgram.actualInput C N labels := by
  simp only [scaleInput,actualInput,QuantumListGraph.packed,List.map_ofFn]
  rfl

theorem parameters_actual {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) {m : ℕ}
    (labels : C.base.Edge ≃ Fin m) :
    parameters (actualInput C N labels)=(C.base.n,C.scale N) := by
  unfold parameters
  rw [scaleInput_actual,QuantumCrossingScaleProgram.value_actual]
  rfl

theorem constant_actual {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) {m : ℕ}
    (labels : C.base.Edge ≃ Fin m) :
    constant (actualInput C N labels)=(C.output N).constant := by
  unfold constant familyInput
  rw [parameters_actual]
  change C.base.constant+familyOffset ((C.base.n,C.scale N),List.ofFn (actualCrossing C)) = _
  simp only [familyOffset,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  change C.base.constant+(∑ i, (3/2+3*(C.J i)^2+3*(C.K i)^2+3*(C.scale N)^2)) =
    (C.base.constant+∑ i, (3/2+3*(C.J i)^2+3*(C.K i)^2))+3*(r:ℚ)*(C.scale N)^2
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

end ContinuumCoulomb.QuantumCrossingListLayer

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingListMatrix
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPathSchedule.mem_active _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_old _root_.OAI.ContinuumCoulomb.QMAPortRouteData.mem_crossingCells _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_fresh _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_old _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.ContinuumCoulomb.qmaSubdivisionCell_fresh _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact full-space matrix semantics for the computed crossing packet.
The nine serialized bonds are the nine physical edges of each crossing. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingListLayer
open QuantumCrossingListBlock MediatorGraph
open scoped BigOperators Classical

private theorem fresh_value (n r : ℕ) (i : Fin r) (a : Fin 2) :
    (fresh n r i a).val=n+2*i.val+a.val := by
  change n+(a.val+2*i.val)=_
  omega

private theorem old_value (n r : ℕ) (i : Fin n) : (old n r i).val=i.val := rfl

theorem bond_actual {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ)
    (i : Fin r) (k : Fin 9) :
    bond ((C.base.n,C.scale N),i.val,actualCrossing C i) k =
      (((C.output N).left (edgeTag C N i k)).val,
        ((C.output N).right (edgeTag C N i k)).val,
        (C.output N).weight (edgeTag C N i k)) := by
  fin_cases k <;>
    simp [bond,left,right,coefficient,base,actualCrossing,site,edgeTag,
      QMARationalCrossingLayer.output,qmaParallelGraphLeft,qmaParallelGraphRight,
      qmaCrossingsBaseLeft,qmaCrossingsBaseRight,qmaCrossingLeft,qmaCrossingRight,
      qmaCrossingMember,fresh_value,old_value]

theorem block_matrix_actual {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ)
    (i : Fin r) :
    SourceBondLists.matrix (C.output N).n
      (block ((C.base.n,C.scale N),i.val,actualCrossing C i)) =
      ∑ k : Fin 9, ((C.output N).weight (edgeTag C N i k):ℂ) •
        sourceHeisenbergMatrix (C.output N).n
          ((C.output N).left (edgeTag C N i k)) ((C.output N).right (edgeTag C N i k)) := by
  simp only [SourceBondLists.matrix,block,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [bond_actual,SourceBondLists.bondMatrix,dite_eq_left
    ⟨((C.output N).left (edgeTag C N i k)).isLt,
      ((C.output N).right (edgeTag C N i k)).isLt⟩]

private theorem indexed_ofFn {r : ℕ} (p : Parameters) (f : Fin r → Crossing)
    (i : Fin r) : indexed (i.val,(p,List.ofFn f))=(p,i.val,f i) := by
  unfold indexed
  rw [List.headD_eq_head?_getD,List.head?_drop,
    List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using i.isLt)]
  simp only [List.getElem_ofFn,Option.getD_some]

theorem family_ofFn {r : ℕ} (p : Parameters) (f : Fin r → Crossing) :
    family (p,List.ofFn f)=(List.ofFn fun i => block (p,i.val,f i)).flatten := by
  have hr (g : ℕ → List MediatorListProgram.Bond) :
      (List.range r).map g=List.ofFn (fun i : Fin r => g i.val) := by
    simpa only [List.length_range,List.getElem_range,Fin.val_cast] using
      (List.ofFn_getElem_eq_map (List.range r) g).symm
  unfold family
  rw [List.length_ofFn,hr]
  apply congrArg List.flatten
  apply congrArg (fun g : Fin r → List MediatorListProgram.Bond => List.ofFn g)
  funext i
  rw [indexed_ofFn]

theorem family_matrix_actual {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) :
    SourceBondLists.matrix (C.output N).n
      (family ((C.base.n,C.scale N),List.ofFn (actualCrossing C))) =
      ∑ i : Fin r, ∑ k : Fin 9, ((C.output N).weight (edgeTag C N i k):ℂ) •
        sourceHeisenbergMatrix (C.output N).n
          ((C.output N).left (edgeTag C N i k)) ((C.output N).right (edgeTag C N i k)) := by
  rw [family_ofFn,QuantumListPathProgram.matrix_flatten]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  exact Finset.sum_congr rfl (fun i _ => block_matrix_actual C N i)

theorem edgeTag_sum {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ)
    {V : Type*} [AddCommMonoid V] (f : (C.output N).Edge → V) (i : Fin r) :
    (∑ k : Fin 9, f (edgeTag C N i k)) =
      (∑ a : Fin 4, f (.inl (.inr (i,a))))+f (.inr (.inl i))+
        ∑ a : Fin 4, f (.inr (.inr (i,a))) := by
  simp [Fin.sum_univ_succ,edgeTag,add_assoc]

private theorem sum_crossing_edges {α V : Type*} [Fintype α] [AddCommMonoid V]
    {r : ℕ} (f : ((α ⊕ (Fin r × Fin 4)) ⊕ (Fin r ⊕ (Fin r × Fin 4))) → V) :
    (∑ e, f e) = (∑ e : α, f (.inl (.inl e)))+
      (∑ i : Fin r, ((∑ a : Fin 4, f (.inl (.inr (i,a))))+
        f (.inr (.inl i))+(∑ a : Fin 4, f (.inr (.inr (i,a)))))) := by
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Finset.sum_add_distrib]
  ac_rfl

theorem matrix_actual {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) {m : ℕ}
    (labels : C.base.Edge ≃ Fin m) :
    SourceBondLists.matrix (C.output N).n (bonds (actualInput C N labels))+
      ((C.output N).constant:ℂ) • 1 =
      qmaExchangeMatrix (C.output N).left (C.output N).right
        (fun e => ((C.output N).weight e:ℝ)) (C.output N).constant := by
  let f : (C.output N).Edge →
      Matrix (SourceSpinBasis (C.output N).n) (SourceSpinBasis (C.output N).n) ℂ :=
    fun e => ((C.output N).weight e:ℂ) • sourceHeisenbergMatrix (C.output N).n
      ((C.output N).left e) ((C.output N).right e)
  have hb : SourceBondLists.matrix (C.output N).n (QuantumListGraph.packed C.base labels) =
      ∑ e : C.base.Edge, f (.inl (.inl e)) := by
    change SourceBondLists.matrix (C.base.n+r*2)
      (List.ofFn fun i => ((C.base.left (labels.symm i)).val,
        (C.base.right (labels.symm i)).val,C.base.weight (labels.symm i))) = _
    rw [QuantumListPathProgram.retained_matrix]
    exact labels.symm.sum_comp (fun e => (C.base.weight e:ℂ) •
      sourceHeisenbergMatrix (C.base.n+r*2)
        (old C.base.n r (C.base.left e)) (old C.base.n r (C.base.right e)))
  have hfamily : familyInput (actualInput C N labels) =
      ((C.base.n,C.scale N),List.ofFn (actualCrossing C)) := by
    unfold familyInput
    rw [parameters_actual]
    rfl
  unfold bonds
  simp only [SourceBondLists.matrix,List.map_append,List.sum_append]
  change (SourceBondLists.matrix (C.output N).n (QuantumListGraph.packed C.base labels)+
    SourceBondLists.matrix (C.output N).n (family (familyInput (actualInput C N labels))))+_ = _
  rw [hfamily,hb,family_matrix_actual]
  change ((∑ e : C.base.Edge, f (.inl (.inl e)))+
    ∑ i : Fin r, ∑ k : Fin 9, f (edgeTag C N i k))+_ = _
  have ht : (∑ i : Fin r, ∑ k : Fin 9, f (edgeTag C N i k)) =
      ∑ i : Fin r, ((∑ a : Fin 4, f (.inl (.inr (i,a))))+
        f (.inr (.inl i))+(∑ a : Fin 4, f (.inr (.inr (i,a))))) :=
    Finset.sum_congr rfl (fun i _ => edgeTag_sum C N f i)
  rw [ht]
  have hf : (∑ e, f e) = (∑ e : C.base.Edge, f (.inl (.inl e)))+
      (∑ i : Fin r, ((∑ a : Fin 4, f (.inl (.inr (i,a))))+
        f (.inr (.inl i))+(∑ a : Fin 4, f (.inr (.inr (i,a)))))) := by
    exact sum_crossing_edges (α := C.base.Edge) f
  simp only [qmaExchangeMatrix,Complex.ofReal_ratCast]
  exact congrArg (fun x => x+((C.output N).constant:ℂ) • 1) hf.symm

theorem energy_actual {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) {m : ℕ}
    (labels : C.base.Edge ≃ Fin m) : (actualGraph C N labels).energy=(C.output N).energy := by
  unfold actualGraph graph
  rw [QuantumListGraph.ofBonds_energy,count_actual,constant_actual]
  exact congrArg (sourceMatrixBottom (C.output N).n) (matrix_actual C N labels)

theorem energy_error {r : ℕ} (C : QMARationalCrossingLayer r) {N : ℚ} (hN : 0 < N)
    {m : ℕ} (labels : C.base.Edge ≃ Fin m) :
    |(actualGraph C N labels).energy-C.source.energy| ≤ 1/(N:ℝ) := by
  rw [energy_actual]
  exact C.output_energy_error hN

end ContinuumCoulomb.QuantumCrossingListLayer

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingSelection
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Group a selected family of physical crossing edges without assuming a matrix
identity. Each source edge is either retained or assigned to one crossing pair. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaSumSubtypePredicate {α M : Type*} [Fintype α] [AddCommMonoid M]
    (p : α → Prop) [DecidablePred p] (f : α → M) :
    (∑ a : {a // p a}, f a.val) = ∑ a, if p a then f a else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter p) (by simp) f]
  exact Finset.sum_filter _ _

theorem qmaOptionFiberSum {α β M : Type*} [Fintype α] [Fintype β] [DecidableEq β] [AddCommMonoid M]
    (tag : α → Option β) (f : α → M) :
    (∑ a : {a // tag a = none}, f a.val) +
      (∑ b : β, ∑ a : {a // tag a = some b}, f a.val) = ∑ a, f a := by
  rw [qmaSumSubtypePredicate]
  simp_rw [qmaSumSubtypePredicate]
  rw [Finset.sum_comm,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  cases tag a with
  | none => simp
  | some b => simp [eq_comm]

namespace QMARationalCrossingSelection
variable {G : QMARationalExchangeGraph} {r : ℕ} (S : QMARationalCrossingSelection G r)

theorem tagged_matrix (e : G.Edge) (i : Fin r) (a : Fin 2) (he : S.tag e = some (i,a)) :
    sourceHeisenbergMatrix G.n (G.left e) (G.right e) =
      sourceHeisenbergMatrix G.n (S.site i (if a = 0 then 0 else 1))
        (S.site i (if a = 0 then 2 else 3)) := by
  rcases S.tagged e i a he with ⟨hl,hr⟩ | ⟨hl,hr⟩
  · rw [hl,hr]
  · rw [hl,hr,qmaHeisenberg_symm]

theorem weight_matrix (p : Fin r × Fin 2) :
    (S.weight p:ℂ) • sourceHeisenbergMatrix G.n (S.site p.1 (if p.2 = 0 then 0 else 1))
      (S.site p.1 (if p.2 = 0 then 2 else 3)) =
    ∑ e : {e // S.tag e = some p}, (G.weight e.val:ℂ) •
      sourceHeisenbergMatrix G.n (G.left e.val) (G.right e.val) := by
  unfold weight
  push_cast
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro e _
  rw [S.tagged_matrix e.val p.1 p.2 e.property]

theorem source_matrix :
    qmaExchangeMatrix S.layer.source.left S.layer.source.right
      (fun e => (S.layer.source.weight e:ℝ)) S.layer.source.constant =
    qmaExchangeMatrix G.left G.right (fun e => (G.weight e:ℝ)) G.constant := by
  rw [S.layer.source_matrix]
  let f := fun e : G.Edge => (G.weight e:ℂ) • sourceHeisenbergMatrix G.n (G.left e) (G.right e)
  have hp := qmaOptionFiberSum S.tag f
  have hs : (∑ i, ((S.weight (i,0):ℂ) • sourceHeisenbergMatrix G.n (S.site i 0) (S.site i 2) +
      (S.weight (i,1):ℂ) • sourceHeisenbergMatrix G.n (S.site i 1) (S.site i 3))) =
      ∑ p : Fin r × Fin 2, ∑ e : {e // S.tag e = some p}, f e.val := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.sum_univ_two]
    simpa only [f,ite_true, if_true,ite_false, if_false,show (1 : Fin 2) ≠ 0 from by decide] using
      congrArg₂ (· + ·) (S.weight_matrix (i,0)) (S.weight_matrix (i,1))
  change ((∑ e : {e // S.tag e = none}, f e.val)+(G.constant:ℂ) • 1)+
    (∑ i, ((S.weight (i,0):ℂ) • sourceHeisenbergMatrix G.n (S.site i 0) (S.site i 2) +
      (S.weight (i,1):ℂ) • sourceHeisenbergMatrix G.n (S.site i 1) (S.site i 3))) =
        (∑ e, f e)+(G.constant:ℂ) • 1
  rw [hs]
  calc
    _ = ((∑ e : {e // S.tag e = none}, f e.val)+
        ∑ p : Fin r × Fin 2, ∑ e : {e // S.tag e = some p}, f e.val)+(G.constant:ℂ) • 1 := by abel
    _ = _ := congrArg (fun x => x+(G.constant:ℂ) • 1) hp

end QMARationalCrossingSelection
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingSelectionUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disjoint physical terminal sets make crossing-edge assignment unique.
Consequently the finite endpoint test computes the canonical selection. -/

noncomputable section
namespace ContinuumCoulomb.QMARationalExchangeGraph
open scoped Classical

private theorem crossingMatch_left_parity (G : QMARationalExchangeGraph) {r : ℕ}
    (site : Fin r → Fin 4 → Fin G.n) (e : G.Edge) (p : Fin r × Fin 2)
    (h : G.CrossingMatch site e p) :
    ∃ k : Fin 4, site p.1 k=G.left e ∧ k.val%2=p.2.val := by
  rcases p with ⟨i,a⟩
  fin_cases a
  · rcases h with ⟨hl,_⟩ | ⟨hl,_⟩
    · exact ⟨0,hl.symm,rfl⟩
    · exact ⟨2,hl.symm,rfl⟩
  · rcases h with ⟨hl,_⟩ | ⟨hl,_⟩
    · exact ⟨1,hl.symm,rfl⟩
    · exact ⟨3,hl.symm,rfl⟩

theorem crossingMatch_unique (G : QMARationalExchangeGraph) {r : ℕ}
    (site : Fin r → Fin 4 → Fin G.n)
    (hinj : Function.Injective (fun p : Fin r × Fin 4 => site p.1 p.2))
    {e : G.Edge} {p q : Fin r × Fin 2}
    (hp : G.CrossingMatch site e p) (hq : G.CrossingMatch site e q) : p=q := by
  obtain ⟨a,ha,hpa⟩ := crossingMatch_left_parity G site e p hp
  obtain ⟨b,hb,hqb⟩ := crossingMatch_left_parity G site e q hq
  have hi : (p.1,a)=(q.1,b) := hinj (ha.trans hb.symm)
  have hab : a=b := congrArg Prod.snd hi
  have hindex : p.1=q.1 := congrArg (fun z : Fin r × Fin 4 => z.1) hi
  refine Prod.ext hindex (Fin.ext ?_)
  rw [← hpa,← hqb,hab]

theorem crossingTag_some_iff (G : QMARationalExchangeGraph) {r : ℕ}
    (site : Fin r → Fin 4 → Fin G.n)
    (hinj : Function.Injective (fun p : Fin r × Fin 4 => site p.1 p.2))
    (e : G.Edge) (p : Fin r × Fin 2) :
    G.crossingTag site e=some p ↔ G.CrossingMatch site e p := by
  constructor
  · exact G.crossingTag_some site
  · intro hp
    cases ht : G.crossingTag site e with
    | none => exact ((G.crossingTag_none site).mp ht p hp).elim
    | some q =>
      have hq := G.crossingTag_some site ht
      have hqp := G.crossingMatch_unique site hinj hq hp
      exact congrArg some hqp

end ContinuumCoulomb.QMARationalExchangeGraph

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingSelectCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite endpoint scans recover the actual selected rational couplings.
No matrix or energy comparison is assumed by this source-data bridge. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingSelectProgram
open QuantumCrossingListBlock
open scoped BigOperators Classical

theorem terminalPair_encoded {n r : ℕ} (site : Fin r → Fin 4 → Fin n)
    (i : Fin r) (a : Fin 2) :
    terminalPair a (encodedSites site i)=
      ((site i (if a=0 then 0 else 1)).val,(site i (if a=0 then 2 else 3)).val) := by
  fin_cases a <;> rfl

theorem hits_selected {G : QMARationalExchangeGraph} {r : ℕ}
    (S : QMARationalCrossingSelection G r)
    (htag : ∀ e i a, S.tag e=some (i,a) ↔ G.CrossingMatch S.site e (i,a))
    (e : G.Edge) (i : Fin r) (a : Fin 2) :
    hits (((G.left e).val,(G.right e).val,G.weight e),terminalPair a (encodedSites S.site i)) =
      decide (S.tag e=some (i,a)) := by
  apply Bool.eq_iff_iff.mpr
  rw [hits_iff,decide_eq_true_eq,htag,terminalPair_encoded]
  simp only [QMARationalExchangeGraph.CrossingMatch,Prod.mk.injEq,Fin.ext_iff]
  tauto

theorem weight_selected {G : QMARationalExchangeGraph} {r : ℕ}
    (S : QMARationalCrossingSelection G r)
    (htag : ∀ e i a, S.tag e=some (i,a) ↔ G.CrossingMatch S.site e (i,a))
    {m : ℕ} (labels : G.Edge ≃ Fin m) (i : Fin r) (a : Fin 2) :
    weight (QuantumListGraph.packed G labels,terminalPair a (encodedSites S.site i))=
      S.weight (i,a) := by
  simp only [weight,QuantumListGraph.packed,List.map_ofFn,List.sum_ofFn,
    Function.comp_apply,contribution,hits_selected S htag,decide_eq_true_eq]
  unfold QMARationalCrossingSelection.weight
  rw [qmaSumSubtypePredicate]
  exact labels.symm.sum_comp (fun e => if S.tag e=some (i,a) then G.weight e else 0)

end ContinuumCoulomb.QuantumCrossingSelectProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingRetention
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPathSchedule.mem_active _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_old _root_.OAI.ContinuumCoulomb.QMAPortRouteData.mem_crossingCells _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_fresh _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_old _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.value_length _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact retained-edge semantics of the finite crossing scan. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingSelectProgram
open QuantumCrossingListBlock
open scoped BigOperators Classical

theorem pairs_ofFn_mem {r : ℕ} (ss : Fin r → Sites) (p : QuantumRouteCode.Pair) :
    p ∈ pairs (List.ofFn ss) ↔ ∃ i a, terminalPair a (ss i)=p := by
  rw [pairs,List.map_ofFn]
  constructor
  · intro h
    obtain ⟨xs,hxs,hp⟩ := List.mem_flatten.mp h
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hxs
    rcases List.mem_cons.mp hp with hp | hp
    · exact ⟨i,0,hp.symm⟩
    · exact ⟨i,1,(List.mem_singleton.mp hp).symm⟩
  · rintro ⟨i,a,rfl⟩
    apply List.mem_flatten.mpr
    refine ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,?_⟩
    fin_cases a <;> simp

theorem keep_selected {G : QMARationalExchangeGraph} {r : ℕ}
    (S : QMARationalCrossingSelection G r)
    (htag : ∀ e i a, S.tag e=some (i,a) ↔ G.CrossingMatch S.site e (i,a))
    (e : G.Edge) :
    keep (pairs (List.ofFn (encodedSites S.site)),
      ((G.left e).val,(G.right e).val,G.weight e))=decide (S.tag e=none) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  change (!(pairs (List.ofFn (encodedSites S.site))).any
    (fun p => hits (((G.left e).val,(G.right e).val,G.weight e),p)))=true ↔ _
  rw [Bool.not_eq_true_eq_eq_false,List.any_eq_false]
  constructor
  · intro h
    cases ht : S.tag e with
    | none => rfl
    | some p =>
      have hm := (pairs_ofFn_mem (encodedSites S.site)
        (terminalPair p.2 (encodedSites S.site p.1))).mpr ⟨p.1,p.2,rfl⟩
      have hn := h _ hm
      rw [hits_selected S htag,ht] at hn
      exact (hn (by simp)).elim
  · intro ht p hp
    obtain ⟨i,a,rfl⟩ := (pairs_ofFn_mem (encodedSites S.site) p).mp hp
    rw [hits_selected S htag,ht]
    simp

private theorem filter_matrix (n : ℕ) (ps : List QuantumRouteCode.Pair)
    (es : List MediatorListProgram.Bond) :
    SourceBondLists.matrix n (retained (ps,es)) =
      (es.map (fun e => if keep (ps,e) then SourceBondLists.bondMatrix n e else 0)).sum := by
  unfold retained
  induction es with
  | nil => rfl
  | cons e es ih =>
    change (List.map (SourceBondLists.bondMatrix n)
      (List.filter (fun e => keep (ps,e)) (e::es))).sum = _
    change (List.map (SourceBondLists.bondMatrix n)
      (List.filter (fun e => keep (ps,e)) es)).sum = _ at ih
    cases h : keep (ps,e) <;> simp only [List.filter_cons,h,Bool.false_eq_true,
      ite_false, if_false,ite_true, if_true,List.map_cons,List.sum_cons,zero_add] <;> rw [ih]

theorem retained_matrix {G : QMARationalExchangeGraph} {r : ℕ}
    (S : QMARationalCrossingSelection G r)
    (htag : ∀ e i a, S.tag e=some (i,a) ↔ G.CrossingMatch S.site e (i,a))
    {m : ℕ} (labels : G.Edge ≃ Fin m) :
    SourceBondLists.matrix G.n
      (retained (pairs (List.ofFn (encodedSites S.site)),QuantumListGraph.packed G labels))+
      (G.constant:ℂ) • 1 =
      qmaExchangeMatrix S.retained.left S.retained.right
        (fun e => (S.retained.weight e:ℝ)) S.retained.constant := by
  rw [filter_matrix]
  have hb (e : G.Edge) : SourceBondLists.bondMatrix G.n
      ((G.left e).val,(G.right e).val,G.weight e)=
        (G.weight e:ℂ) • sourceHeisenbergMatrix G.n (G.left e) (G.right e) := by
    rw [SourceBondLists.bondMatrix,dite_eq_left ⟨(G.left e).isLt,(G.right e).isLt⟩]
  simp only [QuantumListGraph.packed,List.map_ofFn,List.sum_ofFn,Function.comp_apply,
    keep_selected S htag,decide_eq_true_eq,hb]
  have hs := labels.symm.sum_comp (fun e => if S.tag e=none then
    (G.weight e:ℂ) • sourceHeisenbergMatrix G.n (G.left e) (G.right e) else 0)
  rw [hs,← qmaSumSubtypePredicate]
  rfl

end ContinuumCoulomb.QuantumCrossingSelectProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingCompiled
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full-space correctness of the computed crossing transformation, starting
from an ordinary finite bond tape and its selected physical terminals. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingSelectProgram
open QuantumCrossingListBlock
open scoped Classical

variable {G : QMARationalExchangeGraph} {r : ℕ}
    (S : QMARationalCrossingSelection G r) {m : ℕ} (labels : G.Edge ≃ Fin m)

private theorem packed_ofBonds (n : ℕ) (xs : List MediatorListProgram.Bond) (c : ℚ)
    (hb : SourceBondLists.bounded n xs) (hn : ∀ e ∈ xs, e.1 ≠ e.2.1) :
    QuantumListGraph.packed (QuantumListGraph.ofBonds n xs c hb hn) (Equiv.refl _)=xs := by
  change List.ofFn (fun i : Fin xs.length => xs.get i)=xs
  exact List.ofFn_get xs

theorem compiled_packet (N : ℚ) :
    value (N,(G.n,QuantumListGraph.packed G labels,G.constant),
      List.ofFn (encodedSites S.site)) =
      QuantumCrossingListLayer.actualInput (computedLayer S labels) N (Equiv.refl _) := by
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · exact (packed_ofBonds G.n
            (retained (pairs (List.ofFn (encodedSites S.site)),QuantumListGraph.packed G labels))
            G.constant (retained_bounded _ _ (QuantumListGraph.packed_bounded G labels))
            (retained_noLoops _ _ (QuantumListGraph.packed_noLoops G labels))).symm
        · rfl
  · simp only [value,crossings,QuantumCrossingListLayer.actualInput,List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    rfl

variable (htag : ∀ e i a, S.tag e=some (i,a) ↔ G.CrossingMatch S.site e (i,a))
include htag

theorem retainedGraph_matrix :
    qmaExchangeMatrix (retainedGraph S labels).left (retainedGraph S labels).right
      (fun e => ((retainedGraph S labels).weight e:ℝ)) (retainedGraph S labels).constant =
      qmaExchangeMatrix S.retained.left S.retained.right
        (fun e => (S.retained.weight e:ℝ)) S.retained.constant := by
  exact (QuantumListGraph.ofBonds_matrix G.n
    (retained (pairs (List.ofFn (encodedSites S.site)),QuantumListGraph.packed G labels))
    G.constant (retained_bounded _ _ (QuantumListGraph.packed_bounded G labels))
    (retained_noLoops _ _ (QuantumListGraph.packed_noLoops G labels))).trans
      (retained_matrix S htag labels)

theorem computedLayer_source_matrix :
    qmaExchangeMatrix (computedLayer S labels).source.left (computedLayer S labels).source.right
      (fun e => ((computedLayer S labels).source.weight e:ℝ))
      (computedLayer S labels).source.constant =
      qmaExchangeMatrix G.left G.right (fun e => (G.weight e:ℝ)) G.constant := by
  apply (QMARationalCrossingLayer.source_matrix (computedLayer S labels)).trans
  apply Eq.trans _ ((S.layer.source_matrix).symm.trans S.source_matrix)
  apply congrArg₂ (fun a b : Matrix (SourceSpinBasis G.n) (SourceSpinBasis G.n) ℂ => a+b)
  · exact retainedGraph_matrix S labels htag
  · apply Finset.sum_congr rfl
    intro i _
    change
      (weight (QuantumListGraph.packed G labels,terminalPair 0 (encodedSites S.site i)):ℂ) •
          sourceHeisenbergMatrix G.n (S.site i 0) (S.site i 2) +
        (weight (QuantumListGraph.packed G labels,terminalPair 1 (encodedSites S.site i)):ℂ) •
          sourceHeisenbergMatrix G.n (S.site i 1) (S.site i 3) = _
    rw [weight_selected S htag,weight_selected S htag]
    rfl

theorem computedLayer_source_energy : (computedLayer S labels).source.energy=G.energy := by
  exact congrArg (sourceMatrixBottom G.n) (computedLayer_source_matrix S labels htag)

theorem compiled_energy_error {N : ℚ} (hN : 0 < N) :
    |(QuantumCrossingListLayer.actualGraph (computedLayer S labels) N (Equiv.refl _)).energy-
        G.energy| ≤ 1/(N:ℝ) := by
  rw [← computedLayer_source_energy S labels htag]
  exact QuantumCrossingListLayer.energy_error (computedLayer S labels) hN (Equiv.refl _)

end ContinuumCoulomb.QuantumCrossingSelectProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingPacketEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full-space crossing error stated directly for the serialized bond packet. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingPacketEnergy
open QuantumCrossingListBlock MediatorListProgram QuantumCrossingSelectProgram
open scoped Classical

theorem actual_energy {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) {m : ℕ}
    (labels : C.base.Edge ≃ Fin m) :
    energy (QuantumCrossingListLayer.value (QuantumCrossingListLayer.actualInput C N labels))=
      (QuantumCrossingListLayer.actualGraph C N labels).energy := by
  symm
  unfold QuantumCrossingListLayer.actualGraph QuantumCrossingListLayer.graph
  rw [QuantumListGraph.ofBonds_energy]
  rfl

theorem compiled_error {G : QMARationalExchangeGraph} {r m : ℕ}
    (S : QMARationalCrossingSelection G r) (labels : G.Edge ≃ Fin m)
    (htag : ∀ e i a, S.tag e=some (i,a) ↔ G.CrossingMatch S.site e (i,a))
    {N : ℚ} (hN : 0<N) :
    |energy (QuantumCrossingListLayer.value
      (QuantumCrossingSelectProgram.value
        (N,(G.n,QuantumListGraph.packed G labels,G.constant),List.ofFn (encodedSites S.site))))-
      G.energy|≤1/(N:ℝ) := by
  rw [QuantumCrossingSelectProgram.compiled_packet,
    actual_energy (computedLayer S labels) N (Equiv.refl _)]
  exact QuantumCrossingSelectProgram.compiled_energy_error S labels htag hN

theorem list_error_oai (n : ℕ) (bs : List Bond) (c : ℚ)
    (hb : SourceBondLists.bounded n bs) (hn : ∀ e ∈ bs, e.1≠e.2.1)
    {r : ℕ} (site : Fin r → Fin 4 → Fin n)
    (hinj : Function.Injective (fun p : Fin r × Fin 4 => site p.1 p.2))
    {N : ℚ} (hN : 0<N) :
    |energy (QuantumCrossingListLayer.value
      (QuantumCrossingSelectProgram.value (N,(n,bs,c),List.ofFn (encodedSites site))))-
      energy (n,bs,c)|≤1/(N:ℝ) := by
  let G := QuantumListGraph.ofBonds n bs c hb hn
  have hi (i : Fin r) : Function.Injective (site i) := by
    intro a b h
    exact congrArg Prod.snd (hinj (a₁ := (i,a)) (a₂ := (i,b)) h)
  let S : QMARationalCrossingSelection G r := G.crossingSelection site hi
  have ht : ∀ e i a, S.tag e=some (i,a) ↔ G.CrossingMatch S.site e (i,a) := by
    intro e i a
    exact G.crossingTag_some_iff site hinj e (i,a)
  have he := compiled_error S (Equiv.refl _) ht hN
  have hp : QuantumListGraph.packed G (Equiv.refl _)=bs := by
    exact List.ofFn_get bs
  rw [hp] at he
  have hge : G.energy=energy (n,bs,c) := QuantumListGraph.ofBonds_energy n bs c hb hn
  rw [hge] at he
  exact he

end ContinuumCoulomb.QuantumCrossingPacketEnergy

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.QuantumCrossingPacketEnergy.list_error_oai := @OAI.ContinuumCoulomb.QuantumCrossingPacketEnergy.list_error_oai
