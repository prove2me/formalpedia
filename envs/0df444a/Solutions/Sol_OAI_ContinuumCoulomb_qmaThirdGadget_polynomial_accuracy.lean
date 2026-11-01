-- Prove2me | solution 1 for OAI.ContinuumCoulomb.qmaThirdGadget_polynomial_accuracy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:16:06.8623+00:00
-- url     : https://prove2.me/submissions/532976ad-3a0f-467c-b72e-6e4c500e1d36

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
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Size
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
import Definitions.Def_OAIQ092A007

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

end Perturbation
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_SpinMatrixNorm
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

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorGraph
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

section Reindex
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

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

end ContinuumCoulomb.MediatorGraph

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_ClockWeightedBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-weight clock bounds retain a strict completeness/soundness margin. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

theorem norm_add_sq_two {E : Type*} [NormedAddCommGroup E] (a b : E) :
    ‖a+b‖^2 ≤ 2*‖a‖^2+2*‖b‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg (a+b)) (norm_add_le a b) 2
  nlinarith [sq_nonneg (‖a‖-‖b‖)]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ThirdOrderPerturbation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A third-order block estimate. Keeping the high-block correction in the
effective form makes simultaneous three-body gadgets have a decreasing error. -/

noncomputable section
namespace ContinuumCoulomb.Perturbation
open scoped InnerProductSpace

variable {L H : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem thirdOrder_square_identity (C : L →L[ℝ] L) (A T D : H →L[ℝ] H)
    (B : L →L[ℝ] H) (hAT : ∀ x, A (T x) = x)
    (hAsymm : ∀ x y, ⟪x,A y⟫_ℝ = ⟪A x,y⟫_ℝ)
    (hDsymm : ∀ x y, ⟪x,D y⟫_ℝ = ⟪D x,y⟫_ℝ) (p : L) (q : H) :
    lowBlockEnergy C A D B p q = thirdOrderForm C T D B p +
      penaltyForm A (q+T (B p)) + ⟪q+T (B p),D (q+T (B p))⟫_ℝ -
        2*⟪q+T (B p),D (T (B p))⟫_ℝ := by
  have hi := penalty_square_identity A T B hAT hAsymm p q (by norm_num : (1:ℝ) ≠ 0)
  simp only [one_mul,inv_one,one_smul] at hi
  have hc : ⟪T (B p),D q⟫_ℝ = ⟪q,D (T (B p))⟫_ℝ := by
    rw [hDsymm,real_inner_comm]
  simp only [map_add,inner_add_left,inner_add_right,hc]
  unfold lowBlockEnergy blockEnergy thirdOrderForm effectiveForm
  linarith

private theorem quadratic_cross_bound {g d x z : ℝ} (hg : 0 < g) :
    -(2*d^2/g)*z^2 ≤ g/2*x^2-2*d*x*z := by
  apply (mul_le_mul_iff_right₀ hg).mp
  field_simp
  nlinarith [sq_nonneg (g*x-2*d*z)]

theorem thirdOrder_energy_lower (C : L →L[ℝ] L) (A T D : H →L[ℝ] H)
    (B : L →L[ℝ] H) {g d m η μ : ℝ} (hg : 0 < g)
    (_hd : 0 ≤ d) (hm : 0 ≤ m) (hsmall : 2*d+4*m ≤ g)
    (hAT : ∀ x, A (T x) = x)
    (hAsymm : ∀ x y, ⟪x,A y⟫_ℝ = ⟪A x,y⟫_ℝ)
    (hDsymm : ∀ x y, ⟪x,D y⟫_ℝ = ⟪D x,y⟫_ℝ)
    (hgap : ∀ q, g*‖q‖^2 ≤ penaltyForm A q)
    (hTB : ∀ p, ‖T (B p)‖ ≤ η*‖p‖) (hD : ‖D‖ ≤ d)
    (hμ : μ ≤ m) (hmin : ∀ p, μ*‖p‖^2 ≤ thirdOrderForm C T D B p)
    (p : L) (q : H) :
    -(2*d^2/g+2*m)*η^2*‖p‖^2 ≤
      lowBlockEnergy C A D B p q-μ*(‖p‖^2+‖q‖^2) := by
  let z := T (B p)
  let y := q+z
  have hi := thirdOrder_square_identity C A T D B hAT hAsymm hDsymm p q
  have hnorm := norm_add_sq_two y (-z)
  have hyz : y+(-z) = q := by dsimp [y]; abel
  rw [hyz,norm_neg] at hnorm
  have hz : ‖z‖^2 ≤ η^2*‖p‖^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hTB p) 2
  have hdq : -(d*‖y‖^2) ≤ ⟪y,D y⟫_ℝ := by
    have h := highPerturbation_abs_le D (g := 1) (ε := d) (by simpa using hD) y
    simpa using (abs_le.mp h).1
  have hDz : ‖D z‖ ≤ d*‖z‖ :=
    (D.le_opNorm z).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
  have hcross : ⟪y,D z⟫_ℝ ≤ ‖y‖*d*‖z‖ := by
    calc
      _ ≤ ‖y‖*‖D z‖ := real_inner_le_norm _ _
      _ ≤ ‖y‖*(d*‖z‖) := mul_le_mul_of_nonneg_left hDz (norm_nonneg _)
      _ = _ := by ring
  have hquad := quadratic_cross_bound (d := d) (x := ‖y‖) (z := ‖z‖) hg
  have hscale := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖y‖)
  have hμq := mul_le_mul_of_nonneg_right hμ (sq_nonneg ‖q‖)
  have hmnorm := mul_le_mul_of_nonneg_left hnorm hm
  have hK : 0 ≤ 2*d^2/g+2*m := by positivity
  have hKz := mul_le_mul_of_nonneg_left hz hK
  have hgp := hgap y
  have hmp := hmin p
  change lowBlockEnergy C A D B p q = thirdOrderForm C T D B p +
    penaltyForm A y + ⟪y,D y⟫_ℝ - 2*⟪y,D z⟫_ℝ at hi
  nlinarith

theorem thirdOrder_trial_identity (C : L →L[ℝ] L) (A T D : H →L[ℝ] H)
    (B : L →L[ℝ] H) (hAT : ∀ x, A (T x) = x) (p : L) :
    lowBlockEnergy C A D B p (-(T (B p))) = thirdOrderForm C T D B p := by
  unfold lowBlockEnergy thirdOrderForm effectiveForm
  rw [blockEnergy_trial_identity A T D B hAT]
  simp only [map_neg,inner_neg_left,inner_neg_right]
  ring

theorem thirdOrder_trial_upper (C : L →L[ℝ] L) (A T D : H →L[ℝ] H)
    (B : L →L[ℝ] H) {m η μ : ℝ} (hm : 0 ≤ m)
    (hAT : ∀ x, A (T x) = x) (hTB : ∀ p, ‖T (B p)‖ ≤ η*‖p‖)
    (hμ : -m ≤ μ) (p : L) (hp : ‖p‖ = 1) (he : thirdOrderForm C T D B p = μ) :
    lowBlockRayleigh C A D B p (-(T (B p))) ≤ μ+m*η^2 := by
  have hz := pow_le_pow_left₀ (norm_nonneg _) (hTB p) 2
  rw [hp,mul_one] at hz
  unfold lowBlockRayleigh
  rw [thirdOrder_trial_identity C A T D B hAT,he,hp,norm_neg]
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 1^2+‖T (B p)‖^2)).mpr
  have hmz := mul_le_mul_of_nonneg_right hμ (sq_nonneg ‖T (B p)‖)
  have hη := mul_le_mul_of_nonneg_left hz hm
  have hx : 0 ≤ m*η^2*‖T (B p)‖^2 := by positivity
  nlinarith

end ContinuumCoulomb.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ThirdOrderBottom
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Third-order comparison of actual finite-dimensional ground energies. -/

noncomputable section
namespace ContinuumCoulomb.Perturbation
open scoped InnerProductSpace
variable {L H : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem thirdOrderForm_smul (C : L →L[ℝ] L) (T D : H →L[ℝ] H)
    (B : L →L[ℝ] H) (r : ℝ) (p : L) :
    thirdOrderForm C T D B (r • p) = r^2*thirdOrderForm C T D B p := by
  simp only [thirdOrderForm,effectiveForm_smul,map_smul,
    real_inner_smul_left,real_inner_smul_right]
  ring

theorem thirdOrderForm_minimizer [FiniteDimensional ℝ L]
    (C : L →L[ℝ] L) (T D : H →L[ℝ] H) (B : L →L[ℝ] H)
    (u : L) (hu : ‖u‖ = 1) :
    ∃ p : L, ‖p‖ = 1 ∧ ∀ x : L,
      thirdOrderForm C T D B p*‖x‖^2 ≤ thirdOrderForm C T D B x := by
  have := FiniteDimensional.proper_rclike ℝ L
  have hTB : Continuous (fun p => T (B p)) := T.continuous.comp B.continuous
  have hc : Continuous (thirdOrderForm C T D B) :=
    ((continuous_id.inner C.continuous).sub
      (B.continuous.inner hTB)).add (hTB.inner (D.continuous.comp hTB))
  have hn : (Metric.sphere (0 : L) 1).Nonempty := ⟨u,by simpa using hu⟩
  obtain ⟨p,hp,hmin⟩ := (isCompact_sphere (0 : L) 1).exists_isMinOn hn hc.continuousOn
  refine ⟨p,by simpa using hp,?_⟩
  intro x
  by_cases hx : x = 0
  · simp [hx,thirdOrderForm,effectiveForm,inverseForm]
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hunit : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := norm_smul_inv_norm hx
  have h := hmin (show (‖x‖⁻¹ : ℝ) • x ∈ Metric.sphere (0 : L) 1 by simpa using hunit)
  change thirdOrderForm C T D B p ≤ thirdOrderForm C T D B ((‖x‖⁻¹ : ℝ) • x) at h
  rw [thirdOrderForm_smul] at h
  calc
    _ ≤ (‖x‖⁻¹^2*thirdOrderForm C T D B x)*‖x‖^2 :=
      mul_le_mul_of_nonneg_right h (sq_nonneg _)
    _ = _ := by field_simp

theorem thirdOrderBottom_eq (C : L →L[ℝ] L) (T D : H →L[ℝ] H)
    (B : L →L[ℝ] H) (p : L) (hp : ‖p‖ = 1)
    (hmin : ∀ x, thirdOrderForm C T D B p*‖x‖^2 ≤ thirdOrderForm C T D B x) :
    thirdOrderBottom C T D B = thirdOrderForm C T D B p := by
  have hl (e : ℝ) (he : ∃ x : L, ‖x‖ = 1 ∧ e = thirdOrderForm C T D B x) :
      thirdOrderForm C T D B p ≤ e := by
    obtain ⟨x,hx,rfl⟩ := he
    simpa only [hx,one_pow,mul_one] using hmin x
  exact le_antisymm (csInf_le ⟨_,hl⟩ ⟨p,hp,rfl⟩) (le_csInf ⟨_,p,hp,rfl⟩ hl)

end ContinuumCoulomb.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_OrthogonalBlockDecomposition
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Block coordinates on an orthogonal subspace and its actual complement.
The high space may retain an unused copy of the low coordinates, since the
physical vectors and trial vectors lie in the kernel of the restriction. -/

noncomputable section
namespace ContinuumCoulomb.Perturbation
open scoped InnerProductSpace
variable {L H : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem orthogonalHighPart_kernel (E : L →L[ℝ] H) (R : H →L[ℝ] L)
    (hRE : ∀ p, R (E p) = p) (x : H) : R (orthogonalHighPart E R x) = 0 := by
  simp [orthogonalHighPart,hRE]

theorem orthogonal_assemble (E : L →L[ℝ] H) (R : H →L[ℝ] L) (x : H) :
    E (R x)+orthogonalHighPart E R x = x := by
  unfold orthogonalHighPart
  abel

theorem orthogonalInclusion_norm (E : L →L[ℝ] H) (R : H →L[ℝ] L)
    (hRE : ∀ p, R (E p) = p) (hAdj : ∀ p x, ⟪E p,x⟫_ℝ = ⟪p,R x⟫_ℝ) (p : L) :
    ‖E p‖ = ‖p‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, hAdj,hRE,real_inner_self_eq_norm_sq]

theorem orthogonalParts_norm (E : L →L[ℝ] H) (R : H →L[ℝ] L)
    (hRE : ∀ p, R (E p) = p) (hAdj : ∀ p x, ⟪E p,x⟫_ℝ = ⟪p,R x⟫_ℝ) (x : H) :
    ‖R x‖^2+‖orthogonalHighPart E R x‖^2 = ‖x‖^2 := by
  have h := norm_add_sq_real (E (R x)) (orthogonalHighPart E R x)
  rw [orthogonal_assemble,hAdj,orthogonalHighPart_kernel E R hRE,inner_zero_right,
    orthogonalInclusion_norm E R hRE hAdj] at h
  linarith

theorem orthogonalAssemble_norm (E : L →L[ℝ] H) (R : H →L[ℝ] L)
    (hRE : ∀ p, R (E p) = p) (hAdj : ∀ p x, ⟪E p,x⟫_ℝ = ⟪p,R x⟫_ℝ)
    (p : L) (q : H) (hq : R q = 0) : ‖E p+q‖^2 = ‖p‖^2+‖q‖^2 := by
  rw [norm_add_sq_real,hAdj,hq,inner_zero_right,orthogonalInclusion_norm E R hRE hAdj]
  ring

theorem orthogonalBlock_energy (E : L →L[ℝ] H) (R : H →L[ℝ] L)
    (M A D : H →L[ℝ] H) (C : L →L[ℝ] L) (B : L →L[ℝ] H)
    (hRE : ∀ p, R (E p) = p) (hAdj : ∀ p x, ⟪E p,x⟫_ℝ = ⟪p,R x⟫_ℝ)
    (hM : ∀ x y, ⟪x,M y⟫_ℝ = ⟪M x,y⟫_ℝ)
    (hLow : ∀ p, M (E p) = E (C p)+B p) (hRB : ∀ p, R (B p) = 0)
    (hHigh : ∀ q, R q = 0 → ⟪q,M q⟫_ℝ = penaltyForm A q+⟪q,D q⟫_ℝ)
    (p : L) (q : H) (hq : R q = 0) :
    ⟪E p+q,M (E p+q)⟫_ℝ = lowBlockEnergy C A D B p q := by
  have hEq : ⟪E p,M (E p)⟫_ℝ = ⟪p,C p⟫_ℝ := by
    rw [hLow,inner_add_right,hAdj,hRE,hAdj,hRB,inner_zero_right,add_zero]
  have hqE : ⟪q,E (C p)⟫_ℝ = 0 := by
    rw [real_inner_comm,hAdj,hq,inner_zero_right]
  have hqM : ⟪q,M (E p)⟫_ℝ = ⟪q,B p⟫_ℝ := by
    rw [hLow,inner_add_right,hqE,zero_add]
  have hMq : ⟪E p,M q⟫_ℝ = ⟪q,B p⟫_ℝ := by
    rw [hM,real_inner_comm,hqM]
  simp only [map_add,inner_add_left,inner_add_right,hEq,hqM,hMq,hHigh q hq]
  unfold lowBlockEnergy blockEnergy
  ring

theorem orthogonalBlock_full_energy (E : L →L[ℝ] H) (R : H →L[ℝ] L)
    (M A D : H →L[ℝ] H) (C : L →L[ℝ] L) (B : L →L[ℝ] H)
    (hRE : ∀ p, R (E p) = p) (hAdj : ∀ p x, ⟪E p,x⟫_ℝ = ⟪p,R x⟫_ℝ)
    (hM : ∀ x y, ⟪x,M y⟫_ℝ = ⟪M x,y⟫_ℝ)
    (hLow : ∀ p, M (E p) = E (C p)+B p) (hRB : ∀ p, R (B p) = 0)
    (hHigh : ∀ q, R q = 0 → ⟪q,M q⟫_ℝ = penaltyForm A q+⟪q,D q⟫_ℝ) (x : H) :
    ⟪x,M x⟫_ℝ = lowBlockEnergy C A D B (R x) (orthogonalHighPart E R x) := by
  have h := orthogonalBlock_energy E R M A D C B hRE hAdj hM hLow hRB hHigh
    (R x) (orthogonalHighPart E R x) (orthogonalHighPart_kernel E R hRE x)
  rwa [orthogonal_assemble] at h

end ContinuumCoulomb.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ThirdOrderScale
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial scales for the simultaneous third-order estimate. -/

namespace ContinuumCoulomb.Perturbation

theorem thirdOrder_scale_small {K R : ℝ} (hK : 1 ≤ K) (hR : 4*K ≤ R) :
    2*(K*R^2)+4*(2*K) ≤ R^3 := by
  have hR4 : 4 ≤ R := by linarith
  have hr2 : 4 ≤ R^2 := by nlinarith
  have hfirst := mul_le_mul_of_nonneg_right hR (sq_nonneg R)
  have hsecond := mul_le_mul_of_nonneg_left hr2 (show 0 ≤ R by linarith)
  nlinarith

theorem thirdOrder_scale_error {K R : ℝ} (hK : 1 ≤ K) (hR : 4*K ≤ R) :
    (2*(K*R^2)^2/R^3+2*(2*K))*(K/R)^2 ≤ 4*K^4/R := by
  have hRp : 0 < R := by linarith
  have hKp : 0 < K := by linarith
  apply (le_div_iff₀ hRp).mpr
  have he : ((2*(K*R^2)^2/R^3+2*(2*K))*(K/R)^2)*R =
      2*K^4+4*K^3/R := by field_simp; ring
  rw [he]
  have hKR : 2 ≤ K*R := by nlinarith
  have hk3 : 0 ≤ K^3 := by positivity
  have h : 4*K^3/R ≤ 2*K^4 := by
    apply (div_le_iff₀ hRp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hKR (show 0 ≤ 2*K^3 by positivity)]
  linarith

theorem thirdOrder_polynomial_schedule {K N : ℝ} (hK : 1 ≤ K) (hN : 1 ≤ N) :
    let R := 8*K^4*N
    4*K ≤ R ∧
      2*(K*R^2)+4*(2*K) ≤ R^3 ∧
      (2*(K*R^2)^2/R^3+2*(2*K))*(K/R)^2 ≤ 1/N := by
  let R := 8*K^4*N
  have hk4 : K ≤ K^4 := le_self_pow₀ hK (by norm_num : (4:ℕ) ≠ 0)
  have hk4p : 0 < K^4 := by positivity
  have hR : 4*K ≤ R := by
    dsimp [R]
    have h := mul_le_mul_of_nonneg_left hN (show 0 ≤ 8*K^4 by positivity)
    nlinarith
  refine ⟨hR,thirdOrder_scale_small hK hR,(thirdOrder_scale_error hK hR).trans ?_⟩
  have hNp : 0 < N := by linarith
  change 4*K^4/(8*K^4*N) ≤ 1/N
  calc
    _ = 1/(2*N) := by field_simp; ring
    _ ≤ 1/N := one_div_le_one_div_of_le hNp (by linarith)

end ContinuumCoulomb.Perturbation

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumQuadratic
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite matrix quadratic forms used by the explicit history Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaQuadratic_add {ι : Type*} [Fintype ι]
    (M N : Matrix ι ι ℂ) (u : ι → ℂ) :
    qmaQuadratic (M+N) u = qmaQuadratic M u+qmaQuadratic N u := by
  simp [qmaQuadratic,Matrix.add_mulVec,dotProduct_add]

theorem qmaQuadratic_smul {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℂ) (a : ℝ) (u : ι → ℂ) :
    qmaQuadratic ((a:ℂ) • M) u = a*qmaQuadratic M u := by
  simp [qmaQuadratic,Matrix.smul_mulVec,dotProduct_smul,Complex.mul_re]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLocalAction
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actions of local flips and spectator-identity tensor factors. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem qmaBitFlip_involutive (i : ι) : Function.Involutive (qmaBitFlip i) := by
  intro s
  funext j
  by_cases h : j = i
  · subst j
    simp [qmaBitFlip]
  · simp [qmaBitFlip,h]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitMediatorAncilla
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Occupation coordinates for the parallel qubit mediator gadgets. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [Fintype κ] in
theorem qmaAncillaSingle_apply (e f : κ) :
    qmaAncillaSingle e f = if f = e then 1 else 0 := by
  simp [qmaAncillaSingle,qmaAncillaVacuum,Function.update_apply]

omit [Fintype κ] in
theorem qmaAncillaSingle_ne_vacuum (e : κ) : qmaAncillaSingle e ≠ qmaAncillaVacuum := by
  intro h
  have he := congrFun h e
  simp [qmaAncillaSingle,qmaAncillaVacuum] at he

omit [Fintype κ] in
theorem qmaAncillaSingle_injective : Function.Injective (qmaAncillaSingle (κ := κ)) := by
  intro e f h
  by_contra hef
  have he := congrFun h e
  simp [qmaAncillaSingle_apply,hef] at he

omit [Fintype κ] in
theorem qmaBitFlip_vacuum (e : κ) : qmaBitFlip e qmaAncillaVacuum = qmaAncillaSingle e := by
  simp [qmaBitFlip,qmaAncillaSingle,qmaAncillaVacuum]

omit [Fintype κ] in
theorem qmaBitFlip_single_self (e : κ) : qmaBitFlip e (qmaAncillaSingle e) = qmaAncillaVacuum := by
  rw [← qmaBitFlip_vacuum,qmaBitFlip_involutive]

omit [Fintype κ] in
theorem qmaBitFlip_single_ne_single (e f d : κ) :
    qmaAncillaSingle e ≠ qmaBitFlip f (qmaAncillaSingle d) := by
  intro h
  by_cases hfd : f = d
  · subst f
    rw [qmaBitFlip_single_self] at h
    exact qmaAncillaSingle_ne_vacuum e h
  · have hf := congrFun h f
    have hd := congrFun h d
    by_cases hef : e = f
    · subst e
      simp [qmaAncillaSingle_apply,qmaBitFlip,hfd,Ne.symm hfd] at hd
    · simp [qmaAncillaSingle_apply,qmaBitFlip,Ne.symm hef,hfd] at hf

@[simp] theorem qmaAncillaNumber_single (e : κ) :
    qmaAncillaNumber (qmaAncillaSingle e) = 1 := by
  simp [qmaAncillaNumber,qmaAncillaSingle_apply,apply_ite]

omit [DecidableEq κ] in
theorem qmaAncillaNumber_pos (a : κ → Fin 2) (ha : a ≠ qmaAncillaVacuum) :
    0 < qmaAncillaNumber a := by
  by_contra h
  have hz : qmaAncillaNumber a = 0 := by omega
  apply ha
  funext e
  have he : (a e).val ≤ qmaAncillaNumber a :=
    Finset.single_le_sum (f := fun i => (a i).val) (fun i _ => Nat.zero_le _) (Finset.mem_univ e)
  apply Fin.ext
  change (a e).val = 0
  omega

theorem qmaAncillaOccupation_single (e f d : κ) :
    qmaAncillaOccupation e (qmaAncillaSingle f) (qmaAncillaSingle d) =
      if f = d ∧ e = d then 1 else 0 := by
  unfold qmaAncillaOccupation
  rw [Matrix.diagonal_apply]
  by_cases hfd : f = d
  · subst f
    by_cases hed : e = d <;> simp [hed,qmaAncillaSingle_apply]
  · have hn := (Function.Injective.ne qmaAncillaSingle_injective hfd)
    simp [hfd,hn]

theorem qmaBitFlipMatrix_single (e f d : κ) :
    qmaBitFlipMatrix e (qmaAncillaSingle f) (qmaAncillaSingle d) = 0 := by
  exact ite_eq_right (qmaBitFlip_single_ne_single f e d)

theorem qmaBitFlipMatrix_vacuum_right (e : κ) (a : κ → Fin 2) :
    qmaBitFlipMatrix e a qmaAncillaVacuum = if a = qmaAncillaSingle e then 1 else 0 := by
  rw [qmaBitFlipMatrix,qmaBitFlip_vacuum]

omit [DecidableEq κ] in
theorem qmaAncillaOccupation_vacuum_right (e : κ) (a : κ → Fin 2) :
    qmaAncillaOccupation e a qmaAncillaVacuum = 0 := by
  by_cases ha : a = qmaAncillaVacuum
  · subst a
    simp [qmaAncillaOccupation,qmaAncillaVacuum]
  · simp [qmaAncillaOccupation,ha]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAncillaCompression
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact vacuum-to-one-excitation columns and their compressions.
All matrices retain every original system coordinate. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {σ α κ : Type*} [Fintype σ]
  [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]

theorem qmaSliceColumn_gram (a b : α) (A B : Matrix σ σ ℂ) :
    (qmaSliceColumn a A).conjTranspose*qmaSliceColumn b B =
      if a = b then A.conjTranspose*B else 0 := by
  ext s t
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,qmaSliceColumn,
    Fintype.sum_prod_type]
  by_cases hab : a = b
  · subst b
    simp [Matrix.mul_apply,Matrix.conjTranspose_apply]
  · simp [hab,Ne.symm hab]

theorem qmaSliceColumn_kronecker_apply (b : α) (D B : Matrix σ σ ℂ)
    (P : Matrix α α ℂ) (s : σ) (a : α) (t : σ) :
    ((D ⊗ₖ P)*qmaSliceColumn b B) (s,a) t = P a b*(D*B) s t := by
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,Matrix.kronecker_apply,
    qmaSliceColumn,mul_ite,mul_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  ring

theorem qmaSliceColumn_sandwich (a b : α) (A B D : Matrix σ σ ℂ)
    (P : Matrix α α ℂ) :
    (qmaSliceColumn a A).conjTranspose*(D ⊗ₖ P)*qmaSliceColumn b B =
      P a b • (A.conjTranspose*D*B) := by
  rw [Matrix.mul_assoc]
  ext s t
  change (∑ p : σ × α, star (qmaSliceColumn a A p s)*
    ((D ⊗ₖ P)*qmaSliceColumn b B) p t) = P a b*((A.conjTranspose*D*B) s t)
  rw [Fintype.sum_prod_type]
  simp only [qmaSliceColumn_kronecker_apply,qmaSliceColumn]
  simp only [apply_ite,star_zero,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]
  rw [Matrix.mul_assoc,Matrix.mul_apply,Finset.mul_sum]
  simp only [Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro u _
  ring

theorem qmaAncillaColumn_gram (V W : κ → Matrix σ σ ℂ) :
    (qmaAncillaColumn V).conjTranspose*qmaAncillaColumn W = ∑ e, (V e).conjTranspose*W e := by
  simp only [qmaAncillaColumn,Matrix.conjTranspose_sum,Matrix.sum_mul,Matrix.mul_sum,
    qmaSliceColumn_gram,qmaAncillaSingle_injective.eq_iff]
  simp

theorem qmaAncillaColumn_sandwich (V W : κ → Matrix σ σ ℂ) (D : Matrix σ σ ℂ)
    (P : Matrix (κ → Fin 2) (κ → Fin 2) ℂ) :
    (qmaAncillaColumn V).conjTranspose*(D ⊗ₖ P)*qmaAncillaColumn W =
      ∑ e, ∑ f, P (qmaAncillaSingle e) (qmaAncillaSingle f) •
        ((V e).conjTranspose*D*W f) := by
  unfold qmaAncillaColumn
  rw [Matrix.conjTranspose_sum,Matrix.sum_mul,Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  rw [Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  exact qmaSliceColumn_sandwich (qmaAncillaSingle e) (qmaAncillaSingle f) (V e) (W f) D P

theorem qmaAncillaColumn_occupation (V W : κ → Matrix σ σ ℂ)
    (D : Matrix σ σ ℂ) (e : κ) :
    (qmaAncillaColumn V).conjTranspose*(D ⊗ₖ qmaAncillaOccupation e)*qmaAncillaColumn W =
      (V e).conjTranspose*D*W e := by
  rw [qmaAncillaColumn_sandwich]
  simp only [qmaAncillaOccupation_single,ite_smul,one_smul,zero_smul]
  simp only [ite_and]
  simp

theorem qmaAncillaColumn_flip (V W : κ → Matrix σ σ ℂ) (D : Matrix σ σ ℂ) (e : κ) :
    (qmaAncillaColumn V).conjTranspose*(D ⊗ₖ qmaBitFlipMatrix e)*qmaAncillaColumn W = 0 := by
  rw [qmaAncillaColumn_sandwich]
  simp only [qmaBitFlipMatrix_single,zero_smul,Finset.sum_const_zero]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGadgetAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact low-block algebra for subdivision and three-body mediator gadgets. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qmaGadget_pair_square (A B : Matrix ι ι ℂ) (b : ℂ)
    (hA : A*A = 1) (hB : B*B = 1) (hAB : A*B = B*A) :
    (A+b • B)*(A+b • B) = (1+b^2) • (1 : Matrix ι ι ℂ)+(2*b) • (A*B) := by
  calc
    _ = A*A+b • (A*B)+b • (B*A)+(b*b) • (B*B) := by
      simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,smul_add,smul_smul]
      abel
    _ = _ := by
      rw [hA,hB,←hAB]
      module

theorem qmaGadget_pair_sandwich (A B C : Matrix ι ι ℂ) (b : ℂ)
    (hA : A*A = 1) (hB : B*B = 1) (hAB : A*B = B*A)
    (hAC : A*C = C*A) (hBC : B*C = C*B) :
    (A+b • B)*C*(A+b • B) = (1+b^2) • C+(2*b) • (A*B*C) := by
  have hc : (A+b • B)*C = C*(A+b • B) := by
    simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,hAC,hBC]
  rw [hc,mul_assoc,qmaGadget_pair_square A B b hA hB hAB,mul_add,mul_smul_comm,
    mul_smul_comm,mul_one]
  have he : C*(A*B) = A*B*C := by
    rw [←mul_assoc,←hAC,mul_assoc,←hBC,←mul_assoc]
  rw [he]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitMediatorMatrix
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

attribute [default_instance 200] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace OAI

/-! The literal parallel mediator Hamiltonian and its exact first three
vacuum-compressed terms. Single flips have zero third-order compression. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

theorem qmaMediatorFlips_vacuum (V : κ → Matrix σ σ ℂ) :
    qmaMediatorFlips V*qmaSliceColumn (qmaAncillaVacuum (κ := κ)) 1 = qmaAncillaColumn V := by
  unfold qmaMediatorFlips qmaAncillaColumn
  rw [Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  ext s t
  rcases s with ⟨s,a⟩
  rw [qmaSliceColumn_kronecker_apply,qmaBitFlipMatrix_vacuum_right,Matrix.mul_one]
  simp only [qmaSliceColumn,ite_mul,one_mul,zero_mul]

theorem qmaMediatorOccupations_vacuum (D : κ → Matrix σ σ ℂ) :
    qmaMediatorOccupations D*qmaSliceColumn (qmaAncillaVacuum (κ := κ)) (1 : Matrix σ σ ℂ) = 0 := by
  unfold qmaMediatorOccupations
  rw [Matrix.sum_mul]
  apply Finset.sum_eq_zero
  intro e _
  ext s t
  rcases s with ⟨s,a⟩
  rw [qmaSliceColumn_kronecker_apply,qmaAncillaOccupation_vacuum_right,zero_mul]
  rfl

omit [DecidableEq σ] in
theorem qmaAncillaColumn_identity (V W : κ → Matrix σ σ ℂ) (C : Matrix σ σ ℂ) :
    (qmaAncillaColumn V).conjTranspose*(C ⊗ₖ 1)*qmaAncillaColumn W =
      ∑ e, (V e).conjTranspose*C*W e := by
  rw [qmaAncillaColumn_sandwich]
  simp only [Matrix.one_apply,qmaAncillaSingle_injective.eq_iff,ite_smul,one_smul,zero_smul]
  simp

omit [DecidableEq σ] in
theorem qmaMediatorPerturbation_compression (C : Matrix σ σ ℂ)
    (D V W Z : κ → Matrix σ σ ℂ) :
    (qmaAncillaColumn W).conjTranspose*qmaMediatorPerturbation C D V*qmaAncillaColumn Z =
      (∑ e, (W e).conjTranspose*C*Z e)+(∑ e, (W e).conjTranspose*D e*Z e) := by
  unfold qmaMediatorPerturbation qmaMediatorOccupations qmaMediatorFlips
  rw [Matrix.mul_add,Matrix.mul_add,Matrix.add_mul,Matrix.add_mul,qmaAncillaColumn_identity,
    Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_sum,Matrix.sum_mul]
  simp only [qmaAncillaColumn_occupation,qmaAncillaColumn_flip,Finset.sum_const_zero,add_zero]

theorem qmaAncillaDiagonal_slice (w : (κ → Fin 2) → ℂ) (a : κ → Fin 2)
    (A : Matrix σ σ ℂ) :
    qmaAncillaDiagonal w*qmaSliceColumn a A = w a • qmaSliceColumn a A := by
  ext s t
  rcases s with ⟨s,b⟩
  rw [qmaAncillaDiagonal,qmaSliceColumn_kronecker_apply,Matrix.one_mul]
  by_cases h : b = a
  · subst b
    simp [qmaSliceColumn]
  · simp [qmaSliceColumn,h]

theorem qmaAncillaDiagonal_column (w : (κ → Fin 2) → ℂ) (V : κ → Matrix σ σ ℂ)
    (c : ℂ) (hw : ∀ e, w (qmaAncillaSingle e) = c) :
    qmaAncillaDiagonal w*qmaAncillaColumn V = c • qmaAncillaColumn V := by
  unfold qmaAncillaColumn
  rw [Matrix.mul_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [qmaAncillaDiagonal_slice,hw]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitMediatorNorm
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.spinMatrixOperator_diagonal _root_.OAI.ContinuumCoulomb.spinMatrixOperator_sub _root_.OAI.ContinuumCoulomb.spinMatrixOperator_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectator-independent norm estimates for the physical mediator terms. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {ι κ σ α : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype σ] [DecidableEq σ]
  [Fintype α] [DecidableEq α]

theorem qmaBitFlipMatrix_square (e : κ) : qmaBitFlipMatrix e*qmaBitFlipMatrix e = 1 := by
  ext s t
  simp [qmaBitFlipMatrix,Matrix.mul_apply,mul_ite,qmaBitFlip_involutive e t,Matrix.one_apply]

theorem qmaBitFlipMatrix_star (e : κ) : (qmaBitFlipMatrix e).conjTranspose = qmaBitFlipMatrix e := by
  ext s t
  have he : t = qmaBitFlip e s ↔ s = qmaBitFlip e t := by
    constructor <;> intro h <;> rw [h,qmaBitFlip_involutive]
  simp [Matrix.conjTranspose_apply,qmaBitFlipMatrix,he]

theorem qmaKronecker_unitary_norm (M : Matrix σ σ ℂ) (N : Matrix α α ℂ)
    (hM : M.conjTranspose*M = 1) (hN : N.conjTranspose*N = 1) :
    ‖spinMatrixOperator (M ⊗ₖ N)‖ ≤ 1 := by
  apply spinMatrixOperator_unitary_norm
  rw [Matrix.conjTranspose_kronecker,← Matrix.mul_kronecker_mul,hM,hN,Matrix.one_kronecker_one]

omit [DecidableEq σ] in
theorem qmaOccupation_mulVec (M : Matrix σ σ ℂ) (e : κ)
    (u : (σ × (κ → Fin 2)) → ℂ) (s : σ) (a : κ → Fin 2) :
    (M ⊗ₖ qmaAncillaOccupation e).mulVec u (s,a) =
      if a e = 1 then M.mulVec (fun t => u (t,a)) s else 0 := by
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Matrix.kronecker_apply,
    qmaAncillaOccupation,Matrix.diagonal_apply]
  by_cases ha : a e = 1
  · simp [ha]
  · simp [ha]

theorem qmaKronecker_occupation_norm (M : Matrix σ σ ℂ) (hM : M.conjTranspose*M = 1)
    (e : κ) : ‖spinMatrixOperator (M ⊗ₖ qmaAncillaOccupation e)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq,Fintype.sum_prod_type]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  let y : EuclideanSpace ℂ σ := WithLp.toLp 2 (fun s => x (s,a))
  have heq : ∑ s, ‖(spinMatrixOperator M y) s‖^2 = ∑ s, ‖x (s,a)‖^2 := by
    have h := congrArg (fun r : ℝ => r^2) (spinMatrixOperator_unitary_norm_map M hM y)
    simpa only [EuclideanSpace.norm_sq_eq,y] using h
  by_cases ha : a e = 1
  · convert le_of_eq heq using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro s _
    change ‖(M ⊗ₖ qmaAncillaOccupation e).mulVec (fun t => x t) (s,a)‖^2 =
      ‖(spinMatrixOperator M y) s‖^2
    rw [qmaOccupation_mulVec,ite_eq_left ha]
    rfl
  · have hz : ∑ s, ‖spinMatrixOperator (M ⊗ₖ qmaAncillaOccupation e) x (s,a)‖^2 = 0 := by
      apply Finset.sum_eq_zero
      intro s _
      change ‖(M ⊗ₖ qmaAncillaOccupation e).mulVec (fun t => x t) (s,a)‖^2 = 0
      rw [qmaOccupation_mulVec,ite_eq_right ha]
      norm_num
    rw [hz]
    positivity

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRectangularOperator
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.spinMatrixOperator_diagonal _root_.OAI.ContinuumCoulomb.spinMatrixOperator_sub _root_.OAI.ContinuumCoulomb.spinMatrixOperator_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rectangular Euclidean operators for the actual mediator columns. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace Classical

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem qmaMatrixOperator_add (M N : Matrix α β ℂ) :
    qmaMatrixOperator (M+N) = qmaMatrixOperator M+qmaMatrixOperator N := by
  unfold qmaMatrixOperator
  rw [map_add,map_add]

theorem qmaMatrixOperator_smul (c : ℂ) (M : Matrix α β ℂ) :
    qmaMatrixOperator (c • M) = c • qmaMatrixOperator M := by
  unfold qmaMatrixOperator
  rw [map_smul,map_smul]

theorem qmaMatrixOperator_sum {δ : Type*} (s : Finset δ) (M : δ → Matrix α β ℂ) :
    qmaMatrixOperator (∑ a ∈ s, M a) = ∑ a ∈ s, qmaMatrixOperator (M a) := by
  unfold qmaMatrixOperator
  rw [map_sum,map_sum]

theorem qmaMatrixOperator_mul [DecidableEq γ] (M : Matrix α β ℂ) (N : Matrix β γ ℂ) :
    qmaMatrixOperator (M*N) = (qmaMatrixOperator M).comp (qmaMatrixOperator N) := by
  ext x a
  change Matrix.toLpLin 2 2 (M*N) x a = Matrix.toLpLin 2 2 M (Matrix.toLpLin 2 2 N x) a
  rw [Matrix.toLpLin_mul_same,LinearMap.comp_apply]

theorem qmaMatrixOperator_star (M : Matrix α β ℂ) :
    qmaMatrixOperator M.conjTranspose = (qmaMatrixOperator M).adjoint := by
  unfold qmaMatrixOperator
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint,LinearMap.adjoint_toContinuousLinearMap]

theorem qmaMatrixOperator_square [DecidableEq α] (M : Matrix α α ℂ) :
    qmaMatrixOperator M = spinMatrixOperator M := rfl

theorem qmaEuclidean_real_inner (x y : EuclideanSpace ℂ α) :
    ⟪x,y⟫_ℝ = (⟪x,y⟫_ℂ).re := by
  simp only [PiLp.inner_apply,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro a _
  rfl

variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]
variable [DecidableEq α]

theorem qmaSliceColumn_operator_norm_map (a : α) (M : Matrix σ σ ℂ)
    (x : EuclideanSpace ℂ σ) :
    ‖qmaMatrixOperator (qmaSliceColumn a M) x‖ = ‖spinMatrixOperator M x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq,Fintype.sum_prod_type,qmaMatrixOperator_apply,qmaSliceColumn]
  have hentry (s : σ) (b : α) :
      (∑ t, (if b = a then M s t else 0)*x t) =
        if b = a then spinMatrixOperator M x s else 0 := by
    by_cases hb : b = a <;> simp [hb,spinMatrixOperator_apply]
  simp only [hentry]
  simp [apply_ite]

theorem qmaSliceColumn_operator_norm (a : α) (M : Matrix σ σ ℂ) :
    ‖qmaMatrixOperator (qmaSliceColumn a M)‖ ≤ ‖spinMatrixOperator M‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [qmaSliceColumn_operator_norm_map]
  exact (spinMatrixOperator M).le_opNorm x

omit [DecidableEq κ] in
theorem qmaSliceFamily_operator_norm (a : κ → α) (V : κ → Matrix σ σ ℂ) :
    ‖qmaMatrixOperator (∑ e, qmaSliceColumn (a e) (V e))‖ ≤
      ∑ e, ‖spinMatrixOperator (V e)‖ := by
  rw [qmaMatrixOperator_sum]
  calc
    _ ≤ ∑ e, ‖qmaMatrixOperator (qmaSliceColumn (a e) (V e))‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro e _
      exact qmaSliceColumn_operator_norm (a e) (V e)

theorem qmaAncillaColumn_operator_norm (V : κ → Matrix σ σ ℂ) :
    ‖qmaMatrixOperator (qmaAncillaColumn V)‖ ≤ ∑ e, ‖spinMatrixOperator (V e)‖ :=
  qmaSliceFamily_operator_norm qmaAncillaSingle V

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOperatorQuadratic
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix quadratic forms agree with the real forms of their actual
complex Euclidean operators, including rectangular compressions. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped InnerProductSpace
variable {α β : Type*} [Fintype α] [Fintype β]

theorem qmaMatrixOperator_real_adjoint (B : Matrix α β ℂ)
    (p : EuclideanSpace ℂ β) (y : EuclideanSpace ℂ α) :
    ⟪qmaMatrixOperator B p,y⟫_ℝ = ⟪p,qmaMatrixOperator B.conjTranspose y⟫_ℝ := by
  rw [qmaEuclidean_real_inner,qmaEuclidean_real_inner]
  have h := ContinuousLinearMap.adjoint_inner_right (qmaMatrixOperator B) p y
  rw [← qmaMatrixOperator_star] at h
  exact congrArg Complex.re h.symm

theorem qmaQuadratic_operator (M : Matrix α α ℂ) (p : EuclideanSpace ℂ α) :
    qmaQuadratic M (fun i => p i) = ⟪p,qmaMatrixOperator M p⟫_ℝ := by
  rw [qmaEuclidean_real_inner]
  simp only [qmaQuadratic,PiLp.inner_apply,RCLike.inner_apply',qmaMatrixOperator_apply,
    Matrix.mulVec,dotProduct,Pi.star_apply,starRingEnd_apply]

theorem qmaQuadratic_sandwich [DecidableEq α] [DecidableEq β] (B : Matrix α β ℂ) (M : Matrix α α ℂ)
    (p : EuclideanSpace ℂ β) :
    qmaQuadratic (B.conjTranspose*M*B) (fun i => p i) =
      ⟪qmaMatrixOperator B p,qmaMatrixOperator M (qmaMatrixOperator B p)⟫_ℝ := by
  rw [qmaQuadratic_operator,qmaMatrixOperator_mul,qmaMatrixOperator_mul]
  simp only [ContinuousLinearMap.comp_apply]
  exact (qmaMatrixOperator_real_adjoint B p _).symm

theorem qmaQuadratic_sub (M N : Matrix α α ℂ) (p : α → ℂ) :
    qmaQuadratic (M-N) p = qmaQuadratic M p-qmaQuadratic N p := by
  have hn : qmaQuadratic (-N) p = -qmaQuadratic N p := by
    have h := qmaQuadratic_smul N (-1) p
    simpa using h
  simp only [sub_eq_add_neg,qmaQuadratic_add,hn]

theorem qmaQuadratic_real_smul (M : Matrix α α ℂ) (a : ℝ) (p : α → ℂ) :
    qmaQuadratic (a • M) p = a*qmaQuadratic M p := by
  have he : a • M = (a:ℂ) • M := rfl
  rw [he,qmaQuadratic_smul]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGroundComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Operator-norm perturbations of the actual finite spin ground energy. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped InnerProductSpace
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem qmaQuadratic_norm_bound (M : Matrix σ σ ℂ) (x : EuclideanSpace ℂ σ) :
    |qmaQuadratic M (fun i => x i)| ≤ ‖spinMatrixOperator M‖*‖x‖^2 := by
  rw [qmaQuadratic_operator,qmaMatrixOperator_square]
  calc
    _ ≤ ‖x‖*‖spinMatrixOperator M x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖*(‖spinMatrixOperator M‖*‖x‖) :=
      mul_le_mul_of_nonneg_left ((spinMatrixOperator M).le_opNorm x) (norm_nonneg x)
    _ = _ := by ring

theorem qmaNormalizedBottom_bddBelow (M : Matrix σ σ ℂ) :
    BddBelow {e | ∃ x : EuclideanSpace ℂ σ, ‖x‖ = 1 ∧
      e = ⟪x,spinMatrixOperator M x⟫_ℝ} := by
  refine ⟨-‖spinMatrixOperator M‖,?_⟩
  rintro e ⟨x,hx,rfl⟩
  have h := (abs_le.mp (qmaQuadratic_norm_bound M x)).1
  simpa only [hx,one_pow,mul_one,qmaQuadratic_operator,qmaMatrixOperator_square] using h

theorem qmaNormalizedBottom_le (M : Matrix σ σ ℂ) (x : EuclideanSpace ℂ σ)
    (hx : ‖x‖ = 1) :
    MediatorGraph.normalizedBottom M ≤ qmaQuadratic M (fun i => x i) := by
  rw [qmaQuadratic_operator,qmaMatrixOperator_square]
  exact csInf_le (qmaNormalizedBottom_bddBelow M) ⟨x,hx,rfl⟩

theorem le_qmaNormalizedBottom (M : Matrix σ σ ℂ) (u : EuclideanSpace ℂ σ)
    (hu : ‖u‖ = 1) {b : ℝ}
    (h : ∀ x : EuclideanSpace ℂ σ, ‖x‖ = 1 → b ≤ qmaQuadratic M (fun i => x i)) :
    b ≤ MediatorGraph.normalizedBottom M := by
  apply le_csInf (show {e | ∃ x : EuclideanSpace ℂ σ, ‖x‖ = 1 ∧
    e = ⟪x,spinMatrixOperator M x⟫_ℝ}.Nonempty from ⟨_,u,hu,rfl⟩)
  rintro e ⟨x,hx,rfl⟩
  simpa only [qmaQuadratic_operator,qmaMatrixOperator_square] using h x hx

theorem qmaNormalizedBottom_error (M N : Matrix σ σ ℂ)
    (u : EuclideanSpace ℂ σ) (hu : ‖u‖ = 1) {δ : ℝ}
    (herror : ∀ x : EuclideanSpace ℂ σ, ‖x‖ = 1 →
      |qmaQuadratic M (fun i => x i)-qmaQuadratic N (fun i => x i)| ≤ δ) :
    |MediatorGraph.normalizedBottom M-MediatorGraph.normalizedBottom N| ≤ δ := by
  have hMN : MediatorGraph.normalizedBottom N-δ ≤ MediatorGraph.normalizedBottom M := by
    apply le_qmaNormalizedBottom M u hu
    intro x hx
    have hN := qmaNormalizedBottom_le N x hx
    have he := (abs_le.mp (herror x hx)).1
    linarith
  have hNM : MediatorGraph.normalizedBottom M-δ ≤ MediatorGraph.normalizedBottom N := by
    apply le_qmaNormalizedBottom N u hu
    intro x hx
    have hM := qmaNormalizedBottom_le M x hx
    have he := (abs_le.mp (herror x hx)).2
    linarith
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem qmaNormalizedBottom_norm_error (M N : Matrix σ σ ℂ)
    (u : EuclideanSpace ℂ σ) (hu : ‖u‖ = 1) {δ : ℝ}
    (herror : ‖spinMatrixOperator (M-N)‖ ≤ δ) :
    |MediatorGraph.normalizedBottom M-MediatorGraph.normalizedBottom N| ≤ δ := by
  apply qmaNormalizedBottom_error M N u hu
  intro x hx
  rw [← qmaQuadratic_sub]
  have h := (qmaQuadratic_norm_bound (M-N) x).trans
    (mul_le_mul_of_nonneg_right herror (sq_nonneg ‖x‖))
  simpa only [hx,one_pow,mul_one] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumThirdCounterterm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The third-order series gadget uses only polynomial coefficients.
Its parallel version is controlled by ThirdOrderPerturbation. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qmaThirdSeries_effective (A B C : Matrix ι ι ℂ) (r J : ℂ)
    (hA : A*A = 1) (hB : B*B = 1) (hAB : A*B = B*A)
    (hAC : A*C = C*A) (hBC : B*C = C*B) :
    qmaThirdSeriesCounter A B C r J -
      r • (qmaThirdSeriesPair A B J*qmaThirdSeriesPair A B J)+
      qmaThirdSeriesPair A B J*C*qmaThirdSeriesPair A B J = J • (A*B*C) := by
  unfold qmaThirdSeriesCounter qmaThirdSeriesPair
  rw [qmaGadget_pair_square A B (J/2) hA hB hAB,
    qmaGadget_pair_sandwich A B C (J/2) hA hB hAB hAC hBC]
  module

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitMediatorProjection
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.spinMatrixOperator_diagonal _root_.OAI.ContinuumCoulomb.spinMatrixOperator_sub _root_.OAI.ContinuumCoulomb.spinMatrixOperator_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact vacuum and complementary projections for the physical qubits. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

omit [Fintype σ] [DecidableEq κ] in
theorem qmaAncillaDiagonal_eq (w : (κ → Fin 2) → ℂ) :
    (qmaAncillaDiagonal w : Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ) =
      Matrix.diagonal (fun p => w p.2) := by
  ext ⟨s,a⟩ ⟨t,b⟩
  by_cases hs : s = t <;> by_cases hab : a = b <;>
    simp [qmaAncillaDiagonal,Prod.mk.injEq,hs,hab]

theorem qmaMediatorVacuum_gram :
    (qmaMediatorVacuumColumn (σ := σ) (κ := κ)).conjTranspose*
      qmaMediatorVacuumColumn (σ := σ) (κ := κ) = 1 := by
  rw [qmaMediatorVacuumColumn,qmaSliceColumn_gram]
  simp

theorem qmaMediatorHigh_column (V : κ → Matrix σ σ ℂ) :
    qmaMediatorHighMatrix*qmaAncillaColumn V = qmaAncillaColumn V := by
  unfold qmaMediatorHighMatrix
  simpa only [one_smul] using qmaAncillaDiagonal_column
    (fun a => if a = qmaAncillaVacuum then (0:ℂ) else 1) V 1
    (fun e => ite_eq_right (qmaAncillaSingle_ne_vacuum e))

theorem qmaMediatorHigh_vacuum :
    (qmaMediatorHighMatrix (σ := σ) (κ := κ))*qmaMediatorVacuumColumn (σ := σ) (κ := κ) = 0 := by
  rw [qmaMediatorHighMatrix,qmaMediatorVacuumColumn,qmaAncillaDiagonal_slice]
  simp

omit [Fintype σ] [DecidableEq κ] in
theorem qmaMediatorHigh_star :
    (qmaMediatorHighMatrix (σ := σ) (κ := κ)).conjTranspose = qmaMediatorHighMatrix := by
  rw [qmaMediatorHighMatrix,qmaAncillaDiagonal_eq]
  ext p q
  by_cases hpq : p = q
  · subst q
    by_cases hp : p.2 = qmaAncillaVacuum <;>
      simp [Matrix.conjTranspose_apply,hp]
  · simp [Matrix.conjTranspose_apply,hpq,Ne.symm hpq]

theorem qmaMediatorVacuum_high :
    (qmaMediatorVacuumColumn (σ := σ) (κ := κ)).conjTranspose*
      qmaMediatorHighMatrix (σ := σ) (κ := κ) = 0 := by
  have h := congrArg Matrix.conjTranspose (qmaMediatorHigh_vacuum (σ := σ) (κ := κ))
  simpa only [Matrix.conjTranspose_mul,qmaMediatorHigh_star,Matrix.conjTranspose_zero] using h

omit [DecidableEq κ] in
theorem qmaMediator_projection_sum :
    (qmaMediatorVacuumColumn (σ := σ) (κ := κ))*qmaMediatorVacuumColumn.conjTranspose+
      qmaMediatorHighMatrix = 1 := by
  rw [qmaMediatorHighMatrix,qmaAncillaDiagonal_eq]
  ext ⟨s,a⟩ ⟨t,b⟩
  by_cases ha : a = qmaAncillaVacuum <;> by_cases hb : b = qmaAncillaVacuum <;>
    simp [qmaMediatorVacuumColumn,qmaSliceColumn,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Matrix.one_apply,Matrix.diagonal_apply,ha,hb,eq_comm,Prod.mk.injEq]

theorem qmaMediatorHigh_norm :
    ‖spinMatrixOperator (qmaMediatorHighMatrix (σ := σ) (κ := κ))‖ ≤ 1 := by
  have he : (spinMatrixOperator (qmaMediatorHighMatrix (σ := σ) (κ := κ))).restrictScalars ℝ =
      diagonalPenalty (fun p : σ × (κ → Fin 2) => if p.2 = qmaAncillaVacuum then 0 else 1) := by
    ext x p
    change spinMatrixOperator qmaMediatorHighMatrix x p = _
    rw [qmaMediatorHighMatrix,qmaAncillaDiagonal_eq]
    simp [spinMatrixOperator_apply,Matrix.diagonal_apply]
  have hn := congrArg (fun f => ‖f‖) he
  rw [ContinuousLinearMap.norm_restrictScalars] at hn
  rw [hn]
  apply diagonalPenalty_norm_le _ zero_le_one
  intro p
  split_ifs <;> norm_num

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitMediatorPenalty
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An invertible diagonal extension of the physical excitation penalty.
The extension agrees with the physical penalty on the actual complement. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
theorem qmaPaddedExcitationNumber_pos (a : κ → Fin 2) : 0 < qmaPaddedExcitationNumber a := by
  unfold qmaPaddedExcitationNumber
  split_ifs with h
  · exact Nat.zero_lt_one
  · exact qmaAncillaNumber_pos a h

theorem qmaPaddedExcitationNumber_single (e : κ) :
    qmaPaddedExcitationNumber (qmaAncillaSingle e) = 1 := by
  simp [qmaPaddedExcitationNumber,qmaAncillaSingle_ne_vacuum]

omit [DecidableEq σ] in
theorem qmaPaddedPenalty_gap {g : ℝ} (hg : 0 < g) (x : EuclideanSpace ℂ (σ × (κ → Fin 2))) :
    g*‖x‖^2 ≤ ⟪x,qmaPaddedPenalty g x⟫_ℝ := by
  apply diagonalPenalty_gap
  intro p
  have hn : (1:ℝ) ≤ qmaPaddedExcitationNumber p.2 := by
    exact_mod_cast qmaPaddedExcitationNumber_pos p.2
  exact (mul_one g).ge.trans (mul_le_mul_of_nonneg_left hn hg.le)

omit [DecidableEq σ] in
theorem qmaPaddedPenalty_inverse {g : ℝ} (hg : 0 < g)
    (x : EuclideanSpace ℂ (σ × (κ → Fin 2))) : qmaPaddedPenalty g (qmaPaddedInverse g x) = x := by
  apply diagonalPenalty_inverse_right
  intro p
  have hn : (0:ℝ) < qmaPaddedExcitationNumber p.2 := by exact_mod_cast qmaPaddedExcitationNumber_pos p.2
  exact ne_of_gt (mul_pos hg hn)

theorem qmaAncillaDiagonal_real_operator (w : (κ → Fin 2) → ℝ) :
    (qmaMatrixOperator (qmaAncillaDiagonal (σ := σ) (fun a => (w a : ℂ)))).restrictScalars ℝ =
      diagonalPenalty (fun p : σ × (κ → Fin 2) => w p.2) := by
  ext x p
  change qmaMatrixOperator (qmaAncillaDiagonal (fun a => (w a : ℂ))) x p = w p.2 • x p
  rw [qmaAncillaDiagonal_eq]
  simp [qmaMatrixOperator_apply,Matrix.diagonal_apply,RCLike.real_smul_eq_coe_mul]

theorem qmaPaddedInverse_column (g : ℝ) (V : κ → Matrix σ σ ℂ) (x : EuclideanSpace ℂ σ) :
    qmaPaddedInverse g (qmaMatrixOperator (qmaAncillaColumn V) x) =
      g⁻¹ • qmaMatrixOperator (qmaAncillaColumn V) x := by
  have hw (e : κ) : ((g*qmaPaddedExcitationNumber (qmaAncillaSingle e) : ℝ)⁻¹ : ℂ) =
      (g⁻¹ : ℝ) := by rw [qmaPaddedExcitationNumber_single]; simp
  have hm := qmaAncillaDiagonal_column
    (σ := σ) (fun a => ((g*qmaPaddedExcitationNumber a : ℝ)⁻¹ : ℂ)) V (g⁻¹ : ℝ) hw
  have ho := congrArg (fun M : Matrix (σ × (κ → Fin 2)) σ ℂ => qmaMatrixOperator M x) hm
  rw [qmaMatrixOperator_mul,qmaMatrixOperator_smul] at ho
  have he := qmaAncillaDiagonal_real_operator (σ := σ) (κ := κ)
    (fun a => (g*qmaPaddedExcitationNumber a : ℝ)⁻¹)
  have heapp := congrArg (fun f : EuclideanSpace ℂ (σ × (κ → Fin 2)) →L[ℝ]
    EuclideanSpace ℂ (σ × (κ → Fin 2)) => f (qmaMatrixOperator (qmaAncillaColumn V) x)) he
  change qmaMatrixOperator _ (qmaMatrixOperator (qmaAncillaColumn V) x) =
    qmaPaddedInverse g (qmaMatrixOperator (qmaAncillaColumn V) x) at heapp
  simp only [Complex.ofReal_inv] at heapp
  rw [ContinuousLinearMap.comp_apply,heapp,_root_.smul_apply] at ho
  exact ho

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitMediatorHilbert
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Hilbert-space low and complementary coordinates for qubit mediators. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

theorem qmaMediator_restrict_include (p : EuclideanSpace ℂ σ) :
    qmaMediatorRestriction (κ := κ) (qmaMediatorInclusion p) = p := by
  change qmaMatrixOperator _ (qmaMatrixOperator _ p) = p
  rw [← ContinuousLinearMap.comp_apply,← qmaMatrixOperator_mul,qmaMediatorVacuum_gram,
    qmaMatrixOperator_square,spinMatrixOperator_one]
  rfl

theorem qmaMediator_inclusion_adjoint (p : EuclideanSpace ℂ σ)
    (x : EuclideanSpace ℂ (σ × (κ → Fin 2))) :
    ⟪qmaMediatorInclusion p,x⟫_ℝ = ⟪p,qmaMediatorRestriction x⟫_ℝ := by
  have h := ContinuousLinearMap.adjoint_inner_right
    (qmaMatrixOperator (qmaMediatorVacuumColumn (σ := σ) (κ := κ))) p x
  rw [← qmaMatrixOperator_star] at h
  rw [qmaEuclidean_real_inner,qmaEuclidean_real_inner]
  exact congrArg Complex.re h.symm

theorem qmaMediator_highPart (x : EuclideanSpace ℂ (σ × (κ → Fin 2))) :
    Perturbation.orthogonalHighPart qmaMediatorInclusion qmaMediatorRestriction x =
      qmaMediatorHighProjection x := by
  have hm := qmaMediator_projection_sum (σ := σ) (κ := κ)
  have h := congrArg (fun M => qmaMatrixOperator M x) hm
  rw [qmaMatrixOperator_add,qmaMatrixOperator_mul] at h
  simp only [qmaMatrixOperator_square,spinMatrixOperator_one] at h
  change qmaMediatorInclusion (qmaMediatorRestriction x)+qmaMediatorHighProjection x = x at h
  unfold Perturbation.orthogonalHighPart
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using h.symm)

theorem qmaMediator_norm_decomposition (x : EuclideanSpace ℂ (σ × (κ → Fin 2))) :
    ‖qmaMediatorRestriction x‖^2+‖qmaMediatorHighProjection x‖^2 = ‖x‖^2 := by
  rw [← qmaMediator_highPart]
  exact Perturbation.orthogonalParts_norm qmaMediatorInclusion qmaMediatorRestriction
    qmaMediator_restrict_include qmaMediator_inclusion_adjoint x

theorem qmaMediatorHighProjection_norm :
    ‖qmaMediatorHighProjection (σ := σ) (κ := κ)‖ ≤ 1 := by
  rw [qmaMediatorHighProjection,ContinuousLinearMap.norm_restrictScalars]
  exact qmaMediatorHigh_norm

theorem qmaMediatorRestriction_high (x : EuclideanSpace ℂ (σ × (κ → Fin 2))) :
    qmaMediatorRestriction (qmaMediatorHighProjection x) = 0 := by
  change qmaMatrixOperator _ (qmaMatrixOperator _ x) = 0
  rw [← ContinuousLinearMap.comp_apply,← qmaMatrixOperator_mul,qmaMediatorVacuum_high]
  ext p
  simp [qmaMatrixOperator_apply]

theorem qmaMediatorRestriction_column (V : κ → Matrix σ σ ℂ) (p : EuclideanSpace ℂ σ) :
    qmaMediatorRestriction (qmaMatrixOperator (qmaAncillaColumn V) p) = 0 := by
  have hQ := congrArg (fun M => qmaMatrixOperator M p) (qmaMediatorHigh_column V)
  rw [qmaMatrixOperator_mul] at hQ
  change qmaMediatorHighProjection (qmaMatrixOperator (qmaAncillaColumn V) p) =
    qmaMatrixOperator (qmaAncillaColumn V) p at hQ
  rw [← hQ]
  exact qmaMediatorRestriction_high _

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitMediatorSeriesMatrix
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact simultaneous cancellation for the polynomial third-order gadgets. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]

theorem qmaThirdSeries_sum_effective (H : Matrix σ σ ℂ) (A B C : κ → Matrix σ σ ℂ)
    (r : ℂ) (J : κ → ℂ) (hA : ∀ e, A e*A e = 1) (hB : ∀ e, B e*B e = 1)
    (hAB : ∀ e, A e*B e = B e*A e) (hAC : ∀ e, A e*C e = C e*A e)
    (hBC : ∀ e, B e*C e = C e*B e) :
    qmaThirdSeriesLow H A B C r J-
      ∑ e, r • (qmaThirdSeriesPair (A e) (B e) (J e)*qmaThirdSeriesPair (A e) (B e) (J e))+
      ∑ e, qmaThirdSeriesPair (A e) (B e) (J e)*C e*qmaThirdSeriesPair (A e) (B e) (J e) =
        qmaThirdSeriesTarget H A B C J := by
  calc
    _ = H+∑ e, (qmaThirdSeriesCounter (A e) (B e) (C e) r (J e)-
        r • (qmaThirdSeriesPair (A e) (B e) (J e)*qmaThirdSeriesPair (A e) (B e) (J e))+
        qmaThirdSeriesPair (A e) (B e) (J e)*C e*qmaThirdSeriesPair (A e) (B e) (J e)) := by
      simp only [qmaThirdSeriesLow,Finset.sum_add_distrib,Finset.sum_sub_distrib]
      abel
    _ = _ := by
      unfold qmaThirdSeriesTarget
      congr 1
      apply Finset.sum_congr rfl
      intro e _
      exact qmaThirdSeries_effective _ _ _ _ _ (hA e) (hB e) (hAB e) (hAC e) (hBC e)

theorem qmaThirdMatrix_scaled (L : Matrix σ σ ℂ) (P C : κ → Matrix σ σ ℂ)
    (r : ℝ) (hr : r ≠ 0) (hP : ∀ e, (P e).conjTranspose = P e) :
    qmaThirdMatrix L (fun e => (r^2 : ℝ) • C e) (fun e => (r^2 : ℝ) • P e) (r^3 : ℝ) =
      L-(r : ℂ) • (∑ e, P e*P e)+(∑ e, P e*C e*P e)+
        ((r : ℂ)⁻¹)^2 • (∑ e, P e*L*P e) := by
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hfirst : ((r:ℂ)^3)⁻¹*((r:ℂ)^2*(r:ℂ)^2) = r := by field_simp
  have hthird : (((r:ℂ)^3)⁻¹)^2*((r:ℂ)^2*((r:ℂ)^2*(r:ℂ)^2)) = 1 := by field_simp
  have hremain : (((r:ℂ)^3)⁻¹)^2*((r:ℂ)^2*(r:ℂ)^2) = ((r:ℂ)⁻¹)^2 := by field_simp
  have hs (s : ℝ) (M : Matrix σ σ ℂ) : s • M = (s:ℂ) • M := rfl
  unfold qmaThirdMatrix
  simp only [hs,Complex.ofReal_pow,Matrix.conjTranspose_smul,star_pow,Complex.star_def,Complex.conj_ofReal,
    hP,smul_mul_assoc,mul_smul_comm,smul_smul,← Finset.smul_sum,
    smul_add,hfirst,hthird,hremain,one_smul]
  abel

theorem qmaThirdMatrix_target (H : Matrix σ σ ℂ) (A B C : κ → Matrix σ σ ℂ)
    (r : ℝ) (J : κ → ℂ) (hr : r ≠ 0)
    (hA : ∀ e, A e*A e = 1) (hB : ∀ e, B e*B e = 1)
    (hAB : ∀ e, A e*B e = B e*A e) (hAC : ∀ e, A e*C e = C e*A e)
    (hBC : ∀ e, B e*C e = C e*B e)
    (hP : ∀ e, (qmaThirdSeriesPair (A e) (B e) (J e)).conjTranspose =
      qmaThirdSeriesPair (A e) (B e) (J e)) :
    let L := qmaThirdSeriesLow H A B C r J
    let P := fun e => qmaThirdSeriesPair (A e) (B e) (J e)
    qmaThirdMatrix L (fun e => (r^2 : ℝ) • C e) (fun e => (r^2 : ℝ) • P e) (r^3 : ℝ) =
      qmaThirdSeriesTarget H A B C J+((r:ℂ)⁻¹)^2 • (∑ e, P e*L*P e) := by
  dsimp only
  rw [qmaThirdMatrix_scaled _ _ _ r hr hP]
  have h := qmaThirdSeries_sum_effective H A B C (r:ℂ) J hA hB hAB hAC hBC
  rw [← Finset.smul_sum] at h
  rw [h]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitMediatorPhysical
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical parallel-qubit Hamiltonian has the calculated vacuum column. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

omit [DecidableEq σ] [DecidableEq κ] in
theorem qmaSliceColumn_right_mul (a : κ → Fin 2) (A B : Matrix σ σ ℂ) :
    qmaSliceColumn a A*B = qmaSliceColumn a (A*B) := by
  ext ⟨s,b⟩ t
  by_cases h : b = a <;> simp [Matrix.mul_apply,qmaSliceColumn,h]

theorem qmaPhysicalPenalty_vacuum (g : ℝ) :
    qmaPhysicalPenaltyMatrix (σ := σ) (κ := κ) g*
      qmaMediatorVacuumColumn (σ := σ) (κ := κ) = 0 := by
  rw [qmaPhysicalPenaltyMatrix,qmaMediatorVacuumColumn,qmaAncillaDiagonal_slice]
  simp

theorem qmaLiftedLow_vacuum (C : Matrix σ σ ℂ) :
    (C ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ))*qmaMediatorVacuumColumn =
      qmaMediatorVacuumColumn*C := by
  rw [qmaMediatorVacuumColumn,qmaSliceColumn_right_mul,Matrix.one_mul]
  ext ⟨s,a⟩ t
  rw [qmaSliceColumn_kronecker_apply,Matrix.mul_one]
  simp [qmaSliceColumn,Matrix.one_apply]

theorem qmaPhysicalMediator_vacuum (g : ℝ) (C : Matrix σ σ ℂ)
    (D V : κ → Matrix σ σ ℂ) :
    qmaPhysicalMediatorMatrix g C D V*qmaMediatorVacuumColumn =
      qmaMediatorVacuumColumn*C+qmaAncillaColumn V := by
  have hd0 : qmaMediatorOccupations D*qmaMediatorVacuumColumn (σ := σ) (κ := κ) = 0 := by
    simpa only [qmaMediatorVacuumColumn] using qmaMediatorOccupations_vacuum D
  have hv : qmaMediatorFlips V*qmaMediatorVacuumColumn (σ := σ) (κ := κ) = qmaAncillaColumn V := by
    simpa only [qmaMediatorVacuumColumn] using qmaMediatorFlips_vacuum V
  unfold qmaPhysicalMediatorMatrix qmaMediatorPerturbation
  rw [Matrix.add_mul,qmaPhysicalPenalty_vacuum,zero_add,Matrix.add_mul,Matrix.add_mul,
    qmaLiftedLow_vacuum,hd0,hv,add_zero]

omit [Fintype σ] [DecidableEq κ] in
theorem qmaAncillaDiagonal_real_star (w : (κ → Fin 2) → ℝ) :
    (qmaAncillaDiagonal (σ := σ) (fun a => (w a : ℂ))).conjTranspose =
      qmaAncillaDiagonal (fun a => (w a : ℂ)) := by
  rw [qmaAncillaDiagonal_eq]
  ext p q
  by_cases hpq : p = q
  · subst q
    simp [Matrix.conjTranspose_apply]
  · simp [Matrix.conjTranspose_apply,hpq,Ne.symm hpq]

omit [DecidableEq κ] in
theorem qmaAncillaOccupation_star (e : κ) :
    (qmaAncillaOccupation e).conjTranspose = qmaAncillaOccupation e := by
  ext a b
  by_cases hab : a = b
  · subst b
    by_cases ha : a e = 1 <;> simp [qmaAncillaOccupation,Matrix.conjTranspose_apply,ha]
  · simp [qmaAncillaOccupation,Matrix.conjTranspose_apply,hab,Ne.symm hab]

omit [Fintype σ] [DecidableEq σ] in
theorem qmaMediatorPerturbation_star (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ)
    (hC : C.conjTranspose = C) (hD : ∀ e, (D e).conjTranspose = D e)
    (hV : ∀ e, (V e).conjTranspose = V e) :
    (qmaMediatorPerturbation C D V).conjTranspose = qmaMediatorPerturbation C D V := by
  simp only [qmaMediatorPerturbation,qmaMediatorOccupations,qmaMediatorFlips,
    Matrix.conjTranspose_add,Matrix.conjTranspose_sum,Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one,qmaAncillaOccupation_star,qmaBitFlipMatrix_star,hC,hD,hV]

omit [Fintype σ] in
theorem qmaPhysicalMediator_star (g : ℝ) (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ)
    (hC : C.conjTranspose = C) (hD : ∀ e, (D e).conjTranspose = D e)
    (hV : ∀ e, (V e).conjTranspose = V e) :
    (qmaPhysicalMediatorMatrix g C D V).conjTranspose = qmaPhysicalMediatorMatrix g C D V := by
  rw [qmaPhysicalMediatorMatrix,Matrix.conjTranspose_add,qmaPhysicalPenaltyMatrix,
    qmaAncillaDiagonal_real_star,qmaMediatorPerturbation_star C D V hC hD hV]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitMediatorForms
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full physical energy equals the block energy on its genuine
vacuum/complement decomposition. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

omit [DecidableEq σ] in
theorem qmaMatrixOperator_real_symmetric (M : Matrix σ σ ℂ) (hM : M.conjTranspose = M)
    (x y : EuclideanSpace ℂ σ) :
    ⟪x,qmaMatrixOperator M y⟫_ℝ = ⟪qmaMatrixOperator M x,y⟫_ℝ := by
  rw [qmaEuclidean_real_inner,qmaEuclidean_real_inner]
  have h := ContinuousLinearMap.adjoint_inner_right (qmaMatrixOperator M) x y
  rw [← qmaMatrixOperator_star,hM] at h
  exact congrArg Complex.re h

theorem qmaMediatorRestriction_apply (x : EuclideanSpace ℂ (σ × (κ → Fin 2))) (s : σ) :
    qmaMediatorRestriction x s = x (s,qmaAncillaVacuum) := by
  change (∑ t, (qmaMediatorVacuumColumn (σ := σ) (κ := κ)).conjTranspose s t*x t) = _
  simp [Matrix.conjTranspose_apply,qmaMediatorVacuumColumn,qmaSliceColumn,
    Fintype.sum_prod_type,Matrix.one_apply,apply_ite]

theorem qmaPhysicalOperator_low (g : ℝ) (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ)
    (p : EuclideanSpace ℂ σ) :
    qmaPhysicalOperator g C D V (qmaMediatorInclusion p) =
      qmaMediatorInclusion (qmaMatrixOperator C p)+qmaCouplingOperator V p := by
  have hm := qmaPhysicalMediator_vacuum g C D V
  have ho := congrArg (fun M : Matrix (σ × (κ → Fin 2)) σ ℂ => qmaMatrixOperator M p) hm
  simp only [qmaMatrixOperator_mul,qmaMatrixOperator_add,ContinuousLinearMap.comp_apply,
    _root_.add_apply] at ho
  exact ho

theorem qmaPhysicalPenalty_high (g : ℝ) (x : EuclideanSpace ℂ (σ × (κ → Fin 2)))
    (hx : qmaMediatorRestriction x = 0) :
    qmaMatrixOperator (qmaPhysicalPenaltyMatrix g) x = qmaPaddedPenalty g x := by
  have he := qmaAncillaDiagonal_real_operator (σ := σ) (κ := κ)
    (fun a => g*qmaAncillaNumber a)
  have hp := congrArg (fun f : EuclideanSpace ℂ (σ × (κ → Fin 2)) →L[ℝ]
    EuclideanSpace ℂ (σ × (κ → Fin 2)) => f x) he
  change qmaMatrixOperator (qmaPhysicalPenaltyMatrix g) x = _ at hp
  rw [hp]
  ext p
  by_cases ha : p.2 = qmaAncillaVacuum
  · have hzero := congrArg (fun u : EuclideanSpace ℂ σ => u p.1) hx
    rw [qmaMediatorRestriction_apply] at hzero
    change x (p.1,qmaAncillaVacuum) = 0 at hzero
    have hxp : x p = 0 := by
      change x (p.1,p.2) = 0
      rw [ha]
      exact hzero
    simp [qmaPaddedPenalty,diagonalPenalty_apply,hxp]
  · simp [qmaPaddedPenalty,diagonalPenalty_apply,qmaPaddedWeight,qmaPaddedExcitationNumber,ha]

theorem qmaComplementOperator_form (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ)
    (x : EuclideanSpace ℂ (σ × (κ → Fin 2))) (hx : qmaMediatorRestriction x = 0) :
    ⟪x,qmaComplementOperator C D V x⟫_ℝ = ⟪x,qmaPerturbationOperator C D V x⟫_ℝ := by
  have hQx : qmaMediatorHighProjection x = x := by
    rw [← qmaMediator_highPart]
    simp [Perturbation.orthogonalHighPart,hx]
  have hs := qmaMatrixOperator_real_symmetric
    (qmaMediatorHighMatrix (σ := σ) (κ := κ)) qmaMediatorHigh_star x
    (qmaPerturbationOperator C D V x)
  change ⟪x,qmaMediatorHighProjection (qmaPerturbationOperator C D V
    (qmaMediatorHighProjection x))⟫_ℝ = _
  rw [hQx]
  change ⟪x,qmaMediatorHighProjection (qmaPerturbationOperator C D V x)⟫_ℝ =
    ⟪qmaMediatorHighProjection x,qmaPerturbationOperator C D V x⟫_ℝ at hs
  simpa only [hQx] using hs

theorem qmaPhysicalOperator_high (g : ℝ) (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ)
    (x : EuclideanSpace ℂ (σ × (κ → Fin 2))) (hx : qmaMediatorRestriction x = 0) :
    ⟪x,qmaPhysicalOperator g C D V x⟫_ℝ =
      Perturbation.penaltyForm (qmaPaddedPenalty g) x+⟪x,qmaComplementOperator C D V x⟫_ℝ := by
  have he : qmaPhysicalOperator g C D V x =
      qmaMatrixOperator (qmaPhysicalPenaltyMatrix g) x+qmaPerturbationOperator C D V x := by
    change qmaMatrixOperator (_+_) x = _
    rw [qmaMatrixOperator_add,_root_.add_apply]
    rfl
  rw [he,qmaPhysicalPenalty_high g x hx,inner_add_right,qmaComplementOperator_form C D V x hx]
  rfl

theorem qmaPhysicalOperator_energy (g : ℝ) (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ)
    (hC : C.conjTranspose = C) (hD : ∀ e, (D e).conjTranspose = D e)
    (hV : ∀ e, (V e).conjTranspose = V e) (x : EuclideanSpace ℂ (σ × (κ → Fin 2))) :
    ⟪x,qmaPhysicalOperator g C D V x⟫_ℝ =
      Perturbation.lowBlockEnergy ((qmaMatrixOperator C).restrictScalars ℝ) (qmaPaddedPenalty g)
        (qmaComplementOperator C D V) (qmaCouplingOperator V) (qmaMediatorRestriction x)
        (qmaMediatorHighProjection x) := by
  rw [← qmaMediator_highPart]
  apply Perturbation.orthogonalBlock_full_energy
    (qmaMediatorInclusion (σ := σ) (κ := κ)) (qmaMediatorRestriction (σ := σ) (κ := κ))
    (qmaPhysicalOperator g C D V) (qmaPaddedPenalty g) (qmaComplementOperator C D V)
    ((qmaMatrixOperator C).restrictScalars ℝ) (qmaCouplingOperator V)
  · exact qmaMediator_restrict_include
  · exact qmaMediator_inclusion_adjoint
  · exact qmaMatrixOperator_real_symmetric _ (qmaPhysicalMediator_star g C D V hC hD hV)
  · exact qmaPhysicalOperator_low g C D V
  · exact qmaMediatorRestriction_column V
  · exact qmaPhysicalOperator_high g C D V

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitMediatorSeriesError
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.spinMatrixOperator_diagonal _root_.OAI.ContinuumCoulomb.spinMatrixOperator_sub _root_.OAI.ContinuumCoulomb.spinMatrixOperator_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common low Hamiltonian contributes only a decreasing residual
to the exact third-order compression. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]

theorem qmaSandwich_operator_norm (P L : Matrix σ σ ℂ) :
    ‖spinMatrixOperator (P*L*P)‖ ≤ ‖spinMatrixOperator P‖^2*‖spinMatrixOperator L‖ := by
  rw [spinMatrixOperator_mul,spinMatrixOperator_mul]
  calc
    _ ≤ ‖(spinMatrixOperator P).comp (spinMatrixOperator L)‖*‖spinMatrixOperator P‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖spinMatrixOperator P‖*‖spinMatrixOperator L‖)*‖spinMatrixOperator P‖ :=
      mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ = _ := by ring

theorem qmaThirdResidual_norm (L : Matrix σ σ ℂ) (P : κ → Matrix σ σ ℂ)
    (r : ℝ) (hr : 0 < r) :
    ‖spinMatrixOperator (((r:ℂ)⁻¹)^2 • (∑ e, P e*L*P e))‖ ≤
      r⁻¹^2*((∑ e, ‖spinMatrixOperator (P e)‖^2)*‖spinMatrixOperator L‖) := by
  rw [spinMatrixOperator_smul,norm_smul,norm_pow,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hr,spinMatrixOperator_sum]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  calc
    _ ≤ ∑ e, ‖spinMatrixOperator (P e*L*P e)‖ := norm_sum_le _ _
    _ ≤ ∑ e, ‖spinMatrixOperator (P e)‖^2*‖spinMatrixOperator L‖ :=
      Finset.sum_le_sum (fun e _ => qmaSandwich_operator_norm _ _)
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem qmaThirdResidual_polynomial_bound (L : Matrix σ σ ℂ) (P : κ → Matrix σ σ ℂ)
    {r K : ℝ} (hr : 0 < r) (hK : 0 ≤ K)
    (hP : ∑ e, ‖spinMatrixOperator (P e)‖^2 ≤ K) (hL : ‖spinMatrixOperator L‖ ≤ K*r) :
    ‖spinMatrixOperator (((r:ℂ)⁻¹)^2 • (∑ e, P e*L*P e))‖ ≤ K^2/r := by
  calc
    _ ≤ r⁻¹^2*((∑ e, ‖spinMatrixOperator (P e)‖^2)*‖spinMatrixOperator L‖) :=
      qmaThirdResidual_norm L P r hr
    _ ≤ r⁻¹^2*(K*(K*r)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hP hL (norm_nonneg _) hK) (sq_nonneg _)
    _ = _ := by field_simp

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitMediatorThirdForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual third-order Hilbert form is the computed finite matrix. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

omit [DecidableEq σ] in
theorem qmaThirdMatrix_compressed (g : ℝ) (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ) :
    qmaThirdMatrix C D V (g:ℂ) =
      C-(g⁻¹:ℝ) • ((qmaAncillaColumn V).conjTranspose*qmaAncillaColumn V)+
        (g⁻¹^2:ℝ) • ((qmaAncillaColumn V).conjTranspose*
          qmaMediatorPerturbation C D V*qmaAncillaColumn V) := by
  have hs (s : ℝ) (M : Matrix σ σ ℂ) : s • M = (s:ℂ) • M := rfl
  simp only [hs,Complex.ofReal_pow,Complex.ofReal_inv,qmaThirdMatrix,
    qmaAncillaColumn_gram,qmaMediatorPerturbation_compression]

theorem qmaActual_thirdOrderForm (g : ℝ) (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ)
    (p : EuclideanSpace ℂ σ) :
    Perturbation.thirdOrderForm ((qmaMatrixOperator C).restrictScalars ℝ)
      (qmaPaddedInverse g) (qmaComplementOperator C D V) (qmaCouplingOperator V) p =
        qmaQuadratic (qmaThirdMatrix C D V (g:ℂ)) (fun i => p i) := by
  have hgram : qmaQuadratic ((qmaAncillaColumn V).conjTranspose*qmaAncillaColumn V)
      (fun i => p i) = ⟪qmaMatrixOperator (qmaAncillaColumn V) p,
        qmaMatrixOperator (qmaAncillaColumn V) p⟫_ℝ := by
    have h := qmaQuadratic_sandwich (qmaAncillaColumn V)
      (1 : Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ) p
    simpa only [Matrix.mul_one,qmaMatrixOperator_square,spinMatrixOperator_one,
      one_apply_eq_self] using h
  have hcompress := qmaQuadratic_sandwich (qmaAncillaColumn V) (qmaMediatorPerturbation C D V) p
  rw [qmaThirdMatrix_compressed,qmaQuadratic_add,qmaQuadratic_sub,qmaQuadratic_real_smul,
    qmaQuadratic_real_smul,qmaQuadratic_operator C p,hgram,hcompress]
  unfold Perturbation.thirdOrderForm Perturbation.effectiveForm Perturbation.inverseForm
  change ⟪p,qmaMatrixOperator C p⟫_ℝ-
    ⟪qmaMatrixOperator (qmaAncillaColumn V) p,qmaPaddedInverse g (qmaMatrixOperator (qmaAncillaColumn V) p)⟫_ℝ+
    ⟪qmaPaddedInverse g (qmaMatrixOperator (qmaAncillaColumn V) p),
      qmaComplementOperator C D V (qmaPaddedInverse g (qmaMatrixOperator (qmaAncillaColumn V) p))⟫_ℝ = _
  rw [qmaPaddedInverse_column]
  simp only [map_smul,real_inner_smul_left,real_inner_smul_right]
  rw [qmaComplementOperator_form C D V _ (qmaMediatorRestriction_column V p)]
  have he : qmaPerturbationOperator C D V (qmaMatrixOperator (qmaAncillaColumn V) p) =
      qmaMatrixOperator (qmaMediatorPerturbation C D V) (qmaMatrixOperator (qmaAncillaColumn V) p) := rfl
  rw [he]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitMediatorBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.spinMatrixOperator_diagonal _root_.OAI.ContinuumCoulomb.spinMatrixOperator_sub _root_.OAI.ContinuumCoulomb.spinMatrixOperator_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Applying the third-order estimate to the actual full qubit Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

theorem qmaComplementOperator_norm (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ) :
    ‖qmaComplementOperator C D V‖ ≤ ‖qmaPerturbationOperator C D V‖ := by
  let Q := qmaMediatorHighProjection (σ := σ) (κ := κ)
  let P := qmaPerturbationOperator C D V
  have hQ : ‖Q‖ ≤ 1 := qmaMediatorHighProjection_norm
  change ‖Q.comp (P.comp Q)‖ ≤ ‖P‖
  calc
    _ ≤ ‖Q‖*‖P.comp Q‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Q‖*(‖P‖*‖Q‖) := mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ 1*(‖P‖*1) := mul_le_mul hQ
      (mul_le_mul_of_nonneg_left hQ (norm_nonneg _)) (by positivity) zero_le_one
    _ = _ := by ring

theorem qmaComplementOperator_symmetric (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ)
    (hC : C.conjTranspose = C) (hD : ∀ e, (D e).conjTranspose = D e)
    (hV : ∀ e, (V e).conjTranspose = V e)
    (x y : EuclideanSpace ℂ (σ × (κ → Fin 2))) :
    ⟪x,qmaComplementOperator C D V y⟫_ℝ = ⟪qmaComplementOperator C D V x,y⟫_ℝ := by
  have hQ (u v : EuclideanSpace ℂ (σ × (κ → Fin 2))) :
      ⟪u,qmaMediatorHighProjection v⟫_ℝ = ⟪qmaMediatorHighProjection u,v⟫_ℝ :=
    qmaMatrixOperator_real_symmetric _ qmaMediatorHigh_star u v
  have hP (u v : EuclideanSpace ℂ (σ × (κ → Fin 2))) :
      ⟪u,qmaPerturbationOperator C D V v⟫_ℝ = ⟪qmaPerturbationOperator C D V u,v⟫_ℝ :=
    qmaMatrixOperator_real_symmetric _ (qmaMediatorPerturbation_star C D V hC hD hV) u v
  change ⟪x,qmaMediatorHighProjection (qmaPerturbationOperator C D V (qmaMediatorHighProjection y))⟫_ℝ =
    ⟪qmaMediatorHighProjection (qmaPerturbationOperator C D V (qmaMediatorHighProjection x)),y⟫_ℝ
  rw [hQ,hP,← hQ]

theorem qmaInverseCoupling_bound (g : ℝ) (hg : 0 < g) (V : κ → Matrix σ σ ℂ)
    {η : ℝ} (hV : ∑ e, ‖spinMatrixOperator (V e)‖ ≤ g*η) (p : EuclideanSpace ℂ σ) :
    ‖qmaPaddedInverse g (qmaCouplingOperator V p)‖ ≤ η*‖p‖ := by
  change ‖qmaPaddedInverse g (qmaMatrixOperator (qmaAncillaColumn V) p)‖ ≤ _
  rw [qmaPaddedInverse_column,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hg)]
  have hnorm : ‖qmaMatrixOperator (qmaAncillaColumn V)‖ ≤ g*η :=
    (qmaAncillaColumn_operator_norm V).trans hV
  have hpoint : ‖qmaMatrixOperator (qmaAncillaColumn V) p‖ ≤
      ‖qmaMatrixOperator (qmaAncillaColumn V)‖*‖p‖ :=
    ContinuousLinearMap.le_opNorm (qmaMatrixOperator (qmaAncillaColumn V)) p
  have hb : ‖qmaMatrixOperator (qmaAncillaColumn V) p‖ ≤ (g*η)*‖p‖ :=
    hpoint.trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg p))
  calc
    _ ≤ g⁻¹*((g*η)*‖p‖) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hg.le)
    _ = _ := by field_simp

private theorem extendBlock_lower (a b e μ ε : ℝ)
    (hb : 0 ≤ ε*b) (hl : -ε*a ≤ e-μ*(a+b)) : (μ-ε)*(a+b) ≤ e := by
  nlinarith

theorem qmaPhysical_thirdOrder_lower (g : ℝ) (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ)
    (hg : 0 < g) (hC : C.conjTranspose = C) (hD : ∀ e, (D e).conjTranspose = D e)
    (hV : ∀ e, (V e).conjTranspose = V e) {d m η μ : ℝ}
    (hd : 0 ≤ d) (hm : 0 ≤ m) (hsmall : 2*d+4*m ≤ g)
    (hPert : ‖qmaPerturbationOperator C D V‖ ≤ d)
    (hCouple : ∑ e, ‖spinMatrixOperator (V e)‖ ≤ g*η) (hμ : μ ≤ m)
    (hmin : ∀ p : EuclideanSpace ℂ σ,
      μ*‖p‖^2 ≤ qmaQuadratic (qmaThirdMatrix C D V (g:ℂ)) (fun i => p i))
    (x : EuclideanSpace ℂ (σ × (κ → Fin 2))) :
    (μ-(2*d^2/g+2*m)*η^2)*‖x‖^2 ≤ ⟪x,qmaPhysicalOperator g C D V x⟫_ℝ := by
  have hAT (z : EuclideanSpace ℂ (σ × (κ → Fin 2))) :
      qmaPaddedPenalty g (qmaPaddedInverse g z) = z :=
    qmaPaddedPenalty_inverse (σ := σ) (κ := κ) hg z
  have hAsym (z w : EuclideanSpace ℂ (σ × (κ → Fin 2))) :
      ⟪z,qmaPaddedPenalty g w⟫_ℝ = ⟪qmaPaddedPenalty g z,w⟫_ℝ :=
    diagonalPenalty_symmetric (qmaPaddedWeight g) z w
  have hgap (z : EuclideanSpace ℂ (σ × (κ → Fin 2))) :
      g*‖z‖^2 ≤ Perturbation.penaltyForm (qmaPaddedPenalty g) z :=
    qmaPaddedPenalty_gap (σ := σ) (κ := κ) hg z
  have hminForm (p : EuclideanSpace ℂ σ) : μ*‖p‖^2 ≤
      Perturbation.thirdOrderForm ((qmaMatrixOperator C).restrictScalars ℝ)
        (qmaPaddedInverse g) (qmaComplementOperator C D V) (qmaCouplingOperator V) p := by
    rw [qmaActual_thirdOrderForm]
    exact hmin p
  have hl : -(2*d^2/g+2*m)*η^2*‖qmaMediatorRestriction x‖^2 ≤
      Perturbation.lowBlockEnergy ((qmaMatrixOperator C).restrictScalars ℝ)
        (qmaPaddedPenalty g) (qmaComplementOperator C D V) (qmaCouplingOperator V)
        (qmaMediatorRestriction x) (qmaMediatorHighProjection x) -
      μ*(‖qmaMediatorRestriction x‖^2+‖qmaMediatorHighProjection x‖^2) := by
    apply Perturbation.thirdOrder_energy_lower
      ((qmaMatrixOperator C).restrictScalars ℝ) (qmaPaddedPenalty g) (qmaPaddedInverse g)
      (qmaComplementOperator C D V) (qmaCouplingOperator V) hg hd hm hsmall
    · exact hAT
    · exact hAsym
    · exact qmaComplementOperator_symmetric C D V hC hD hV
    · exact hgap
    · exact qmaInverseCoupling_bound g hg V hCouple
    · exact (qmaComplementOperator_norm C D V).trans hPert
    · exact hμ
    · exact hminForm
  have hK : 0 ≤ (2*d^2/g+2*m)*η^2 := by positivity
  have hextra := mul_nonneg hK (sq_nonneg ‖qmaMediatorHighProjection x‖)
  rw [← qmaMediator_norm_decomposition, qmaPhysicalOperator_energy g C D V hC hD hV x]
  apply extendBlock_lower _ _ _ _ _ hextra
  simpa only [neg_mul] using hl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitMediatorTrial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The third-order trial vector lies in the genuine physical spin space. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

theorem qmaThirdTrial_high_kernel (g : ℝ) (V : κ → Matrix σ σ ℂ) (p : EuclideanSpace ℂ σ) :
    qmaMediatorRestriction (-(qmaPaddedInverse g (qmaCouplingOperator V p))) = 0 := by
  change qmaMediatorRestriction (-(qmaPaddedInverse g (qmaMatrixOperator (qmaAncillaColumn V) p))) = 0
  rw [qmaPaddedInverse_column,map_neg,map_smul,qmaMediatorRestriction_column,smul_zero,neg_zero]

theorem qmaThirdTrial_norm (g : ℝ) (V : κ → Matrix σ σ ℂ) (p : EuclideanSpace ℂ σ) :
    ‖qmaThirdTrial g V p‖^2 = ‖p‖^2+‖qmaPaddedInverse g (qmaCouplingOperator V p)‖^2 := by
  have h := Perturbation.orthogonalAssemble_norm
    (qmaMediatorInclusion (σ := σ) (κ := κ)) (qmaMediatorRestriction (σ := σ) (κ := κ))
    qmaMediator_restrict_include qmaMediator_inclusion_adjoint p
    (-(qmaPaddedInverse g (qmaCouplingOperator V p))) (qmaThirdTrial_high_kernel g V p)
  simpa only [qmaThirdTrial,norm_neg] using h

theorem qmaThirdTrial_energy (g : ℝ) (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ)
    (hC : C.conjTranspose = C) (hD : ∀ e, (D e).conjTranspose = D e)
    (hV : ∀ e, (V e).conjTranspose = V e) (p : EuclideanSpace ℂ σ) :
    ⟪qmaThirdTrial g V p,qmaPhysicalOperator g C D V (qmaThirdTrial g V p)⟫_ℝ =
      Perturbation.lowBlockEnergy ((qmaMatrixOperator C).restrictScalars ℝ)
        (qmaPaddedPenalty g) (qmaComplementOperator C D V) (qmaCouplingOperator V) p
        (-(qmaPaddedInverse g (qmaCouplingOperator V p))) := by
  exact Perturbation.orthogonalBlock_energy
    (qmaMediatorInclusion (σ := σ) (κ := κ)) (qmaMediatorRestriction (σ := σ) (κ := κ))
    (qmaPhysicalOperator g C D V) (qmaPaddedPenalty g) (qmaComplementOperator C D V)
    ((qmaMatrixOperator C).restrictScalars ℝ) (qmaCouplingOperator V)
    qmaMediator_restrict_include qmaMediator_inclusion_adjoint
    (qmaMatrixOperator_real_symmetric _ (qmaPhysicalMediator_star g C D V hC hD hV))
    (qmaPhysicalOperator_low g C D V) (qmaMediatorRestriction_column V)
    (qmaPhysicalOperator_high g C D V) p _ (qmaThirdTrial_high_kernel g V p)

theorem qmaPhysical_thirdOrder_trial (g : ℝ) (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ)
    (hg : 0 < g) (hC : C.conjTranspose = C) (hD : ∀ e, (D e).conjTranspose = D e)
    (hV : ∀ e, (V e).conjTranspose = V e) {m η μ : ℝ} (hm : 0 ≤ m)
    (hCouple : ∑ e, ‖spinMatrixOperator (V e)‖ ≤ g*η) (hμ : -m ≤ μ)
    (p : EuclideanSpace ℂ σ) (hp : ‖p‖ = 1)
    (he : qmaQuadratic (qmaThirdMatrix C D V (g:ℂ)) (fun i => p i) = μ) :
    0 < ‖qmaThirdTrial g V p‖^2 ∧
      ⟪qmaThirdTrial g V p,qmaPhysicalOperator g C D V (qmaThirdTrial g V p)⟫_ℝ /
        ‖qmaThirdTrial g V p‖^2 ≤ μ+m*η^2 := by
  constructor
  · rw [qmaThirdTrial_norm,hp]
    positivity
  · rw [qmaThirdTrial_energy g C D V hC hD hV,qmaThirdTrial_norm]
    have hAT (z : EuclideanSpace ℂ (σ × (κ → Fin 2))) :
        qmaPaddedPenalty g (qmaPaddedInverse g z) = z :=
      qmaPaddedPenalty_inverse (σ := σ) (κ := κ) hg z
    have heForm : Perturbation.thirdOrderForm ((qmaMatrixOperator C).restrictScalars ℝ)
        (qmaPaddedInverse g) (qmaComplementOperator C D V) (qmaCouplingOperator V) p = μ := by
      rw [qmaActual_thirdOrderForm]
      exact he
    have h : Perturbation.lowBlockRayleigh ((qmaMatrixOperator C).restrictScalars ℝ)
        (qmaPaddedPenalty g) (qmaComplementOperator C D V) (qmaCouplingOperator V) p
        (-(qmaPaddedInverse g (qmaCouplingOperator V p))) ≤ μ+m*η^2 := by
      apply Perturbation.thirdOrder_trial_upper ((qmaMatrixOperator C).restrictScalars ℝ)
        (qmaPaddedPenalty g) (qmaPaddedInverse g) (qmaComplementOperator C D V) (qmaCouplingOperator V) hm
      · exact hAT
      · exact qmaInverseCoupling_bound g hg V hCouple
      · exact hμ
      · exact hp
      · exact heForm
    simpa only [Perturbation.lowBlockRayleigh,norm_neg] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitMediatorGround
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A full-space ground-energy estimate for the explicit parallel gadget. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

theorem qmaPhysical_thirdOrder_ground (g : ℝ) (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ)
    (hg : 0 < g) (hC : C.conjTranspose = C) (hD : ∀ e, (D e).conjTranspose = D e)
    (hV : ∀ e, (V e).conjTranspose = V e) {d m η : ℝ}
    (hd : 0 ≤ d) (hm : 0 ≤ m) (hsmall : 2*d+4*m ≤ g)
    (hPert : ‖qmaPerturbationOperator C D V‖ ≤ d)
    (hCouple : ∑ e, ‖spinMatrixOperator (V e)‖ ≤ g*η)
    (hbound : ∀ p : EuclideanSpace ℂ σ, ‖p‖ = 1 →
      |qmaQuadratic (qmaThirdMatrix C D V (g:ℂ)) (fun i => p i)| ≤ m)
    (u : EuclideanSpace ℂ σ) (hu : ‖u‖ = 1) :
    |MediatorGraph.normalizedBottom (qmaPhysicalMediatorMatrix g C D V)-
      Perturbation.thirdOrderBottom ((qmaMatrixOperator C).restrictScalars ℝ)
        (qmaPaddedInverse g) (qmaComplementOperator C D V) (qmaCouplingOperator V)| ≤
      (2*d^2/g+2*m)*η^2 := by
  obtain ⟨p,hp,hmin⟩ := Perturbation.thirdOrderForm_minimizer
    ((qmaMatrixOperator C).restrictScalars ℝ) (qmaPaddedInverse g)
    (qmaComplementOperator C D V) (qmaCouplingOperator V) u hu
  rw [Perturbation.thirdOrderBottom_eq _ _ _ _ p hp hmin,qmaActual_thirdOrderForm]
  let μ := qmaQuadratic (qmaThirdMatrix C D V (g:ℂ)) (fun i => p i)
  let ε := (2*d^2/g+2*m)*η^2
  have hμ : |μ| ≤ m := hbound p hp
  have hmin' (v : EuclideanSpace ℂ σ) :
      μ*‖v‖^2 ≤ qmaQuadratic (qmaThirdMatrix C D V (g:ℂ)) (fun i => v i) := by
    simpa only [qmaActual_thirdOrderForm] using hmin v
  have hl (x : EuclideanSpace ℂ (σ × (κ → Fin 2))) :
      (μ-ε)*‖x‖^2 ≤ ⟪x,qmaPhysicalOperator g C D V x⟫_ℝ :=
    qmaPhysical_thirdOrder_lower g C D V hg hC hD hV hd hm hsmall hPert hCouple
      (abs_le.mp hμ).2 hmin' x
  have hu0 : ‖qmaMediatorInclusion (κ := κ) u‖ = 1 :=
    (Perturbation.orthogonalInclusion_norm
      (qmaMediatorInclusion (σ := σ) (κ := κ)) (qmaMediatorRestriction (σ := σ) (κ := κ))
      qmaMediator_restrict_include qmaMediator_inclusion_adjoint u).trans hu
  have hnon : {e | ∃ x : EuclideanSpace ℂ (σ × (κ → Fin 2)), ‖x‖ = 1 ∧
      e = ⟪x,qmaPhysicalOperator g C D V x⟫_ℝ}.Nonempty := ⟨_,_,hu0,rfl⟩
  have hlow : μ-ε ≤ MediatorGraph.normalizedBottom (qmaPhysicalMediatorMatrix g C D V) := by
    apply le_csInf hnon
    rintro e ⟨x,hx,rfl⟩
    simpa only [hx,one_pow,mul_one] using hl x
  obtain ⟨ht,htrial⟩ := qmaPhysical_thirdOrder_trial g C D V hg hC hD hV hm hCouple
    (abs_le.mp hμ).1 p hp rfl
  have hb : BddBelow {e | ∃ x : EuclideanSpace ℂ (σ × (κ → Fin 2)), 0 < ‖x‖^2 ∧
      e = ⟪x,qmaPhysicalOperator g C D V x⟫_ℝ/‖x‖^2} := by
    refine ⟨μ-ε,?_⟩
    rintro e ⟨x,hx,rfl⟩
    exact (le_div_iff₀ hx).mpr (hl x)
  have hup : MediatorGraph.normalizedBottom (qmaPhysicalMediatorMatrix g C D V) ≤ μ+m*η^2 := by
    rw [MediatorGraph.normalizedBottom_eq_rayleigh]
    exact (csInf_le hb ⟨qmaThirdTrial g V p,ht,rfl⟩).trans htrial
  have heps : m*η^2 ≤ ε := by
    have hz : 0 ≤ 2*d^2/g := by positivity
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg η)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitMediatorNormBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.spinMatrixOperator_diagonal _root_.OAI.ContinuumCoulomb.spinMatrixOperator_sub _root_.OAI.ContinuumCoulomb.spinMatrixOperator_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Norm bounds for arbitrary old-spin operators tensored with the actual
mediator identity, occupation projections, and flips. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {σ α κ : Type*} [Fintype σ] [DecidableEq σ]
  [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]

theorem qmaKronecker_identity_apply (M : Matrix σ σ ℂ)
    (x : EuclideanSpace ℂ (σ × α)) (s : σ) (a : α) :
    spinMatrixOperator (M ⊗ₖ (1 : Matrix α α ℂ)) x (s,a) =
      spinMatrixOperator M (WithLp.toLp 2 (fun t => x (t,a))) s := by
  simp [spinMatrixOperator_apply,Matrix.one_apply,
    Fintype.sum_prod_type]

theorem qmaKronecker_identity_norm (M : Matrix σ σ ℂ) :
    ‖spinMatrixOperator (M ⊗ₖ (1 : Matrix α α ℂ))‖ ≤ ‖spinMatrixOperator M‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow]
  simp only [EuclideanSpace.norm_sq_eq,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ a : α, ‖spinMatrixOperator M‖^2*(∑ s : σ, ‖x (s,a)‖^2) := by
      apply Finset.sum_le_sum
      intro a _
      let y : EuclideanSpace ℂ σ := WithLp.toLp 2 (fun t => x (t,a))
      have h := pow_le_pow_left₀ (norm_nonneg _) ((spinMatrixOperator M).le_opNorm y) 2
      simpa only [mul_pow,EuclideanSpace.norm_sq_eq,qmaKronecker_identity_apply,y] using h
    _ = _ := by rw [← Finset.mul_sum,Finset.sum_comm]

theorem qmaKronecker_flip_norm (M : Matrix σ σ ℂ) (e : κ) :
    ‖spinMatrixOperator (M ⊗ₖ qmaBitFlipMatrix e)‖ ≤ ‖spinMatrixOperator M‖ := by
  have hfac : M ⊗ₖ qmaBitFlipMatrix e =
      (M ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ))*
        ((1 : Matrix σ σ ℂ) ⊗ₖ qmaBitFlipMatrix e) := by
    rw [← Matrix.mul_kronecker_mul,mul_one,one_mul]
  rw [hfac,spinMatrixOperator_mul]
  have hflip : ‖spinMatrixOperator ((1 : Matrix σ σ ℂ) ⊗ₖ qmaBitFlipMatrix e)‖ ≤ 1 := by
    apply qmaKronecker_unitary_norm
    · simp
    · rw [qmaBitFlipMatrix_star,qmaBitFlipMatrix_square]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (qmaKronecker_identity_norm M) hflip (norm_nonneg _) (norm_nonneg _)).trans_eq
      (mul_one _))

theorem qmaKronecker_occupation_norm_bound (M : Matrix σ σ ℂ) (e : κ) :
    ‖spinMatrixOperator (M ⊗ₖ qmaAncillaOccupation e)‖ ≤ ‖spinMatrixOperator M‖ := by
  have hfac : M ⊗ₖ qmaAncillaOccupation e =
      (M ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ))*
        ((1 : Matrix σ σ ℂ) ⊗ₖ qmaAncillaOccupation e) := by
    rw [← Matrix.mul_kronecker_mul,mul_one,one_mul]
  rw [hfac,spinMatrixOperator_mul]
  have hocc : ‖spinMatrixOperator ((1 : Matrix σ σ ℂ) ⊗ₖ qmaAncillaOccupation e)‖ ≤ 1 :=
    qmaKronecker_occupation_norm _ (by simp) e
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (qmaKronecker_identity_norm M) hocc (norm_nonneg _) (norm_nonneg _)).trans_eq
      (mul_one _))

theorem qmaPerturbationOperator_norm (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ) :
    ‖qmaPerturbationOperator C D V‖ ≤ ‖spinMatrixOperator C‖+
      ∑ e, ‖spinMatrixOperator (D e)‖+∑ e, ‖spinMatrixOperator (V e)‖ := by
  change ‖(qmaMatrixOperator (qmaMediatorPerturbation C D V)).restrictScalars ℝ‖ ≤ _
  rw [ContinuousLinearMap.norm_restrictScalars,qmaMatrixOperator_square]
  unfold qmaMediatorPerturbation qmaMediatorOccupations qmaMediatorFlips
  simp only [spinMatrixOperator_add,spinMatrixOperator_sum]
  have hD : ‖∑ e, spinMatrixOperator (D e ⊗ₖ qmaAncillaOccupation e)‖ ≤
      ∑ e, ‖spinMatrixOperator (D e)‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum (fun e _ => qmaKronecker_occupation_norm_bound _ e))
  have hV : ‖∑ e, spinMatrixOperator (V e ⊗ₖ qmaBitFlipMatrix e)‖ ≤
      ∑ e, ‖spinMatrixOperator (V e)‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum (fun e _ => qmaKronecker_flip_norm _ e))
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (qmaKronecker_identity_norm C) hD)) hV)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitMediatorTargetGround
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual parallel gadget approximates its intended finite Hamiltonian,
including the residual left by the common counterterm. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

theorem qmaThirdOrderBottom_eq (g : ℝ) (L : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ) :
    Perturbation.thirdOrderBottom ((qmaMatrixOperator L).restrictScalars ℝ)
      (qmaPaddedInverse g) (qmaComplementOperator L D V) (qmaCouplingOperator V) =
        MediatorGraph.normalizedBottom (qmaThirdMatrix L D V (g:ℂ)) := by
  unfold Perturbation.thirdOrderBottom MediatorGraph.normalizedBottom
  congr 1
  ext e
  constructor <;> rintro ⟨p,hp,he⟩ <;> refine ⟨p,hp,?_⟩
  · rw [qmaActual_thirdOrderForm] at he
    simpa only [qmaQuadratic_operator,qmaMatrixOperator_square] using he
  · rw [qmaActual_thirdOrderForm]
    simpa only [qmaQuadratic_operator,qmaMatrixOperator_square] using he

theorem qmaThirdSeries_target_ground (H : Matrix σ σ ℂ) (A B C : κ → Matrix σ σ ℂ)
    (J : κ → ℂ) {R K : ℝ} (hK : 1 ≤ K) (hR : 4*K ≤ R)
    (hA : ∀ e, A e*A e = 1) (hB : ∀ e, B e*B e = 1)
    (hAB : ∀ e, A e*B e = B e*A e) (hAC : ∀ e, A e*C e = C e*A e)
    (hBC : ∀ e, B e*C e = C e*B e)
    (hC : ∀ e, (C e).conjTranspose = C e)
    (hP : ∀ e, (qmaThirdSeriesPair (A e) (B e) (J e)).conjTranspose =
      qmaThirdSeriesPair (A e) (B e) (J e))
    (hLstar : (qmaThirdSeriesLow H A B C R J).conjTranspose = qmaThirdSeriesLow H A B C R J)
    (hL : ‖spinMatrixOperator (qmaThirdSeriesLow H A B C R J)‖ ≤ K*R)
    (hPsq : ∑ e, ‖spinMatrixOperator (qmaThirdSeriesPair (A e) (B e) (J e))‖^2 ≤ K)
    (hTarget : ‖spinMatrixOperator (qmaThirdSeriesTarget H A B C J)‖ ≤ K)
    (hPert : ‖qmaPerturbationOperator (qmaThirdSeriesLow H A B C R J)
      (fun e => (R^2 : ℝ) • C e)
      (fun e => (R^2 : ℝ) • qmaThirdSeriesPair (A e) (B e) (J e))‖ ≤ K*R^2)
    (hCouple : ∑ e, ‖spinMatrixOperator ((R^2 : ℝ) •
      qmaThirdSeriesPair (A e) (B e) (J e))‖ ≤ R^3*(K/R))
    (u : EuclideanSpace ℂ σ) (hu : ‖u‖ = 1) :
    |MediatorGraph.normalizedBottom (qmaPhysicalMediatorMatrix (R^3)
        (qmaThirdSeriesLow H A B C R J) (fun e => (R^2 : ℝ) • C e)
        (fun e => (R^2 : ℝ) • qmaThirdSeriesPair (A e) (B e) (J e)))-
      MediatorGraph.normalizedBottom (qmaThirdSeriesTarget H A B C J)| ≤ 5*K^4/R := by
  let L := qmaThirdSeriesLow H A B C R J
  let P := fun e => qmaThirdSeriesPair (A e) (B e) (J e)
  let D := fun e => (R^2 : ℝ) • C e
  let V := fun e => (R^2 : ℝ) • P e
  let M := qmaThirdMatrix L D V (R^3 : ℝ)
  let T := qmaThirdSeriesTarget H A B C J
  let E := ((R:ℂ)⁻¹)^2 • (∑ e, P e*L*P e)
  have hRp : 0 < R := by linarith
  have hKp : 0 ≤ K := by linarith
  have hident : M = T+E := qmaThirdMatrix_target H A B C R J hRp.ne' hA hB hAB hAC hBC hP
  have hE : ‖spinMatrixOperator E‖ ≤ K^2/R :=
    qmaThirdResidual_polynomial_bound L P hRp hKp hPsq hL
  have hsmallE : K^2/R ≤ K := by
    apply (div_le_iff₀ hRp).mpr
    nlinarith
  have hM : ‖spinMatrixOperator M‖ ≤ 2*K := by
    rw [hident,spinMatrixOperator_add]
    exact (norm_add_le _ _).trans ((add_le_add hTarget (hE.trans hsmallE)).trans_eq (by ring))
  have hDstar (e : κ) : (D e).conjTranspose = D e := by
    change ((R^2 : ℝ) • C e).conjTranspose = (R^2 : ℝ) • C e
    simp only [Matrix.conjTranspose_smul,star_trivial,hC]
  have hVstar (e : κ) : (V e).conjTranspose = V e := by
    change ((R^2 : ℝ) • P e).conjTranspose = (R^2 : ℝ) • P e
    have hPe : (P e).conjTranspose = P e := hP e
    rw [Matrix.conjTranspose_smul,star_trivial,hPe]
  have hbound (p : EuclideanSpace ℂ σ) (hp : ‖p‖ = 1) :
      |qmaQuadratic M (fun i => p i)| ≤ 2*K := by
    have hb := (qmaQuadratic_norm_bound M p).trans
      (mul_le_mul_of_nonneg_right hM (sq_nonneg ‖p‖))
    simpa only [hp,one_pow,mul_one] using hb
  have hg : 0 < R^3 := pow_pos hRp 3
  have hground := qmaPhysical_thirdOrder_ground (R^3) L D V hg hLstar hDstar hVstar
    (show 0 ≤ K*R^2 by positivity) (show 0 ≤ 2*K by positivity)
    (Perturbation.thirdOrder_scale_small hK hR) hPert hCouple hbound u hu
  rw [qmaThirdOrderBottom_eq] at hground
  have hMT : |MediatorGraph.normalizedBottom M-MediatorGraph.normalizedBottom T| ≤ K^2/R := by
    apply qmaNormalizedBottom_norm_error M T u hu
    simpa only [hident,add_sub_cancel_left] using hE
  have hK24 : K^2 ≤ K^4 := by
    exact pow_le_pow_right₀ hK (by omega : (2:ℕ) ≤ 4)
  calc
    _ ≤ |MediatorGraph.normalizedBottom (qmaPhysicalMediatorMatrix (R^3) L D V)-
          MediatorGraph.normalizedBottom M|+
        |MediatorGraph.normalizedBottom M-MediatorGraph.normalizedBottom T| := abs_sub_le _ _ _
    _ ≤ (2*(K*R^2)^2/R^3+2*(2*K))*(K/R)^2+K^2/R := add_le_add hground hMT
    _ ≤ 4*K^4/R+K^4/R := add_le_add (Perturbation.thirdOrder_scale_error hK hR)
      (div_le_div_of_nonneg_right hK24 hRp.le)
    _ = _ := by ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitThirdNormBudget
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.spinMatrixOperator_diagonal _root_.OAI.ContinuumCoulomb.spinMatrixOperator_sub _root_.OAI.ContinuumCoulomb.spinMatrixOperator_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A rational polynomial budget for the third-order counterterms. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem qmaThirdWeight_bounds (j : ℝ) :
    1 ≤ qmaThirdWeight j ∧ |j| ≤ qmaThirdWeight j ∧
      1+(j/2)^2+|j| ≤ qmaThirdWeight j ∧
      1+|j|/2 ≤ 1+|j| := by
  have hj := abs_nonneg j
  have hs := sq_abs j
  dsimp [qmaThirdWeight]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem qmaMatrix_real_smul_norm (r : ℝ) (M : Matrix σ σ ℂ) :
    ‖spinMatrixOperator (r • M)‖ = |r| * ‖spinMatrixOperator M‖ := by
  change ‖spinMatrixOperator ((r:ℂ) • M)‖ = _
  rw [spinMatrixOperator_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs]

theorem qmaMatrix_product_norm (A B : Matrix σ σ ℂ)
    (hA : ‖spinMatrixOperator A‖ ≤ 1) (hB : ‖spinMatrixOperator B‖ ≤ 1) :
    ‖spinMatrixOperator (A*B)‖ ≤ 1 := by
  rw [spinMatrixOperator_mul]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hA hB (norm_nonneg _) zero_le_one).trans_eq (one_mul _))

theorem qmaMatrixOperator_neg (A : Matrix σ σ ℂ) :
    spinMatrixOperator (-A) = -spinMatrixOperator A := by
  unfold spinMatrixOperator
  rw [map_neg,map_neg]

theorem qmaThirdPair_norm (A B : Matrix σ σ ℂ) (j : ℝ)
    (hA : ‖spinMatrixOperator A‖ ≤ 1) (hB : ‖spinMatrixOperator B‖ ≤ 1) :
    ‖spinMatrixOperator (qmaThirdSeriesPair A B j)‖ ≤ 1+|j| := by
  have he : (j:ℂ)/2 = ((j/2:ℝ):ℂ) := by push_cast; rfl
  unfold qmaThirdSeriesPair
  rw [he,spinMatrixOperator_add,spinMatrixOperator_smul]
  calc
    _ ≤ ‖spinMatrixOperator A‖+‖((j/2:ℝ):ℂ) • spinMatrixOperator B‖ := norm_add_le _ _
    _ = ‖spinMatrixOperator A‖+(|j|/2)*‖spinMatrixOperator B‖ := by
      rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_div,
        abs_of_pos (by norm_num : (0:ℝ) < 2)]
    _ ≤ 1+|j|/2 := by
      simpa only [mul_one] using add_le_add hA (mul_le_mul_of_nonneg_left hB (by positivity))
    _ ≤ 1+|j| := (qmaThirdWeight_bounds j).2.2.2

theorem qmaThirdCounter_norm (A B C : Matrix σ σ ℂ) (r j : ℝ) (hr : 0 ≤ r)
    (hA : ‖spinMatrixOperator A‖ ≤ 1) (hB : ‖spinMatrixOperator B‖ ≤ 1)
    (hC : ‖spinMatrixOperator C‖ ≤ 1) :
    ‖spinMatrixOperator (qmaThirdSeriesCounter A B C r j)‖ ≤ (r+1)*qmaThirdWeight j := by
  let c : ℝ := 1+(j/2)^2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcast : (1+((j:ℂ)/2)^2) = (c:ℂ) := by dsimp [c]; push_cast; rfl
  have hI : ‖spinMatrixOperator (1 : Matrix σ σ ℂ)‖ ≤ 1 := by
    exact spinMatrixOperator_unitary_norm _ (by simp)
  have hAB := qmaMatrix_product_norm A B hA hB
  have he : qmaThirdSeriesCounter A B C r j =
      (r:ℝ) • ((c:ℝ) • (1 : Matrix σ σ ℂ)+(j:ℝ) • (A*B))-(c:ℝ) • C := by
    simp only [qmaThirdSeriesCounter,hcast]
    rfl
  rw [he]
  have hfirst : ‖spinMatrixOperator ((c:ℝ) • (1 : Matrix σ σ ℂ)+(j:ℝ) • (A*B))‖ ≤ c+|j| := by
    rw [spinMatrixOperator_add]
    apply (norm_add_le _ _).trans
    rw [qmaMatrix_real_smul_norm,qmaMatrix_real_smul_norm,abs_of_nonneg hc]
    simpa only [mul_one] using add_le_add
      (mul_le_mul_of_nonneg_left hI hc) (mul_le_mul_of_nonneg_left hAB (abs_nonneg j))
  have hnormsub : ‖spinMatrixOperator (r • (c • (1 : Matrix σ σ ℂ)+j • (A*B))-c • C)‖ ≤
      ‖spinMatrixOperator (r • (c • (1 : Matrix σ σ ℂ)+j • (A*B)))‖+
      ‖spinMatrixOperator (c • C)‖ := by
    rw [sub_eq_add_neg]
    rw [spinMatrixOperator_add]
    rw [qmaMatrixOperator_neg]
    simpa only [norm_neg] using norm_add_le (spinMatrixOperator (r • (c • (1 : Matrix σ σ ℂ)+j • (A*B))))
      (-(spinMatrixOperator (c • C)))
  apply hnormsub.trans
  rw [qmaMatrix_real_smul_norm,qmaMatrix_real_smul_norm,abs_of_nonneg hr,abs_of_nonneg hc]
  calc
    _ ≤ r*(c+|j|)+c := by
      simpa only [mul_one] using add_le_add (mul_le_mul_of_nonneg_left hfirst hr)
        (mul_le_mul_of_nonneg_left hC hc)
    _ ≤ (r+1)*qmaThirdWeight j := by
      have hb := (qmaThirdWeight_bounds j).2.2.1
      change c+|j| ≤ qmaThirdWeight j at hb
      have hm := mul_le_mul_of_nonneg_left hb hr
      nlinarith [abs_nonneg j]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitThirdFamilyBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summed polynomial coefficient bounds for an actual parallel gadget family. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

theorem qmaThirdWeight_pair (j : ℝ) : 1+|j| ≤ qmaThirdWeight j := by
  have hj := abs_nonneg j
  dsimp [qmaThirdWeight]
  nlinarith

omit [DecidableEq κ] in
theorem qmaThirdBudget_pos {b : ℝ} (hb : 0 ≤ b) (J : κ → ℝ) : 1 ≤ qmaThirdBudget b J := by
  have hs : 0 ≤ ∑ e, qmaThirdWeight (J e) := Finset.sum_nonneg (fun e _ => sq_nonneg _)
  unfold qmaThirdBudget
  linarith

omit [DecidableEq κ] in
theorem qmaThirdPair_sum_bounds (A B : κ → Matrix σ σ ℂ) (J : κ → ℝ)
    (hA : ∀ e, ‖spinMatrixOperator (A e)‖ ≤ 1)
    (hB : ∀ e, ‖spinMatrixOperator (B e)‖ ≤ 1) :
    (∑ e, ‖spinMatrixOperator (qmaThirdSeriesPair (A e) (B e) (J e))‖ ≤
        ∑ e, qmaThirdWeight (J e)) ∧
      (∑ e, ‖spinMatrixOperator (qmaThirdSeriesPair (A e) (B e) (J e))‖^2 ≤
        ∑ e, qmaThirdWeight (J e)) := by
  constructor
  · exact Finset.sum_le_sum (fun e _ =>
      (qmaThirdPair_norm (A e) (B e) (J e) (hA e) (hB e)).trans (qmaThirdWeight_pair (J e)))
  · apply Finset.sum_le_sum
    intro e _
    exact pow_le_pow_left₀ (norm_nonneg _) (qmaThirdPair_norm (A e) (B e) (J e) (hA e) (hB e)) 2

omit [DecidableEq κ] in
theorem qmaThirdLow_norm (H : Matrix σ σ ℂ) (A B C : κ → Matrix σ σ ℂ) (J : κ → ℝ)
    {r b : ℝ} (hr : 0 ≤ r) (hH : ‖spinMatrixOperator H‖ ≤ b)
    (hA : ∀ e, ‖spinMatrixOperator (A e)‖ ≤ 1)
    (hB : ∀ e, ‖spinMatrixOperator (B e)‖ ≤ 1)
    (hC : ∀ e, ‖spinMatrixOperator (C e)‖ ≤ 1) :
    ‖spinMatrixOperator (qmaThirdSeriesLow H A B C r (fun e => J e))‖ ≤
      b+(r+1)*(∑ e, qmaThirdWeight (J e)) := by
  unfold qmaThirdSeriesLow
  rw [spinMatrixOperator_add,spinMatrixOperator_sum]
  calc
    _ ≤ ‖spinMatrixOperator H‖+∑ e, ‖spinMatrixOperator
        (qmaThirdSeriesCounter (A e) (B e) (C e) r (J e))‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ b+∑ e, (r+1)*qmaThirdWeight (J e) := add_le_add hH
      (Finset.sum_le_sum (fun e _ => qmaThirdCounter_norm _ _ _ r (J e) hr (hA e) (hB e) (hC e)))
    _ = _ := by rw [Finset.mul_sum]

omit [DecidableEq κ] in
theorem qmaThirdTarget_norm (H : Matrix σ σ ℂ) (A B C : κ → Matrix σ σ ℂ) (J : κ → ℝ)
    {b : ℝ} (hH : ‖spinMatrixOperator H‖ ≤ b)
    (hA : ∀ e, ‖spinMatrixOperator (A e)‖ ≤ 1)
    (hB : ∀ e, ‖spinMatrixOperator (B e)‖ ≤ 1)
    (hC : ∀ e, ‖spinMatrixOperator (C e)‖ ≤ 1) :
    ‖spinMatrixOperator (qmaThirdSeriesTarget H A B C (fun e => J e))‖ ≤
      b+∑ e, qmaThirdWeight (J e) := by
  unfold qmaThirdSeriesTarget
  rw [spinMatrixOperator_add,spinMatrixOperator_sum]
  apply (norm_add_le _ _).trans
  apply add_le_add hH
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro e _
  rw [spinMatrixOperator_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs]
  have hp := qmaMatrix_product_norm (A e*B e) (C e)
    (qmaMatrix_product_norm (A e) (B e) (hA e) (hB e)) (hC e)
  exact (mul_le_mul_of_nonneg_left hp (abs_nonneg _)).trans
    (by simpa only [mul_one] using (qmaThirdWeight_bounds (J e)).2.1)

omit [DecidableEq κ] in
theorem qmaScaledCoupling_sum (V : κ → Matrix σ σ ℂ) (r : ℝ) :
    (∑ e, ‖spinMatrixOperator ((r^2:ℝ) • V e)‖) = r^2*∑ e, ‖spinMatrixOperator (V e)‖ := by
  simp only [qmaMatrix_real_smul_norm,abs_of_nonneg (sq_nonneg r),Finset.mul_sum]

theorem qmaScaledPerturbation_norm (L : Matrix σ σ ℂ) (C P : κ → Matrix σ σ ℂ)
    {r w : ℝ} (hr : 1 ≤ r) (hw : 0 ≤ w)
    (hL : ‖spinMatrixOperator L‖ ≤ 2*w*r)
    (hC : ∑ e, ‖spinMatrixOperator (C e)‖ ≤ w)
    (hP : ∑ e, ‖spinMatrixOperator (P e)‖ ≤ w) :
    ‖qmaPerturbationOperator L (fun e => (r^2:ℝ) • C e)
      (fun e => (r^2:ℝ) • P e)‖ ≤ (4*w)*r^2 := by
  have hn := qmaPerturbationOperator_norm L (fun e => (r^2:ℝ) • C e)
    (fun e => (r^2:ℝ) • P e)
  rw [qmaScaledCoupling_sum,qmaScaledCoupling_sum] at hn
  have hc := mul_le_mul_of_nonneg_left hC (sq_nonneg r)
  have hp := mul_le_mul_of_nonneg_left hP (sq_nonneg r)
  have hr2 : r ≤ r^2 := by nlinarith
  have hwr := mul_le_mul_of_nonneg_left hr2 (show 0 ≤ 2*w by positivity)
  nlinarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitThirdCalibration
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.spinMatrixOperator_diagonal _root_.OAI.ContinuumCoulomb.spinMatrixOperator_sub _root_.OAI.ContinuumCoulomb.spinMatrixOperator_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All norm hypotheses of the physical third-order comparison follow from
one explicit polynomial in the original real coefficients. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

theorem qmaThirdFamily_calibration (H : Matrix σ σ ℂ) (A B C : κ → Matrix σ σ ℂ)
    (J : κ → ℝ) {b R : ℝ} (hb : 0 ≤ b) (hR : 1 ≤ R)
    (hH : ‖spinMatrixOperator H‖ ≤ b)
    (hA : ∀ e, ‖spinMatrixOperator (A e)‖ ≤ 1)
    (hB : ∀ e, ‖spinMatrixOperator (B e)‖ ≤ 1)
    (hC : ∀ e, ‖spinMatrixOperator (C e)‖ ≤ 1) :
    let K := qmaThirdBudget b J
    let L := qmaThirdSeriesLow H A B C R (fun e => J e)
    let P := fun e => qmaThirdSeriesPair (A e) (B e) (J e)
    ‖spinMatrixOperator L‖ ≤ K*R ∧
      (∑ e, ‖spinMatrixOperator (P e)‖^2 ≤ K) ∧
      ‖spinMatrixOperator (qmaThirdSeriesTarget H A B C (fun e => J e))‖ ≤ K ∧
      ‖qmaPerturbationOperator L (fun e => (R^2:ℝ) • C e)
        (fun e => (R^2:ℝ) • P e)‖ ≤ K*R^2 ∧
      (∑ e, ‖spinMatrixOperator ((R^2:ℝ) • P e)‖ ≤ R^3*(K/R)) := by
  let S := ∑ e, qmaThirdWeight (J e)
  let W := 1+b+S
  let L := qmaThirdSeriesLow H A B C R (fun e => J e)
  let P := fun e => qmaThirdSeriesPair (A e) (B e) (J e)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun e _ => sq_nonneg _)
  have hSW : S ≤ W := by dsimp [W]; linarith
  have hW : 0 ≤ W := by dsimp [W]; linarith
  have hR0 : 0 ≤ R := by linarith
  have hRp : 0 < R := by linarith
  have hpair := qmaThirdPair_sum_bounds A B J hA hB
  have hnormL : ‖spinMatrixOperator L‖ ≤ b+(R+1)*S := qmaThirdLow_norm H A B C J hR0 hH hA hB hC
  have hL : ‖spinMatrixOperator L‖ ≤ 2*W*R := by
    apply hnormL.trans
    have hbr : b ≤ b*R := by nlinarith
    have hsr : S ≤ S*R := by nlinarith
    dsimp [W]
    nlinarith
  have hsumC : ∑ e, ‖spinMatrixOperator (C e)‖ ≤ W := by
    apply le_trans (Finset.sum_le_sum (fun e _ => (hC e).trans (qmaThirdWeight_bounds (J e)).1))
    exact hSW
  have hsumP : ∑ e, ‖spinMatrixOperator (P e)‖ ≤ W := hpair.1.trans hSW
  have hLbig : ‖spinMatrixOperator L‖ ≤ (4*W)*R := by
    apply hL.trans
    nlinarith
  have hPsq : ∑ e, ‖spinMatrixOperator (P e)‖^2 ≤ 4*W := by
    apply hpair.2.trans
    nlinarith
  have htarget : ‖spinMatrixOperator (qmaThirdSeriesTarget H A B C (fun e => J e))‖ ≤ 4*W := by
    apply (qmaThirdTarget_norm H A B C J hH hA hB hC).trans
    dsimp [W]
    linarith
  have hpert := qmaScaledPerturbation_norm L C P hR hW hL hsumC hsumP
  have hcouple : ∑ e, ‖spinMatrixOperator ((R^2:ℝ) • P e)‖ ≤ R^3*((4*W)/R) := by
    rw [qmaScaledCoupling_sum]
    calc
      _ ≤ R^2*W := mul_le_mul_of_nonneg_left hsumP (sq_nonneg R)
      _ ≤ R^2*(4*W) := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg R)
      _ = _ := by field_simp
  exact ⟨hLbig,hPsq,htarget,hpert,hcouple⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitThirdHermitian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial counterterms preserve Hermiticity for real couplings. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]

omit [Fintype σ] [DecidableEq σ] in
theorem qmaThirdPair_star (A B : Matrix σ σ ℂ) (j : ℝ)
    (hA : A.conjTranspose = A) (hB : B.conjTranspose = B) :
    (qmaThirdSeriesPair A B j).conjTranspose = qmaThirdSeriesPair A B j := by
  have hj : (j:ℂ)/2 = ((j/2:ℝ):ℂ) := by push_cast; rfl
  unfold qmaThirdSeriesPair
  rw [hj]
  change (A+(j/2:ℝ) • B).conjTranspose = A+(j/2:ℝ) • B
  rw [Matrix.conjTranspose_add,Matrix.conjTranspose_smul,star_trivial,hA,hB]

theorem qmaThirdCounter_star (A B C : Matrix σ σ ℂ) (r j : ℝ)
    (hA : A.conjTranspose = A) (hB : B.conjTranspose = B) (hC : C.conjTranspose = C)
    (hAB : A*B = B*A) :
    (qmaThirdSeriesCounter A B C r j).conjTranspose = qmaThirdSeriesCounter A B C r j := by
  have hc : 1+((j:ℂ)/2)^2 = ((1+(j/2)^2:ℝ):ℂ) := by push_cast; rfl
  unfold qmaThirdSeriesCounter
  rw [hc]
  change ((r:ℝ) • ((1+(j/2)^2:ℝ) • (1 : Matrix σ σ ℂ)+(j:ℝ) • (A*B))-
    (1+(j/2)^2:ℝ) • C).conjTranspose = _
  simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_add,Matrix.conjTranspose_smul,
    Matrix.conjTranspose_mul,Matrix.conjTranspose_one,star_trivial,hA,hB,hC,← hAB]
  rfl

theorem qmaThirdLow_star (H : Matrix σ σ ℂ) (A B C : κ → Matrix σ σ ℂ)
    (r : ℝ) (J : κ → ℝ) (hH : H.conjTranspose = H)
    (hA : ∀ e, (A e).conjTranspose = A e) (hB : ∀ e, (B e).conjTranspose = B e)
    (hC : ∀ e, (C e).conjTranspose = C e) (hAB : ∀ e, A e*B e = B e*A e) :
    (qmaThirdSeriesLow H A B C r (fun e => J e)).conjTranspose =
      qmaThirdSeriesLow H A B C r (fun e => J e) := by
  simp only [qmaThirdSeriesLow,Matrix.conjTranspose_add,Matrix.conjTranspose_sum,hH]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  exact qmaThirdCounter_star (A e) (B e) (C e) r (J e) (hA e) (hB e) (hC e) (hAB e)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitThirdGadget
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit parallel third-order gadget with a polynomial accuracy scale. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

theorem qmaThirdGadget_error (H : Matrix σ σ ℂ) (A B C : κ → Matrix σ σ ℂ)
    (J : κ → ℝ) {b R : ℝ} (hb : 0 ≤ b)
    (hR : 4*qmaThirdBudget b J ≤ R)
    (hH : H.conjTranspose = H) (hHnorm : ‖spinMatrixOperator H‖ ≤ b)
    (hAstar : ∀ e, (A e).conjTranspose = A e)
    (hBstar : ∀ e, (B e).conjTranspose = B e)
    (hCstar : ∀ e, (C e).conjTranspose = C e)
    (hA : ∀ e, A e*A e = 1) (hB : ∀ e, B e*B e = 1) (hC : ∀ e, C e*C e = 1)
    (hAB : ∀ e, A e*B e = B e*A e) (hAC : ∀ e, A e*C e = C e*A e)
    (hBC : ∀ e, B e*C e = C e*B e)
    (u : EuclideanSpace ℂ σ) (hu : ‖u‖ = 1) :
    |MediatorGraph.normalizedBottom (qmaThirdGadget H A B C R J)-
      MediatorGraph.normalizedBottom (qmaThirdSeriesTarget H A B C (fun e => J e))| ≤
        5*(qmaThirdBudget b J)^4/R := by
  have hK : 1 ≤ qmaThirdBudget b J := qmaThirdBudget_pos hb J
  have hr : 1 ≤ R := by linarith
  have hAnorm (e : κ) : ‖spinMatrixOperator (A e)‖ ≤ 1 := by
    apply spinMatrixOperator_unitary_norm
    rw [hAstar,hA]
  have hBnorm (e : κ) : ‖spinMatrixOperator (B e)‖ ≤ 1 := by
    apply spinMatrixOperator_unitary_norm
    rw [hBstar,hB]
  have hCnorm (e : κ) : ‖spinMatrixOperator (C e)‖ ≤ 1 := by
    apply spinMatrixOperator_unitary_norm
    rw [hCstar,hC]
  obtain ⟨hL,hPsq,hTarget,hPert,hCouple⟩ :=
    qmaThirdFamily_calibration H A B C J hb hr hHnorm hAnorm hBnorm hCnorm
  exact qmaThirdSeries_target_ground H A B C (fun e => J e) hK hR hA hB hAB hAC hBC
    hCstar (fun e => qmaThirdPair_star (A e) (B e) (J e) (hAstar e) (hBstar e))
    (qmaThirdLow_star H A B C R J hH hAstar hBstar hCstar hAB)
    hL hPsq hTarget hPert hCouple u hu

theorem qmaThirdGadget_polynomial_accuracy_oai (H : Matrix σ σ ℂ)
    (A B C : κ → Matrix σ σ ℂ) (J : κ → ℝ) {b N : ℝ} (hb : 0 ≤ b) (hN : 1 ≤ N)
    (hH : H.conjTranspose = H) (hHnorm : ‖spinMatrixOperator H‖ ≤ b)
    (hAstar : ∀ e, (A e).conjTranspose = A e)
    (hBstar : ∀ e, (B e).conjTranspose = B e)
    (hCstar : ∀ e, (C e).conjTranspose = C e)
    (hA : ∀ e, A e*A e = 1) (hB : ∀ e, B e*B e = 1) (hC : ∀ e, C e*C e = 1)
    (hAB : ∀ e, A e*B e = B e*A e) (hAC : ∀ e, A e*C e = C e*A e)
    (hBC : ∀ e, B e*C e = C e*B e)
    (u : EuclideanSpace ℂ σ) (hu : ‖u‖ = 1) :
    let R := 8*(qmaThirdBudget b J)^4*N
    |MediatorGraph.normalizedBottom (qmaThirdGadget H A B C R J)-
      MediatorGraph.normalizedBottom (qmaThirdSeriesTarget H A B C (fun e => J e))| ≤ 1/N := by
  let K := qmaThirdBudget b J
  have hK : 1 ≤ K := qmaThirdBudget_pos hb J
  have hR := (Perturbation.thirdOrder_polynomial_schedule hK hN).1
  have he := qmaThirdGadget_error H A B C J hb hR hH hHnorm hAstar hBstar hCstar
    hA hB hC hAB hAC hBC u hu
  apply he.trans
  have hNp : 0 < N := by linarith
  have hKp : 0 < K := by linarith
  change 5*K^4/(8*K^4*N) ≤ 1/N
  have heq : 5*K^4/(8*K^4*N) = (5/8:ℝ)/N := by field_simp
  rw [heq]
  exact div_le_div_of_nonneg_right (by norm_num) hNp.le

end ContinuumCoulomb

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.ContinuumCoulomb.qmaThirdGadget_polynomial_accuracy_oai.{u_1, u_2} := @OAI.ContinuumCoulomb.qmaThirdGadget_polynomial_accuracy_oai.{u_1, u_2}
