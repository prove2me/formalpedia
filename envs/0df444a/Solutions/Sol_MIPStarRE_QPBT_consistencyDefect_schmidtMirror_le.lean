-- Prove2me | solution 1 for MIPStarRE.QPBT.consistencyDefect_schmidtMirror_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:56:25.825725+00:00
-- url     : https://prove2.me/submissions/c9ceb3d5-a519-4fa3-97af-ea51a9f2e58d

-- Generated proof for MIPStarRE.QPBT.consistencyDefect_schmidtMirror_le.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Defs
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Pasting_SchmidtMirror
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_point_distance_eq_two_defect_of_projective
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_point_distance_le_two_defect
import Theorems.Thm_MIPStarRE_QPBT_schmidtMirror_norm_sq_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.SandwichProduct
end MIPStarRE.QPBT.SandwichProduct

/- Source helpers from QPBT/Games/DistanceTheorems/Support.lean. -/
/-!
# Finite-dimensional operator estimates for state-dependent distance

This module contains finite-dimensional operator and finite-sum identities used
by the paper-facing distance theorems. It introduces no new mathematical
assumptions or source-facing statements.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-395`
- `references/ldt-paper/preliminaries.tex:649-666`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective























































/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14): the matrix-vector term in `consistencyDefect` is the state quadratic
form. -/
theorem consistency_term_eq_stateQForm {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    (inner ℂ ψ ((EuclideanSpace.equiv ι ℂ).symm (M.mulVec ψ))).re =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := by
  rfl



































end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Games/Sandwich/Defs.lean. -/
/-! # Definitions for sandwiched measurements

This module defines the palindromic operator products and the conditional
collision predicate used by the sandwich and pasting lemmas.

## References

Blueprint `lem:ld-sandwich` and `lem:pasting`; paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-525`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open DistanceCalculus












/-! ### Tensor placements of measurements

The operator families compared in `lem:pasting` are placed on one factor of a
bipartite space. The two constructions below present such a placed family as a
measurement, so that the consistency calculus applies to it verbatim. -/









/-- The left placement of a projective measurement is projective.
Formalization support for `lem:pasting`, blueprint
`ch12_qpbt_games.tex:960-990`. -/
theorem Measurement.isProjective_leftPlacement {α ιA ιB : Type*} [Fintype α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιA) (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M) :
    _root_.MIPStarRE.QPBT.Measurement.IsProjective (_root_.MIPStarRE.QPBT.Measurement.leftPlacement (ιB := ιB) M) := by
  intro a
  constructor
  · show _root_.MIPStarRE.QPBT.heteroKron (M.effect a) 1 * _root_.MIPStarRE.QPBT.heteroKron (M.effect a) 1 =
      _root_.MIPStarRE.QPBT.heteroKron (M.effect a) 1
    rw [_root_.MIPStarRE.QPBT.heteroKron_mul, (hM a).isIdempotentElem.eq, mul_one]
  · show (_root_.MIPStarRE.QPBT.heteroKron (M.effect a) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB))ᴴ = _root_.MIPStarRE.QPBT.heteroKron (M.effect a) 1
    unfold _root_.MIPStarRE.QPBT.heteroKron Matrix.kronecker
    rw [Matrix.conjTranspose_kronecker, _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian M a,
      Matrix.conjTranspose_one]

/-- The right placement of a projective measurement is projective. This is the
right-factor mirror of the preceding lemma and the second of the four
properties of the placement collected in the formalization-support node
`lem:pasting-tensor-placement`, blueprint `ch12_qpbt_games.tex:1063-1071`. -/
theorem Measurement.isProjective_rightPlacement {α ιA ιB : Type*} [Fintype α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιB) (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M) :
    _root_.MIPStarRE.QPBT.Measurement.IsProjective (_root_.MIPStarRE.QPBT.Measurement.rightPlacement (ιA := ιA) M) := by
  intro a
  constructor
  · show _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (M.effect a) * _root_.MIPStarRE.QPBT.heteroKron 1 (M.effect a) =
      _root_.MIPStarRE.QPBT.heteroKron 1 (M.effect a)
    rw [_root_.MIPStarRE.QPBT.heteroKron_mul, (hM a).isIdempotentElem.eq, mul_one]
  · show (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (M.effect a))ᴴ = _root_.MIPStarRE.QPBT.heteroKron 1 (M.effect a)
    unfold _root_.MIPStarRE.QPBT.heteroKron Matrix.kronecker
    rw [Matrix.conjTranspose_kronecker, _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian M a,
      Matrix.conjTranspose_one]














end MIPStarRE.QPBT

/- Source helpers from QPBT/Games/Sandwich/Pasting/SchmidtMirror.lean. -/
/-! # State-dependent Schmidt mirrors

This module constructs the opposite-register mirror used in the one-sided
pasting argument. The auxiliary construction uses the spectral theorem and
orthonormal completion, including zero Schmidt coefficients.

## References

`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`, `lem:pasting`;
`docs/paper-gaps/qpbt_pasting-product-error.tex`, issue Dengnifer/MIPStarRE-QPBT-bak#201. The
Schmidt-mirror
argument is a formalization auxiliary, not an additional paper hypothesis.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective











variable {ι : Type*} [Fintype ι] [DecidableEq ι]















/-- Multiplication is reversed by the Schmidt mirror. -/
theorem schmidtMirror_mul (ψ : EuclideanSpace ℂ (ι × ι)) (first second : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.schmidtMirror ψ (first * second) = _root_.MIPStarRE.QPBT.schmidtMirror ψ second * _root_.MIPStarRE.QPBT.schmidtMirror ψ first := by
  have hunitary : (_root_.MIPStarRE.QPBT.schmidtMirrorUnitary ψ : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᴴ *
      (_root_.MIPStarRE.QPBT.schmidtMirrorUnitary ψ : _root_.LIDT.MIPStarRE.Quantum.Op ι) = 1 := Unitary.coe_star_mul_self _
  change _ * (first * second)ᵀ * _ = (_ * secondᵀ * _) * (_ * firstᵀ * _)
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (_root_.MIPStarRE.QPBT.schmidtMirrorUnitary ψ : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᴴ
    (_root_.MIPStarRE.QPBT.schmidtMirrorUnitary ψ : _root_.LIDT.MIPStarRE.Quantum.Op ι), hunitary, Matrix.one_mul]

/-- The mirror preserves adjoints, in addition to reversing products. -/
theorem schmidtMirror_adjoint (ψ : EuclideanSpace ℂ (ι × ι)) (bob : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.schmidtMirror ψ bobᴴ = (_root_.MIPStarRE.QPBT.schmidtMirror ψ bob)ᴴ := by
  change _ * bobᴴᵀ * _ = (_ * bobᵀ * _)ᴴ
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rfl









/-- A projective measurement has a projective Schmidt mirror. -/
theorem schmidtMirrorMeasurement_isProjective {α : Type*} [Fintype α]
    (ψ : EuclideanSpace ℂ (ι × ι)) (measurement : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι)
    (hprojective : _root_.MIPStarRE.QPBT.Measurement.IsProjective measurement) :
    _root_.MIPStarRE.QPBT.Measurement.IsProjective (_root_.MIPStarRE.QPBT.schmidtMirrorMeasurement ψ measurement) := by
  intro answer
  change _root_.LIDT.MIPStarRE.Quantum.IsProj (_root_.MIPStarRE.QPBT.schmidtMirror ψ (measurement.effect answer))
  refine ⟨?_, ?_⟩
  · change _root_.MIPStarRE.QPBT.schmidtMirror ψ (measurement.effect answer) *
      _root_.MIPStarRE.QPBT.schmidtMirror ψ (measurement.effect answer) = _
    rw [← _root_.MIPStarRE.QPBT.schmidtMirror_mul, (hprojective answer).isIdempotentElem.eq]
  · change (_root_.MIPStarRE.QPBT.schmidtMirror ψ (measurement.effect answer))ᴴ = _
    rw [← _root_.MIPStarRE.QPBT.schmidtMirror_adjoint,
      (hprojective answer).isSelfAdjoint.isHermitian.eq]

end MIPStarRE.QPBT

/-! # Consistency and commutation of the pasting codeword families

This module records the cross consistency of the coarse second codeword family,
the commutator estimate for the two coarse families, the collision average of
the distinct second codewords, and the comparison of the fine second codeword
family with its coarse-graining.  These are the codeword-family steps of the
proof of `lem:pasting` recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex`.

## References

Blueprint `blueprint/src/chapter/ch12_qpbt_games.tex:960-1050`; paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open MIPStarRE.QPBT.DistanceCalculus

theorem solution {Q α ι : Type*}
    [Fintype Q] [DecidableEq Q] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (D : _root_.LIDT.MIPStarRE.LDT.Distribution Q) (A B : Q → _root_.LIDT.MIPStarRE.Quantum.Measurement α ι)
    (ψ : EuclideanSpace ℂ (ι × ι))
    (hB : ∀ question, _root_.MIPStarRE.QPBT.Measurement.IsProjective (B question)) :
    _root_.MIPStarRE.QPBT.consistencyDefect D
      (fun question answer => _root_.MIPStarRE.QPBT.heteroKron
        ((_root_.MIPStarRE.QPBT.schmidtMirrorMeasurement ψ (B question)).effect answer) 1)
      (fun question answer => _root_.MIPStarRE.QPBT.heteroKron 1 ((B question).effect answer)) ψ ≤
    2 * _root_.MIPStarRE.QPBT.consistencyDefect D
      (fun question answer => _root_.MIPStarRE.QPBT.heteroKron ((A question).effect answer) 1)
      (fun question answer => _root_.MIPStarRE.QPBT.heteroKron 1 ((B question).effect answer)) ψ := by
  classical
  unfold _root_.MIPStarRE.QPBT.consistencyDefect
  simp_rw [_root_.MIPStarRE.QPBT.DistanceCalculus.consistency_term_eq_stateQForm]
  rw [← _root_.LIDT.MIPStarRE.LDT.avgOver_const_mul]
  refine _root_.LIDT.MIPStarRE.LDT.avgOver_mono D _ _ fun question => ?_
  have hmirror := _root_.MIPStarRE.QPBT.DistanceCalculus.point_distance_eq_two_defect_of_projective
    (_root_.MIPStarRE.QPBT.Measurement.leftPlacement (ιB := ι) (_root_.MIPStarRE.QPBT.schmidtMirrorMeasurement ψ (B question)))
    (_root_.MIPStarRE.QPBT.Measurement.rightPlacement (ιA := ι) (B question)) ψ
    (_root_.MIPStarRE.QPBT.Measurement.isProjective_leftPlacement _
      (_root_.MIPStarRE.QPBT.schmidtMirrorMeasurement_isProjective ψ _ (hB question)))
    (_root_.MIPStarRE.QPBT.Measurement.isProjective_rightPlacement _ (hB question))
  have hpredict := _root_.MIPStarRE.QPBT.DistanceCalculus.point_distance_le_two_defect
    (_root_.MIPStarRE.QPBT.Measurement.leftPlacement (ιB := ι) (A question))
    (_root_.MIPStarRE.QPBT.Measurement.rightPlacement (ιA := ι) (B question)) ψ
  have hnorm : (∑ answer : α, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
      (_root_.MIPStarRE.QPBT.heteroKron ((_root_.MIPStarRE.QPBT.schmidtMirrorMeasurement ψ (B question)).effect answer) 1 -
        _root_.MIPStarRE.QPBT.heteroKron 1 ((B question).effect answer)) ψ‖ ^ 2) ≤
      2 * ∑ answer : α, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron ((A question).effect answer) 1 -
          _root_.MIPStarRE.QPBT.heteroKron 1 ((B question).effect answer)) ψ‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun answer _ => ?_
    simpa only [_root_.MIPStarRE.QPBT.schmidtMirrorMeasurement, _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne,
      _root_.MIPStarRE.QPBT.applyOperatorToState, map_sub, LinearMap.sub_apply] using
      _root_.MIPStarRE.QPBT.schmidtMirror_norm_sq_le ψ ((A question).effect answer) ((B question).effect answer)
        (_root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian _ _) (_root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian _ _)
  simp only [_root_.MIPStarRE.QPBT.Measurement.leftPlacement_effect, _root_.MIPStarRE.QPBT.Measurement.rightPlacement_effect]
    at hmirror hpredict
  linarith
