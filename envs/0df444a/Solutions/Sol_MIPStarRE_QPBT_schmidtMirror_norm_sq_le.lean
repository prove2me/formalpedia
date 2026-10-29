-- Prove2me | solution 1 for MIPStarRE.QPBT.schmidtMirror_norm_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:52:45.112199+00:00
-- url     : https://prove2.me/submissions/2ae2d2c5-e5cf-40b5-b482-2b99af1f721a

-- Generated proof for MIPStarRE.QPBT.schmidtMirror_norm_sq_le.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
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
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Pasting_SchmidtMirror
import Theorems.Thm_MIPStarRE_QPBT_schmidt_action_norm_sq
import Theorems.Thm_MIPStarRE_QPBT_schmidt_diagonal_mirror_estimate

namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
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







private theorem schmidt_entry_mass_eq_trace {ι : Type*} [Fintype ι] (coeff : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    (∑ row, ∑ col, Complex.normSq (coeff row col)) = (coeff * coeffᴴ).trace.re := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.normSq_apply, Complex.mul_re]

private theorem schmidt_entry_mass_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (left right : Matrix.unitaryGroup ι ℂ) (coeff : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    (∑ row, ∑ col, Complex.normSq (((left : _root_.LIDT.MIPStarRE.Quantum.Op ι) * coeff * (right : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᴴ) row col)) =
      ∑ row, ∑ col, Complex.normSq (coeff row col) := by
  rw [schmidt_entry_mass_eq_trace, schmidt_entry_mass_eq_trace]
  have hright : (right : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᴴ * (right : _root_.LIDT.MIPStarRE.Quantum.Op ι) = 1 := Unitary.coe_star_mul_self right
  have hleft : (left : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᴴ * (left : _root_.LIDT.MIPStarRE.Quantum.Op ι) = 1 := Unitary.coe_star_mul_self left
  have hprod : ((left : _root_.LIDT.MIPStarRE.Quantum.Op ι) * coeff * (right : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᴴ) *
      ((left : _root_.LIDT.MIPStarRE.Quantum.Op ι) * coeff * (right : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᴴ)ᴴ =
      (left : _root_.LIDT.MIPStarRE.Quantum.Op ι) * (coeff * coeffᴴ) * (left : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (right : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᴴ (right : _root_.LIDT.MIPStarRE.Quantum.Op ι), hright, Matrix.one_mul]
  rw [hprod, Matrix.trace_mul_cycle, hleft, Matrix.one_mul]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]





/-- The chosen coordinates reconstruct the coefficient matrix with nonnegative
Schmidt coefficients. In particular, this includes nonfaithful reduced states. -/
theorem schmidtCoordinates_spec (ψ : EuclideanSpace ℂ (ι × ι)) :
    (∀ index, 0 ≤ (_root_.MIPStarRE.QPBT.schmidtCoordinates ψ).2.2 index) ∧
      _root_.MIPStarRE.QPBT.schmidtCoefficientMatrix ψ = ((_root_.MIPStarRE.QPBT.schmidtCoordinates ψ).1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) *
        Matrix.diagonal (fun index => ((_root_.MIPStarRE.QPBT.schmidtCoordinates ψ).2.2 index : ℂ)) *
          ((_root_.MIPStarRE.QPBT.schmidtCoordinates ψ).2.1 : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᴴ :=
  Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (_root_.MIPStarRE.QPBT.exists_schmidt_coordinates (_root_.MIPStarRE.QPBT.schmidtCoefficientMatrix ψ))))























end MIPStarRE.QPBT

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



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective











variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution (ψ : EuclideanSpace ℂ (ι × ι))
    (alice bob : _root_.LIDT.MIPStarRE.Quantum.Op ι) (halice : alice.IsHermitian) (hbob : bob.IsHermitian) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.schmidtMirror ψ bob) 1) ψ -
      _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 bob) ψ‖ ^ 2 ≤
      2 * ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron alice 1) ψ -
        _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 bob) ψ‖ ^ 2 := by
  let left := (_root_.MIPStarRE.QPBT.schmidtCoordinates ψ).1
  let right := (_root_.MIPStarRE.QPBT.schmidtCoordinates ψ).2.1
  let values := (_root_.MIPStarRE.QPBT.schmidtCoordinates ψ).2.2
  let diagonal := Matrix.diagonal (fun index => (values index : ℂ))
  let alice' := (left : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᴴ * alice * (left : _root_.LIDT.MIPStarRE.Quantum.Op ι)
  let bob' := (right : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᴴ * bobᵀ * (right : _root_.LIDT.MIPStarRE.Quantum.Op ι)
  have hvalues : ∀ index, 0 ≤ values index := (_root_.MIPStarRE.QPBT.schmidtCoordinates_spec ψ).1
  have hfactor : _root_.MIPStarRE.QPBT.schmidtCoefficientMatrix ψ =
      (left : _root_.LIDT.MIPStarRE.Quantum.Op ι) * diagonal * (right : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᴴ := (_root_.MIPStarRE.QPBT.schmidtCoordinates_spec ψ).2
  have hmirror : _root_.MIPStarRE.QPBT.schmidtMirror ψ bob = (left : _root_.LIDT.MIPStarRE.Quantum.Op ι) * bob' * (left : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᴴ := by
    simp [_root_.MIPStarRE.QPBT.schmidtMirror, _root_.MIPStarRE.QPBT.schmidtMirrorUnitary, left, right, bob', Matrix.mul_assoc,
      Matrix.star_eq_conjTranspose]
  have halice' : alice'.IsHermitian := by
    change ((left : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᴴ * alice * (left : _root_.LIDT.MIPStarRE.Quantum.Op ι))ᴴ = _
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      halice.eq, alice', Matrix.mul_assoc]
  have hbob' : bob'.IsHermitian := by
    change ((right : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᴴ * bobᵀ * (right : _root_.LIDT.MIPStarRE.Quantum.Op ι))ᴴ = _
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hbob.transpose.eq, bob', Matrix.mul_assoc]
  have hleft : (left : _root_.LIDT.MIPStarRE.Quantum.Op ι) * (left : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᴴ = 1 := Unitary.coe_mul_star_self left
  have hleft' : (left : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᴴ * (left : _root_.LIDT.MIPStarRE.Quantum.Op ι) = 1 := Unitary.coe_star_mul_self left
  have hright : (right : _root_.LIDT.MIPStarRE.Quantum.Op ι) * (right : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᴴ = 1 := Unitary.coe_mul_star_self right
  have hcancel (middle : _root_.LIDT.MIPStarRE.Quantum.Op ι) : (left : _root_.LIDT.MIPStarRE.Quantum.Op ι) * ((left : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᴴ * middle) = middle := by
    rw [← Matrix.mul_assoc, hleft, Matrix.one_mul]
  have hcancel' (middle : _root_.LIDT.MIPStarRE.Quantum.Op ι) : (left : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᴴ * ((left : _root_.LIDT.MIPStarRE.Quantum.Op ι) * middle) = middle := by
    rw [← Matrix.mul_assoc, hleft', Matrix.one_mul]
  have hmirrordiff : _root_.MIPStarRE.QPBT.schmidtMirror ψ bob * _root_.MIPStarRE.QPBT.schmidtCoefficientMatrix ψ -
      _root_.MIPStarRE.QPBT.schmidtCoefficientMatrix ψ * bobᵀ =
      (left : _root_.LIDT.MIPStarRE.Quantum.Op ι) * (bob' * diagonal - diagonal * bob') * (right : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᴴ := by
    rw [hmirror, hfactor]
    simp only [bob', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hcancel', hright,
      Matrix.mul_one]
  have halicediff : alice * _root_.MIPStarRE.QPBT.schmidtCoefficientMatrix ψ - _root_.MIPStarRE.QPBT.schmidtCoefficientMatrix ψ * bobᵀ =
      (left : _root_.LIDT.MIPStarRE.Quantum.Op ι) * (alice' * diagonal - diagonal * bob') * (right : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᴴ := by
    rw [hfactor]
    simp only [alice', bob', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hcancel,
      hright, Matrix.mul_one]
  rw [_root_.MIPStarRE.QPBT.schmidt_action_norm_sq, _root_.MIPStarRE.QPBT.schmidt_action_norm_sq, hmirrordiff, halicediff,
    schmidt_entry_mass_unitary, schmidt_entry_mass_unitary]
  exact _root_.MIPStarRE.QPBT.schmidt_diagonal_mirror_estimate values hvalues alice' bob' halice' hbob'
