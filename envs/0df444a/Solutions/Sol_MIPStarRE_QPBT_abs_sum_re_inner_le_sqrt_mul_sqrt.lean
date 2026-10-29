-- Prove2me | solution 1 for MIPStarRE.QPBT.abs_sum_re_inner_le_sqrt_mul_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:44:57.079707+00:00
-- url     : https://prove2.me/submissions/fbd2bd99-6d7b-479b-b77b-4d7377510ff9

-- Generated proof for MIPStarRE.QPBT.abs_sum_re_inner_le_sqrt_mul_sqrt.
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
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono
import Theorems.Thm_MIPStarRE_QPBT_norm_inner_applyOperatorToState_le_sqrt_mul_sqrt

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





























/-- A positive semidefinite operator has nonnegative state quadratic form. This
is the formalization-only order fact `lem:distance-qform-nonnegative`, used for
the nonnegative overlap terms in `lem:ld-sandwich`; detailed source proof
`references/neexp-paper/05_quantum_preliminaries.tex:952-999`. -/
theorem stateQForm_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) {M : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hM : 0 ≤ M) :
    0 ≤ _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := by
  calc
    0 = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ 0 := by simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]
    _ ≤ _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := _root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono hM ψ





























































end MIPStarRE.QPBT.DistanceCalculus

/-!
# Replacing one factor of a measurement-weighted overlap

The scalar estimates used to combine the two Pauli bases compare averaged
overlaps whose left factor is one complete measurement and whose right factors
are operator families at small state-dependent distance.  This module records
the corresponding Cauchy--Schwarz estimate.  The right-hand families are
arbitrary, so the estimate covers an ordered product of point effects, which
is not itself a measurement.

## References

The estimate is `lem:overlap-gap-distance` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`; it is the Cauchy--Schwarz
step at paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1147-1166`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



/-! ## The Cauchy--Schwarz inequality weighted by a positive operator -/

theorem solution {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (A : α → _root_.LIDT.MIPStarRE.Quantum.Op ι) (hA : ∀ a, 0 ≤ A a)
    (u v : α → EuclideanSpace ℂ ι) :
    |∑ a, (inner ℂ (u a) (_root_.MIPStarRE.QPBT.applyOperatorToState (A a) (v a))).re| ≤
      Real.sqrt (∑ a, (inner ℂ (u a) (_root_.MIPStarRE.QPBT.applyOperatorToState (A a) (u a))).re) *
        Real.sqrt (∑ a, (inner ℂ (v a) (_root_.MIPStarRE.QPBT.applyOperatorToState (A a) (v a))).re) := by
  have hu : ∀ a, 0 ≤ (inner ℂ (u a) (_root_.MIPStarRE.QPBT.applyOperatorToState (A a) (u a))).re :=
    fun a => _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_nonneg (u a) (hA a)
  have hv : ∀ a, 0 ≤ (inner ℂ (v a) (_root_.MIPStarRE.QPBT.applyOperatorToState (A a) (v a))).re :=
    fun a => _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_nonneg (v a) (hA a)
  calc
    |∑ a, (inner ℂ (u a) (_root_.MIPStarRE.QPBT.applyOperatorToState (A a) (v a))).re|
        ≤ ∑ a, |(inner ℂ (u a) (_root_.MIPStarRE.QPBT.applyOperatorToState (A a) (v a))).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, Real.sqrt (inner ℂ (u a) (_root_.MIPStarRE.QPBT.applyOperatorToState (A a) (u a))).re *
          Real.sqrt (inner ℂ (v a) (_root_.MIPStarRE.QPBT.applyOperatorToState (A a) (v a))).re := by
      refine Finset.sum_le_sum fun a _ => ?_
      exact (Complex.abs_re_le_norm _).trans
        (_root_.MIPStarRE.QPBT.norm_inner_applyOperatorToState_le_sqrt_mul_sqrt (hA a) (u a) (v a))
    _ ≤ Real.sqrt (∑ a,
            Real.sqrt (inner ℂ (u a) (_root_.MIPStarRE.QPBT.applyOperatorToState (A a) (u a))).re ^ 2) *
          Real.sqrt (∑ a,
            Real.sqrt (inner ℂ (v a) (_root_.MIPStarRE.QPBT.applyOperatorToState (A a) (v a))).re ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by
      rw [Finset.sum_congr rfl fun a _ => Real.sq_sqrt (hu a),
        Finset.sum_congr rfl fun a _ => Real.sq_sqrt (hv a)]
