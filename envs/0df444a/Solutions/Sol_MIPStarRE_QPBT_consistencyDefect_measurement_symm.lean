-- Prove2me | solution 1 for MIPStarRE.QPBT.consistencyDefect_measurement_symm
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:21:21.364411+00:00
-- url     : https://prove2.me/submissions/3d0e5db5-c65f-4313-ac13-1cb125813098

-- Generated proof for MIPStarRE.QPBT.consistencyDefect_measurement_symm.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

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

/-!
# Evaluated total-Pauli consistency before extraction

The supplied-witness point estimates combine with point self-consistency and
the two orientations of the game's Pauli-basis check. All estimates act on the
original six-register state, before conjugation by the swaps.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1785-1810`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

open MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open LIDT.MIPStarRE.LDT hiding Measurement

theorem solution {X α I : Type*}
    [Fintype X] [DecidableEq X]
    [Fintype α] [DecidableEq α] [Fintype I] [DecidableEq I]
    (mu : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A B : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α I) (psi : EuclideanSpace ℂ I) :
    _root_.MIPStarRE.QPBT.consistencyDefect mu (fun x a => (A x).effect a) (fun x a => (B x).effect a) psi =
      _root_.MIPStarRE.QPBT.consistencyDefect mu (fun x a => (B x).effect a) (fun x a => (A x).effect a) psi := by
  unfold _root_.MIPStarRE.QPBT.consistencyDefect
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro x
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  by_cases hab : a = b
  · simp [hab]
  · simp only [if_neg hab, if_neg (Ne.symm hab), _root_.MIPStarRE.QPBT.DistanceCalculus.consistency_term_eq_stateQForm]
    have hstar : ((A x).effect a * (B x).effect b)ᴴ =
        (B x).effect b * (A x).effect a := by
      simp only [Matrix.conjTranspose_mul, _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian]
    rw [← hstar]
    unfold _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm _root_.MIPStarRE.QPBT.applyOperatorToState
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]
    exact inner_re_symm (𝕜 := ℂ) _ _
