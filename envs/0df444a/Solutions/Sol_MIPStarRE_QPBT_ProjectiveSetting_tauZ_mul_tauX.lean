-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.tauZ_mul_tauX
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:52:44.882341+00:00
-- url     : https://prove2.me/submissions/25c400dc-437f-4165-b46d-f70074f69ea6

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.tauZ_mul_tauX.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Algebra_PauliTheorems
import Definitions.Def_QPBT_QPBT_Observables_Anticommuting
import Definitions.Def_QPBT_QPBT_Observables_ExpandedCommutation
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/- Source helpers from QPBT/Algebra/Pauli.lean. -/
/-!
# Generalized Pauli operators and EPR states

The definitions here use finite matrix entries and rank-one projectors, so they
are usable by the later game statements without introducing an abstract
operator algebra.  The observable/projector expansions are obtained from
finite-field Fourier orthogonality in characteristic two.

## References

The source-facing nodes are blueprint `def:lin-reg`, `def:EPR`,
`def:generalized-pauli`, and `lem:pauli-observable-expansion`.  The paper origin is
`references/qpbt-paper/04_preliminaries.tex:908-1161`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.Preliminaries

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod 2) K]















/-- The binary sign character squares to one, since the binary field has
characteristic two. This is the eigenvalue property used by the observables of
blueprint `def:generalized-pauli`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1052-1096`. -/
theorem phaseSign_mul_self (t : ZMod 2) : _root_.MIPStarRE.QPBT.phaseSign t * _root_.MIPStarRE.QPBT.phaseSign t = 1 := by
  rw [← _root_.MIPStarRE.QPBT.phaseSign_add]
  have hzero : t + t = 0 := by
    rcases _root_.MIPStarRE.QPBT.zmod_two_eq_zero_or_one t with ht | ht <;> subst ht <;> decide
  rw [hzero, _root_.MIPStarRE.QPBT.phaseSign, if_pos rfl]

































































end MIPStarRE.QPBT

/-!
# Approximate commutation of the expanded point projections

The trace-coarse-grained expanded point projections approximately commute on
each of the four register placements.  The commutator of the two projections is
a scalar multiple of a factorized operator whose strategy factor is the twisted
commutator of the two point observables and whose Pauli factor is a product of
generalized Pauli observables; the latter is an isometry, so the placement
bookkeeping of `ExpandedPlacement` reduces the estimate to the twisted
commutation relation of `lem:qld-win-implications-obs` on the corresponding
player side.  Both player sides are treated explicitly.

## References

The declarations prove item 2 of `lem:qld-comm-cons` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:1139-1178`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:466-505`.
-/



open scoped BigOperators Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



/-! ## Algebraic preliminaries -/





open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-! ## The commutator of two expanded point projections -/

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ω : _root_.MIPStarRE.QPBT.PauliTuple P) :
    _root_.MIPStarRE.QPBT.ProjectiveSetting.tauZ P ω * _root_.MIPStarRE.QPBT.ProjectiveSetting.tauX P ω =
      _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
        (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauX P ω * _root_.MIPStarRE.QPBT.ProjectiveSetting.tauZ P ω) := by
  have h := _root_.MIPStarRE.QPBT.tauObservable_X_mul_Z (K := _root_.MIPStarRE.QPBT.PauliScalar P)
    (fun h => ω.2.2.1 * _root_.MIPStarRE.QPBT.indicatorVec ω.1 h)
    (fun h => ω.2.2.2 * _root_.MIPStarRE.QPBT.indicatorVec ω.2.1 h)
  have hg : _root_.MIPStarRE.QPBT.binTrace (_root_.MIPStarRE.QPBT.PauliScalar P)
      (dotProduct (fun h => ω.2.2.1 * _root_.MIPStarRE.QPBT.indicatorVec ω.1 h)
        (fun h => ω.2.2.2 * _root_.MIPStarRE.QPBT.indicatorVec ω.2.1 h)) =
      _root_.MIPStarRE.QPBT.gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 := rfl
  rw [hg, show (_root_.MIPStarRE.QPBT.tauObservable .X fun k => ω.2.2.1 * _root_.MIPStarRE.QPBT.indicatorVec ω.1 k) =
      _root_.MIPStarRE.QPBT.ProjectiveSetting.tauX P ω from rfl,
    show (_root_.MIPStarRE.QPBT.tauObservable .Z fun k => ω.2.2.2 * _root_.MIPStarRE.QPBT.indicatorVec ω.2.1 k) =
      _root_.MIPStarRE.QPBT.ProjectiveSetting.tauZ P ω from rfl] at h
  have hsq := _root_.MIPStarRE.QPBT.phaseSign_mul_self (_root_.MIPStarRE.QPBT.gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
  calc _root_.MIPStarRE.QPBT.ProjectiveSetting.tauZ P ω * _root_.MIPStarRE.QPBT.ProjectiveSetting.tauX P ω
      = (_root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) *
          _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)) •
            (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauZ P ω * _root_.MIPStarRE.QPBT.ProjectiveSetting.tauX P ω) := by rw [hsq, one_smul]
    _ = _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
          (_root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
            (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauZ P ω * _root_.MIPStarRE.QPBT.ProjectiveSetting.tauX P ω)) := by rw [smul_smul]
    _ = _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
          (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauX P ω * _root_.MIPStarRE.QPBT.ProjectiveSetting.tauZ P ω) := by rw [← h]
