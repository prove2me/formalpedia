-- Prove2me | solution 1 for MIPStarRE.QPBT.stateQForm_eprState_tauPointProj_tauLineProj
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:08:33.241003+00:00
-- url     : https://prove2.me/submissions/9e183b46-3453-4c4c-95bb-54adb8ca8ca8

-- Generated proof for MIPStarRE.QPBT.stateQForm_eprState_tauPointProj_tauLineProj.
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
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Projector
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Restriction
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_tauLineProj_mul_tauPointProj

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/MagicSquareTheorems/PerfectStrategy/Observables.lean. -/
/-!
# Observables of the perfect Magic Square strategy

This module builds the operator table of `thm:ms-from-ac`.  It records the EPR
state carried by the perfect strategy, the binary reflection effects attached
to a Hermitian involution, the real Pauli matrices on the auxiliary qubit, and
the nine cell observables together with their Hermiticity, involutivity,
commutation, and constraint-product identities.

## References

The source statement is blueprint
`thm:ms-from-ac`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:654-722`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section







/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): a symmetric operator acting on the first factor
of the EPR state acts on it exactly as it does on the second factor. -/
theorem epr_action_eq_of_transpose
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (E : _root_.LIDT.MIPStarRE.Quantum.Op V) (hE : Eᵀ = E) :
    (_root_.MIPStarRE.QPBT.heteroKron E 1).mulVec (_root_.MIPStarRE.QPBT.eprState V) =
      (_root_.MIPStarRE.QPBT.heteroKron 1 E).mulVec (_root_.MIPStarRE.QPBT.eprState V) := by
  ext p
  rcases p with ⟨i, j⟩
  simpa [_root_.MIPStarRE.QPBT.heteroKron, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    _root_.MIPStarRE.QPBT.eprState, Matrix.one_apply] using congrFun (congrFun hE j) i























local notation "qubitX" => (_root_.MIPStarRE.QPBT.tauShift (K := ZMod 2) 1)
local notation "qubitZ" => (_root_.MIPStarRE.QPBT.tauPhase (K := ZMod 2) 1)











































end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/LineMeasurement/Projector.lean. -/
/-!
# Pauli-register line projectors

This module constructs the projective measurement `tau^{W,line}` of one
generalized-Pauli register whose outcome is the restriction to a canonical
line of the low-degree encoding of the measured basis label. It records that
the outcome projectors are orthogonal projections summing to the identity,
that they are symmetric matrices (so that they act identically on either half
of an EPR pair), and that on an axis-parallel line they vanish outside the
embedded degree-`d` subspace.

## References

The projectors are `tau^{W,line}_{f''}` of `def:expanded-line-measurement`,
with paper source
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:552-556`. Their
perfect self-consistency on an EPR pair is the ancillary input to item 1 of
`lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:527-532`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section





/-- The line coarse-graining of the generalized Pauli projectors is a
symmetric matrix. Symmetry is what makes the projector act identically on
either half of an EPR pair, and hence is the hypothesis behind the perfect
ancilla consistency used in `enu:qld-comm-line-self-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:527-532`. -/
theorem tauLineProj_transpose (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (line : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams) (f : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d)) :
    (_root_.MIPStarRE.QPBT.tauLineProj P W line f)ᵀ = _root_.MIPStarRE.QPBT.tauLineProj P W line f := by
  classical
  simp only [_root_.MIPStarRE.QPBT.tauLineProj, Matrix.transpose_sum, _root_.MIPStarRE.QPBT.pauliProj_transpose]











/-! ## Interaction with the point projectors -/





/-- Pauli line and point projectors commute. -/
theorem tauPointProj_mul_tauLineProj (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (line : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
    (f : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d)) (b : _root_.MIPStarRE.QPBT.PauliScalar P) :
    _root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u b * _root_.MIPStarRE.QPBT.tauLineProj P W line f =
      _root_.MIPStarRE.QPBT.tauLineProj P W line f * _root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u b := by
  classical
  unfold _root_.MIPStarRE.QPBT.tauLineProj _root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun e' _ => ?_
  rw [_root_.MIPStarRE.QPBT.pauliProj_mul_pauliProj, _root_.MIPStarRE.QPBT.pauliProj_mul_pauliProj]
  by_cases h : e = e'
  · subst h
    simp
  · rw [if_neg (Ne.symm h), if_neg h]



/-- On an EPR pair, a point projector on the first factor and a line
projector on the second act as the product of the two projectors on the first
factor alone. This is the transport with the two factors interchanged, and it
uses the symmetry of the line projector rather than that of the point
projector. Formalization-only auxiliary for the ancillary consistency of
`def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:527-532`. -/
theorem tauPointProj_tauLineProj_mulVec_eprState (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (line : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams)
    (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (f : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d))
    (b : _root_.MIPStarRE.QPBT.PauliScalar P) :
    (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u b)
        (_root_.MIPStarRE.QPBT.tauLineProj P W line f)).mulVec
        (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)) =
      (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.tauLineProj P W line f * _root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u b)
        1).mulVec (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)) := by
  let T := _root_.MIPStarRE.QPBT.tauLineProj P W line f
  let T' := _root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u b
  have hfactor : _root_.MIPStarRE.QPBT.heteroKron T' T = _root_.MIPStarRE.QPBT.heteroKron T' 1 * _root_.MIPStarRE.QPBT.heteroKron 1 T := by
    rw [_root_.MIPStarRE.QPBT.heteroKron_mul, Matrix.mul_one, Matrix.one_mul]
  rw [hfactor, ← Matrix.mulVec_mulVec,
    ← _root_.MIPStarRE.QPBT.epr_action_eq_of_transpose T (_root_.MIPStarRE.QPBT.tauLineProj_transpose P W line f),
    Matrix.mulVec_mulVec, _root_.MIPStarRE.QPBT.heteroKron_mul, Matrix.mul_one,
    _root_.MIPStarRE.QPBT.tauPointProj_mul_tauLineProj]





/-! ## Perfect consistency on an EPR pair -/







end

end MIPStarRE.QPBT

/-!
# Pauli-register line projectors

This module constructs the projective measurement `tau^{W,line}` of one
generalized-Pauli register whose outcome is the restriction to a canonical
line of the low-degree encoding of the measured basis label. It records that
the outcome projectors are orthogonal projections summing to the identity,
that they are symmetric matrices (so that they act identically on either half
of an EPR pair), and that on an axis-parallel line they vanish outside the
embedded degree-`d` subspace.

## References

The projectors are `tau^{W,line}_{f''}` of `def:expanded-line-measurement`,
with paper source
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:552-556`. Their
perfect self-consistency on an EPR pair is the ancillary input to item 1 of
`lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:527-532`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



















/-! ## Interaction with the point projectors -/

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (line : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams)
    (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (hu : u ∈ line.pointSet)
    (f : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d)) (b : _root_.MIPStarRE.QPBT.PauliScalar P) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))
        (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u b)
          (_root_.MIPStarRE.QPBT.tauLineProj P W line f)) =
      if _root_.MIPStarRE.QPBT.evalOpt line u f = some b then
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))
          (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.tauLineProj P W line f) (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P)))
      else 0 := by
  have h : _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))
      (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u b)
        (_root_.MIPStarRE.QPBT.tauLineProj P W line f)) =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))
        (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.tauLineProj P W line f *
          _root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u b) (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P))) := by
    unfold _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm
    congr 2
    ext p
    simpa [_root_.MIPStarRE.QPBT.applyOperatorToState] using
      congrFun (_root_.MIPStarRE.QPBT.tauPointProj_tauLineProj_mulVec_eprState P W line u f b) p
  rw [h, _root_.MIPStarRE.QPBT.tauLineProj_mul_tauPointProj P W line u hu f b]
  split_ifs
  · rfl
  · simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState, _root_.MIPStarRE.QPBT.heteroKron]
