-- Prove2me | solution 1 for MIPStarRE.QPBT.swapUnitary_conj_tildeM
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:21:21.759733+00:00
-- url     : https://prove2.me/submissions/e0a39758-6e9b-4f51-8e5b-b0260ebfc91d

-- Generated proof for MIPStarRE.QPBT.swapUnitary_conj_tildeM.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_Decoding
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Algebra_PauliTheorems
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Extraction_Defs
import Definitions.Def_QPBT_QPBT_Extraction_Observables
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Quantum_ControlledUnitary
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_pauliProj_eq_avg_tauObservable

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.GlobalPairWitness
end MIPStarRE.QPBT.GlobalPairWitness
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity
namespace MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn
end MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn
namespace MIPStarRE.QPBT.PauliKind
end MIPStarRE.QPBT.PauliKind

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

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/Reflections.lean. -/
/-!
# Reflections and the state-dependent metric on operators

The self-testing argument for the Magic Square game manipulates `±1`-valued
observables rather than positive operator valued measures.  This file records
the algebra of such observables and the estimates that convert Born masses into
operator bounds.

Postprocessing a projective measurement along a binary relabelling of its
answers produces a *reflection*, that is, a self-adjoint involution; two
reflections coming from one and the same measurement commute, and their product
is the reflection attached to the sum of the two relabellings.  The reflections
of the source are the binary observables of the rest of the development, so this
file uses `MIPStarRE.QPBT.IsBinaryObservable` and its algebra, defined in
`MIPStarRE/QPBT/Combining/Linearity/Defs.lean`, rather than a second predicate of
its own.  Two operators are compared through the norm of the difference of their
actions on a fixed state, the relation `NormCloseOn` below.  That relation is the
unsquared Euclidean distance between `M ψ` and `N ψ`; it is *not* the
state-dependent distance `≈_δ` of the source, which bounds the squared quantity
`⟨ψ|(M - N)ᴴ (M - N)|ψ⟩` and is formalized in this development by `opDistSq`.
The comparison is symmetric, satisfies the triangle inequality, and is unchanged
by multiplication on the left by an isometric operator; `NormCloseOn.opDistSq_le`
converts it into the source's relation.  Finally, a real spectral combination of
the joint effects of the two players has state-dependent norm controlled by the
Born mass of the answer pairs carrying a nonzero coefficient; this is the step
that turns each rejection mass of the value-to-parity layer into an operator
estimate.

## References

The statements supported here are the operator relations in `thm:ms-rigidity`,
blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:224-253`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`,
proved in Coladangelo--Stark, arXiv:1709.09267v2, Theorem 6.9.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Rectangular tensor placement -/

section Kron

/-- Formalization-only: the tensor placement commutes with adjoints. -/
theorem heteroKron_conjTranspose {ιA ιB : Type} (M : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (N : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    (_root_.MIPStarRE.QPBT.heteroKron M N)ᴴ = _root_.MIPStarRE.QPBT.heteroKron Mᴴ Nᴴ := by
  unfold _root_.MIPStarRE.QPBT.heteroKron
  exact Matrix.conjTranspose_kronecker M N







end Kron

/-! ## The state-dependent norm -/



/-! ## Reflections

The *reflections* of `thm:ms-rigidity`, blueprint
`ch13_qpbt_test.tex:228-250`, are the self-adjoint involutions attached to
two-outcome projective measurements, which are exactly the binary observables
`MIPStarRE.QPBT.IsBinaryObservable` of
`MIPStarRE/QPBT/Combining/Linearity/Defs.lean`.  The Magic Square rigidity
argument therefore uses that predicate and its algebra directly:
`IsBinaryObservable.one`, `IsBinaryObservable.mul`,
`IsBinaryObservable.isometry`, `isBinaryObservable_heteroKron_one` and
`isBinaryObservable_one_heteroKron`. -/



/-! ## Closeness in the state-dependent norm -/





/-! ## Sign observables of a projective measurement -/



/-! ## Deviation of joint spectral combinations on the strategy state -/



end

end MIPStarRE.QPBT.MagicSquareRigidity

/- Source helpers from QPBT/Extraction/Observables.lean. -/
/-!
# Pulled-apart Pauli observables

This module constructs the measurements and observables used to pull the two
Pauli bases onto separate registers. The construction retains the distinct
local spaces of the two players and uses the binary basis fixed in the
canonical field model.

## References

The product form and observable relations formalize blueprint
`lem:tildew-product-form`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1415-1456`.
The swap identities formalize blueprint `lem:v-swap-conjugation`, from paper
lines 1687-1713.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.LDT.Preliminaries LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Pulled-apart measurements and observables -/

























/-! ## Swap conjugation -/



/-- The crossed Pauli factors acquire the phase determined by the selected
polynomial. This is the commutation identity used at paper
`14_analysis_of_the_pauli_basis_test.tex:1701-1713`. -/
private theorem swapPauli_mul_tauObservable {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    (pair : _root_.MIPStarRE.QPBT.PolyPair P) (W : _root_.MIPStarRE.QPBT.PauliKind) (u : _root_.MIPStarRE.QPBT.PauliRegister P) :
    (_root_.MIPStarRE.QPBT.tauObservable .X (_root_.MIPStarRE.QPBT.decodeFq pair.2) * _root_.MIPStarRE.QPBT.tauObservable .Z (_root_.MIPStarRE.QPBT.decodeFq pair.1)) *
        _root_.MIPStarRE.QPBT.tauObservable W u =
      _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model
        (dotProduct (_root_.MIPStarRE.QPBT.decodeFq (W.selectPoly pair)) u)) •
        (_root_.MIPStarRE.QPBT.tauObservable W u *
          (_root_.MIPStarRE.QPBT.tauObservable .X (_root_.MIPStarRE.QPBT.decodeFq pair.2) * _root_.MIPStarRE.QPBT.tauObservable .Z (_root_.MIPStarRE.QPBT.decodeFq pair.1))) := by
  cases W with
  | X =>
      have hcomm : _root_.MIPStarRE.QPBT.tauObservable .X (_root_.MIPStarRE.QPBT.decodeFq pair.2) * _root_.MIPStarRE.QPBT.tauObservable .X u =
          _root_.MIPStarRE.QPBT.tauObservable .X u * _root_.MIPStarRE.QPBT.tauObservable .X (_root_.MIPStarRE.QPBT.decodeFq pair.2) := by
        rw [_root_.MIPStarRE.QPBT.tauObservable_mul, _root_.MIPStarRE.QPBT.tauObservable_mul, add_comm]
      have hcross := congrArg
        (fun A : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P) =>
          _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.binTrace (_root_.MIPStarRE.QPBT.PauliScalar P) (dotProduct u (_root_.MIPStarRE.QPBT.decodeFq pair.1))) • A)
        (_root_.MIPStarRE.QPBT.tauObservable_X_mul_Z u (_root_.MIPStarRE.QPBT.decodeFq pair.1))
      simp only [smul_smul, _root_.MIPStarRE.QPBT.phaseSign_mul_self, one_smul] at hcross
      simp only [_root_.MIPStarRE.QPBT.PauliKind.selectPoly, _root_.MIPStarRE.QPBT.fixedBinTrace]
      rw [dotProduct_comm (_root_.MIPStarRE.QPBT.decodeFq pair.1) u]
      calc
        _ = _root_.MIPStarRE.QPBT.tauObservable .X (_root_.MIPStarRE.QPBT.decodeFq pair.2) *
            (_root_.MIPStarRE.QPBT.tauObservable .Z (_root_.MIPStarRE.QPBT.decodeFq pair.1) * _root_.MIPStarRE.QPBT.tauObservable .X u) :=
          Matrix.mul_assoc _ _ _
        _ = _ := by
          rw [← hcross, Matrix.mul_smul, ← Matrix.mul_assoc, hcomm, Matrix.mul_assoc]
  | Z =>
      have hcomm : _root_.MIPStarRE.QPBT.tauObservable .Z (_root_.MIPStarRE.QPBT.decodeFq pair.1) * _root_.MIPStarRE.QPBT.tauObservable .Z u =
          _root_.MIPStarRE.QPBT.tauObservable .Z u * _root_.MIPStarRE.QPBT.tauObservable .Z (_root_.MIPStarRE.QPBT.decodeFq pair.1) := by
        rw [_root_.MIPStarRE.QPBT.tauObservable_mul, _root_.MIPStarRE.QPBT.tauObservable_mul, add_comm]
      simp only [_root_.MIPStarRE.QPBT.PauliKind.selectPoly, _root_.MIPStarRE.QPBT.fixedBinTrace]
      calc
        _ = _root_.MIPStarRE.QPBT.tauObservable .X (_root_.MIPStarRE.QPBT.decodeFq pair.2) *
            (_root_.MIPStarRE.QPBT.tauObservable .Z (_root_.MIPStarRE.QPBT.decodeFq pair.1) * _root_.MIPStarRE.QPBT.tauObservable .Z u) :=
          Matrix.mul_assoc _ _ _
        _ = _ := by
          rw [hcomm, ← Matrix.mul_assoc, _root_.MIPStarRE.QPBT.tauObservable_X_mul_Z,
            Matrix.smul_mul, Matrix.mul_assoc]

/-- Conjugating a Pauli observable by the crossed Pauli factors multiplies it
by the selected binary phase, as in paper
`14_analysis_of_the_pauli_basis_test.tex:1701-1713`. -/
private theorem swapPauli_conj_tauObservable {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    (pair : _root_.MIPStarRE.QPBT.PolyPair P) (W : _root_.MIPStarRE.QPBT.PauliKind) (u : _root_.MIPStarRE.QPBT.PauliRegister P) :
    _root_.MIPStarRE.QPBT.conjBy (_root_.MIPStarRE.QPBT.tauObservable .X (_root_.MIPStarRE.QPBT.decodeFq pair.2) * _root_.MIPStarRE.QPBT.tauObservable .Z (_root_.MIPStarRE.QPBT.decodeFq pair.1))
        (_root_.MIPStarRE.QPBT.tauObservable W u) =
      _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model
        (dotProduct (_root_.MIPStarRE.QPBT.decodeFq (W.selectPoly pair)) u)) • _root_.MIPStarRE.QPBT.tauObservable W u := by
  rw [_root_.MIPStarRE.QPBT.conjBy, swapPauli_mul_tauObservable, Matrix.smul_mul, Matrix.mul_assoc,
    swapPauli_mul_conjTranspose, Matrix.mul_one]

/-- Fourier inversion turns the Pauli conjugation phase into a translation of
the projector label. This is the projector identity used at paper
`14_analysis_of_the_pauli_basis_test.tex:1805-1822`. -/
private theorem swapPauli_conj_pauliProj {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    (pair : _root_.MIPStarRE.QPBT.PolyPair P) (W : _root_.MIPStarRE.QPBT.PauliKind) (h : _root_.MIPStarRE.QPBT.PauliRegister P) :
    _root_.MIPStarRE.QPBT.conjBy (_root_.MIPStarRE.QPBT.tauObservable .X (_root_.MIPStarRE.QPBT.decodeFq pair.2) * _root_.MIPStarRE.QPBT.tauObservable .Z (_root_.MIPStarRE.QPBT.decodeFq pair.1))
        (_root_.MIPStarRE.QPBT.pauliProj W h) =
      _root_.MIPStarRE.QPBT.pauliProj W (h + _root_.MIPStarRE.QPBT.decodeFq (W.selectPoly pair)) := by
  classical
  rw [_root_.MIPStarRE.QPBT.pauliProj_eq_avg_tauObservable, _root_.MIPStarRE.QPBT.conjBy, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sum, Finset.sum_mul, _root_.MIPStarRE.QPBT.pauliProj_eq_avg_tauObservable]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  rw [Matrix.mul_smul, Matrix.smul_mul]
  change _ • _root_.MIPStarRE.QPBT.conjBy _ _ = _
  rw [swapPauli_conj_tauObservable, smul_smul]
  congr 1
  rw [_root_.MIPStarRE.QPBT.fixedBinTrace, ← _root_.MIPStarRE.QPBT.phaseSign_add, ← map_add,
    dotProduct_comm (_root_.MIPStarRE.QPBT.decodeFq (W.selectPoly pair)) u, dotProduct_add]

/-- Translation of the Pauli label translates its dot-product outcome. This
is the finite reindexing in paper
`14_analysis_of_the_pauli_basis_test.tex:1805-1822`; it does not require a
polynomial to be in the image of the low-degree encoding. -/
private theorem swapPauli_conj_tauDotProj {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    (pair : _root_.MIPStarRE.QPBT.PolyPair P) (W : _root_.MIPStarRE.QPBT.PauliKind) (u : _root_.MIPStarRE.QPBT.PauliRegister P) (a : _root_.MIPStarRE.QPBT.PauliScalar P) :
    _root_.MIPStarRE.QPBT.conjBy (_root_.MIPStarRE.QPBT.tauObservable .X (_root_.MIPStarRE.QPBT.decodeFq pair.2) * _root_.MIPStarRE.QPBT.tauObservable .Z (_root_.MIPStarRE.QPBT.decodeFq pair.1))
        (_root_.MIPStarRE.QPBT.tauDotProj W u a) =
      _root_.MIPStarRE.QPBT.tauDotProj W u (a + dotProduct (_root_.MIPStarRE.QPBT.decodeFq (W.selectPoly pair)) u) := by
  classical
  simp only [_root_.MIPStarRE.QPBT.tauDotProj, _root_.MIPStarRE.QPBT.bracketOp, _root_.MIPStarRE.QPBT.conjBy, Matrix.mul_sum, Finset.sum_mul]
  change (∑ h ∈ Finset.univ.filter (fun h => dotProduct h u = a),
    _root_.MIPStarRE.QPBT.conjBy (_root_.MIPStarRE.QPBT.tauObservable .X (_root_.MIPStarRE.QPBT.decodeFq pair.2) * _root_.MIPStarRE.QPBT.tauObservable .Z (_root_.MIPStarRE.QPBT.decodeFq pair.1))
      (_root_.MIPStarRE.QPBT.pauliProj W h)) = _
  simp_rw [swapPauli_conj_pauliProj]
  apply Finset.sum_equiv (Equiv.addRight (_root_.MIPStarRE.QPBT.decodeFq (W.selectPoly pair)))
  · intro h
    simp [add_dotProduct]
  · intro h _
    rfl







/-- Conjugation by the swap map acts separately on each joint outcome. This
is the diagonal-projector reduction at paper
`14_analysis_of_the_pauli_basis_test.tex:1701-1713,1805-1822`. -/
private theorem swapUnitary_conj_controlled {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    {epsilon delta : ℝ} {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
    (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S delta) (side : _root_.MIPStarRE.QPBT.PlayerSide)
    (R : _root_.MIPStarRE.QPBT.PolyPair P → _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P)) :
    _root_.MIPStarRE.QPBT.conjBy (_root_.MIPStarRE.QPBT.swapUnitary w side)
        (∑ pair, _root_.MIPStarRE.QPBT.heteroKron ((w.Smeas side).effect pair) (R pair)) =
      ∑ pair, _root_.MIPStarRE.QPBT.heteroKron ((w.Smeas side).effect pair)
        (_root_.MIPStarRE.QPBT.conjBy (_root_.MIPStarRE.QPBT.tauObservable .X (_root_.MIPStarRE.QPBT.decodeFq pair.2) *
          _root_.MIPStarRE.QPBT.tauObservable .Z (_root_.MIPStarRE.QPBT.decodeFq pair.1)) (R pair)) := by
  have hself (pair : _root_.MIPStarRE.QPBT.PolyPair P) :
      ((w.Smeas side).effect pair)ᴴ = (w.Smeas side).effect pair :=
    (w.projective side pair).isSelfAdjoint
  simp only [_root_.MIPStarRE.QPBT.conjBy, _root_.MIPStarRE.QPBT.swapUnitary, Matrix.conjTranspose_sum,
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.heteroKron_conjTranspose, hself]
  rw [_root_.LIDT.MIPStarRE.Quantum.sum_heteroKron_mul_sum_heteroKron (w.Smeas side) (w.projective side),
    _root_.LIDT.MIPStarRE.Quantum.sum_heteroKron_mul_sum_heteroKron (w.Smeas side) (w.projective side)]





end

end MIPStarRE.QPBT

/-!
# Pulled-apart Pauli observables

This module constructs the measurements and observables used to pull the two
Pauli bases onto separate registers. The construction retains the distinct
local spaces of the two players and uses the binary basis fixed in the
canonical field model.

## References

The product form and observable relations formalize blueprint
`lem:tildew-product-form`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1415-1456`.
The swap identities formalize blueprint `lem:v-swap-conjugation`, from paper
lines 1687-1713.
-/



open scoped BigOperators Matrix

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.LDT.Preliminaries LIDT.MIPStarRE.Quantum



/-! ## Pulled-apart measurements and observables -/

open MIPStarRE.QPBT.PauliKind





open MIPStarRE.QPBT.GlobalPairWitness



























/-! ## Swap conjugation -/

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    {epsilon delta : ℝ} {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
    (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S delta) (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (u : Fin P.m -> _root_.MIPStarRE.QPBT.PauliScalar P) (a : _root_.MIPStarRE.QPBT.PauliScalar P) :
    _root_.MIPStarRE.QPBT.conjBy (_root_.MIPStarRE.QPBT.swapUnitary w side) (_root_.MIPStarRE.QPBT.tildeM w side W (_root_.MIPStarRE.QPBT.indicatorVec u) a) =
      _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace side))
        (_root_.MIPStarRE.QPBT.bracketOp (_root_.MIPStarRE.QPBT.pauliProj W) (fun h => _root_.MIPStarRE.QPBT.lowDegreeEnc h u) a) := by
  classical
  have hM : _root_.MIPStarRE.QPBT.tildeM w side W (_root_.MIPStarRE.QPBT.indicatorVec u) a =
      ∑ pair : _root_.MIPStarRE.QPBT.PolyPair P, _root_.MIPStarRE.QPBT.heteroKron ((w.Smeas side).effect pair)
        (_root_.MIPStarRE.QPBT.tauDotProj W (_root_.MIPStarRE.QPBT.indicatorVec u)
          (dotProduct (_root_.MIPStarRE.QPBT.decodeFq (W.selectPoly pair)) (_root_.MIPStarRE.QPBT.indicatorVec u) - a)) := by
    simp only [_root_.MIPStarRE.QPBT.tildeM, _root_.MIPStarRE.QPBT.GlobalPairWitness.marginalPoly, _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
    simp_rw [_root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_left]
    rw [← Finset.sum_fiberwise Finset.univ W.selectPoly
      (fun pair => _root_.MIPStarRE.QPBT.heteroKron ((w.Smeas side).effect pair)
        (_root_.MIPStarRE.QPBT.tauDotProj W (_root_.MIPStarRE.QPBT.indicatorVec u)
          (dotProduct (_root_.MIPStarRE.QPBT.decodeFq (W.selectPoly pair)) (_root_.MIPStarRE.QPBT.indicatorVec u) - a)))]
    apply Finset.sum_congr rfl
    intro g _
    apply Finset.sum_congr rfl
    intro pair hpair
    rw [(Finset.mem_filter.mp hpair).2]
  rw [hM, swapUnitary_conj_controlled]
  simp_rw [swapPauli_conj_tauDotProj]
  have hcancel (b : _root_.MIPStarRE.QPBT.PauliScalar P) : b - a + b = a := by
    letI : CharP (_root_.MIPStarRE.QPBT.PauliScalar P) 2 :=
      (Algebra.charP_iff (ZMod 2) (_root_.MIPStarRE.QPBT.PauliScalar P) 2).mp (ZMod.charP 2)
    rw [sub_eq_add_neg, CharTwo.neg_eq, add_right_comm, CharTwo.add_self_eq_zero, zero_add]
  simp_rw [hcancel]
  rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_left, (w.Smeas side).sum_eq_one]
  congr 1
  simp only [_root_.MIPStarRE.QPBT.tauDotProj, _root_.MIPStarRE.QPBT.bracketOp, _root_.MIPStarRE.QPBT.lowDegreeEnc_eq_dotProduct]
