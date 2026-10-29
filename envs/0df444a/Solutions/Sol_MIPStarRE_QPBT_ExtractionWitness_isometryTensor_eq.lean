-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtractionWitness.isometryTensor_eq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:49:51.271372+00:00
-- url     : https://prove2.me/submissions/60d610ec-9894-4919-9c16-e4166fedbe96

-- Generated proof for MIPStarRE.QPBT.ExtractionWitness.isometryTensor_eq.
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
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Extraction_Defs
import Definitions.Def_QPBT_QPBT_Extraction_Observables
import Definitions.Def_QPBT_QPBT_Extraction_Unitary
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Dilation
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Definitions.Def_QPBT_QPBT_Test_SoundnessDefs
import Definitions.Def_QPBT_QPBT_Test_Soundness_Ancilla
import Definitions.Def_QPBT_QPBT_Test_Soundness_StateTransfer
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
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/Dilation.lean. -/
/-!
# A simultaneous projective dilation of a Magic Square strategy

The rigidity argument for the Magic Square game is stated for an arbitrary
tensor-product strategy, whose measurements are positive operator valued
measures.  The self-testing argument, however, manipulates projections.  This
file removes that discrepancy by dilating an arbitrary strategy to a projective
one without changing any observable quantity.

Each local Hilbert space `ℂ^ι` is enlarged by one auxiliary register whose
basis is indexed by `Option MsAnswer`, and the original space is identified with
the *ground slice* `ℂ^ι ⊗ |⊥⟩`.  The one-measurement Naimark lemma of the low
individual degree development supplies, for every question separately, a family
of projections on the enlarged space whose compression to the ground slice
returns the original effects; the ancilla is the same for all questions, so the
identification of `ℂ^ι` with the ground slice is a single isometry serving every
question at once.  Folding the deficiency `1 - ∑_a P_a` into one distinguished
answer turns the dilated family into a complete projective measurement without
disturbing the compression, because the original effects already sum to the
identity.

Since the dilated state is the image of the original state under the two ground
embeddings, every Born probability, and hence the game value and all the
rejection, malformed-answer, cell-consistency and parity masses of the
value-to-parity layer, is unchanged.  Conversely, the local isometries produced
by a rigidity argument applied to the dilated strategy compose with the ground
embeddings to give local isometries of the original strategy, and the
state-dependent norms occurring in the conclusion of `thm:ms-rigidity` transfer
along that composition.

## References

The rigidity statement supported here is blueprint
`thm:ms-rigidity`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`,
proved in Coladangelo--Stark, Theorem 6.9.  The dilation reuses the
one-measurement Naimark lemma of
`references/ldt-paper/orthonormalization.tex:121-159`, formalized as
`MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimark`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

noncomputable section

/-! ## Orthogonality inside a subnormalized family of projections -/







/-! ## The ground slice of an enlarged local space -/



























/-! ## The dilated projective measurement -/

























/-! ## The dilated state -/













/-! ## The dilated Magic Square strategy -/













/-! ## Preservation of the value-to-parity layer -/



































/-! ## Composition of the dilation with later local isometries -/





/-- The matrix of an isometry acts on vectors as the isometry does. -/
theorem isometryMatrix_mulVec {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι') (x : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ *ᵥ WithLp.ofLp x = WithLp.ofLp (φ x) := by
  have h : Matrix.toEuclideanLin (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ) = φ.toLinearMap :=
    Matrix.toEuclideanLin.apply_symm_apply φ.toLinearMap
  have h' : Matrix.toEuclideanLin (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ) x = φ x := by rw [h]; rfl
  simpa using congrArg WithLp.ofLp h'

/-- The columns of the matrix of an isometry are the images of the basis
vectors. -/
theorem isometryMatrix_apply {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι') (k : ι') (i : ι) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ k i =
      φ ((EuclideanSpace.equiv ι ℂ).symm (Pi.single i 1)) k := by
  have h := congrFun (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix_mulVec φ
    ((EuclideanSpace.equiv ι ℂ).symm (Pi.single i 1))) k
  rw [← h]
  simp [Matrix.mulVec, dotProduct, EuclideanSpace.equiv, eq_comm]





/-- The two-sided isometry image of a bipartite state, written through the
Kronecker product of the two isometry matrices. -/
theorem isometryTensor_apply_eq {ιA ιB κA κB : Type}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (φA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (p : κA × κB) :
    _root_.MIPStarRE.QPBT.isometryTensor φA φB ψ p =
      ∑ q : ιA × ιB,
        Matrix.kronecker (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φA) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φB) p q * ψ q := by
  simp [_root_.MIPStarRE.QPBT.isometryTensor, Matrix.kronecker, Fintype.sum_prod_type, _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix_apply,
    EuclideanSpace.equiv, mul_assoc]





/-! ## Transfer of state-dependent bounds -/

















end

end MIPStarRE.QPBT.MagicSquareRigidity

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/GroundSlice.lean. -/
/-!
# Contractions, isometries and the ground slice of the dilation

Support for the transfer step of `thm:ms-rigidity` (blueprint
`thm:ms-rigidity`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`):
the calculus needed to compare the dilated projective strategy of
`Rigidity/Dilation.lean` with the original strategy on states.

* Contractions: operators `K` with `Kᴴ K ≤ 1` do not increase norms; effects,
  observables of binary measurements, orthogonal projections, tensor placements,
  products and isometry conjugates are contractions.
* Matrices of isometries: `Vᴴ V = 1`, the two-sided isometry image of a state
  preserves norms, and a conjugated local operator acts on the transported state
  as the original operator acts on the original state.
* The ground projection `Π` of an enlarged local space: an orthogonal projection
  fixing the dilated state, with `Π P Π` the inflation of the compression of `P`.
* Leakage: the part `(1 - Π) P ψ'` of a dilated operator that leaves the ground
  slice is bounded by the intertwining defect of `P ⊗ 1` against any `1 ⊗ Q`,
  because `(1 - Π) ⊗ 1` annihilates `(1 ⊗ Q) ψ'`.  This is the estimate that
  replaces the `≈_δ`-preservation which Naimark dilation lacks in general
  (`references/ldt-paper/orthonormalization.tex:82-101`, blueprint
  `ex:easy-but-long`).

## References

blueprint `thm:ms-rigidity`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

/-! ## Contractions and their action on states -/











/-- Applying a product of rectangular matrices is successive application. -/
theorem toEuclideanLin_mul_apply {m n o : Type*} [Fintype n] [Fintype o]
    [DecidableEq n] [DecidableEq o]
    (A : Matrix m n ℂ) (B : Matrix n o ℂ) (v : EuclideanSpace ℂ o) :
    Matrix.toEuclideanLin (A * B) v =
      Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v) := by
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]























/-! ## Kronecker algebra of placed operators

The mixed-product rule `heteroKron_mul`, the identity `heteroKron_one_one` and
the additive and difference identities are the shared tensor-placement lemmas of
`MIPStarRE/QPBT/Games/Defs.lean`; the identities below extend them with the
finite-sum and scalar facts used by the transfer step. -/









/-! ## Matrices of isometries -/











/-- The two-sided isometry image of a state is the action of the Kronecker
product of the two isometry matrices. -/
theorem isometryTensor_eq_toEuclideanLin {ιA ιB κA κB : Type}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (φA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    _root_.MIPStarRE.QPBT.isometryTensor φA φB ψ =
      Matrix.toEuclideanLin
        (Matrix.kronecker (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φA) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φB)) ψ := by
  ext p
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryTensor_apply_eq]
  simp [Matrix.toEuclideanLin, Matrix.mulVec, dotProduct]









/-! ## The ground projection -/





















/-! ## Leakage out of the ground slice is bounded by the intertwining defect -/





end

end MIPStarRE.QPBT.MagicSquareRigidity

/- Source helpers from QPBT/Test/Soundness/Ancilla.lean. -/
/-!
# Ancilla isometries for Pauli soundness

Adjoining a unit vector and applying a unitary gives the local isometry in the
final soundness argument. The exact intertwining identity below supplies the
algebraic hypothesis of the range-projection estimates. These results are
recorded in blueprint `thm:pauli-ancilla-intertwining-support`.

## References

Formalization support for blueprint `thm:pauli`, specifically the isometry at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1864-1875`.
The registers are ordered as `AA'A''`, with the first two factors grouped.
These constructions do not assume or construct a global polynomial measurement.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum MagicSquareRigidity

noncomputable section

variable {ι κ ν : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]



/-- The columns of the ancilla isometry are the original basis vectors
tensored with the fixed ancilla. -/
theorem ancillaBlockIsometry_matrix_apply
    (eta : EuclideanSpace ℂ (κ × ν)) (heta : ‖eta‖ = 1)
    (p : (ι × κ) × ν) (i : ι) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix (_root_.MIPStarRE.QPBT.ancillaBlockIsometry (ι := ι) eta heta) p i =
      if p.1.1 = i then eta (p.1.2, p.2) else 0 := by
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix_apply]
  simp [_root_.MIPStarRE.QPBT.ancillaBlockIsometry, _root_.MIPStarRE.QPBT.reindexState, _root_.MIPStarRE.QPBT.vecTensor, eq_comm]





/-- The matrix of the extraction isometry is the unitary times the ancilla
embedding, with no range projection omitted. -/
theorem unitaryAncillaIsometry_matrix
    (eta : EuclideanSpace ℂ (κ × ν)) (heta : ‖eta‖ = 1)
    (U : _root_.LIDT.MIPStarRE.Quantum.Op ((ι × κ) × ν)) (hU : Uᴴ * U = 1) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix (_root_.MIPStarRE.QPBT.unitaryAncillaIsometry eta heta U hU) =
      U * _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix (_root_.MIPStarRE.QPBT.ancillaBlockIsometry (ι := ι) eta heta) := by
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro psi
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.toEuclideanLin_mul_apply]
  simp only [_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix, Matrix.toEuclideanLin.apply_symm_apply]
  rfl



end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/Soundness/StateTransfer.lean. -/
/-!
# State transfer from supplied extraction data

The extraction witness uses six registers, while the test conclusion groups
each player's first two registers into the auxiliary space. Adjoining the local
EPR states and applying the supplied swap unitaries gives the test isometries.
The squared state error is unchanged by this identification.

## References

Formalization support for blueprint `thm:pauli` and
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1864-1875`.
This module transports supplied data without invoking either existence theorem.
The companion `OperatorTransfer` module completes both operator comparisons.
The source-facing obligations are tracked by issues #529 and #586 and
`docs/paper-gaps/qpbt_extraction-transfer.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum MagicSquareRigidity

noncomputable section

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaG delta : ℝ}
  {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon} {w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG}



open Classical in
/-- The two ancilla embeddings produce exactly the expanded strategy state,
after grouping the local registers as `(AA')A''` and `(BB')B''`.
This identity is part of blueprint `thm:pauli-extraction-isometry-construction-support`. -/
theorem isometryTensor_ancilla_eq_psiHat (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon) :
    _root_.MIPStarRE.QPBT.isometryTensor
        (_root_.MIPStarRE.QPBT.ancillaBlockIsometry (ι := S.toStrategy.ιA)
          (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)) (_root_.MIPStarRE.QPBT.eprState_norm _))
        (_root_.MIPStarRE.QPBT.ancillaBlockIsometry (ι := S.toStrategy.ιB)
          (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)) (_root_.MIPStarRE.QPBT.eprState_norm _)) S.toStrategy.ψ =
      _root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB) S.psiHat := by
  ext p
  simp [_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryTensor_apply_eq, _root_.MIPStarRE.QPBT.ancillaBlockIsometry_matrix_apply, Matrix.kronecker,
    Fintype.sum_prod_type, _root_.MIPStarRE.QPBT.ProjectiveSetting.psiHat, _root_.MIPStarRE.QPBT.reindexState, _root_.MIPStarRE.QPBT.vecTensor,
    _root_.MIPStarRE.QPBT.sixRegExtractionEquiv, _root_.MIPStarRE.QPBT.sixRegShuffle, mul_comm, mul_left_comm]











end

end MIPStarRE.QPBT

/-!
# State transfer from supplied extraction data

The extraction witness uses six registers, while the test conclusion groups
each player's first two registers into the auxiliary space. Adjoining the local
EPR states and applying the supplied swap unitaries gives the test isometries.
The squared state error is unchanged by this identification.

## References

Formalization support for blueprint `thm:pauli` and
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1864-1875`.
This module transports supplied data without invoking either existence theorem.
The companion `OperatorTransfer` module completes both operator comparisons.
The source-facing obligations are tracked by issues #529 and #586 and
`docs/paper-gaps/qpbt_extraction-transfer.tex`.
-/



open scoped BigOperators Matrix

open MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.MagicSquareRigidity



variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaG delta : ℝ}
  {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon} {w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG}

open Classical in

theorem solution (v : _root_.MIPStarRE.QPBT.ExtractionWitness S w delta) :
    _root_.MIPStarRE.QPBT.isometryTensor v.toPauliSoundnessWitness.φA v.toPauliSoundnessWitness.φB
        S.toStrategy.ψ =
      _root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
        (S.applyBoth (_root_.MIPStarRE.QPBT.swapUnitary w .alice) (_root_.MIPStarRE.QPBT.swapUnitary w .bob) S.psiHat) := by
  have haction := _root_.MIPStarRE.QPBT.isometryTensor_ancilla_eq_psiHat S
  change _root_.MIPStarRE.QPBT.isometryTensor
    (_root_.MIPStarRE.QPBT.unitaryAncillaIsometry (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)) (_root_.MIPStarRE.QPBT.eprState_norm _)
      (_root_.MIPStarRE.QPBT.swapUnitary w .alice) (v.swap_left_unitary .alice))
    (_root_.MIPStarRE.QPBT.unitaryAncillaIsometry (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)) (_root_.MIPStarRE.QPBT.eprState_norm _)
      (_root_.MIPStarRE.QPBT.swapUnitary w .bob) (v.swap_left_unitary .bob)) S.toStrategy.ψ = _
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryTensor_eq_toEuclideanLin]
  have hA := _root_.MIPStarRE.QPBT.unitaryAncillaIsometry_matrix (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))
    (_root_.MIPStarRE.QPBT.eprState_norm _) (_root_.MIPStarRE.QPBT.swapUnitary w .alice) (v.swap_left_unitary .alice)
  have hB := _root_.MIPStarRE.QPBT.unitaryAncillaIsometry_matrix (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))
    (_root_.MIPStarRE.QPBT.eprState_norm _) (_root_.MIPStarRE.QPBT.swapUnitary w .bob) (v.swap_left_unitary .bob)
  rw [hA, hB]
  rw [Matrix.kronecker, Matrix.mul_kronecker_mul, _root_.MIPStarRE.QPBT.MagicSquareRigidity.toEuclideanLin_mul_apply]
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryTensor_eq_toEuclideanLin] at haction
  erw [haction]
  ext p
  symm
  change ((Matrix.kronecker (_root_.MIPStarRE.QPBT.swapUnitary w .alice) (_root_.MIPStarRE.QPBT.swapUnitary w .bob)).submatrix
      (_root_.MIPStarRE.QPBT.sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
      (_root_.MIPStarRE.QPBT.sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB) *ᵥ
        (fun i => S.psiHat i))
      ((_root_.MIPStarRE.QPBT.sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB).symm p) = _
  erw [Matrix.submatrix_mulVec_equiv]
  rfl
