-- Prove2me | solution 1 for MIPStarRE.QPBT.MagicSquareRigidity.conjTranspose_mul_le_one_conjIsometry
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:16:53.893564+00:00
-- url     : https://prove2.me/submissions/941021a7-475b-4a31-b28a-a0ebf4b94714

-- Generated proof for MIPStarRE.QPBT.MagicSquareRigidity.conjTranspose_mul_le_one_conjIsometry.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Dilation
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_isometryMatrix_conjTranspose_mul

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
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



/-- Conjugation by an isometry is conjugation by its matrix. -/
theorem conjIsometry_eq {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι') (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.conjIsometry φ M = _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ * M * (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)ᴴ := rfl















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



































/-! ## Kronecker algebra of placed operators

The mixed-product rule `heteroKron_mul`, the identity `heteroKron_one_one` and
the additive and difference identities are the shared tensor-placement lemmas of
`MIPStarRE/QPBT/Games/Defs.lean`; the identities below extend them with the
finite-sum and scalar facts used by the transfer step. -/









/-! ## Matrices of isometries -/



/-- The range projection `V Vᴴ` of a matrix isometry is at most the identity. -/
theorem isometryMatrix_mul_conjTranspose_le_one {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι') :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ * (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)ᴴ ≤ 1 := by
  have hproj : _root_.LIDT.MIPStarRE.Quantum.IsProj (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ * (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)ᴴ) := by
    constructor
    · change (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ * (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)ᴴ) *
        (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ * (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)ᴴ) = _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ * (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)ᴴ
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)ᴴ,
        _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix_conjTranspose_mul, Matrix.one_mul]
    · change star (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ * (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)ᴴ) =
        _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ * (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)ᴴ
      simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul]
  exact sub_nonneg.mp hproj.one_sub.nonneg

















/-! ## The ground projection -/





















/-! ## Leakage out of the ground slice is bounded by the intertwining defect -/





end

end MIPStarRE.QPBT.MagicSquareRigidity

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



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



/-! ## Contractions and their action on states -/



































/-! ## Kronecker algebra of placed operators

The mixed-product rule `heteroKron_mul`, the identity `heteroKron_one_one` and
the additive and difference identities are the shared tensor-placement lemmas of
`MIPStarRE/QPBT/Games/Defs.lean`; the identities below extend them with the
finite-sum and scalar facts used by the transfer step. -/









/-! ## Matrices of isometries -/

theorem solution {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι') {A : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hA : Aᴴ * A ≤ 1) :
    (_root_.MIPStarRE.QPBT.conjIsometry φ A)ᴴ * _root_.MIPStarRE.QPBT.conjIsometry φ A ≤ 1 := by
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.conjIsometry_eq]
  have h1 : (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ * A * (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)ᴴ)ᴴ *
      (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ * A * (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)ᴴ) =
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ * (Aᴴ * A) * (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)ᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)ᴴ (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ),
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix_conjTranspose_mul, Matrix.one_mul]
  rw [h1]
  calc _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ * (Aᴴ * A) * (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)ᴴ ≤
        _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ * (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) * (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)ᴴ := by
        rw [Matrix.le_iff]
        have h := (Matrix.le_iff.mp hA).mul_mul_conjTranspose_same (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)
        convert h using 1
        simp [Matrix.mul_sub, Matrix.sub_mul]
    _ = _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ * (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)ᴴ := by rw [Matrix.mul_one]
    _ ≤ 1 := _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix_mul_conjTranspose_le_one φ
