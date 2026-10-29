-- Prove2me | solution 1 for MIPStarRE.QPBT.tildeM_consistencyDefect_le_pulling_eval_add
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:18:01.40808+00:00
-- url     : https://prove2.me/submissions/7aaee3ee-6219-4c17-9bc6-bb3173d7be38

-- Generated proof for MIPStarRE.QPBT.tildeM_consistencyDefect_le_pulling_eval_add.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_Decoding
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Extraction_Defs
import Definitions.Def_QPBT_QPBT_Extraction_Observables
import Definitions.Def_QPBT_QPBT_Extraction_PullingMeasurement
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_SandwichProduct_point_codeword_defect_le_avg_evaluated_add
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_stateQForm_reindexState
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_postprocess_le
import Theorems.Thm_MIPStarRE_QPBT_polyFunc_eval_collision_le
import Theorems.Thm_MIPStarRE_QPBT_pullingMeas_postprocess_effect

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Extraction/PolynomialCollision.lean. -/
/-!
# Real polynomial collision bounds

The existing Schwartz–Zippel estimate for bounded polynomial representatives
is expressed as a nonnegative rational cardinality ratio. This module converts
it to the real uniform average used by the sandwich support comparison and
specializes it to the polynomial outcomes of the Pauli basis test.

## References

* `references/qpbt-paper/04_preliminaries.tex`, `lem:schwartz-zippel`.
* Blueprint `lem:schwartz-zippel-individual` and the collision calculation
  preceding `eq:qld-nonencoding-mass` in `sec:separating`.
* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1483-1492`,
  the consistency calculation in `lem:qld-construct-the-paulis` whose decoder
  substitution requires the blueprint's nonencoding-mass estimate.
* `docs/paper-gaps/qpbt_decoding-identity.tex`, for that substitution's scope.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.LDT.Preliminaries



/-- The collision hypothesis for the sandwich support comparison on QPBT
polynomial outcomes, with the field cardinality written as `P.q`.

This specializes `polyFunc_eval_collision_le` to the fixed field model and
`evalPoly`; it adds no assumptions to the admissible parameter domain of
blueprint `eq:qld-nonencoding-mass`. -/
theorem poly_eval_collision_le {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    (first second : _root_.MIPStarRE.QPBT.Poly P) (hne : first ≠ second) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
      (fun point => if _root_.MIPStarRE.QPBT.evalPoly first point = _root_.MIPStarRE.QPBT.evalPoly second point then (1 : ℝ) else 0) ≤
        (P.m * P.d : ℝ) / P.q := by
  have hcard : Fintype.card (_root_.MIPStarRE.QPBT.PauliScalar P) = P.q :=
    @_root_.LIDT.MIPStarRE.LDT.FieldModel.card P.q P.model.toFieldModel
  unfold _root_.MIPStarRE.QPBT.evalPoly
  conv_rhs => rw [← hcard]
  exact _root_.MIPStarRE.QPBT.polyFunc_eval_collision_le first second hne

end MIPStarRE.QPBT

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

/- Source helpers from QPBT/Games/DistanceTheorems/TensorSupport.lean. -/
/-!
# Tensor-placement and marginal identities

This module collects tensor-placement, marginal, and finite-fiber identities
used in data processing and the commutator estimate.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:397-461`
- Blueprint `fact:triangle-for-simeq`, `fact:data-processing`, and
  `lem:commutation-analysis`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective





/-- Formalization-only auxiliary lemma for Fact 4.26: products of left and right
placements evaluate as a Kronecker product. -/
theorem placed_product_stateQForm_eq {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron A 1 * _root_.MIPStarRE.QPBT.heteroKron 1 B) =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron A B) := by
  congr 1
  exact _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor A B































end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Observables/ExpandedPlacement.lean. -/
/-!
# Placing operators on the expanded state

The four register placements of `def:symmetric-equivalents` put an operator of
one player's expanded local space on one of the register pairs `AA'`, `BA''`,
`BB'` and `AB''` of the expanded state `psiHat`.  This module records how such
a placement acts on `psiHat`: after the shuffle of `eq:def-psihat` the placed
operator is a threefold tensor product, so a factorized operator whose Pauli
factor is an isometry has the same state-dependent norm as its strategy factor
placed on the original state.  No symmetry between the two players is used;
each of the four placements is treated explicitly.

## References

The declarations support `def:symmetric-equivalents` and `lem:qld-comm-cons`
in `blueprint/src/chapter/ch14_qpbt_observables.tex:1002-1031` and
`blueprint/src/chapter/ch14_qpbt_observables.tex:1139-1178`.  Their paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-505`.
-/

@[expose] public section

-- The unshuffled six-register index type of `eq:def-psihat` is a fourfold
-- iterated product; instance search for its `Fintype` and `DecidableEq`
-- structure needs a larger budget than the default.
set_option synthInstance.maxSize 400

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Coordinate tensors -/











namespace ProjectiveSetting





variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-! ## The strategy factor of a placement -/





/-! ## The action of a placement on the expanded state -/

/-- The expanded state is the shuffle of the coordinate tensor of the strategy
state with the two EPR ancillas. This is `eq:def-psihat`, paper
`14_analysis_of_the_pauli_basis_test.tex:367-372`, blueprint
`ch14_qpbt_observables.tex:895-918`. -/
theorem psiHat_eq_reindexState (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) :
    S.psiHat = _root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB)
      (_root_.MIPStarRE.QPBT.vecTensor (_root_.MIPStarRE.QPBT.vecTensor S.toStrategy.ψ (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)))
        (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))) := rfl

/-- The expanded strategy state is normalized. -/
theorem psiHat_norm (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) : ‖S.psiHat‖ = 1 := by
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.psiHat_eq_reindexState, _root_.MIPStarRE.QPBT.reindexState_norm_eq, _root_.MIPStarRE.QPBT.vecTensor_norm_eq,
    _root_.MIPStarRE.QPBT.vecTensor_norm_eq, S.toStrategy.ψ_norm, _root_.MIPStarRE.QPBT.eprState_norm]
  norm_num

/-! ## Opposite-placement bipartitions -/













/-! ## The four placements -/



























end ProjectiveSetting

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/WinImplications/FactorTransport.lean. -/
/-!
# Transport of the winning implications to the interchanged tensor factor

This module carries the state-dependent functionals of the winning
implications across the interchange of the two tensor factors.  The
factor-interchanged conclusions of `lem:qld-win-implications` are stated with
the second player on the left factor and the reindexed state
`ProjectiveSetting.swappedState`; the lemmas here identify those quantities
with the ones proved on `S.toStrategy.psi`, so that the second pass of
`lem:qld-win-implications-obs` can reuse the first pass verbatim on the
interchanged side.

## References

The declarations support the trailing clause of `lem:qld-win-implications` and
the second assertion of `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794` and
`blueprint/src/chapter/ch14_qpbt_observables.tex:701-703`.  Their paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:227,309-362`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Reindexing the identity and the strategy state -/





/-! ## Transport of the consistency defect -/



/-- Reindexing an operator along an equivalence is multiplicative.
Formalization-only support for the interchanged conclusions of
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:701-703`. -/
theorem reindexOp_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (M N : _root_.LIDT.MIPStarRE.Quantum.Op κ) :
    _root_.MIPStarRE.QPBT.reindexOp e (M * N) = _root_.MIPStarRE.QPBT.reindexOp e M * _root_.MIPStarRE.QPBT.reindexOp e N := by
  ext i j
  change (M * N) (e i) (e j) = ∑ k : ι, M (e i) (e k) * N (e k) (e j)
  rw [Matrix.mul_apply, ← e.sum_comp (fun l : κ => M (e i) l * N l (e j))]





/-! ## Transport of the phase-signed operator distance -/





end WinImplications

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Extraction/PullingMeasurement.lean. -/
/-!
# Polynomial outcomes in the pulling argument

The joint measurement of a polynomial marginal and an ideal Pauli register
returns the difference between the polynomial and the encoding of the register.
Decoding this difference gives exactly the pulled-apart measurement. Polynomial
collision estimates apply to these representatives without an encoding-support
restriction on the original marginal.

## References

- Blueprint `lem:qld-construct-the-paulis`, Item 2.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1530-1605`,
  `eq:qld-pulling-11`, `eq:qld-pulling-12`, and the following symmetry argument.
- `docs/paper-gaps/qpbt_decoding-identity.tex`; only decoder linearity and its
  left-inverse identity are used here.
- Issue Dengnifer/MIPStarRE-QPBT-bak#123 tracks the `eq:qld-pulling-cons` extraction obligation;
  these
  auxiliary results do not assert it. This module was originally filed
  under issue Dengnifer/MIPStarRE-QPBT-bak#520, now closed.
- The collision estimate compares unequal difference polynomials under uniform
  evaluation.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus
open WinImplications

noncomputable section

open scoped Classical













/-- The coordinate change to two extraction blocks preserves the consistency
defect, including every off-diagonal outcome and the question distribution. -/
private theorem consistencyDefect_placeSide_eq {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon : ℝ}
    {X A : Type*} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A]
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon) (mu : _root_.LIDT.MIPStarRE.LDT.Distribution X)
    (left : X → A → _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.ExtractionBlock P (S.LocalSpace .alice)))
    (right : X → A → _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.ExtractionBlock P (S.LocalSpace .bob))) :
    _root_.MIPStarRE.QPBT.consistencyDefect mu (fun x a => S.placeSide .alice (left x a))
        (fun x a => S.placeSide .bob (right x a)) S.psiHat =
      _root_.MIPStarRE.QPBT.consistencyDefect mu (fun x a => _root_.MIPStarRE.QPBT.heteroKron (left x a) 1)
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 (right x a))
        (_root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB) S.psiHat) := by
  unfold _root_.MIPStarRE.QPBT.consistencyDefect
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro x
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : a = b
  · simp only [hab, if_true]
  · simp only [if_neg hab, _root_.MIPStarRE.QPBT.DistanceCalculus.consistency_term_eq_stateQForm]
    rw [_root_.MIPStarRE.QPBT.WinImplications.stateQForm_reindexState, _root_.MIPStarRE.QPBT.WinImplications.reindexOp_mul]
    rfl

/-- Polynomial collision and deterministic decoding, before choosing a
register placement. This separates the finite probability calculation from
the six-register coordinate identities. -/
private theorem polynomial_decoding_defect_le_evaluated_add {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.Poly P) I) (B : _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.Poly P) J)
    (psi : EuclideanSpace ℂ (I × J)) (hpsi : ‖psi‖ = 1) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliRegister P))
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron
          ((A.postprocess (fun g => dotProduct (_root_.MIPStarRE.QPBT.decodeFq g) u)).effect a) 1)
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron 1
          ((B.postprocess (fun g => dotProduct (_root_.MIPStarRE.QPBT.decodeFq g) u)).effect a)) psi ≤
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron ((A.postprocess (fun g => _root_.MIPStarRE.QPBT.evalPoly g u)).effect a) 1)
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron 1 ((B.postprocess (fun g => _root_.MIPStarRE.QPBT.evalPoly g u)).effect a)) psi +
          (P.m * P.d : ℝ) / P.q := by
  have hcollision := _root_.MIPStarRE.QPBT.SandwichProduct.point_codeword_defect_le_avg_evaluated_add
    A B psi _root_.MIPStarRE.QPBT.evalPoly ((P.m * P.d : ℝ) / P.q) hpsi
    (by positivity) (fun g h hne => _root_.MIPStarRE.QPBT.poly_eval_collision_le g h hne)
  have hpost (u : _root_.MIPStarRE.QPBT.PauliRegister P) := _root_.MIPStarRE.QPBT.consistencyDefect_postprocess_le
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit) (fun _ => A) (fun _ => B) psi
    (fun g => dotProduct (_root_.MIPStarRE.QPBT.decodeFq g) u)
  simp only [_root_.MIPStarRE.QPBT.consistencyDefect, _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const,
    _root_.MIPStarRE.QPBT.DistanceCalculus.consistency_term_eq_stateQForm, _root_.MIPStarRE.QPBT.DistanceCalculus.placed_product_stateQForm_eq] at hpost
  simp only [_root_.MIPStarRE.QPBT.consistencyDefect, _root_.MIPStarRE.QPBT.DistanceCalculus.consistency_term_eq_stateQForm,
    _root_.MIPStarRE.QPBT.DistanceCalculus.placed_product_stateQForm_eq]
  exact (_root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ hpost).trans
    ((_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const _).le.trans hcollision)





end

end MIPStarRE.QPBT

/-!
# Polynomial outcomes in the pulling argument

The joint measurement of a polynomial marginal and an ideal Pauli register
returns the difference between the polynomial and the encoding of the register.
Decoding this difference gives exactly the pulled-apart measurement. Polynomial
collision estimates apply to these representatives without an encoding-support
restriction on the original marginal.

## References

- Blueprint `lem:qld-construct-the-paulis`, Item 2.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1530-1605`,
  `eq:qld-pulling-11`, `eq:qld-pulling-12`, and the following symmetry argument.
- `docs/paper-gaps/qpbt_decoding-identity.tex`; only decoder linearity and its
  left-inverse identity are used here.
- Issue Dengnifer/MIPStarRE-QPBT-bak#123 tracks the `eq:qld-pulling-cons` extraction obligation;
  these
  auxiliary results do not assert it. This module was originally filed
  under issue Dengnifer/MIPStarRE-QPBT-bak#520, now closed.
- The collision estimate compares unequal difference polynomials under uniform
  evaluation.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open MIPStarRE.QPBT.WinImplications



open scoped Classical

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    {epsilon deltaG : ℝ} {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
    (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliRegister P))
        (fun u a => S.placeSide .alice (_root_.MIPStarRE.QPBT.tildeM w .alice W u a))
        (fun u a => S.placeSide .bob (_root_.MIPStarRE.QPBT.tildeM w .bob W u a)) S.psiHat ≤
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
        (fun u a => S.placeSide .alice
          (((_root_.MIPStarRE.QPBT.pullingMeas w .alice W).postprocess (fun g => _root_.MIPStarRE.QPBT.evalPoly g u)).effect a))
        (fun u a => S.placeSide .bob
          (((_root_.MIPStarRE.QPBT.pullingMeas w .bob W).postprocess (fun g => _root_.MIPStarRE.QPBT.evalPoly g u)).effect a))
        S.psiHat + (P.m * P.d : ℝ) / P.q := by
  classical
  rw [consistencyDefect_placeSide_eq, consistencyDefect_placeSide_eq]
  have h := polynomial_decoding_defect_le_evaluated_add
      (_root_.MIPStarRE.QPBT.pullingMeas w .alice W) (_root_.MIPStarRE.QPBT.pullingMeas w .bob W)
      (_root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB) S.psiHat)
      (by rw [_root_.MIPStarRE.QPBT.reindexState_norm_eq, S.psiHat_norm])
  have hAlice :
      (fun u a => _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.tildeM w .alice W u a)
        (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.ExtractionBlock P S.toStrategy.ιB))) =
        fun u a => _root_.MIPStarRE.QPBT.heteroKron
          (((_root_.MIPStarRE.QPBT.pullingMeas w .alice W).postprocess (fun g => dotProduct (_root_.MIPStarRE.QPBT.decodeFq g) u)).effect a)
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.ExtractionBlock P S.toStrategy.ιB)) := by
    funext u a
    rw [_root_.MIPStarRE.QPBT.pullingMeas_postprocess_effect]
  have hBob :
      (fun u a => _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.ExtractionBlock P S.toStrategy.ιA))
        (_root_.MIPStarRE.QPBT.tildeM w .bob W u a)) =
        fun u a => _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.ExtractionBlock P S.toStrategy.ιA))
          (((_root_.MIPStarRE.QPBT.pullingMeas w .bob W).postprocess (fun g => dotProduct (_root_.MIPStarRE.QPBT.decodeFq g) u)).effect a) := by
    funext u a
    rw [_root_.MIPStarRE.QPBT.pullingMeas_postprocess_effect]
  rw [hAlice, hBob]
  exact h
