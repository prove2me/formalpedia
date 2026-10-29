-- Prove2me | solution 1 for MIPStarRE.QPBT.directLdPointPair_consistencyDefect_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:13:59.576763+00:00
-- url     : https://prove2.me/submissions/8e917782-b03e-428f-b736-e0d7c12acf4f

-- Generated proof for MIPStarRE.QPBT.directLdPointPair_consistencyDefect_le.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_GameValue
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_BranchComparison
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Strategy
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_StrategyClasses
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_congr
import Theorems.Thm_MIPStarRE_QPBT_directLdBranchRejectionProbability_nonneg
import Theorems.Thm_MIPStarRE_QPBT_directLdRejectionProbability_eq_one_sub_value
import Theorems.Thm_MIPStarRE_QPBT_qBipartiteConsDefect_le_directRejectedMass
import Theorems.Thm_MIPStarRE_QPBT_strategyConsRel_consistencyDefect_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Distribution.IsProbability
end LIDT.MIPStarRE.LDT.Distribution.IsProbability
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace LIDT.MIPStarRE.Quantum.Measurement
end LIDT.MIPStarRE.Quantum.Measurement
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Geometry.lean. -/
/-!
# Geometry for the directly indexed low-degree game

This module defines the parameters, line carrier, and line-point distributions
for the directly indexed low-degree game.

## References

The line-point distributions originate in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-272`.
The directly indexed repair is documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum

noncomputable section









instance instNonemptyFinM_1 (D : _root_.MIPStarRE.QPBT.DirectLdParams) : Nonempty (Fin D.m) := ⟨D.firstIndex⟩



















/-! ## Finite direct-line carrier -/

















































end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/BranchComparison.lean. -/
/-!
# Branch comparison for the coordinate strategies of the direct low-degree game

Every branch of the low individual degree failure probability of a coordinate
strategy `directCoordinateProjStrat` is compared with the ordered type-pair
branch of the direct game asking the same questions.  An accepted direct
answer pair reads out to equal LDT answers: the line answer, rebased to the
LDT line and evaluated at the LDT base point, is the point answer, and the
zero-direction convention reads the constant value at the base point.  Hence
the LDT inconsistency mass at a question pair is at most the rejected direct
Born mass there.  The point-agreement and axis-line branches then compare
exactly after the coordinate reindexing of `directPointEquiv`; the diagonal
branches are treated in `Transport.DiagonalRecursion`.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:214-458`
- `references/ldt-paper/test_definition.tex:130-151`
- Blueprint `def:ld-question-distribution`, `lem:ld-aline-level`,
  `lem:ld-dline-level`, `lem:ld-question-typed-cl`, `lem:alnf`, `lem:dlnf`,
  `def:ld-win-predicate`, `rem:ld-win-zero-direction`, and `def:ld-meas`
- `MIPStarRE/LDT/Test/StrategyFailures.lean:18-130`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

noncomputable section



/-! ## Rejected Born mass at a fixed question pair -/





/-- The branch rejection probability of an ordered type pair is the uniform
average of the rejected Born mass at the canonical questions of the common
direct sample. -/
theorem directLdBranchRejectionProbability_eq_avgOver (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D)) (types : _root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.LdType) :
    _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S types =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace D)) fun sample =>
        _root_.MIPStarRE.QPBT.directRejectedMass D S
          (types.1, _root_.MIPStarRE.QPBT.directLdMap D types.1 sample)
          (types.2, _root_.MIPStarRE.QPBT.directLdMap D types.2 sample) :=
  rfl



/-! ## Accepted answer pairs read out consistently

An accepted answer pair of the direct game consists of well-formed answers
satisfying the line-versus-point clause or the consistency clause of
`def:ld-win-predicate`.  The readouts of `Transport.Questions` evaluate the
rebased line polynomial at the LDT base point, which is the direct point
at the canonical rebase parameter; the accepted clause forces this value to
be the point answer.  Zero directions use the constant readout at the base
point, where the universal clause of `rem:ld-win-zero-direction` gives the
value at parameter zero. -/















/-! ## Direct samples as products -/



/-! ## The point-agreement and axis-line branches -/



end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Upstream.lean. -/
/-!
# Public helpers for the upstream LIDT interface

These finite-sum and measurement lemmas support the QPBT without modifying its LIDT dependency.
The marginal-state construction and rank-zero argument adapt the private proofs in
`LionSR/MIPStarRE`, commit `f382c801026f53a9efc260fdee707cb35e0adb15`, module
`MIPStarRE.LDT.MakingMeasurementsProjective.LocalityPreservingRepair`.
The remaining lemmas are QPBT extensions of the upstream measurement and distribution APIs.
Their proofs use the public definitions and Mathlib finite-dimensional linear algebra.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder



namespace LIDT
namespace MIPStarRE.LDT



/-- A uniform average over a finite type is its normalized finite sum. -/
theorem avgOver_uniform_eq_inv_card_mul_sum {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] (f : α → ℝ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α) f = (Fintype.card α : ℝ)⁻¹ * ∑ a, f a := by
  unfold _root_.LIDT.MIPStarRE.LDT.avgOver _root_.LIDT.MIPStarRE.LDT.uniformDistribution _root_.LIDT.MIPStarRE.LDT.Distribution.uniformOnFinset
  simp only [Finset.mem_univ, ite_true, Finset.card_univ, one_div, Finset.mul_sum]


end MIPStarRE.LDT
end LIDT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/PointAgreement.lean. -/
/-!
# The point-agreement branch as a consistency estimate

The low-degree game asks both players a point question in one of its nine
ordered type branches and accepts only equal point answers.  This module reads
that branch as a quantitative consistency relation between the two point
readouts, first for the directly indexed game and then, through the correlated
seed-residue dilation, for the seed-indexed game.

The estimate is the third input, besides the two conclusions of the low
individual degree theorem, from which the global polynomial relation of
`lem:ld-soundness` is obtained after the seed-residue ancilla has been
compressed away: the compressed polynomial measurements are consistent with
the point measurements of the *opposite* player only, and the point-agreement
branch is what links the two point measurements to each other.

## Main results

* `directLdPointPair_consistencyDefect_le` bounds the point-readout
  consistency defect of a direct strategy of value at least `1 - ε` by
  `9 ε`, the loss being the uniform weight of one of the nine ordered type
  branches.
* `ldPointPair_consistencyDefect_le` is the same estimate for the
  seed-indexed game, obtained from the direct one because the point
  measurements of the dilated strategy act trivially on the correlated
  residue register.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:137-167`
* `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## The point-agreement branch of the directly indexed game -/

/-- On the point-agreement branch an accepted pair of answers has equal
simultaneous point readouts.  This is the tuple-valued form of
`directPointAnswerReadout_eq_of_win`. -/
private theorem directLdPointValuesOrZero_eq_of_win (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (p : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) (a b : _root_.MIPStarRE.QPBT.DirectLdAnswer D)
    (hwin : _root_.MIPStarRE.QPBT.directLdWinPredicate D (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D p)
      (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D p) a b = true) :
    _root_.MIPStarRE.QPBT.directLdPointValuesOrZero D a = _root_.MIPStarRE.QPBT.directLdPointValuesOrZero D b := by
  cases a with
  | pointVals u =>
      cases b with
      | pointVals v =>
          have huv : u = v := by
            simpa [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.directLdPointQuestionOf,
              _root_.MIPStarRE.QPBT.validDirectLdAnswer] using hwin
          subst huv
          rfl
      | alinePolys _ =>
          simp [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.directLdPointQuestionOf,
            _root_.MIPStarRE.QPBT.validDirectLdAnswer] at hwin
      | dlinePolys _ =>
          simp [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.directLdPointQuestionOf,
            _root_.MIPStarRE.QPBT.validDirectLdAnswer] at hwin
  | alinePolys _ =>
      simp [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.directLdPointQuestionOf,
        _root_.MIPStarRE.QPBT.validDirectLdAnswer] at hwin
  | dlinePolys _ =>
      simp [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.directLdPointQuestionOf,
        _root_.MIPStarRE.QPBT.validDirectLdAnswer] at hwin

/-- Postprocessing the associated projective measurement has the same effects
as postprocessing the original measurement. -/
private theorem projMeas_postprocess_outcome_eq
    {alpha beta iota : Type*} [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta] [Fintype iota] [DecidableEq iota]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement alpha iota)
    (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M) (f : alpha → beta)
    (b : beta) :
    (_root_.LIDT.MIPStarRE.LDT.ProjMeas.postprocess (_root_.MIPStarRE.QPBT.matrixMeasurementToLDTProjMeas M hM) f).outcome b =
      (M.postprocess f).effect b := by
  classical
  simp only [_root_.LIDT.MIPStarRE.LDT.ProjMeas.postprocess, _root_.LIDT.MIPStarRE.LDT.SubMeas.postprocess_outcome,
    _root_.MIPStarRE.QPBT.matrixMeasurementToLDTProjMeas_outcome,
    _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]

/-- The uniform average of the rejected mass at the canonical point questions
is the point-agreement branch rejection probability. -/
private theorem avgOver_directRejectedMass_point_eq (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D)) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
        (fun u => _root_.MIPStarRE.QPBT.directRejectedMass D S (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)
          (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)) =
      _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S (.point, .point) := by
  rw [_root_.MIPStarRE.QPBT.directLdBranchRejectionProbability_eq_avgOver]
  let f : (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) → ℝ := fun p =>
    _root_.MIPStarRE.QPBT.directRejectedMass D S (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D p)
      (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D p)
  calc _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)) f
      = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution ((Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) × Fin D.m))
          (fun pi => f pi.1) := (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_fst f).symm
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace D))
          (fun sample => f ((_root_.MIPStarRE.QPBT.directLdSpaceSplitEquiv D sample).1).1) :=
        (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv_fst (_root_.MIPStarRE.QPBT.directLdSpaceSplitEquiv D)
          (fun pi => f pi.1)).symm
    _ = _ := by
        apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
        intro sample
        rfl

/-- One of the nine ordered type branches carries at most nine times the
uniformly weighted rejection probability. -/
private theorem directLdBranchRejectionProbability_le_nine_mul
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D))
    (types : _root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.LdType) (ε : ℝ) (hwin : 1 - ε ≤ S.value) :
    _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S types ≤ 9 * ε := by
  have hcard : Fintype.card (_root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.LdType) = 9 := by
    rw [Fintype.card_prod, show Fintype.card _root_.MIPStarRE.QPBT.LdType = 3 from by decide]
  have hsum : _root_.MIPStarRE.QPBT.directLdRejectionProbability D S =
      (Fintype.card (_root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.LdType) : ℝ)⁻¹ *
        ∑ t : _root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.LdType, _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S t :=
    _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_eq_inv_card_mul_sum _
  rw [hcard] at hsum
  have hsingle : _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S types ≤
      ∑ t : _root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.LdType, _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S t :=
    Finset.single_le_sum
      (f := fun t => _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S t)
      (fun t _ => _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability_nonneg D S t)
      (Finset.mem_univ types)
  have hrej : _root_.MIPStarRE.QPBT.directLdRejectionProbability D S ≤ ε := by
    rw [_root_.MIPStarRE.QPBT.directLdRejectionProbability_eq_one_sub_value]
    linarith
  norm_num at hsum
  linarith



/-! ## Transport through the correlated seed-residue dilation -/







end

end MIPStarRE.QPBT

/-!
# The point-agreement branch as a consistency estimate

The low-degree game asks both players a point question in one of its nine
ordered type branches and accepts only equal point answers.  This module reads
that branch as a quantitative consistency relation between the two point
readouts, first for the directly indexed game and then, through the correlated
seed-residue dilation, for the seed-indexed game.

The estimate is the third input, besides the two conclusions of the low
individual degree theorem, from which the global polynomial relation of
`lem:ld-soundness` is obtained after the seed-residue ancilla has been
compressed away: the compressed polynomial measurements are consistent with
the point measurements of the *opposite* player only, and the point-agreement
branch is what links the two point measurements to each other.

## Main results

* `directLdPointPair_consistencyDefect_le` bounds the point-readout
  consistency defect of a direct strategy of value at least `1 - ε` by
  `9 ε`, the loss being the uniform weight of one of the nine ordered type
  branches.
* `ldPointPair_consistencyDefect_le` is the same estimate for the
  seed-indexed game, obtained from the direct one because the point
  measurements of the dilated strategy act trivially on the correlated
  residue register.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:137-167`
* `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum



/-! ## The point-agreement branch of the directly indexed game -/

set_option maxHeartbeats 1000000 in

theorem solution
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D)) (hS : S.IsProjective)
    (ε : ℝ) (hwin : 1 - ε ≤ S.value) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron
          (((S.A (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
            (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).effect a) 1)
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron 1
          (((S.B (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
            (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).effect a)) S.ψ ≤ 9 * ε := by
  classical
  let PA : (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) →
      _root_.LIDT.MIPStarRE.LDT.ProjMeas (Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D) S.ιA := fun u =>
    _root_.LIDT.MIPStarRE.LDT.ProjMeas.postprocess
      (_root_.MIPStarRE.QPBT.matrixMeasurementToLDTProjMeas (S.A (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u))
        (hS.1 (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)))
      (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)
  let PB : (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) →
      _root_.LIDT.MIPStarRE.LDT.ProjMeas (Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D) S.ιB := fun u =>
    _root_.LIDT.MIPStarRE.LDT.ProjMeas.postprocess
      (_root_.MIPStarRE.QPBT.matrixMeasurementToLDTProjMeas (S.B (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u))
        (hS.2 (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)))
      (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)
  have hpoint : ∀ u : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D,
      _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect (_root_.MIPStarRE.QPBT.strategyQuantumState S)
          (PA u).toSubMeas (PB u).toSubMeas ≤
        _root_.MIPStarRE.QPBT.directRejectedMass D S (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)
          (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u) := by
    intro u
    exact _root_.MIPStarRE.QPBT.qBipartiteConsDefect_le_directRejectedMass D S hS
      (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u) (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)
      (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D) (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)
      (fun a b hab => directLdPointValuesOrZero_eq_of_win D u a b hab)
  have hconsrel : _root_.LIDT.MIPStarRE.LDT.ConsRel (_root_.MIPStarRE.QPBT.strategyQuantumState S)
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
      (fun u => (PA u).toSubMeas) (fun u => (PB u).toSubMeas) (9 * ε) := by
    refine ⟨?_⟩
    unfold _root_.LIDT.MIPStarRE.LDT.bipartiteConsError
    calc _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
          (fun u => _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect (_root_.MIPStarRE.QPBT.strategyQuantumState S)
            (PA u).toSubMeas (PB u).toSubMeas)
        ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
            (fun u => _root_.MIPStarRE.QPBT.directRejectedMass D S (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)
              (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)) := _root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ hpoint
      _ = _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S (.point, .point) :=
          avgOver_directRejectedMass_point_eq D S
      _ ≤ 9 * ε :=
          directLdBranchRejectionProbability_le_nine_mul D S _ ε hwin
  have hfinal := _root_.MIPStarRE.QPBT.strategyConsRel_consistencyDefect_le S
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _) PA PB (9 * ε) hconsrel
  refine le_trans (le_of_eq ?_) hfinal
  refine _root_.MIPStarRE.QPBT.consistencyDefect_congr _ _ _ _ _ S.ψ (fun u a => ?_) (fun u a => ?_)
  · rw [projMeas_postprocess_outcome_eq]
  · rw [projMeas_postprocess_outcome_eq]
