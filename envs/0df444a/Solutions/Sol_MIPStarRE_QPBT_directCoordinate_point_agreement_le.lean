-- Prove2me | solution 1 for MIPStarRE.QPBT.directCoordinate_point_agreement_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:36:27.803949+00:00
-- url     : https://prove2.me/submissions/63d7002c-6a01-4d86-b9db-2aa959a9ddce

-- Generated proof for MIPStarRE.QPBT.directCoordinate_point_agreement_le.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyBiProj_Measurements
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_GameValue
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_BranchComparison
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Correspondence
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Questions
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Strategy
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_StrategyClasses
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_directPointAnswerReadout_eq_of_win
import Theorems.Thm_MIPStarRE_QPBT_qBipartiteConsDefect_le_directRejectedMass

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
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

/-- Admissible field sizes are positive, so LDT points over a direct
parameter tuple form a nonempty type. -/
instance instNeZeroNatQ (D : _root_.MIPStarRE.QPBT.DirectLdParams) : NeZero D.q :=
  ⟨Nat.ne_of_gt D.toLDTParameters.hq⟩

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

section PointAxisBranches

variable (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D))
  (hS : S.IsProjective) (r : Fin D.k)

/-- Point-agreement defect at an LDT point is at most the rejected direct
mass at the direct point question. -/
private theorem point_defect_le (u : _root_.LIDT.MIPStarRE.LDT.Point D.toLDTParameters) :
    letI := D.toLDTFieldModel
    _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect (_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).state
        ((_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).pointMeasurementA u).toSubMeas
        ((_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).pointMeasurementB u).toSubMeas ≤
      _root_.MIPStarRE.QPBT.directRejectedMass D S
        (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D (_root_.MIPStarRE.QPBT.ldtPointToDirect D u))
        (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D (_root_.MIPStarRE.QPBT.ldtPointToDirect D u)) := by
  letI := D.toLDTFieldModel
  exact _root_.MIPStarRE.QPBT.qBipartiteConsDefect_le_directRejectedMass D S hS
    (_root_.MIPStarRE.QPBT.directPointQuestionOf D u) (_root_.MIPStarRE.QPBT.directPointQuestionOf D u)
    (_root_.MIPStarRE.QPBT.directPointAnswerReadout D r) (_root_.MIPStarRE.QPBT.directPointAnswerReadout D r)
    (fun a b hab =>
      _root_.MIPStarRE.QPBT.directPointAnswerReadout_eq_of_win D r (_root_.MIPStarRE.QPBT.ldtPointToDirect D u) a b hab)













end PointAxisBranches

end

end MIPStarRE.QPBT

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



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum





/-! ## Rejected Born mass at a fixed question pair -/









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



variable (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D))
  (hS : S.IsProjective) (r : Fin D.k)

theorem solution :
    letI := D.toLDTFieldModel
    (_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).pointAgreementFailureProbability ≤
      _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S (.point, .point) := by
  letI := D.toLDTFieldModel
  unfold _root_.LIDT.MIPStarRE.LDT.ProjStrat.pointAgreementFailureProbability _root_.LIDT.MIPStarRE.LDT.bipartiteConsError
  refine le_trans (_root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ fun u => point_defect_le D S hS r u)
    (le_of_eq ?_)
  rw [_root_.MIPStarRE.QPBT.directLdBranchRejectionProbability_eq_avgOver]
  let f : (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) → ℝ := fun p =>
    _root_.MIPStarRE.QPBT.directRejectedMass D S (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D p) (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D p)
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point D.toLDTParameters))
        (fun u => f (_root_.MIPStarRE.QPBT.ldtPointToDirect D u)) =
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)) f :=
      (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv (_root_.MIPStarRE.QPBT.directPointEquiv D) f).symm
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution ((Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) × Fin D.m))
        (fun pi => f pi.1) :=
      (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_fst f).symm
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace D))
        (fun sample => f ((_root_.MIPStarRE.QPBT.directLdSpaceSplitEquiv D sample).1).1) :=
      (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv_fst (_root_.MIPStarRE.QPBT.directLdSpaceSplitEquiv D) (fun pi => f pi.1)).symm
    _ = _ := by
      apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
      intro sample
      rfl
