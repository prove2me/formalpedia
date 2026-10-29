-- Prove2me | solution 1 for MIPStarRE.QPBT.directLdIndexedBranchRejectionProbability_point_point
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:01:20.430006+00:00
-- url     : https://prove2.me/submissions/83679e2e-7867-49ae-bc1a-5ab87eea976d

-- Generated proof for MIPStarRE.QPBT.directLdIndexedBranchRejectionProbability_point_point.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_BranchComparison
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_GameValue
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Index-conditioned rejection probabilities of the directly indexed game

`lem:ld-combined-value` transports the value of a strategy along
`def:ld-combined-strategy` by splitting each branch of the combined game
according to the event of `lem:ld-combined-question-law`, that is according to
whether the stored coordinate index of the common sample is a point coordinate
or a combining coordinate.  This module provides the corresponding refinement
of the branch rejection probability: the uniform average over the common sample
is the uniform average over the stored coordinate index of the average over the
sampled point and the sampled direction alone.

The point-versus-point branch is recorded separately, because it is the branch
that the combining coordinates of the combined game reduce to: both of its
questions are the point question at the sampled point, so its rejected mass
depends on neither the stored coordinate index nor the sampled direction.

All declarations below are formalization-only support derived from the game
value; none is a paper-labelled result.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:517-568`
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum



/-! ## The index-conditioned branch rejection probability -/







/-! ## The point-versus-point branch -/

theorem solution
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D)) (i : Fin D.m) :
    _root_.MIPStarRE.QPBT.directLdIndexedBranchRejectionProbability D S (.point, .point) i =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)) fun u =>
        _root_.MIPStarRE.QPBT.directRejectedMass D S (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)
          (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u) := by
  have hsplit : _root_.MIPStarRE.QPBT.directLdIndexedBranchRejectionProbability D S (.point, .point) i =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
          ((Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) × (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)))
        (fun pd => (fun (u _ : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) =>
          _root_.MIPStarRE.QPBT.directRejectedMass D S (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)
            (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)) pd.1 pd.2) := rfl
  rw [hsplit,
    _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_prod (f := fun (u _ : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) =>
      _root_.MIPStarRE.QPBT.directRejectedMass D S (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)
        (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u))]
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro _
  exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const _
