-- Prove2me | solution 1 for MIPStarRE.QPBT.avgOver_directCombinedMeasuredRejectedMass_coefficientVar
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:06:24.248391+00:00
-- url     : https://prove2.me/submissions/a8328c54-bda9-419e-bd8b-a948036342e2

-- Generated proof for MIPStarRE.QPBT.avgOver_directCombinedMeasuredRejectedMass_coefficientVar.
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
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_GameValue
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_BranchComparison
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_GameValue
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Polynomial
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Strategy
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Value
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_LDT_avgOver_uniform_equiv_prod
import Theorems.Thm_MIPStarRE_QPBT_directLdIndexedBranchRejectionProbability_point_point

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

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/Combining/GameValue.lean. -/
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

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## The index-conditioned branch rejection probability -/





/-- The branch rejection probability of an ordered type pair is the uniform
average over the stored coordinate index of the index-conditioned rejection
probabilities.  This is the refinement used to split a branch of the combined
game according to the event of `lem:ld-combined-question-law`, whose two cases
are the point coordinates and the combining coordinates of the combined
dimension. -/
theorem directLdBranchRejectionProbability_eq_avgOver_index
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D))
    (types : _root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.LdType) :
    _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S types =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m))
        (_root_.MIPStarRE.QPBT.directLdIndexedBranchRejectionProbability D S types) := by
  rw [_root_.MIPStarRE.QPBT.directLdBranchRejectionProbability_eq_avgOver]
  exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv_prod (e := _root_.MIPStarRE.QPBT.directLdSpaceIndexEquiv D) _

/-! ## The point-versus-point branch -/



/-- The point-versus-point branch rejection probability is the uniform average
over the sampled point of the rejected mass at the two equal point questions.
This is the branch to which the combining coordinates of the combined game
reduce, by `directCombined_measuredQuestion_of_coefficientVar`. -/
theorem directLdBranchRejectionProbability_point_point_eq
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D)) :
    _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S (.point, .point) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)) fun u =>
        _root_.MIPStarRE.QPBT.directRejectedMass D S (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)
          (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u) := by
  rw [_root_.MIPStarRE.QPBT.directLdBranchRejectionProbability_eq_avgOver_index,
    show _root_.MIPStarRE.QPBT.directLdIndexedBranchRejectionProbability D S (.point, .point) =
      fun _ => _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)) fun u =>
        _root_.MIPStarRE.QPBT.directRejectedMass D S (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)
          (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u) from
      funext (_root_.MIPStarRE.QPBT.directLdIndexedBranchRejectionProbability_point_point D S)]
  exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const _

/-! ## The rejected mass of the combined strategy -/





end

end MIPStarRE.QPBT

/-!
# The value of the combined strategy

`lem:ld-combined-value` transports the value of a projective strategy along
`def:ld-combined-strategy`.  Both games weight their nine ordered type pairs
uniformly, so it suffices to bound the rejection probability of each branch of
the combined game by a bounded number of branch rejection probabilities of the
original game.  Splitting a branch according to the event of
`lem:ld-combined-question-law`, the branch conditioned on a point coordinate
index is the branch of the original game at the same ordered type pair, and the
branch conditioned on a combining coordinate index is the point-versus-point
branch of the original game; on each of the two events the relabelling of
`def:ld-combined-strategy` carries acceptance to acceptance, which is
`directCombinedWinTransport_all`.  Each branch of the combined game is therefore
rejected with probability at most the sum of two branch rejection probabilities
of the original game, and summing over the nine branches multiplies the
rejection probability by at most ten.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:526-568`
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum

theorem solution
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D))
    (types : _root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.LdType) (r : Fin D.k) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
        ((Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) × (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)))
      (_root_.MIPStarRE.QPBT.directCombinedMeasuredRejectedMass D S types
        (_root_.MIPStarRE.QPBT.combinedCoefficientVar D.m D.k r)) =
      _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S (.point, .point) := by
  have hcongr : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
        ((Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) × (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)))
      (_root_.MIPStarRE.QPBT.directCombinedMeasuredRejectedMass D S types
        (_root_.MIPStarRE.QPBT.combinedCoefficientVar D.m D.k r)) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
        ((Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) × (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)))
        (fun pd => (fun (u _ : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) =>
          _root_.MIPStarRE.QPBT.directRejectedMass D S (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)
            (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)) pd.1 pd.2) := by
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro pd
    simp only [_root_.MIPStarRE.QPBT.directCombinedMeasuredRejectedMass,
      _root_.MIPStarRE.QPBT.directCombinedIndexSplit_combinedCoefficientVar]
  rw [hcongr, _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_prod
      (f := fun (u _ : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) =>
        _root_.MIPStarRE.QPBT.directRejectedMass D S (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)
          (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)),
    _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability_point_point_eq]
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro _
  exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const _
