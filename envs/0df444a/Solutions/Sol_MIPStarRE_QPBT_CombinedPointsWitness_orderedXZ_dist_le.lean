-- Prove2me | solution 1 for MIPStarRE.QPBT.CombinedPointsWitness.orderedXZ_dist_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:44:56.999874+00:00
-- url     : https://prove2.me/submissions/f599782e-8698-49ed-a035-cf7bf57229ff

-- Generated proof for MIPStarRE.QPBT.CombinedPointsWitness.orderedXZ_dist_le.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_opFamilyDistSq_le_of_le_of_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/OrderedPoints.lean. -/
/-!
# The ordered point product on a single placement

The consistency guarantees carried by the joint point measurement compare it
with the ordered `Z`-then-`X` product across a pair of opposite placements.
The scalar estimates used to combine the two Pauli bases instead need the two
families on one placement.  This module obtains that form by inserting the
joint measurement on the opposite placement and applying the squared-distance
triangle inequality twice.

## References

The statement is `lem:qld-4-10-same-placement` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`; it restates the ordered
`Z`-then-`X` display of `lem:qld-4-10`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:689-709`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

/-- Every placement has an opposite placement, and the relation is symmetric
between the two members of each pair. -/
theorem Placement.exists_isOpposite (p : _root_.MIPStarRE.QPBT.Placement) :
    ∃ q : _root_.MIPStarRE.QPBT.Placement, p.IsOpposite q ∧ q.IsOpposite p := by
  cases p with
  | AA' => exact ⟨.BA'', trivial, trivial⟩
  | BA'' => exact ⟨.AA', trivial, trivial⟩
  | BB' => exact ⟨.AB'', trivial, trivial⟩
  | AB'' => exact ⟨.BB', trivial, trivial⟩






end

end MIPStarRE.QPBT

/-!
# The ordered point product on a single placement

The consistency guarantees carried by the joint point measurement compare it
with the ordered `Z`-then-`X` product across a pair of opposite placements.
The scalar estimates used to combine the two Pauli bases instead need the two
families on one placement.  This module obtains that form by inserting the
joint measurement on the opposite placement and applying the squared-distance
triangle inequality twice.

## References

The statement is `lem:qld-4-10-same-placement` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`; it restates the ordered
`Z`-then-`X` display of `lem:qld-4-10`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:689-709`.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    {ε δ : ℝ} {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε}
    (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δ) (p : _root_.MIPStarRE.QPBT.Placement) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
          ((Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)))
        (fun xz ab => S.place p ((points.Q p.side xz.1 xz.2).effect ab))
        (fun xz ab => S.place p
          ((S.pointMeasExp p.side .X xz.1).effect ab.1 *
            (S.pointMeasExp p.side .Z xz.2).effect ab.2))
        S.psiHat ≤ 4 * δ := by
  obtain ⟨q, hpq, hqp⟩ := p.exists_isOpposite
  have htri := _root_.MIPStarRE.QPBT.opFamilyDistSq_le_of_le_of_le
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
      ((Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)))
    (fun xz ab => S.place p ((points.Q p.side xz.1 xz.2).effect ab))
    (fun xz ab => S.place q ((points.Q q.side xz.1 xz.2).effect ab))
    (fun xz ab => S.place p
      ((S.pointMeasExp p.side .X xz.1).effect ab.1 *
        (S.pointMeasExp p.side .Z xz.2).effect ab.2))
    S.psiHat δ δ (points.self_consistent p q hpq)
    (points.consistent_XZ q p hqp)
  linarith
