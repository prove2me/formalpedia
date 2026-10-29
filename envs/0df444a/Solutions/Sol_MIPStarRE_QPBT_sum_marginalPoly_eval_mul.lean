-- Prove2me | solution 1 for MIPStarRE.QPBT.sum_marginalPoly_eval_mul
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:17:33.871276+00:00
-- url     : https://prove2.me/submissions/31bf73a1-9866-4175-95f1-b04f18aee0ae

-- Generated proof for MIPStarRE.QPBT.sum_marginalPoly_eval_mul.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_Points_PlacementSupport
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Extraction_Observables
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.GlobalPairWitness
end MIPStarRE.QPBT.GlobalPairWitness
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/-!
# Consistency of the pulled-apart Pauli measurements

This module records the two estimates by which the polynomial marginals absorb
the expanded point measurements, with all heterogeneous placements written
explicitly. It also defines the mass of non-encoding marginal outcomes and
states the support estimate needed by the corrected decoder calculation.

The marginal agreement estimates and reverse-placement correlation transports
are developed from a supplied global polynomial-pair witness.

## References

The marginal estimates formalize blueprint
`lem:qld-constructing-the-paulis-helper`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1609-1664`.
The non-encoding support obligation contributes to blueprint
`lem:qld-construct-the-paulis`, from paper lines 1458-1608; see
`docs/paper-gaps/qpbt_decoding-identity.tex`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open MIPStarRE.QPBT.ProjectiveSetting



/-! ## Absorption of expanded point measurements -/





open MIPStarRE.QPBT.GlobalPairWitness

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaG : ℝ}
    {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon} (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG)
    (placement : _root_.MIPStarRE.QPBT.Placement) (W : _root_.MIPStarRE.QPBT.PauliKind) (point : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
    (family : _root_.MIPStarRE.QPBT.PauliScalar P → _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.SixReg P S.toStrategy.ιA S.toStrategy.ιB)) :
    (∑ answer : _root_.MIPStarRE.QPBT.PauliScalar P, S.place placement
      (((w.marginalPoly placement.side W).postprocess
        (fun poly => MvPolynomial.eval point poly.1)).effect answer) * family answer) =
      ∑ poly : _root_.MIPStarRE.QPBT.Poly P, S.place placement ((w.marginalPoly placement.side W).effect poly) *
        family (MvPolynomial.eval point poly.1) := by
  classical
  simp only [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, _root_.MIPStarRE.QPBT.ProjectiveSetting.place_finsetSum,
    Finset.sum_mul]
  calc
    _ = ∑ answer : _root_.MIPStarRE.QPBT.PauliScalar P,
        ∑ poly ∈ Finset.univ.filter (fun poly : _root_.MIPStarRE.QPBT.Poly P =>
          MvPolynomial.eval point poly.1 = answer),
          S.place placement ((w.marginalPoly placement.side W).effect poly) *
            family (MvPolynomial.eval point poly.1) := by
      apply Finset.sum_congr rfl
      intro answer _
      apply Finset.sum_congr rfl
      intro poly hpoly
      rw [(Finset.mem_filter.mp hpoly).2]
    _ = _ := Finset.sum_fiberwise _ _ _
