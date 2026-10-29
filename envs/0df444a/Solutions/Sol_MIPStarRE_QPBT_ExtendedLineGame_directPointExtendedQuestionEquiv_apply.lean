-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.directPointExtendedQuestionEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:42:28.481328+00:00
-- url     : https://prove2.me/submissions/a953ac06-0231-4edc-93eb-5309fd3529f9

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.directPointExtendedQuestionEquiv_apply.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_PointPointRejection
import Definitions.Def_QPBT_QPBT_Combining_Points
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ExtendedLineGame
end MIPStarRE.QPBT.ExtendedLineGame
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/-!
# Point/point rejection for the extended direct game

This module bounds the point-agreement branch of the directly indexed
low-degree strategy by the self-consistency error of the supplied joint point
measurements.  The common extended point is transported by one coordinate
equivalence to the jointly uniform tuple `(x, z, alpha, beta)` before the
scalar coarse-graining is applied.

This is a formalization-only auxiliary for the supplied-witness route in the
proof of `lem:qld-4-7`; it does not construct the point witness or establish
the complete passing-value estimate.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:689-709`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-311`
- Issue Dengnifer/MIPStarRE-QPBT-bak#313.
-/



open scoped BigOperators MatrixOrder ComplexOrder

set_option synthInstance.maxSize 400

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open MIPStarRE.QPBT.ProjectiveSetting



open MIPStarRE.QPBT.ExtendedLineGame

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}

theorem solution
    (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (u : Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) :
    _root_.MIPStarRE.QPBT.ExtendedLineGame.directPointExtendedQuestionEquiv P u =
      ((_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P u), _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P u)),
        (_root_.MIPStarRE.QPBT.directPointToPauli P u (_root_.MIPStarRE.QPBT.alphaVar P.m),
          _root_.MIPStarRE.QPBT.directPointToPauli P u (_root_.MIPStarRE.QPBT.betaVar P.m))) := by
  apply Prod.ext
  · apply Prod.ext
    · funext i
      change (_root_.MIPStarRE.QPBT.finCombineEquiv P.m).piCongrLeft (fun _ => _root_.MIPStarRE.QPBT.PauliScalar P)
        (fun j => _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P (u j)) (.inl (.inl i)) = _
      rw [piCongrLeft_const_apply]
      rfl
    · funext i
      change (_root_.MIPStarRE.QPBT.finCombineEquiv P.m).piCongrLeft (fun _ => _root_.MIPStarRE.QPBT.PauliScalar P)
        (fun j => _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P (u j)) (.inl (.inr i)) = _
      rw [piCongrLeft_const_apply]
      rfl
  · apply Prod.ext
    · change (_root_.MIPStarRE.QPBT.finCombineEquiv P.m).piCongrLeft (fun _ => _root_.MIPStarRE.QPBT.PauliScalar P)
        (fun j => _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P (u j)) (.inr 0) = _
      rw [piCongrLeft_const_apply]
      rfl
    · change (_root_.MIPStarRE.QPBT.finCombineEquiv P.m).piCongrLeft (fun _ => _root_.MIPStarRE.QPBT.PauliScalar P)
        (fun j => _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P (u j)) (.inr 1) = _
      rw [piCongrLeft_const_apply]
      rfl
