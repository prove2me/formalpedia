-- Prove2me | solution 1 for MIPStarRE.QPBT.directLdtPointNonempty
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:15:21.61942+00:00
-- url     : https://prove2.me/submissions/56044b25-f041-483a-9e26-bd89feb1a12f

-- Generated proof for MIPStarRE.QPBT.directLdtPointNonempty.
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
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Correspondence
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
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
# State conversion and direct point readout

This module contains the pure-state conversion and direct point-readout
portion of the low-degree consistency transport.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:393-458`
- `references/ldt-paper/test_definition.tex:180-202`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum



/-! ## Equality of the two consistency formulations -/

-- The following identities identify pure-state expectation with the
-- Euclidean quadratic form used in the consistency calculations below.  They
-- send a pure state to its Euclidean coordinate vector and identify the
-- quadratic form of that vector with evaluation in the associated density
-- state; they are stated for an arbitrary finite index type in
-- `MIPStarRE/QPBT/Games/DistanceTheorems/Support.lean`.




/-! ## Direct-strategy state and point readout -/

@[instance] theorem solution (D : _root_.MIPStarRE.QPBT.DirectLdParams) :
    Nonempty (_root_.LIDT.MIPStarRE.LDT.Point D.toLDTParameters) :=
  ⟨fun _ => ⟨0, D.toLDTParameters.hq⟩⟩
