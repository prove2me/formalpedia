-- Prove2me | solution 1 for MIPStarRE.QPBT.strategyConsRel_consistencyDefect_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:10:09.050999+00:00
-- url     : https://prove2.me/submissions/6e12a58c-149b-4150-830d-07727bc693af

-- Generated proof for MIPStarRE.QPBT.strategyConsRel_consistencyDefect_le.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
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
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Consistency_State
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Strategy
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_consRel_iff_consistencyDefect

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

theorem solution
    {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G)
    {Question Outcome : Type*}
    [Fintype Question] [DecidableEq Question]
    [Fintype Outcome] [DecidableEq Outcome]
    (mu : _root_.LIDT.MIPStarRE.LDT.Distribution Question) (hmu : mu.IsProbability)
    (A : Question → _root_.LIDT.MIPStarRE.LDT.ProjMeas Outcome S.ιA)
    (B : Question → _root_.LIDT.MIPStarRE.LDT.ProjMeas Outcome S.ιB) (delta : ℝ)
    (h : _root_.LIDT.MIPStarRE.LDT.ConsRel (_root_.MIPStarRE.QPBT.strategyQuantumState S) mu
      (fun x => (A x).toSubMeas) (fun x => (B x).toSubMeas) delta) :
    _root_.MIPStarRE.QPBT.consistencyDefect mu
      (fun x a => _root_.MIPStarRE.QPBT.heteroKron ((A x).outcome a) 1)
      (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).outcome a)) S.ψ ≤ delta := by
  letI : Nonempty (S.ιA × S.ιB) :=
    (_root_.MIPStarRE.QPBT.strategyQuantumState_isNormalized S).nonempty
  let pure : _root_.LIDT.MIPStarRE.LDT.PureState (S.ιA × S.ιB) := _root_.MIPStarRE.QPBT.strategyPureState S
  have hpure :
      _root_.LIDT.MIPStarRE.LDT.ConsRel (pure : _root_.LIDT.MIPStarRE.LDT.QuantumState (S.ιA × S.ιB)) mu
        (fun x => (A x).toSubMeas) (fun x => (B x).toSubMeas) delta := by
    simpa [pure, _root_.MIPStarRE.QPBT.strategyQuantumState] using h
  have hconverted := (_root_.MIPStarRE.QPBT.consRel_iff_consistencyDefect pure mu hmu A B delta).mp hpure
  have hv : _root_.MIPStarRE.QPBT.DistanceCalculus.pureStateEuclideanVector pure = S.ψ := by
    exact _root_.MIPStarRE.QPBT.gameStrategyPureState_euclideanVector S
  rw [hv] at hconverted
  exact hconverted
