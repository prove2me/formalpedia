-- Prove2me | solution 1 for MIPStarRE.QPBT.blockDiagonalMeasurement_postprocess
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:15:21.496107+00:00
-- url     : https://prove2.me/submissions/ec4ec489-7f80-49e3-858f-b1c67b123a80

-- Generated proof for MIPStarRE.QPBT.blockDiagonalMeasurement_postprocess.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_SeedFiber
import Definitions.Def_QPBT_QPBT_Upstream
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
# Low-degree consistency transport

This module identifies the low individual degree polynomial outcomes with the
bounded polynomial representatives used by the directly indexed QPBT game.  It
also transports complete measurements and their evaluation postprocessings
without changing either coordinate order or consistency error.

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



/-! ## Polynomial outcomes -/











/-! ## Complete measurements -/



















/-! ## Correlated-ancilla compression -/

/-!
The diagonal-block conditional expectation preserves either mixed defect
exactly because the point measurement on the opposite carrier is constant on
the residue register.  It does not yield a global/global compression theorem:
the lifted state pairs equal residues, whereas separately compressing both
polynomial measurements produces an independent double average over residues.
Neither quantity bounds the other in general.  This open obstruction is
recorded in `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/

theorem solution
    {alpha beta iota block : Type*}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    [Fintype iota] [DecidableEq iota]
    [Fintype block] [DecidableEq block]
    (M : block → _root_.LIDT.MIPStarRE.Quantum.Measurement alpha iota)
    (f : alpha → beta) :
    (_root_.MIPStarRE.QPBT.blockDiagonalMeasurement M).postprocess f =
      _root_.MIPStarRE.QPBT.blockDiagonalMeasurement (fun r => (M r).postprocess f) := by
  classical
  apply _root_.LIDT.MIPStarRE.Quantum.Measurement.ext
  intro b
  ext ⟨i, r⟩ ⟨j, s⟩
  simp only [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect,
    _root_.MIPStarRE.QPBT.blockDiagonalMeasurement_effect, Matrix.sum_apply,
    Matrix.blockDiagonal_apply]
  by_cases hrs : r = s
  · subst s
    simp only [if_pos]
  · simp [hrs]
