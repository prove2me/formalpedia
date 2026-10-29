-- Prove2me | solution 1 for MIPStarRE.QPBT.extraction_small_error_absorption
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:24:57.453007+00:00
-- url     : https://prove2.me/submissions/4171e4d0-196a-40e4-ae97-91718eed0ca7

-- Generated proof for MIPStarRE.QPBT.extraction_small_error_absorption.
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
import Definitions.Def_QPBT_QPBT_Extraction_Defs
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/-!
# Total Pauli comparison on a normalized ideal state

The complete answer-summed distance is controlled by the evaluated overlap on
another normalized state, the Schwartz--Zippel collision probability, and the
distance between the states. This is the operator comparison used after the
swap and auxiliary-state construction.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1827-1858`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open LIDT.MIPStarRE.LDT hiding Measurement

theorem solution (C delta : ℝ) (m d q : ℕ)
    (hC : 18 ≤ C) (hdelta : 0 ≤ delta) (hdelta_one : delta ≤ 1) :
    16 * delta ≤ _root_.MIPStarRE.QPBT.deltaExtract C delta m d q ∧
      2 * delta + 2 * (((m * d : ℕ) : ℝ) / q) + 16 * Real.sqrt delta ≤
        _root_.MIPStarRE.QPBT.deltaExtract C delta m d q := by
  have hroot := Real.self_le_rpow_of_le_one hdelta hdelta_one
    (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have hsqrt : Real.sqrt delta ≤ delta ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge' hdelta hdelta_one (by norm_num) (by norm_num)
  have hr : 0 ≤ (((m * d : ℕ) : ℝ) / q) := by positivity
  have hp := mul_le_mul_of_nonneg_right hC
    (add_nonneg (Real.rpow_nonneg hdelta (1 / 4)) hr)
  constructor
  · exact (show 16 * delta ≤ 18 * (delta ^ (1 / 4 : ℝ) +
      ((m * d : ℕ) : ℝ) / q) by nlinarith).trans hp
  · exact (show 2 * delta + 2 * (((m * d : ℕ) : ℝ) / q) + 16 * Real.sqrt delta ≤
      18 * (delta ^ (1 / 4 : ℝ) + ((m * d : ℕ) : ℝ) / q) by nlinarith).trans hp
