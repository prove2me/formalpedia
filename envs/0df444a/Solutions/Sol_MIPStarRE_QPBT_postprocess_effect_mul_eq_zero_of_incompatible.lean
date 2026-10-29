-- Prove2me | solution 1 for MIPStarRE.QPBT.postprocess_effect_mul_eq_zero_of_incompatible
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:56:53.994064+00:00
-- url     : https://prove2.me/submissions/079f4b39-b33b-4633-b90c-01bc0dc206a1

-- Generated proof for MIPStarRE.QPBT.postprocess_effect_mul_eq_zero_of_incompatible.
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
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# The honest Pauli measurement family

This module collects the measurements of
`MIPStarRE.QPBT.Test.Completeness.HonestStrategy` into a single measurement
family indexed by the question type of the Pauli basis test.  Each honest
measurement acts on the tensor product of the Pauli register with the qubit
supplied to the Magic Square construction, and every outcome is relabelled into
the common answer alphabet of the test.  The results recorded here are the
projectivity and the symmetry of every effect of that family.

## References

The measurement family described here is the one displayed in the proof of
`lem:pauli-completeness`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1237-1360`;
blueprint `lem:pauli-completeness`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



/-! ### Tensor placement and relabeling -/

theorem solution {ζ α β V : Type*}
    [Fintype ζ] [DecidableEq ζ] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype V] [DecidableEq V]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement ζ V) (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M)
    (f : ζ → α) (g : ζ → β) (a : α) (b : β)
    (hbad : ∀ z, f z = a → g z = b → False) :
    (M.postprocess f).effect a * (M.postprocess g).effect b = 0 := by
  classical
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect,
    Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro y hy
  by_cases hxy : x = y
  · subst y
    exact (hbad x (Finset.mem_filter.mp hx).2
      (Finset.mem_filter.mp hy).2).elim
  · exact _root_.MIPStarRE.QPBT.DistanceCalculus.projective_effect_mul_effect_eq_zero M hM hxy
