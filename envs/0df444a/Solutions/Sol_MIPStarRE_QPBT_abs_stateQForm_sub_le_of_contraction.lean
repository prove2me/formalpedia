-- Prove2me | solution 1 for MIPStarRE.QPBT.abs_stateQForm_sub_le_of_contraction
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:24:57.266935+00:00
-- url     : https://prove2.me/submissions/413e6603-bc03-4934-9030-80cb3ae72846

-- Generated proof for MIPStarRE.QPBT.abs_stateQForm_sub_le_of_contraction.
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
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
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
# Transfer of the complete Pauli overlap between states

A selected sum of effects of a complete measurement is a positive contraction.
Applied to the product measurement, this bounds the complete overlap operator,
independently of the number of answers. Its expectation changes by at most twice
the distance between unit vectors. Schwartz--Zippel then removes unequal Pauli
encodings after the change of state.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1827-1858`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open LIDT.MIPStarRE.LDT hiding Measurement

theorem solution {ι : Type*}
    [Fintype ι] [DecidableEq ι] (T : _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (hT : ∀ v : EuclideanSpace ℂ ι, ‖_root_.MIPStarRE.QPBT.applyOperatorToState T v‖ ≤ ‖v‖)
    (psi phi : EuclideanSpace ℂ ι) (hpsi : ‖psi‖ = 1) (hphi : ‖phi‖ = 1) :
    |stateQForm psi T - _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm phi T| ≤ 2 * ‖psi - phi‖ := by
  have hsplit : _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm psi T - _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm phi T =
      (inner ℂ (psi - phi) (_root_.MIPStarRE.QPBT.applyOperatorToState T psi)).re +
        (inner ℂ phi (_root_.MIPStarRE.QPBT.applyOperatorToState T (psi - phi))).re := by
    simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]
  rw [hsplit]
  calc
    _ ≤ |(inner ℂ (psi - phi) (_root_.MIPStarRE.QPBT.applyOperatorToState T psi)).re| +
        |(inner ℂ phi (_root_.MIPStarRE.QPBT.applyOperatorToState T (psi - phi))).re| := abs_add_le _ _
    _ ≤ ‖psi - phi‖ * ‖_root_.MIPStarRE.QPBT.applyOperatorToState T psi‖ +
        ‖phi‖ * ‖_root_.MIPStarRE.QPBT.applyOperatorToState T (psi - phi)‖ :=
      add_le_add ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _))
        ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _))
    _ ≤ ‖psi - phi‖ * ‖psi‖ + ‖phi‖ * ‖psi - phi‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (hT psi) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (hT (psi - phi)) (norm_nonneg _))
    _ = _ := by rw [hpsi, hphi]; ring
