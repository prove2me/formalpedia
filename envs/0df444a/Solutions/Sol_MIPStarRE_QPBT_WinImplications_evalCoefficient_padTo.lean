-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.evalCoefficient_padTo
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:12:24.529981+00:00
-- url     : https://prove2.me/submissions/eb51b118-3635-43cd-a36b-9297e1301cf7

-- Generated proof for MIPStarRE.QPBT.WinImplications.evalCoefficient_padTo.
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
import Definitions.Def_QPBT_QPBT_Algebra_Coefficients
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_LowDegree
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/-!
# Low-degree winning implications

This module proves the exact line-point and Pauli-basis consistency bounds.

## References

The line-point and Pauli-basis consistency theorems prove items 2 and 3
of `lem:qld-win-implications`
from `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`
and blueprint `lem:qld-win-implications` and `lem:qld-win-implications-obs`.
-/



open scoped BigOperators Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.WinImplications
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.instDecidableRel_qPBT
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.linePointFintypeCanonical

theorem solution {L : _root_.MIPStarRE.QPBT.LdParams} {c c' : ℕ} (h : c ≤ c')
    (f : _root_.MIPStarRE.QPBT.DegPoly L c) (t : _root_.MIPStarRE.QPBT.ScalarQ L) :
    _root_.MIPStarRE.QPBT.evalCoefficient (_root_.MIPStarRE.QPBT.DegPoly.padTo h f) t = _root_.MIPStarRE.QPBT.evalCoefficient f t := by
  classical
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero =>
      have heq : _root_.MIPStarRE.QPBT.DegPoly.padTo h f = f := by
        funext i
        simp [_root_.MIPStarRE.QPBT.DegPoly.padTo, i.isLt]
      rw [heq]
  | succ k ih =>
      rw [_root_.MIPStarRE.QPBT.evalCoefficient, Fin.sum_univ_castSucc]
      have hk : c ≤ c + k := Nat.le_add_right c k
      have hcast :
          (∑ i : Fin (c + (k + 1)),
              _root_.MIPStarRE.QPBT.DegPoly.padTo h f i.castSucc * t ^ i.castSucc.val) =
            _root_.MIPStarRE.QPBT.evalCoefficient (_root_.MIPStarRE.QPBT.DegPoly.padTo hk f) t := by
        unfold _root_.MIPStarRE.QPBT.evalCoefficient
        apply Finset.sum_congr rfl
        intro i _
        congr 1
      rw [hcast, ih]
      rw [show _root_.MIPStarRE.QPBT.DegPoly.padTo h f (Fin.last (c + (k + 1))) = 0 by
        simp [_root_.MIPStarRE.QPBT.DegPoly.padTo]]
      simp
