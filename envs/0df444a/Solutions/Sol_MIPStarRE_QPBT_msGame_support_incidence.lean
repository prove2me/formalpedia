-- Prove2me | solution 1 for MIPStarRE.QPBT.msGame_support_incidence
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:04:45.908166+00:00
-- url     : https://prove2.me/submissions/62e21593-785d-4dcd-a185-7daa7e5f8a1b

-- Generated proof for MIPStarRE.QPBT.msGame_support_incidence.
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
import Definitions.Def_QPBT_QPBT_Games_StrategyClasses
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Basic

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Perfect strategies for the Magic Square game

This file completes the construction of `thm:ms-from-ac`.  It identifies the
question pairs in the support of the Magic Square distribution, shows that the
measurement family commutes there and annihilates rejected answer pairs on the
EPR state, evaluates the Born weights of the accepted answers, and assembles a
symmetric SPCC strategy of value one from an anticommuting consistent pair of
binary measurements.

## References

The source statement is blueprint
`thm:ms-from-ac`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:654-722`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

theorem solution (x y : _root_.MIPStarRE.QPBT.MsType)
    (hxy : (x, y) ∈ _root_.MIPStarRE.QPBT.msGameSymm.μ.support) :
    (∃ i : Fin 6, ∃ k : Fin 3,
      x = .constraint i ∧ y = .var (_root_.MIPStarRE.QPBT.msConstraintVars i k)) ∨
      ∃ i : Fin 6, ∃ k : Fin 3,
        x = .var (_root_.MIPStarRE.QPBT.msConstraintVars i k) ∧ y = .constraint i := by
  change (x, y) ∈
    Finset.univ.filter (fun ab : _root_.MIPStarRE.QPBT.MsType × _root_.MIPStarRE.QPBT.MsType =>
      Sym2.mk ab.1 ab.2 ∈ _root_.MIPStarRE.QPBT.msEdges) at hxy
  have hedge : Sym2.mk x y ∈ _root_.MIPStarRE.QPBT.msEdges := (Finset.mem_filter.mp hxy).2
  rw [_root_.MIPStarRE.QPBT.msEdges] at hedge
  rcases Finset.mem_image.mp hedge with ⟨⟨i, k⟩, _, hik⟩
  rcases Sym2.eq_iff.mp hik with hik | hik
  · left
    exact ⟨i, k, hik.1.symm, hik.2.symm⟩
  · right
    exact ⟨i, k, hik.2.symm, hik.1.symm⟩
