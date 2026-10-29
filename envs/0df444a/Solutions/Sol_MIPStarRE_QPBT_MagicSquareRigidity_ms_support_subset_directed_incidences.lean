-- Prove2me | solution 1 for MIPStarRE.QPBT.MagicSquareRigidity.ms_support_subset_directed_incidences
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:27:30.857294+00:00
-- url     : https://prove2.me/submissions/5325f49c-f1ef-4dba-9547-41a4cc048fc2

-- Generated proof for MIPStarRE.QPBT.MagicSquareRigidity.ms_support_subset_directed_incidences.
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
import Definitions.Def_QPBT_QPBT_Games_CondLinear
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Relations

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity

/-!
# Magic Square value-to-parity relations

This file extracts the elementary probability relations used at the start of
the Magic Square rigidity argument.  A strategy of value at least `1 - ε` has
total rejection mass at most `ε`.  Since the question distribution is
supported on at most 36 directed incidences, the rejection mass at each
incidence is at most `36 * ε`.  This controls malformed answers, consistency
of the two reported bits at every cell, and the parity product on each of the
six row or column constraints.

The arguments apply to arbitrary finite POVMs.  In particular, malformed
answers remain in the event masses when `msBitOrZero` and
`constraintBitOrZero` turn the common answer alphabet into binary outcomes.

## References

The Magic Square game is defined in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:512-610`
and blueprint `def:ms-game`.  These relations are the
probabilistic input to the rigidity result cited at paper lines 612-652 from
Coladangelo--Stark, Theorem 6.9.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum



/-! ## The directed incidence distribution -/

theorem solution :
    (_root_.MIPStarRE.QPBT.graphDistribution _root_.MIPStarRE.QPBT.msEdges _root_.MIPStarRE.QPBT.msEdges_nonempty).support ⊆
      (Finset.univ : Finset ((Fin 6 × Fin 3) × Bool)).image _root_.MIPStarRE.QPBT.MagicSquareRigidity.directedIncidence := by
  intro xy hxy
  have hedge : Sym2.mk xy.1 xy.2 ∈ _root_.MIPStarRE.QPBT.msEdges :=
    (Finset.mem_filter.mp hxy).2
  rcases Finset.mem_image.mp hedge with ⟨ik, _hik, heq⟩
  have heq' :
      ((.constraint ik.1, .var (_root_.MIPStarRE.QPBT.msConstraintVars ik.1 ik.2)) : _root_.MIPStarRE.QPBT.MsType × _root_.MIPStarRE.QPBT.MsType) = xy ∨
        ((.constraint ik.1, .var (_root_.MIPStarRE.QPBT.msConstraintVars ik.1 ik.2)) : _root_.MIPStarRE.QPBT.MsType × _root_.MIPStarRE.QPBT.MsType) =
          xy.swap :=
    (Sym2.mk_eq_mk_iff (α := _root_.MIPStarRE.QPBT.MsType)).mp heq
  rcases heq' with heq' | heq'
  · refine Finset.mem_image.mpr ⟨(ik, false), Finset.mem_univ _, ?_⟩
    simpa [_root_.MIPStarRE.QPBT.MagicSquareRigidity.directedIncidence] using heq'
  · refine Finset.mem_image.mpr ⟨(ik, true), Finset.mem_univ _, ?_⟩
    simpa [_root_.MIPStarRE.QPBT.MagicSquareRigidity.directedIncidence] using congrArg Prod.swap heq'
