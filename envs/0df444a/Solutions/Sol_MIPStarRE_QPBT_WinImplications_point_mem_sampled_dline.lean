-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.point_mem_sampled_dline
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:12:24.236602+00:00
-- url     : https://prove2.me/submissions/60725341-86b5-43ec-acb8-e00d69f6abfb

-- Generated proof for MIPStarRE.QPBT.WinImplications.point_mem_sampled_dline.
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
import Definitions.Def_QPBT_QPBT_Algebra_Lines
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_LowDegree
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Observables/WinImplications/LowDegree.lean. -/
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.instDecidableRel_qPBT
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.linePointFintypeCanonical
/-!
# Low-degree winning implications

This module proves the exact line-point and Pauli-basis consistency bounds.

## References

The line-point and Pauli-basis consistency theorems prove items 2 and 3
of `lem:qld-win-implications`
from `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`
and blueprint `lem:qld-win-implications` and `lem:qld-win-implications-obs`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications

































/-- Prefix projection is idempotent at a fixed cutoff. -/
theorem prefixProjection_idem (L : _root_.MIPStarRE.QPBT.LdParams) (i : Fin L.m)
    (v : Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) :
    _root_.MIPStarRE.QPBT.prefixProjection i (_root_.MIPStarRE.QPBT.prefixProjection i v) = _root_.MIPStarRE.QPBT.prefixProjection i v := by
  funext j
  by_cases h : j.val < i.val <;> simp [_root_.MIPStarRE.QPBT.prefixProjection, h]




























































end WinImplications

end

end MIPStarRE.QPBT

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

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) :
    (_root_.MIPStarRE.QPBT.pauliToLd P W z).point ∈
      (_root_.MIPStarRE.QPBT.dLineDescOf P.toLdParams
        (_root_.MIPStarRE.QPBT.ldDLineCL P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z))).pointSet := by
  change (_root_.MIPStarRE.QPBT.pauliToLd P W z).point ∈ _root_.MIPStarRE.QPBT.linePoints
    (_root_.MIPStarRE.QPBT.lineRepMap
      (_root_.MIPStarRE.QPBT.prefixProjection (_root_.MIPStarRE.QPBT.chiIndex P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z).seed)
        (_root_.MIPStarRE.QPBT.prefixProjection (_root_.MIPStarRE.QPBT.chiIndex P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z).seed)
          (_root_.MIPStarRE.QPBT.pauliToLd P W z).direction))
      (_root_.MIPStarRE.QPBT.lineRepMap
        (_root_.MIPStarRE.QPBT.prefixProjection (_root_.MIPStarRE.QPBT.chiIndex P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z).seed)
          (_root_.MIPStarRE.QPBT.pauliToLd P W z).direction) (_root_.MIPStarRE.QPBT.pauliToLd P W z).point))
    (_root_.MIPStarRE.QPBT.prefixProjection (_root_.MIPStarRE.QPBT.chiIndex P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z).seed)
      (_root_.MIPStarRE.QPBT.prefixProjection (_root_.MIPStarRE.QPBT.chiIndex P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z).seed)
        (_root_.MIPStarRE.QPBT.pauliToLd P W z).direction))
  rw [_root_.MIPStarRE.QPBT.WinImplications.prefixProjection_idem, _root_.MIPStarRE.QPBT.lineRepMap_apply_self]
  exact _root_.MIPStarRE.QPBT.mem_linePoints_lineRepMap _ _
