-- Prove2me | solution 1 for MIPStarRE.QPBT.directDiagonalIndexOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:28:22.883989+00:00
-- url     : https://prove2.me/submissions/8541ef64-4a05-4560-89a2-ee37c31b19cc

-- Generated proof for MIPStarRE.QPBT.directDiagonalIndexOf_eq.
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
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Questions
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/Questions.lean. -/
/-!
# Question and answer transport for the directly indexed low-degree game

This module reads low individual degree test questions as canonical direct
questions and rebases direct answers to the LDT line parametrization.

Points and lines are decoded with the coordinate order reversed
(`directPointEquiv`), so that the suffix-zero direction restriction of the
LDT diagonal test becomes the prefix-zero restriction of the direct game.
An LDT diagonal line reveals no coordinate index, whereas a direct diagonal
question carries one.  The transported question uses the *leading index* of
the decoded direction, the least coordinate at which the direction is
nonzero.  Under the direct sampler, this is the index attached to the sampled
direction exactly when the direction is nonzero at the sampled index
(`directDiagonalIndexOf_prefixProjection`), an event of conditional
probability `1 - 1/q`; on the LDT side, the leading index of a decoded
`j`-restricted direction is `Fin.rev j` exactly when its pivot coordinate is
nonzero (`directDiagonalIndexOf_extendRestrictedDirection`).  Diagonal answers
on zero-direction lines are read as the constant polynomial carrying their
value at the base point, following `rem:ld-win-zero-direction`.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:230-272`
- `references/ldt-paper/test_definition.tex:49-65`
- `rem:ld-win-zero-direction`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Canonical line rebasing of LDT lines -/











/-! ## The leading index of a direction -/



theorem mem_directionSupport (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (v : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) (j : Fin D.m) :
    j ∈ _root_.MIPStarRE.QPBT.directionSupport D v ↔ v j ≠ 0 := by
  simp [_root_.MIPStarRE.QPBT.directionSupport]











/-! ## Decoding LDT points and lines -/



















/-! ## Rebasing lines -/





















/-! ## Reading direct answers as LDT answers -/

















end

end MIPStarRE.QPBT

/-!
# Question and answer transport for the directly indexed low-degree game

This module reads low individual degree test questions as canonical direct
questions and rebases direct answers to the LDT line parametrization.

Points and lines are decoded with the coordinate order reversed
(`directPointEquiv`), so that the suffix-zero direction restriction of the
LDT diagonal test becomes the prefix-zero restriction of the direct game.
An LDT diagonal line reveals no coordinate index, whereas a direct diagonal
question carries one.  The transported question uses the *leading index* of
the decoded direction, the least coordinate at which the direction is
nonzero.  Under the direct sampler, this is the index attached to the sampled
direction exactly when the direction is nonzero at the sampled index
(`directDiagonalIndexOf_prefixProjection`), an event of conditional
probability `1 - 1/q`; on the LDT side, the leading index of a decoded
`j`-restricted direction is `Fin.rev j` exactly when its pivot coordinate is
nonzero (`directDiagonalIndexOf_extendRestrictedDirection`).  Diagonal answers
on zero-direction lines are read as the constant polynomial carrying their
value at the base point, following `rem:ld-win-zero-direction`.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:230-272`
- `references/ldt-paper/test_definition.tex:49-65`
- `rem:ld-win-zero-direction`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum



/-! ## Canonical line rebasing of LDT lines -/











/-! ## The leading index of a direction -/

theorem solution (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    {v : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D} {i : Fin D.m}
    (hzero : ∀ j : Fin D.m, j.val < i.val → v j = 0) (hi : v i ≠ 0) :
    _root_.MIPStarRE.QPBT.directDiagonalIndexOf D v = i := by
  classical
  have hmem : i ∈ _root_.MIPStarRE.QPBT.directionSupport D v := (_root_.MIPStarRE.QPBT.mem_directionSupport D v i).mpr hi
  have hnonempty : (_root_.MIPStarRE.QPBT.directionSupport D v).Nonempty := ⟨i, hmem⟩
  unfold _root_.MIPStarRE.QPBT.directDiagonalIndexOf
  rw [dif_pos hnonempty]
  apply le_antisymm
  · exact Finset.min'_le _ _ hmem
  · apply Finset.le_min'
    intro j hj
    by_contra hlt
    exact (_root_.MIPStarRE.QPBT.mem_directionSupport D v j).mp hj
      (hzero j (Fin.lt_def.mp (not_le.mp hlt)))
