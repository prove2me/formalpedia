-- Prove2me | solution 1 for MIPStarRE.QPBT.schmidt_pair_mirror_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:45:51.084427+00:00
-- url     : https://prove2.me/submissions/89c8724c-3c38-437e-b5b5-917ce50e736d

-- Generated proof for MIPStarRE.QPBT.schmidt_pair_mirror_estimate.
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

namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-! # State-dependent Schmidt mirrors

This module constructs the opposite-register mirror used in the one-sided
pasting argument. The auxiliary construction uses the spectral theorem and
orthonormal completion, including zero Schmidt coefficients.

## References

`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`, `lem:pasting`;
`docs/paper-gaps/qpbt_pasting-product-error.tex`, issue Dengnifer/MIPStarRE-QPBT-bak#201. The
Schmidt-mirror
argument is a formalization auxiliary, not an additional paper hypothesis.
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

theorem solution (left right : ℝ) (hleft : 0 ≤ left)
    (hright : 0 ≤ right) (entry target : ℂ) :
    (left - right) ^ 2 * Complex.normSq target ≤
      Complex.normSq ((right : ℂ) * entry - (left : ℂ) * target) +
      Complex.normSq ((left : ℂ) * entry - (right : ℂ) * target) := by
  have hidentity :
      Complex.normSq ((right : ℂ) * entry - (left : ℂ) * target) +
        Complex.normSq ((left : ℂ) * entry - (right : ℂ) * target) -
        (left - right) ^ 2 * Complex.normSq target =
      (left - right) ^ 2 * Complex.normSq entry +
        2 * left * right * Complex.normSq (entry - target) := by
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  have hnonneg : 0 ≤ (left - right) ^ 2 * Complex.normSq entry +
      2 * left * right * Complex.normSq (entry - target) :=
    add_nonneg (mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _))
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hleft) hright)
        (Complex.normSq_nonneg _))
  linarith
