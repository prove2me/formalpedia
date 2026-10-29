-- Prove2me | solution 1 for MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:40:56.661246+00:00
-- url     : https://prove2.me/submissions/900284ea-51c7-4187-80b2-eb2bfc31cb34

-- Generated proof for MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono.
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

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/-!
# Finite-dimensional operator estimates for state-dependent distance

This module contains finite-dimensional operator and finite-sum identities used
by the paper-facing distance theorems. It introduces no new mathematical
assumptions or source-facing statements.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-395`
- `references/ldt-paper/preliminaries.tex:649-666`
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

theorem solution {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {S T : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hST : S ≤ T) (v : EuclideanSpace ℂ ι) :
    (inner ℂ v (_root_.MIPStarRE.QPBT.applyOperatorToState S v)).re ≤
      (inner ℂ v (_root_.MIPStarRE.QPBT.applyOperatorToState T v)).re := by
  have hpsd : (T - S).PosSemidef := Matrix.le_iff.mp hST
  have hnonneg := hpsd.dotProduct_mulVec_nonneg v
  have hdiff : 0 ≤ (inner ℂ v (_root_.MIPStarRE.QPBT.applyOperatorToState (T - S) v)).re := by
    simp only [_root_.MIPStarRE.QPBT.applyOperatorToState, Matrix.toEuclideanLin,
      Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct]
    rw [dotProduct_comm]
    exact (Complex.nonneg_iff.mp hnonneg).1
  rw [show T = S + (T - S) by abel]
  simp only [_root_.MIPStarRE.QPBT.applyOperatorToState, map_add, LinearMap.add_apply, inner_add_right,
    Complex.add_re]
  exact le_add_of_nonneg_right hdiff
