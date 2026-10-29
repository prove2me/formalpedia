-- Prove2me | solution 1 for MIPStarRE.QPBT.consistencyDefect_outcome_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:28:35.375682+00:00
-- url     : https://prove2.me/submissions/f2eb0987-b765-41ed-91d7-7a6551731a05

-- Generated proof for MIPStarRE.QPBT.consistencyDefect_outcome_equiv.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
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
import Definitions.Def_QPBT_QPBT_Games_Consistency

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-! # State-dependent consistency and strategy closeness

The definitions are the finite-dimensional forms of blueprint
`def:consistency` and `def:strategy-distance`,
from `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:219-288`.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

theorem solution
    {X Alpha Beta iota : Type*}
    [Fintype X] [DecidableEq X]
    [Fintype Alpha] [DecidableEq Alpha]
    [Fintype Beta] [DecidableEq Beta]
    [Fintype iota] [DecidableEq iota]
    (mu : _root_.LIDT.MIPStarRE.LDT.Distribution X) (e : Beta ≃ Alpha)
    (A B : X → Alpha → _root_.LIDT.MIPStarRE.Quantum.Op iota) (psi : EuclideanSpace ℂ iota) :
    _root_.MIPStarRE.QPBT.consistencyDefect mu
        (fun x b => A x (e b)) (fun x b => B x (e b)) psi =
      _root_.MIPStarRE.QPBT.consistencyDefect mu A B psi := by
  unfold _root_.MIPStarRE.QPBT.consistencyDefect
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro x
  let term : Alpha → Alpha → ℝ := fun a b =>
    if a = b then 0 else
      (inner ℂ psi ((EuclideanSpace.equiv iota ℂ).symm
        (((A x a) * (B x b)).mulVec psi))).re
  calc
    _ = ∑ a : Beta, ∑ b : Beta, term (e a) (e b) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      unfold term
      by_cases hab : a = b
      · subst b
        simp
      · have heab : e a ≠ e b := fun h => hab (e.injective h)
        simp [hab, heab]
    _ =
        ∑ a : Beta, ∑ b : Alpha, term (e a) b := by
      apply Finset.sum_congr rfl
      intro a _
      exact Equiv.sum_comp e (fun b => term (e a) b)
    _ = ∑ a : Alpha, ∑ b : Alpha, term a b :=
      Equiv.sum_comp e (fun a => ∑ b : Alpha, term a b)
    _ = _ := rfl
