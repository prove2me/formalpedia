-- Prove2me | solution 1 for MIPStarRE.QPBT.consistencyDefect_uniform_question_outcome_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:32:14.389126+00:00
-- url     : https://prove2.me/submissions/813e010e-ff64-410b-a48d-828d62883c24

-- Generated proof for MIPStarRE.QPBT.consistencyDefect_uniform_question_outcome_equiv.
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
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_outcome_equiv

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Games/Consistency.lean. -/
/-! # State-dependent consistency and strategy closeness

The definitions are the finite-dimensional forms of blueprint
`def:consistency` and `def:strategy-distance`,
from `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:219-288`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum



/-- A uniform consistency defect is invariant under a bijective relabeling of
its question type. -/
theorem consistencyDefect_uniform_question_equiv
    {X Y Outcome iota : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype iota] [DecidableEq iota]
    (e : X ≃ Y) (A B : Y → Outcome → _root_.LIDT.MIPStarRE.Quantum.Op iota)
    (psi : EuclideanSpace ℂ iota) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X)
        (fun x a => A (e x) a) (fun x a => B (e x) a) psi =
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y) A B psi := by
  unfold _root_.MIPStarRE.QPBT.consistencyDefect
  simpa using _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv e (fun x =>
    ∑ a : Outcome, ∑ b : Outcome,
      if a = b then 0 else
        (inner ℂ psi ((EuclideanSpace.equiv iota ℂ).symm
          (((A (e x) a) * (B (e x) b)).mulVec psi))).re)















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
    {X Y Alpha Beta iota : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype Alpha] [DecidableEq Alpha]
    [Fintype Beta] [DecidableEq Beta]
    [Fintype iota] [DecidableEq iota]
    (questionEquiv : X ≃ Y) (outcomeEquiv : Beta ≃ Alpha)
    (A B : Y → Alpha → _root_.LIDT.MIPStarRE.Quantum.Op iota) (psi : EuclideanSpace ℂ iota) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X)
        (fun x b => A (questionEquiv x) (outcomeEquiv b))
        (fun x b => B (questionEquiv x) (outcomeEquiv b)) psi =
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y) A B psi := by
  calc
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X)
        (fun x b => A (questionEquiv x) (outcomeEquiv b))
        (fun x b => B (questionEquiv x) (outcomeEquiv b)) psi =
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X)
        (fun x a => A (questionEquiv x) a)
        (fun x a => B (questionEquiv x) a) psi :=
      _root_.MIPStarRE.QPBT.consistencyDefect_outcome_equiv (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X)
        outcomeEquiv _ _ psi
    _ = _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y) A B psi :=
      _root_.MIPStarRE.QPBT.consistencyDefect_uniform_question_equiv questionEquiv A B psi
