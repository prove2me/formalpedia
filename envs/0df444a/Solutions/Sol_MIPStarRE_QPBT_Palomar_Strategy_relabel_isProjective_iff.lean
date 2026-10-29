-- Prove2me | solution 1 for MIPStarRE.QPBT.Palomar.Strategy.relabel_isProjective_iff
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:51:20.415505+00:00
-- url     : https://prove2.me/submissions/54d4573c-eb85-4977-90cb-565b4777d296

-- Generated proof for MIPStarRE.QPBT.Palomar.Strategy.relabel_isProjective_iff.
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
import Definitions.Def_QPBT_QPBT_Palomar_Definitions
import Definitions.Def_QPBT_QPBT_Palomar_LowDegreeGameStrategyBridge
import Mathlib

namespace MIPStarRE.QPBT.Palomar
end MIPStarRE.QPBT.Palomar
namespace MIPStarRE.QPBT.Palomar.Game
end MIPStarRE.QPBT.Palomar.Game
namespace MIPStarRE.QPBT.Palomar.POVM
end MIPStarRE.QPBT.Palomar.POVM
namespace MIPStarRE.QPBT.Palomar.Strategy
end MIPStarRE.QPBT.Palomar.Strategy

/- Source helpers from QPBT/Palomar/LowDegreeGameStrategyBridge.lean. -/
/-!
# Strategy bridge for the compact low individual degree game

This module transports compact strategies across the exact question and answer
equivalences of `LowDegreeGameBridge`.  The transported game is the existing
low-degree game, and every compact strategy has exactly the same Born value
after conversion through the Palomar foundation bridge.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-440`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT.Palomar

noncomputable section

namespace POVM





/-- Outcome relabeling preserves projectivity exactly. -/
theorem relabel_isProjective_iff {A B I : Type*} [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq I] (e : A ≃ B) (M : _root_.MIPStarRE.QPBT.Palomar.POVM A I) :
    (_root_.MIPStarRE.QPBT.Palomar.POVM.relabel e M).IsProjective ↔ M.IsProjective := by
  constructor
  · intro h a
    simpa using h (e a)
  · intro h b
    exact h (e.symm b)

end POVM













end

end MIPStarRE.QPBT.Palomar

/-!
# Strategy bridge for the compact low individual degree game

This module transports compact strategies across the exact question and answer
equivalences of `LowDegreeGameBridge`.  The transported game is the existing
low-degree game, and every compact strategy has exactly the same Born value
after conversion through the Palomar foundation bridge.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-440`.
-/



open scoped BigOperators

open MIPStarRE.QPBT.Palomar



open MIPStarRE.QPBT.Palomar.POVM









open MIPStarRE.QPBT.Palomar.Game







open MIPStarRE.QPBT.Palomar.Strategy

theorem solution {X Y A B X' Y' A' B' : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
    (S : _root_.MIPStarRE.QPBT.Palomar.Strategy X Y A B) (eX : X ≃ X') (eY : Y ≃ Y')
    (eA : A ≃ A') (eB : B ≃ B') :
    (_root_.MIPStarRE.QPBT.Palomar.Strategy.relabel S eX eY eA eB).IsProjective ↔ S.IsProjective := by
  constructor
  · rintro ⟨hA, hB⟩
    constructor
    · intro x
      have hx := hA (eX x)
      change (_root_.MIPStarRE.QPBT.Palomar.POVM.relabel eA (S.alice (eX.symm (eX x)))).IsProjective at hx
      rw [eX.symm_apply_apply] at hx
      exact (_root_.MIPStarRE.QPBT.Palomar.POVM.relabel_isProjective_iff eA (S.alice x)).mp hx
    · intro y
      have hy := hB (eY y)
      change (_root_.MIPStarRE.QPBT.Palomar.POVM.relabel eB (S.bob (eY.symm (eY y)))).IsProjective at hy
      rw [eY.symm_apply_apply] at hy
      exact (_root_.MIPStarRE.QPBT.Palomar.POVM.relabel_isProjective_iff eB (S.bob y)).mp hy
  · rintro ⟨hA, hB⟩
    constructor
    · intro x
      exact (_root_.MIPStarRE.QPBT.Palomar.POVM.relabel_isProjective_iff eA (S.alice (eX.symm x))).mpr
        (hA (eX.symm x))
    · intro y
      exact (_root_.MIPStarRE.QPBT.Palomar.POVM.relabel_isProjective_iff eB (S.bob (eY.symm y))).mpr
        (hB (eY.symm y))
