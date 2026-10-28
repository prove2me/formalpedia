-- Prove2me | solution 1 for OAI.CriticalSK.critical_mixing_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:01:17.177542+00:00
-- url     : https://prove2.me/submissions/ca78404c-4dc3-4aaa-bd76-6bde8e6b8611

import Mathlib
import Definitions.Def_CriticalSKMixing
import Definitions.Def_OAIQ074C000
import Theorems.Thm_OAI_CriticalSK_critical_two_clock_mixing_s2

section
-- module Solutions.OAIQ074_CM.CriticalSK_Rayleigh
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

namespace CriticalSK

section

open Set Filter MeasureTheory ProbabilityTheory

variable {n : ℕ}

@[simp] lemma abs_spinValue (b : Bool) : |spinValue b| = 1 := by cases b <;> norm_num [spinValue]

end

open Set Filter MeasureTheory

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalMixing_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter

namespace CriticalSK

theorem critical_mixing_bounds_oai (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (disorderLaw n {W |
      (n : ℝ) ^ ((2 : ℝ) / 3 - ε) ≤ continuousMixingTime W ∧
      continuousMixingTime W ≤ Real.exp (ε * n)}).toReal) atTop (𝓝 1) ∧
    Tendsto (fun n : ℕ => (disorderLaw n {W |
      (n : ℝ) ^ ((5 : ℝ) / 3 - ε) ≤ (discreteMixingTime W : ℝ) ∧
      (discreteMixingTime W : ℝ) ≤ Real.exp (ε * n)}).toReal) atTop (𝓝 1) := by
  have hp := critical_two_clock_mixing_s2 ε hε
  constructor
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le hp tendsto_const_nhds
    · intro n
      refine measureReal_mono ?_
      intro W hW
      exact ⟨hW.1, hW.2.1⟩
    · intro n
      exact measureReal_le_one
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le hp tendsto_const_nhds
    · intro n
      refine measureReal_mono ?_
      intro W hW
      exact ⟨hW.2.2.1, hW.2.2.2⟩
    · intro n
      exact measureReal_le_one

end CriticalSK
end

end OAI
end

theorem solution : type_of% @OAI.CriticalSK.critical_mixing_bounds_oai := @OAI.CriticalSK.critical_mixing_bounds_oai
