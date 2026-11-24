-- Prove2me | solution 1 for GlobalTheory.PerronPsi.harm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:24:37.520134+00:00
-- url     : https://prove2.me/submissions/37a7b752-7f94-4699-a129-58c6473cc311

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronPsi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.PerronPsi
namespace GlobalTheory.PerronPsi
theorem _root_.solution (N : ℕ) : ∑ k ∈ Finset.range (N + 1), 1 / (k : ℝ) ≤ 1 + Real.log N := by
  calc ∑ k ∈ Finset.range (N + 1), 1 / (k : ℝ) = (harmonic N : ℝ) := by
        rw [Finset.sum_range_succ']
        simp [harmonic]
    _ ≤ 1 + Real.log N := harmonic_le_one_add_log N
end GlobalTheory.PerronPsi
