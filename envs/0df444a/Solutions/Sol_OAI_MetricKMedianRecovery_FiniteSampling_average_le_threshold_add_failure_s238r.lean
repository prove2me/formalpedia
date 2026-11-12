-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.FiniteSampling.average_le_threshold_add_failure_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:25:01.183772+00:00
-- url     : https://prove2.me/submissions/3b6aa7e9-6408-4bed-8271-dca062f2d083

import Mathlib
import Definitions.Def_Q238L002

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Average
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace FiniteSampling

open scoped BigOperators

section Average
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

lemma average_mono {X Y : Ω → ℝ} (h : ∀ ω, X ω ≤ Y ω) : average X ≤ average Y :=
  Finset.expect_le_expect (fun ω _ => h ω)

end Average

end FiniteSampling
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BestFallback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FiniteSampling
variable {Ω Y : Type*} [Fintype Ω] [Nonempty Ω]

lemma average_le_threshold_add_failure_s238r_oai (X : Ω → ℝ) {B M : ℝ}
    (hB : 0 ≤ B) (hX : ∀ s, X s ≤ M) :
    average X ≤ B + probability (fun s => B < X s)*M := by
  classical
  unfold probability
  rw [← average_mul_const, ← average_const (Ω := Ω) B, ← average_add]
  apply average_mono
  intro s
  simp only [average_const]
  by_cases hs : B < X s
  · simpa [hs] using (hX s).trans (le_add_of_nonneg_left hB)
  · simp only [hs,ite_false, if_false,zero_mul,add_zero]
    exact le_of_not_gt hs

end MetricKMedianRecovery.FiniteSampling

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.FiniteSampling.average_le_threshold_add_failure_s238r_oai.{u_1} := @OAI.MetricKMedianRecovery.FiniteSampling.average_le_threshold_add_failure_s238r_oai.{u_1}
