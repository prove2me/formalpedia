-- Prove2me | solution 1 for GlobalTheory.taylorTail_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:50:42.751245+00:00
-- url     : https://prove2.me/submissions/8cfa6b77-76c4-4ff0-a1a5-c89481562e40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormLeLintegralTaylorTailIteratedDeriv
import Theorems.Thm_GlobalTheory_taylorTail_step_one
import Theorems.Thm_GlobalTheory_taylorTail_tonelli

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set Module
open scoped ENNReal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (h : ℝ → F) (m : ℕ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hlim : ∀ j ≤ m, Tendsto (iteratedDeriv j h) atTop (𝓝 0)) :
    ENNReal.ofReal ‖h 0‖ ≤ ∫⁻ t in Ioi (0:ℝ),
      ENNReal.ofReal (t ^ m / (m.factorial : ℝ)) * ‖iteratedDeriv (m + 1) h t‖ₑ := by
  have hdiff : ∀ n : ℕ, Differentiable ℝ (iteratedDeriv n h) := fun n =>
    hh.differentiable_iteratedDeriv n (by exact_mod_cast ENat.coe_lt_top n)
  have hcont : ∀ n : ℕ, Continuous (iteratedDeriv n h) := fun n => (hdiff n).continuous
  have key : ∀ j ≤ m, ENNReal.ofReal ‖h 0‖ ≤ ∫⁻ t in Ioi (0:ℝ),
      ENNReal.ofReal (t ^ j / (j.factorial : ℝ)) * ‖iteratedDeriv (j + 1) h t‖ₑ := by
    intro j
    induction j with
    | zero =>
      intro _
      have := taylorTail_step_one h 0 (hdiff 0) (by rw [← iteratedDeriv_one]; exact hcont 1)
        (by simpa using hlim 0 (Nat.zero_le _))
      simpa [iteratedDeriv_one] using this
    | succ j ih =>
      intro hj
      refine (ih (Nat.le_of_succ_le hj)).trans ?_
      calc ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ j / (j.factorial : ℝ)) * ‖iteratedDeriv (j + 1) h t‖ₑ
          ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ j / (j.factorial : ℝ)) *
              ∫⁻ s in Ioi t, ‖iteratedDeriv (j + 1 + 1) h s‖ₑ := by
            refine lintegral_mono (fun t => ?_)
            refine mul_le_mul_of_nonneg_left ?_ (zero_le')
            have := taylorTail_step_one (iteratedDeriv (j+1) h) t (hdiff _)
              (by rw [← iteratedDeriv_succ]; exact hcont _) (hlim (j+1) hj)
            simpa [iteratedDeriv_succ] using this
        _ = _ := taylorTail_tonelli _ ((hcont _).enorm.measurable) j
  exact key m le_rfl
end GlobalTheory
