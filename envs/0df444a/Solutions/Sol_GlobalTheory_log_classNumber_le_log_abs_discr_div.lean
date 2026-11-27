-- Prove2me | solution 1 for GlobalTheory.log_classNumber_le_log_abs_discr_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:42:08.287691+00:00
-- url     : https://prove2.me/submissions/f94a82dc-af02-4277-b10e-3a059e108759

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIdealInClassOfNormLeSqrtDiscr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LogClassNumberLeLogAbsDiscrDiv
import Theorems.Thm_GlobalTheory_classNumber_le_of_finrank_eq_two_mul
import Theorems.Thm_GlobalTheory_one_le_sqrt_abs_discr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
open NumberField
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (f : ℕ),
      Module.finrank ℚ E = 2*f →
      Real.log (classNumber E) ≤ f*(Real.log |(discr E : ℝ)|/(2*f)) +
        2*f*Real.log (1 + f*(Real.log |(discr E : ℝ)|/(2*f))) := by
  intro E _ _ _ f hf
  have hdeg : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hf0 : (f : ℝ) ≠ 0 := by
    have : f ≠ 0 := by
      rintro rfl
      omega
    exact_mod_cast this
  have key : (f : ℝ) * (Real.log |(discr E : ℝ)| / (2 * f)) = Real.log √|(discr E : ℝ)| := by
    rw [Real.log_sqrt (abs_nonneg _)]
    field_simp
  rw [key]
  have hb := _root_.GlobalTheory.classNumber_le_of_finrank_eq_two_mul E hf
  have hpos : (0 : ℝ) < classNumber E := by exact_mod_cast classNumber_pos E
  have hs : 1 ≤ √|(discr E : ℝ)| := _root_.GlobalTheory.one_le_sqrt_abs_discr E
  have hL : 0 ≤ Real.log √|(discr E : ℝ)| := Real.log_nonneg hs
  calc Real.log (classNumber E)
      ≤ Real.log (√|(discr E : ℝ)| * (1 + Real.log √|(discr E : ℝ)|) ^ (2 * f)) :=
        Real.log_le_log hpos hb
    _ = Real.log √|(discr E : ℝ)| + ((2 * f : ℕ) : ℝ) * Real.log (1 + Real.log √|(discr E : ℝ)|) := by
        rw [Real.log_mul (by linarith) (pow_ne_zero _ (by linarith)), Real.log_pow]
    _ = Real.log √|(discr E : ℝ)| + 2 * f * Real.log (1 + Real.log √|(discr E : ℝ)|) := by
        push_cast
        ring
end _root_.GlobalTheory
end GlobalTheory
