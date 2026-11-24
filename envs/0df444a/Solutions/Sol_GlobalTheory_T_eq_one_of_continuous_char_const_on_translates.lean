-- Prove2me | solution 1 for GlobalTheory.T.eq_one_of_continuous_char_const_on_translates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:13:13.010216+00:00
-- url     : https://prove2.me/submissions/2726e8cf-f603-47fb-bd07-f01ddc507c38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CharConstOnTranslatesTrivial
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CharConstOnTranslatesTrivialStatement
import Theorems.Thm_GlobalTheory_charConstOnTranslates_trivial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ψ : (ι → ℂˣ) →* ℂˣ) (θ : ι → ℂ) (T : Set (ι → ℝ)) (C : ℝ) (c : ℂˣ), Continuous ψ → (∀ i, (θ i).im ≠ 0) → (∀ y : ι → ℝ, ∃ a ∈ T, ‖a - y‖ ≤ C) → (∀ a ∈ T, ∀ z : ι → ℂˣ, (∀ i, (z i : ℂ) = a i + θ i) → ψ z = c) → ψ = 1 := by
  first | exact @GlobalTheory.charConstOnTranslates_trivial | exact GlobalTheory.charConstOnTranslates_trivial | (intros; apply GlobalTheory.charConstOnTranslates_trivial <;> assumption)
end _root_.GlobalTheory.T
