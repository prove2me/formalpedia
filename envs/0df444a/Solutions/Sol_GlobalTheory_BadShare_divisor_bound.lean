-- Prove2me | solution 1 for GlobalTheory.BadShare.divisor_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:25:54.614995+00:00
-- url     : https://prove2.me/submissions/f159d16c-2683-4da8-8e06-91c36ce81deb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MassDegTypeLeCycleTypeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassDivisorBound
import Theorems.Thm_GlobalTheory_BadShare_mass_true_le_one
import Theorems.Thm_GlobalTheory_BadShare_mass_dvd_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare
namespace GlobalTheory.BadShare
theorem _root_.solution : ∀ (g : ℕ) [Fact g.Prime], (∀ N : ℕ, (mass g N fun _ => True) ≤ 1) ∧
    ∀ (N a : ℕ), ∀ h ∈ sqSet g a, (mass g N fun f => h ∣ f) ≤ ((torusCard g h : ℝ))⁻¹ := by
  intro g _
  refine ⟨mass_true_le_one g, fun N a h hh => ?_⟩
  refine (mass_dvd_le g N a h hh).trans ?_
  exact mul_le_of_le_one_right (inv_nonneg.2 (Nat.cast_nonneg _)) (mass_true_le_one g _)
end GlobalTheory.BadShare
