-- Prove2me | solution 1 for GlobalTheory.Cyc.LiftExp.one_add_pow_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:27:50.539008+00:00
-- url     : https://prove2.me/submissions/2c2cddba-2a1b-4c39-a881-6e7490e99ebc

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.LiftExp
variable {l : ℕ} [hl : Fact l.Prime]
namespace GlobalTheory.Cyc.LiftExp
theorem _root_.solution (x : ℚ_[l]) (hx : ‖x‖ ≤ 1) (n : ℕ) :
    ∃ r : ℚ_[l], ‖r‖ ≤ 1 ∧
      (1 + x) ^ n - 1 = n * x + ((n.choose 2 : ℕ) * x ^ 2 + x ^ 3 * r) := by
  induction n with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨r, hr, h⟩ := ih
    refine ⟨(n.choose 2 : ℕ) + (r + x * r), ?_, ?_⟩
    · refine (Padic.nonarchimedean _ _).trans (max_le ?_ ((Padic.nonarchimedean _ _).trans
        (max_le hr ?_)))
      · exact IsUltrametricDist.norm_natCast_le_one _ _
      · rw [norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hr
    · have h2 : (1 + x) ^ n = 1 + (n * x + ((n.choose 2 : ℕ) * x ^ 2 + x ^ 3 * r)) := by
        rw [← h]; ring
      rw [pow_succ, h2, Nat.choose_succ_succ' n 1, Nat.choose_one_right]
      push_cast
      ring
end GlobalTheory.Cyc.LiftExp
