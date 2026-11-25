-- Prove2me | solution 1 for GlobalTheory.exists_dyadic_shell_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:10:56.347012+00:00
-- url     : https://prove2.me/submissions/68dbdbd5-80fe-494a-95fd-1a035df8ed00

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ShellSumElementaryInequalities
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDyadicShellIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (ep : ℝ) (hep : 0 < ep) :
    ∃ sh : ℝ → ℕ, (∀ s, s ≤ 2 ^ sh s * ep) ∧ ∀ s j, j < sh s → 2 ^ j * ep < s := by
  classical
  have hex : ∀ s : ℝ, ∃ n : ℕ, s ≤ 2 ^ n * ep := by
    intro s
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (s / ep) (by norm_num : (1 : ℝ) < 2)
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ hep] at hn
    exact hn.le
  refine ⟨fun s => Nat.find (hex s), fun s => Nat.find_spec (hex s), fun s j hj => ?_⟩
  exact not_le.mp (Nat.find_min (hex s) hj)
end GlobalTheory
