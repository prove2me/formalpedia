-- Prove2me | solution 1 for MusicStreaming.CoreSelection.userCentric_axioms
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T17:04:10.268055+00:00
-- url     : https://prove2.me/submissions/249745b4-de11-49d3-9a43-c6e76e2f49f0

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_MusicStreaming_CoreSelection_Setting
import Theorems.Thm_MusicStreaming_Axioms_userCentric_axioms
import Theorems.Thm_MusicStreaming_CoreSelection_userCentric_reward_mem_core

set_option autoImplicit false

open MusicStreaming.CoreSelection

theorem solution (n : ℕ) :
    HomogeneityOn (userCentric (n := n)) ∧ AdditivityOn (userCentric (n := n)) ∧
      CoreSelectionOn (userCentric (n := n)) := by
  obtain ⟨-, hH, hA, -⟩ := MusicStreaming.Axioms.userCentric_axioms (n := n)
  exact ⟨fun t i i' c _ hc h => hH t i i' c hc h, fun t₁ t₂ _ _ hd => hA t₁ t₂ hd,
    fun t _ => userCentric_reward_mem_core n t⟩
