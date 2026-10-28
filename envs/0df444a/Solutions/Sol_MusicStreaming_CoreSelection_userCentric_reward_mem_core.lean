-- Prove2me | solution 1 for MusicStreaming.CoreSelection.userCentric_reward_mem_core
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T17:04:11.043067+00:00
-- url     : https://prove2.me/submissions/3661cc33-a68d-48cb-bab6-4cf376b38e50

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_MusicStreaming_CoreSelection_Setting
import Theorems.Thm_MusicStreaming_Core_theorem_2
import Theorems.Thm_MusicStreaming_CoreSelection_userCentric_mem_allocSet

set_option autoImplicit false

open MusicStreaming.CoreSelection

theorem solution (n : ℕ) (t : MusicStreaming.Axioms.Problem n) :
    MusicStreaming.Axioms.reward userCentric t ∈
      Supermodularity.Cooperative.Core Finset.univ (MusicStreaming.Core.game t) := by
  rw [MusicStreaming.Core.theorem_2]
  exact userCentric_mem_allocSet n t
