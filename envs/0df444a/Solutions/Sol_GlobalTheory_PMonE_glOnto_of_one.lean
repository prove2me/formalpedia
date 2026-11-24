-- Prove2me | solution 1 for GlobalTheory.PMonE.glOnto_of_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:08:39.889795+00:00
-- url     : https://prove2.me/submissions/8aa0b15b-63df-4f6b-ab3b-504403c88686

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemIntegralSurjectivityOfOne
import Theorems.Thm_GlobalTheory_PMonE_glOnto_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset Matrix
namespace GlobalTheory.PMonE
theorem _root_.solution : ∀ N : ℕ, 1 ≤ N → GLOnto 1 → GLOnto N := by
  intro N hN H
  induction N, hN using Nat.le_induction with
  | base => exact H
  | succ n hn ih =>
    obtain ⟨K, rfl⟩ : ∃ K, n = K + 1 := ⟨n - 1, by omega⟩
    exact glOnto_succ K ih
end GlobalTheory.PMonE
