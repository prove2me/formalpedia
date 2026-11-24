-- Prove2me | solution 1 for GlobalTheory.PMonE.LinCount.glCount_of_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:11:31.1506+00:00
-- url     : https://prove2.me/submissions/df757c87-4112-4450-8ba5-18132dbacd38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemIntegralSolutionCountOfOrderOne
import Theorems.Thm_GlobalTheory_PMonE_LinCount_lin_normal
import Theorems.Thm_GlobalTheory_PMonE_LinCount_lin_det
import Theorems.Thm_GlobalTheory_PMonE_LinCount_card_lin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE GlobalTheory.PMonE.LinCount
open Finset GlobalTheory.PMonE
variable {F : Type*} [NormedField F] {m : Type*} [Fintype m] [DecidableEq m]
namespace GlobalTheory.PMonE.LinCount
theorem _root_.solution : ∀ N : ℕ, 1 ≤ N → GLCount 1 → GLCount N := by
  intro N hN h1 F _ _ _ _ p _ _ m _ _ e D he hD M hM hdet
  obtain ⟨K, rfl⟩ : ∃ K, N = K + 1 := ⟨N - 1, by omega⟩
  obtain ⟨E, rfl⟩ : ∃ E, D = K + (E + 1) := ⟨D - K - 1, by omega⟩
  rw [card_lin, h1 F p (Fin (K + 1) × m) e (E + 1) he (by omega) (lin K M) (lin_normal K M hM) (lin_det K M hdet)]
  simp [mul_comm]
end GlobalTheory.PMonE.LinCount
