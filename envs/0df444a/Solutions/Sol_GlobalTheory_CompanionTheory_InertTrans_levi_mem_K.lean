-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertTrans.levi_mem_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:43:55.444741+00:00
-- url     : https://prove2.me/submissions/3523d7e6-2ecc-4858-8e52-d76d44e7fced

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SphericalTransitiveOfLevi
import Theorems.Thm_GlobalTheory_CompanionTheory_InertTrans_levi_off
import Theorems.Thm_Formalism_UG_P_fSatake_K_int
import Theorems.Thm_GlobalTheory_InertZeta_idx_cases
import Theorems.Thm_GlobalTheory_SatakeWeyl_mem_KU_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertTrans
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
namespace GlobalTheory.CompanionTheory.InertTrans
theorem _root_.solution {ϖ : L} {g : GU σ N} {m : GU σ (N + 2)} (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    (h : IsLeviElt ϖ 0 g m) (hg : g ∈ KU σ N) : m ∈ KU σ (N + 2) := by
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := levi_off h
  rw [mem_KU_iff hσ]
  intro i j
  rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl
  · rw [h.2.1, zpow_zero]; exact one_mem _
  · rw [o1]; exact zero_mem _
  · rw [o3]; exact zero_mem _
  · rw [o2]; exact zero_mem _
  · rw [h.2.2.2]; exact P.fSatake_K_int hg i j
  · rw [o5]; exact zero_mem _
  · rw [o4]; exact zero_mem _
  · rw [o6]; exact zero_mem _
  · rw [h.2.2.1, neg_zero, zpow_zero]; exact one_mem _
end GlobalTheory.CompanionTheory.InertTrans
