-- Prove2me | solution 1 for GlobalTheory.HilbertSamuelPS.val_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:51:22.838506+00:00
-- url     : https://prove2.me/submissions/b67096a8-fb4b-4747-a5c6-969954b6c81e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentOfDistinctValuationLikeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankLeCardValuesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankMulPowLeFinrankOfPowerSeries
import Theorems.Thm_P2M_GlobalTheory_HilbertSamuelPS_lexOrder_smul__030bc8312a06
import Theorems.Thm_GlobalTheory_HilbertSamuelPS_evalAt_smul
import Theorems.Thm_GlobalTheory_HilbertSamuelPS_firstIdx_spec
import Theorems.Thm_GlobalTheory_HilbertSamuelPS_val_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
open GlobalTheory.HilbertSamuelPS
open MvPowerSeries
variable {D n : ℕ} {A : Type} [CommRing A] [Algebra ℂ A]
  (φ : Fin n → (A →ₐ[ℂ] MvPowerSeries (Fin D) ℂ))
variable {φ}
namespace GlobalTheory.HilbertSamuelPS
theorem _root_.solution (c : ℂ) (u : A) (hc : c ≠ 0) : val φ (c • u) = val φ u := by
  by_cases h : ∃ k, evalAt φ k u ≠ 0
  · obtain ⟨h1, h2⟩ := firstIdx_spec φ h
    rw [val_eq φ (k := firstIdx φ u) (by rw [evalAt_smul]; exact smul_ne_zero hc h1)
      (fun i hi => by rw [evalAt_smul, h2 i hi, smul_zero]), evalAt_smul, lexOrder_smul' hc]
    rfl
  · push_neg at h
    have : ∀ k, evalAt φ k (c • u) = evalAt φ k u := fun k => by rw [evalAt_smul, h, smul_zero]
    have h' : ¬ ∃ k, evalAt φ k (c • u) ≠ 0 := by simpa [this] using h
    have h'' : ¬ ∃ k, evalAt φ k u ≠ 0 := by simpa using h
    unfold val firstIdx
    rw [dif_neg h', dif_neg h'', this]
end GlobalTheory.HilbertSamuelPS
