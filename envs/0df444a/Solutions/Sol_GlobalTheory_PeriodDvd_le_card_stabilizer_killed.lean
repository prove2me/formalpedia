-- Prove2me | solution 1 for GlobalTheory.PeriodDvd.le_card_stabilizer_killed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:22:51.29266+00:00
-- url     : https://prove2.me/submissions/7bd06710-4a3c-4e39-a09f-8bf570e56437

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardDvdSumOfInvariantOfCardStabilizerDvd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvdOfPeriodOfDvdSumPowersetCard
import Theorems.Thm_GlobalTheory_PeriodDvd_mem_killed
import Theorems.Thm_GlobalTheory_PeriodDvd_card_killed
import Theorems.Thm_GlobalTheory_PeriodDvd_mem_iff_mem_killed
import Theorems.Thm_GlobalTheory_PeriodDvd_vadd_killed_subset
import Theorems.Thm_GlobalTheory_PeriodDvd_card_stabilizer_dvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Pointwise
open GlobalTheory
open GlobalTheory.PeriodDvd
namespace GlobalTheory.PeriodDvd
theorem _root_.solution {d : ℕ} [NeZero d] {s e : ℕ} (h : s * e = d) :
    s ∣ Nat.card (AddAction.stabilizer (ZMod d) (killed d s)) := by
  obtain ⟨e', he'⟩ := card_stabilizer_dvd (killed d s)
  have h1 : killed d s ⊆ killed d (Nat.card (AddAction.stabilizer (ZMod d) (killed d s))) := by
    intro y hy
    rw [← mem_iff_mem_killed, AddAction.mem_stabilizer_iff]
    refine Finset.eq_of_subset_of_card_le ?_ (by rw [Finset.card_vadd_finset])
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_vadd_finset.mp hz
    rw [mem_killed] at *
    rw [vadd_eq_add, nsmul_add, hy, hw, add_zero]
  have h2 := vadd_killed_subset (killed d s) (x := 0) (by simp [mem_killed])
  have h3 := Finset.card_le_card h1
  have h4 := Finset.card_le_card h2
  rw [Finset.card_vadd_finset] at h4
  rw [card_killed h, card_killed he'.symm] at h3 h4
  exact dvd_of_eq (le_antisymm h3 h4)
end GlobalTheory.PeriodDvd
