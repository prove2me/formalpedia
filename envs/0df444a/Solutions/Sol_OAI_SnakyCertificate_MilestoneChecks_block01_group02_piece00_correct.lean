-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block01_group02_piece00_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T14:06:02.539267+00:00
-- url     : https://prove2.me/submissions/9f5fad1f-f027-4193-8ac5-d5ce8767d3d3

import Definitions.Def_Snaky35Cache01
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_2 (j : ℕ) (hj : j < 20) : entryAt (46 + j) = tableChunk_2[j]?.getD emptyEntry := (chunk_lookups.2.2.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.1).1
theorem row_3 : rowAt 3 = data_3 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.1).1
theorem row_4 : rowAt 4 = data_4 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_7 : rowAt 7 = data_7 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.1).1
theorem row_10 : rowAt 10 = data_10 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_22 : rowAt 22 = data_22 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_26 : rowAt 26 = data_26 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem entry_48_checked : entryAt 48 = entry_48 := by
  rw [entry_chunk_2 2 (by decide)]
  decide +kernel
theorem row_48 : rowAt 48 = data_48 := by
  rw [rowAt, dif_neg (by decide : ¬ 48 < 6), entry_48_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨6, 2, 8, 3⟩ (rowAt 6)] = data_48
  rw [row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_48 : EntryGood 48 := by
  unfold EntryGood
  rw [entry_48_checked]
  decide +kernel
theorem good_48 : Good (rowAt 48) := by
  rw [row_48]
  unfold Good
  decide +kernel

theorem entry_49_checked : entryAt 49 = entry_49 := by
  rw [entry_chunk_2 3 (by decide)]
  decide +kernel
theorem row_49 : rowAt 49 = data_49 := by
  rw [rowAt, dif_neg (by decide : ¬ 49 < 6), entry_49_checked]
  change forkRow [placeRow ⟨4, 7, 3, 1⟩ (rowAt 4), placeRow ⟨7, 1, 5, 4⟩ (rowAt 7)] = data_49
  rw [row_4, row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_49 : EntryGood 49 := by
  unfold EntryGood
  rw [entry_49_checked]
  decide +kernel
theorem good_49 : Good (rowAt 49) := by
  rw [row_49]
  unfold Good
  decide +kernel

theorem entry_50_checked : entryAt 50 = entry_50 := by
  rw [entry_chunk_2 4 (by decide)]
  decide +kernel
theorem row_50 : rowAt 50 = data_50 := by
  rw [rowAt, dif_neg (by decide : ¬ 50 < 6), entry_50_checked]
  change forkRow [placeRow ⟨6, 3, 3, 5⟩ (rowAt 6), placeRow ⟨7, 1, 5, 4⟩ (rowAt 7)] = data_50
  rw [row_6, row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_50 : EntryGood 50 := by
  unfold EntryGood
  rw [entry_50_checked]
  decide +kernel
theorem good_50 : Good (rowAt 50) := by
  rw [row_50]
  unfold Good
  decide +kernel

theorem entry_51_checked : entryAt 51 = entry_51 := by
  rw [entry_chunk_2 5 (by decide)]
  decide +kernel
theorem row_51 : rowAt 51 = data_51 := by
  rw [rowAt, dif_neg (by decide : ¬ 51 < 6), entry_51_checked]
  change forkRow [placeRow ⟨10, 2, 5, 3⟩ (rowAt 10), placeRow ⟨10, 0, 5, 4⟩ (rowAt 10), placeRow ⟨26, 2, 3, 4⟩ (rowAt 26), placeRow ⟨26, 0, 3, 3⟩ (rowAt 26)] = data_51
  rw [row_10, row_26]
  apply row_ext <;> decide +kernel
theorem entry_good_51 : EntryGood 51 := by
  unfold EntryGood
  rw [entry_51_checked]
  decide +kernel
theorem good_51 : Good (rowAt 51) := by
  rw [row_51]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 48 = data_48 ∧ Good (rowAt 48) ∧ EntryGood 48) ∧ (rowAt 49 = data_49 ∧ Good (rowAt 49) ∧ EntryGood 49) ∧ (rowAt 50 = data_50 ∧ Good (rowAt 50) ∧ EntryGood 50) ∧ (rowAt 51 = data_51 ∧ Good (rowAt 51) ∧ EntryGood 51) ∧ True := by
  exact ⟨⟨row_48, good_48, entry_good_48⟩, ⟨row_49, good_49, entry_good_49⟩, ⟨row_50, good_50, entry_good_50⟩, ⟨row_51, good_51, entry_good_51⟩, trivial⟩
