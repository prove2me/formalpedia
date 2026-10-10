-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block01_group03_piece00_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T14:16:47.995698+00:00
-- url     : https://prove2.me/submissions/8dd37241-53d8-4cf3-a877-4df34afb3d74

import Definitions.Def_Snaky35Cache01
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_group02_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_2 (j : ℕ) (hj : j < 20) : entryAt (46 + j) = tableChunk_2[j]?.getD emptyEntry := (chunk_lookups.2.2.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.1).1
theorem row_4 : rowAt 4 = data_4 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_7 : rowAt 7 = data_7 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.1).1
theorem row_14 : rowAt 14 = data_14 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_49 : rowAt 49 = data_49 := (OAI.SnakyCertificate.MilestoneChecks.block01_group02_correct.2.1).1
theorem row_50 : rowAt 50 = data_50 := (OAI.SnakyCertificate.MilestoneChecks.block01_group02_correct.2.2.1).1
theorem row_53 : rowAt 53 = data_53 := (OAI.SnakyCertificate.MilestoneChecks.block01_group02_correct.2.2.2.2.2.1).1
theorem entry_56_checked : entryAt 56 = entry_56 := by
  rw [entry_chunk_2 10 (by decide)]
  decide +kernel
theorem row_56 : rowAt 56 = data_56 := by
  rw [rowAt, dif_neg (by decide : ¬ 56 < 6), entry_56_checked]
  change forkRow [placeRow ⟨7, 4, 0, 5⟩ (rowAt 7), placeRow ⟨7, 6, 0, 3⟩ (rowAt 7)] = data_56
  rw [row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_56 : EntryGood 56 := by
  unfold EntryGood
  rw [entry_56_checked]
  decide +kernel
theorem good_56 : Good (rowAt 56) := by
  rw [row_56]
  unfold Good
  decide +kernel

theorem entry_57_checked : entryAt 57 = entry_57 := by
  rw [entry_chunk_2 11 (by decide)]
  decide +kernel
theorem row_57 : rowAt 57 = data_57 := by
  rw [rowAt, dif_neg (by decide : ¬ 57 < 6), entry_57_checked]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (rowAt 0), placeRow ⟨7, 0, 4, 5⟩ (rowAt 7)] = data_57
  rw [row_0, row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_57 : EntryGood 57 := by
  unfold EntryGood
  rw [entry_57_checked]
  decide +kernel
theorem good_57 : Good (rowAt 57) := by
  rw [row_57]
  unfold Good
  decide +kernel

theorem entry_58_checked : entryAt 58 = entry_58 := by
  rw [entry_chunk_2 12 (by decide)]
  decide +kernel
theorem row_58 : rowAt 58 = data_58 := by
  rw [rowAt, dif_neg (by decide : ¬ 58 < 6), entry_58_checked]
  change forkRow [placeRow ⟨0, 4, 5, 4⟩ (rowAt 0), placeRow ⟨7, 0, 4, 5⟩ (rowAt 7)] = data_58
  rw [row_0, row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_58 : EntryGood 58 := by
  unfold EntryGood
  rw [entry_58_checked]
  decide +kernel
theorem good_58 : Good (rowAt 58) := by
  rw [row_58]
  unfold Good
  decide +kernel

theorem entry_59_checked : entryAt 59 = entry_59 := by
  rw [entry_chunk_2 13 (by decide)]
  decide +kernel
theorem row_59 : rowAt 59 = data_59 := by
  rw [rowAt, dif_neg (by decide : ¬ 59 < 6), entry_59_checked]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (rowAt 0), placeRow ⟨7, 4, 0, 5⟩ (rowAt 7)] = data_59
  rw [row_0, row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_59 : EntryGood 59 := by
  unfold EntryGood
  rw [entry_59_checked]
  decide +kernel
theorem good_59 : Good (rowAt 59) := by
  rw [row_59]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 56 = data_56 ∧ Good (rowAt 56) ∧ EntryGood 56) ∧ (rowAt 57 = data_57 ∧ Good (rowAt 57) ∧ EntryGood 57) ∧ (rowAt 58 = data_58 ∧ Good (rowAt 58) ∧ EntryGood 58) ∧ (rowAt 59 = data_59 ∧ Good (rowAt 59) ∧ EntryGood 59) ∧ True := by
  exact ⟨⟨row_56, good_56, entry_good_56⟩, ⟨row_57, good_57, entry_good_57⟩, ⟨row_58, good_58, entry_good_58⟩, ⟨row_59, good_59, entry_good_59⟩, trivial⟩
