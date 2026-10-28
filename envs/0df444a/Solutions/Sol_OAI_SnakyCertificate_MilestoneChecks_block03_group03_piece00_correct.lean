-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block03_group03_piece00_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T07:58:23.462849+00:00
-- url     : https://prove2.me/submissions/e66443c8-5034-4d39-bab7-8bd28d75fae8

import Definitions.Def_Snaky35Cache03
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_group00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_group01_piece00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks
theorem entry_chunk_5 (j : ℕ) (hj : j < 20) : entryAt (106 + j) = tableChunk_5[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.1) j hj
theorem row_4 : rowAt 4 = data_4 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_7 : rowAt 7 = data_7 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.1).1
theorem row_9 : rowAt 9 = data_9 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_58 : rowAt 58 = data_58 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_64 : rowAt 64 = data_64 := (OAI.SnakyCertificate.MilestoneChecks.block02_group00_correct.1).1
theorem row_105 : rowAt 105 = data_105 := (OAI.SnakyCertificate.MilestoneChecks.block03_group01_piece00_correct.2.1).1
theorem entry_120_checked : entryAt 120 = entry_120 := by
  rw [entry_chunk_5 14 (by decide)]
  decide +kernel
theorem row_120 : rowAt 120 = data_120 := by
  rw [rowAt, dif_neg (by decide : ¬ 120 < 6), entry_120_checked]
  change forkRow [placeRow ⟨4, 0, 4, 5⟩ (rowAt 4), placeRow ⟨58, 2, 5, 4⟩ (rowAt 58)] = data_120
  rw [row_4, row_58]
  apply row_ext <;> decide +kernel
theorem entry_good_120 : EntryGood 120 := by
  unfold EntryGood
  rw [entry_120_checked]
  decide +kernel
theorem good_120 : Good (rowAt 120) := by
  rw [row_120]
  unfold Good
  decide +kernel

theorem entry_121_checked : entryAt 121 = entry_121 := by
  rw [entry_chunk_5 15 (by decide)]
  decide +kernel
theorem row_121 : rowAt 121 = data_121 := by
  rw [rowAt, dif_neg (by decide : ¬ 121 < 6), entry_121_checked]
  change forkRow [placeRow ⟨9, 3, 4, 5⟩ (rowAt 9), placeRow ⟨7, 1, 5, 4⟩ (rowAt 7)] = data_121
  rw [row_9, row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_121 : EntryGood 121 := by
  unfold EntryGood
  rw [entry_121_checked]
  decide +kernel
theorem good_121 : Good (rowAt 121) := by
  rw [row_121]
  unfold Good
  decide +kernel

theorem entry_122_checked : entryAt 122 = entry_122 := by
  rw [entry_chunk_5 16 (by decide)]
  decide +kernel
theorem row_122 : rowAt 122 = data_122 := by
  rw [rowAt, dif_neg (by decide : ¬ 122 < 6), entry_122_checked]
  change forkRow [placeRow ⟨6, 6, 3, 3⟩ (rowAt 6), placeRow ⟨105, 1, 4, 5⟩ (rowAt 105)] = data_122
  rw [row_6, row_105]
  apply row_ext <;> decide +kernel
theorem entry_good_122 : EntryGood 122 := by
  unfold EntryGood
  rw [entry_122_checked]
  decide +kernel
theorem good_122 : Good (rowAt 122) := by
  rw [row_122]
  unfold Good
  decide +kernel

theorem entry_123_checked : entryAt 123 = entry_123 := by
  rw [entry_chunk_5 17 (by decide)]
  decide +kernel
theorem row_123 : rowAt 123 = data_123 := by
  rw [rowAt, dif_neg (by decide : ¬ 123 < 6), entry_123_checked]
  change forkRow [placeRow ⟨6, 6, 1, 3⟩ (rowAt 6), placeRow ⟨64, 2, 2, 5⟩ (rowAt 64)] = data_123
  rw [row_6, row_64]
  apply row_ext <;> decide +kernel
theorem entry_good_123 : EntryGood 123 := by
  unfold EntryGood
  rw [entry_123_checked]
  decide +kernel
theorem good_123 : Good (rowAt 123) := by
  rw [row_123]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks.S213
theorem solution : (rowAt 120 = data_120 ∧ Good (rowAt 120) ∧ EntryGood 120) ∧ (rowAt 121 = data_121 ∧ Good (rowAt 121) ∧ EntryGood 121) ∧ (rowAt 122 = data_122 ∧ Good (rowAt 122) ∧ EntryGood 122) ∧ (rowAt 123 = data_123 ∧ Good (rowAt 123) ∧ EntryGood 123) ∧ True := by
  exact ⟨⟨row_120, good_120, entry_good_120⟩, ⟨row_121, good_121, entry_good_121⟩, ⟨row_122, good_122, entry_good_122⟩, ⟨row_123, good_123, entry_good_123⟩, trivial⟩
