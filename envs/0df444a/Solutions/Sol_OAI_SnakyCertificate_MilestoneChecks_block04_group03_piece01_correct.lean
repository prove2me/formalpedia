-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block04_group03_piece01_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T08:27:26.290635+00:00
-- url     : https://prove2.me/submissions/0b60557d-11d1-4feb-8a90-a2ab79a382d2

import Definitions.Def_Snaky35Cache04
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_group00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_group00_piece00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks
theorem entry_chunk_7 (j : ℕ) (hj : j < 20) : entryAt (146 + j) = tableChunk_7[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.1) j hj
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_7 : rowAt 7 = data_7 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.1).1
theorem row_11 : rowAt 11 = data_11 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_33 : rowAt 33 = data_33 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.1).1
theorem row_45 : rowAt 45 = data_45 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_46 : rowAt 46 = data_46 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_57 : rowAt 57 = data_57 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_65 : rowAt 65 = data_65 := (OAI.SnakyCertificate.MilestoneChecks.block02_group00_correct.2.1).1
theorem row_66 : rowAt 66 = data_66 := (OAI.SnakyCertificate.MilestoneChecks.block02_group00_correct.2.2.1).1
theorem row_98 : rowAt 98 = data_98 := (OAI.SnakyCertificate.MilestoneChecks.block03_group00_piece00_correct.2.2.1).1
theorem entry_156_checked : entryAt 156 = entry_156 := by
  rw [entry_chunk_7 10 (by decide)]
  decide +kernel
theorem row_156 : rowAt 156 = data_156 := by
  rw [rowAt, dif_neg (by decide : ¬ 156 < 6), entry_156_checked]
  change forkRow [placeRow ⟨11, 0, 2, 4⟩ (rowAt 11), placeRow ⟨98, 2, 2, 4⟩ (rowAt 98), placeRow ⟨33, 0, 2, 3⟩ (rowAt 33)] = data_156
  rw [row_11, row_98, row_33]
  apply row_ext <;> decide +kernel
theorem entry_good_156 : EntryGood 156 := by
  unfold EntryGood
  rw [entry_156_checked]
  decide +kernel
theorem good_156 : Good (rowAt 156) := by
  rw [row_156]
  unfold Good
  decide +kernel

theorem entry_157_checked : entryAt 157 = entry_157 := by
  rw [entry_chunk_7 11 (by decide)]
  decide +kernel
theorem row_157 : rowAt 157 = data_157 := by
  rw [rowAt, dif_neg (by decide : ¬ 157 < 6), entry_157_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨57, 1, 5, 6⟩ (rowAt 57)] = data_157
  rw [row_6, row_57]
  apply row_ext <;> decide +kernel
theorem entry_good_157 : EntryGood 157 := by
  unfold EntryGood
  rw [entry_157_checked]
  decide +kernel
theorem good_157 : Good (rowAt 157) := by
  rw [row_157]
  unfold Good
  decide +kernel

theorem entry_158_checked : entryAt 158 = entry_158 := by
  rw [entry_chunk_7 12 (by decide)]
  decide +kernel
theorem row_158 : rowAt 158 = data_158 := by
  rw [rowAt, dif_neg (by decide : ¬ 158 < 6), entry_158_checked]
  change forkRow [placeRow ⟨66, 0, 3, 4⟩ (rowAt 66), placeRow ⟨45, 1, 4, 5⟩ (rowAt 45), placeRow ⟨46, 3, 4, 5⟩ (rowAt 46)] = data_158
  rw [row_66, row_45, row_46]
  apply row_ext <;> decide +kernel
theorem entry_good_158 : EntryGood 158 := by
  unfold EntryGood
  rw [entry_158_checked]
  decide +kernel
theorem good_158 : Good (rowAt 158) := by
  rw [row_158]
  unfold Good
  decide +kernel

theorem entry_159_checked : entryAt 159 = entry_159 := by
  rw [entry_chunk_7 13 (by decide)]
  decide +kernel
theorem row_159 : rowAt 159 = data_159 := by
  rw [rowAt, dif_neg (by decide : ¬ 159 < 6), entry_159_checked]
  change forkRow [placeRow ⟨45, 3, 4, 5⟩ (rowAt 45), placeRow ⟨65, 1, 4, 5⟩ (rowAt 65), placeRow ⟨7, 3, 3, 4⟩ (rowAt 7)] = data_159
  rw [row_45, row_65, row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_159 : EntryGood 159 := by
  unfold EntryGood
  rw [entry_159_checked]
  decide +kernel
theorem good_159 : Good (rowAt 159) := by
  rw [row_159]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks.S213
theorem solution : (rowAt 156 = data_156 ∧ Good (rowAt 156) ∧ EntryGood 156) ∧ (rowAt 157 = data_157 ∧ Good (rowAt 157) ∧ EntryGood 157) ∧ (rowAt 158 = data_158 ∧ Good (rowAt 158) ∧ EntryGood 158) ∧ (rowAt 159 = data_159 ∧ Good (rowAt 159) ∧ EntryGood 159) ∧ True := by
  exact ⟨⟨row_156, good_156, entry_good_156⟩, ⟨row_157, good_157, entry_good_157⟩, ⟨row_158, good_158, entry_good_158⟩, ⟨row_159, good_159, entry_good_159⟩, trivial⟩
