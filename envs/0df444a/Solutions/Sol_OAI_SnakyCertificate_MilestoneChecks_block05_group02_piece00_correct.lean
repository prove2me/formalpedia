-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block05_group02_piece00_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T08:37:48.11759+00:00
-- url     : https://prove2.me/submissions/5d268a40-fa88-495d-9d27-201fe3e76965

import Definitions.Def_Snaky35Cache05
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_group00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_group01_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_group02_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks
theorem entry_chunk_8 (j : ℕ) (hj : j < 20) : entryAt (166 + j) = tableChunk_8[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.1) j hj
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_37 : rowAt 37 = data_37 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.1).1
theorem row_46 : rowAt 46 = data_46 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_55 : rowAt 55 = data_55 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_64 : rowAt 64 = data_64 := (OAI.SnakyCertificate.MilestoneChecks.block02_group00_correct.1).1
theorem row_68 : rowAt 68 = data_68 := (OAI.SnakyCertificate.MilestoneChecks.block02_group00_correct.2.2.2.2.1).1
theorem row_136 : rowAt 136 = data_136 := (OAI.SnakyCertificate.MilestoneChecks.block04_group01_piece00_correct.1).1
theorem row_148 : rowAt 148 = data_148 := (OAI.SnakyCertificate.MilestoneChecks.block04_group02_piece01_correct.1).1
theorem entry_176_checked : entryAt 176 = entry_176 := by
  rw [entry_chunk_8 10 (by decide)]
  decide +kernel
theorem row_176 : rowAt 176 = data_176 := by
  rw [rowAt, dif_neg (by decide : ¬ 176 < 6), entry_176_checked]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨64, 6, 4, 5⟩ (rowAt 64), placeRow ⟨55, 2, 5, 4⟩ (rowAt 55)] = data_176
  rw [row_63, row_64, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_176 : EntryGood 176 := by
  unfold EntryGood
  rw [entry_176_checked]
  decide +kernel
theorem good_176 : Good (rowAt 176) := by
  rw [row_176]
  unfold Good
  decide +kernel

theorem entry_177_checked : entryAt 177 = entry_177 := by
  rw [entry_chunk_8 11 (by decide)]
  decide +kernel
theorem row_177 : rowAt 177 = data_177 := by
  rw [rowAt, dif_neg (by decide : ¬ 177 < 6), entry_177_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨136, 3, 5, 4⟩ (rowAt 136)] = data_177
  rw [row_6, row_136]
  apply row_ext <;> decide +kernel
theorem entry_good_177 : EntryGood 177 := by
  unfold EntryGood
  rw [entry_177_checked]
  decide +kernel
theorem good_177 : Good (rowAt 177) := by
  rw [row_177]
  unfold Good
  decide +kernel

theorem entry_178_checked : entryAt 178 = entry_178 := by
  rw [entry_chunk_8 12 (by decide)]
  decide +kernel
theorem row_178 : rowAt 178 = data_178 := by
  rw [rowAt, dif_neg (by decide : ¬ 178 < 6), entry_178_checked]
  change forkRow [placeRow ⟨37, 0, 3, 4⟩ (rowAt 37), placeRow ⟨68, 1, 4, 5⟩ (rowAt 68), placeRow ⟨46, 3, 4, 5⟩ (rowAt 46)] = data_178
  rw [row_37, row_68, row_46]
  apply row_ext <;> decide +kernel
theorem entry_good_178 : EntryGood 178 := by
  unfold EntryGood
  rw [entry_178_checked]
  decide +kernel
theorem good_178 : Good (rowAt 178) := by
  rw [row_178]
  unfold Good
  decide +kernel

theorem entry_179_checked : entryAt 179 = entry_179 := by
  rw [entry_chunk_8 13 (by decide)]
  decide +kernel
theorem row_179 : rowAt 179 = data_179 := by
  rw [rowAt, dif_neg (by decide : ¬ 179 < 6), entry_179_checked]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (rowAt 6), placeRow ⟨148, 5, 5, 4⟩ (rowAt 148)] = data_179
  rw [row_6, row_148]
  apply row_ext <;> decide +kernel
theorem entry_good_179 : EntryGood 179 := by
  unfold EntryGood
  rw [entry_179_checked]
  decide +kernel
theorem good_179 : Good (rowAt 179) := by
  rw [row_179]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks.S213
theorem solution : (rowAt 176 = data_176 ∧ Good (rowAt 176) ∧ EntryGood 176) ∧ (rowAt 177 = data_177 ∧ Good (rowAt 177) ∧ EntryGood 177) ∧ (rowAt 178 = data_178 ∧ Good (rowAt 178) ∧ EntryGood 178) ∧ (rowAt 179 = data_179 ∧ Good (rowAt 179) ∧ EntryGood 179) ∧ True := by
  exact ⟨⟨row_176, good_176, entry_good_176⟩, ⟨row_177, good_177, entry_good_177⟩, ⟨row_178, good_178, entry_good_178⟩, ⟨row_179, good_179, entry_good_179⟩, trivial⟩
