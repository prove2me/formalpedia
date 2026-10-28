-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block06_group01_piece01_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T08:52:04.6174+00:00
-- url     : https://prove2.me/submissions/5b3d5e21-4277-4af6-88b4-1807aa4bcb5e

import Definitions.Def_Snaky35Cache06
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_group03_piece01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_group00_piece01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_group00_piece01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_group01_piece00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks
theorem entry_chunk_9 (j : ℕ) (hj : j < 20) : entryAt (186 + j) = tableChunk_9[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.1) j hj
theorem entry_chunk_10 (j : ℕ) (hj : j < 20) : entryAt (206 + j) = tableChunk_10[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_2 : rowAt 2 = data_2 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.1).1
theorem row_4 : rowAt 4 = data_4 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.1).1
theorem row_28 : rowAt 28 = data_28 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_127 : rowAt 127 = data_127 := (OAI.SnakyCertificate.MilestoneChecks.block03_group03_piece01_correct.2.2.2.1).1
theorem row_135 : rowAt 135 = data_135 := (OAI.SnakyCertificate.MilestoneChecks.block04_group00_piece01_correct.2.2.2.1).1
theorem row_166 : rowAt 166 = data_166 := (OAI.SnakyCertificate.MilestoneChecks.block05_group00_piece01_correct.2.2.1).1
theorem row_168 : rowAt 168 = data_168 := (OAI.SnakyCertificate.MilestoneChecks.block05_group01_piece00_correct.1).1
theorem entry_204_checked : entryAt 204 = entry_204 := by
  rw [entry_chunk_9 18 (by decide)]
  decide +kernel
theorem row_204 : rowAt 204 = data_204 := by
  rw [rowAt, dif_neg (by decide : ¬ 204 < 6), entry_204_checked]
  change forkRow [placeRow ⟨2, 5, 4, 2⟩ (rowAt 2), placeRow ⟨166, 2, 5, 3⟩ (rowAt 166)] = data_204
  rw [row_2, row_166]
  apply row_ext <;> decide +kernel
theorem entry_good_204 : EntryGood 204 := by
  unfold EntryGood
  rw [entry_204_checked]
  decide +kernel
theorem good_204 : Good (rowAt 204) := by
  rw [row_204]
  unfold Good
  decide +kernel

theorem entry_205_checked : entryAt 205 = entry_205 := by
  rw [entry_chunk_9 19 (by decide)]
  decide +kernel
theorem row_205 : rowAt 205 = data_205 := by
  rw [rowAt, dif_neg (by decide : ¬ 205 < 6), entry_205_checked]
  change forkRow [placeRow ⟨4, 1, 4, 3⟩ (rowAt 4), placeRow ⟨168, 0, 3, 4⟩ (rowAt 168)] = data_205
  rw [row_4, row_168]
  apply row_ext <;> decide +kernel
theorem entry_good_205 : EntryGood 205 := by
  unfold EntryGood
  rw [entry_205_checked]
  decide +kernel
theorem good_205 : Good (rowAt 205) := by
  rw [row_205]
  unfold Good
  decide +kernel

theorem entry_206_checked : entryAt 206 = entry_206 := by
  rw [entry_chunk_10 0 (by decide)]
  decide +kernel
theorem row_206 : rowAt 206 = data_206 := by
  rw [rowAt, dif_neg (by decide : ¬ 206 < 6), entry_206_checked]
  change forkRow [placeRow ⟨28, 3, 4, 5⟩ (rowAt 28), placeRow ⟨135, 2, 8, 4⟩ (rowAt 135)] = data_206
  rw [row_28, row_135]
  apply row_ext <;> decide +kernel
theorem entry_good_206 : EntryGood 206 := by
  unfold EntryGood
  rw [entry_206_checked]
  decide +kernel
theorem good_206 : Good (rowAt 206) := by
  rw [row_206]
  unfold Good
  decide +kernel

theorem entry_207_checked : entryAt 207 = entry_207 := by
  rw [entry_chunk_10 1 (by decide)]
  decide +kernel
theorem row_207 : rowAt 207 = data_207 := by
  rw [rowAt, dif_neg (by decide : ¬ 207 < 6), entry_207_checked]
  change forkRow [placeRow ⟨28, 3, 4, 5⟩ (rowAt 28), placeRow ⟨127, 0, 8, 4⟩ (rowAt 127)] = data_207
  rw [row_28, row_127]
  apply row_ext <;> decide +kernel
theorem entry_good_207 : EntryGood 207 := by
  unfold EntryGood
  rw [entry_207_checked]
  decide +kernel
theorem good_207 : Good (rowAt 207) := by
  rw [row_207]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks.S213
theorem solution : (rowAt 204 = data_204 ∧ Good (rowAt 204) ∧ EntryGood 204) ∧ (rowAt 205 = data_205 ∧ Good (rowAt 205) ∧ EntryGood 205) ∧ (rowAt 206 = data_206 ∧ Good (rowAt 206) ∧ EntryGood 206) ∧ (rowAt 207 = data_207 ∧ Good (rowAt 207) ∧ EntryGood 207) ∧ True := by
  exact ⟨⟨row_204, good_204, entry_good_204⟩, ⟨row_205, good_205, entry_good_205⟩, ⟨row_206, good_206, entry_good_206⟩, ⟨row_207, good_207, entry_good_207⟩, trivial⟩
