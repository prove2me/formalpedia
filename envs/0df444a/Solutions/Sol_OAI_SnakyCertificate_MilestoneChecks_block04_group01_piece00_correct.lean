-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block04_group01_piece00_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T08:18:49.980063+00:00
-- url     : https://prove2.me/submissions/eb10b852-a5b1-461f-8773-f42a4b4bafec

import Definitions.Def_Snaky35Cache04
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_group00_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_group00_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks
theorem entry_chunk_6 (j : ℕ) (hj : j < 20) : entryAt (126 + j) = tableChunk_6[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.1) j hj
theorem row_4 : rowAt 4 = data_4 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_10 : rowAt 10 = data_10 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_27 : rowAt 27 = data_27 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_28 : rowAt 28 = data_28 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_96 : rowAt 96 = data_96 := (OAI.SnakyCertificate.MilestoneChecks.block03_group00_piece00_correct.1).1
theorem row_102 : rowAt 102 = data_102 := (OAI.SnakyCertificate.MilestoneChecks.block03_group00_piece01_correct.2.2.1).1
theorem entry_136_checked : entryAt 136 = entry_136 := by
  rw [entry_chunk_6 10 (by decide)]
  decide +kernel
theorem row_136 : rowAt 136 = data_136 := by
  rw [rowAt, dif_neg (by decide : ¬ 136 < 6), entry_136_checked]
  change forkRow [placeRow ⟨6, 3, 3, 7⟩ (rowAt 6), placeRow ⟨102, 2, 3, 3⟩ (rowAt 102)] = data_136
  rw [row_6, row_102]
  apply row_ext <;> decide +kernel
theorem entry_good_136 : EntryGood 136 := by
  unfold EntryGood
  rw [entry_136_checked]
  decide +kernel
theorem good_136 : Good (rowAt 136) := by
  rw [row_136]
  unfold Good
  decide +kernel

theorem entry_137_checked : entryAt 137 = entry_137 := by
  rw [entry_chunk_6 11 (by decide)]
  decide +kernel
theorem row_137 : rowAt 137 = data_137 := by
  rw [rowAt, dif_neg (by decide : ¬ 137 < 6), entry_137_checked]
  change forkRow [placeRow ⟨4, 1, 4, 3⟩ (rowAt 4), placeRow ⟨96, 0, 3, 4⟩ (rowAt 96)] = data_137
  rw [row_4, row_96]
  apply row_ext <;> decide +kernel
theorem entry_good_137 : EntryGood 137 := by
  unfold EntryGood
  rw [entry_137_checked]
  decide +kernel
theorem good_137 : Good (rowAt 137) := by
  rw [row_137]
  unfold Good
  decide +kernel

theorem entry_138_checked : entryAt 138 = entry_138 := by
  rw [entry_chunk_6 12 (by decide)]
  decide +kernel
theorem row_138 : rowAt 138 = data_138 := by
  rw [rowAt, dif_neg (by decide : ¬ 138 < 6), entry_138_checked]
  change forkRow [placeRow ⟨27, 0, 5, 4⟩ (rowAt 27), placeRow ⟨10, 1, 4, 7⟩ (rowAt 10)] = data_138
  rw [row_27, row_10]
  apply row_ext <;> decide +kernel
theorem entry_good_138 : EntryGood 138 := by
  unfold EntryGood
  rw [entry_138_checked]
  decide +kernel
theorem good_138 : Good (rowAt 138) := by
  rw [row_138]
  unfold Good
  decide +kernel

theorem entry_139_checked : entryAt 139 = entry_139 := by
  rw [entry_chunk_6 13 (by decide)]
  decide +kernel
theorem row_139 : rowAt 139 = data_139 := by
  rw [rowAt, dif_neg (by decide : ¬ 139 < 6), entry_139_checked]
  change forkRow [placeRow ⟨28, 1, 4, 5⟩ (rowAt 28), placeRow ⟨27, 0, 5, 4⟩ (rowAt 27)] = data_139
  rw [row_28, row_27]
  apply row_ext <;> decide +kernel
theorem entry_good_139 : EntryGood 139 := by
  unfold EntryGood
  rw [entry_139_checked]
  decide +kernel
theorem good_139 : Good (rowAt 139) := by
  rw [row_139]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks.S213
theorem solution : (rowAt 136 = data_136 ∧ Good (rowAt 136) ∧ EntryGood 136) ∧ (rowAt 137 = data_137 ∧ Good (rowAt 137) ∧ EntryGood 137) ∧ (rowAt 138 = data_138 ∧ Good (rowAt 138) ∧ EntryGood 138) ∧ (rowAt 139 = data_139 ∧ Good (rowAt 139) ∧ EntryGood 139) ∧ True := by
  exact ⟨⟨row_136, good_136, entry_good_136⟩, ⟨row_137, good_137, entry_good_137⟩, ⟨row_138, good_138, entry_good_138⟩, ⟨row_139, good_139, entry_good_139⟩, trivial⟩
