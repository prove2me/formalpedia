-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block00_group01_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T13:19:11.990983+00:00
-- url     : https://prove2.me/submissions/0596fd95-887a-4b0f-9bde-fe34187f9618

import Definitions.Def_Snaky35Cache00
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_group00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_0 (j : ℕ) (hj : j < 20) : entryAt (6 + j) = tableChunk_0[j]?.getD emptyEntry := (chunk_lookups.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_group00_correct.1).1
theorem row_2 : rowAt 2 = data_2 := (OAI.SnakyCertificate.MilestoneChecks.block00_group00_correct.2.2.1).1
theorem row_3 : rowAt 3 = data_3 := (OAI.SnakyCertificate.MilestoneChecks.block00_group00_correct.2.2.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_group00_correct.2.2.2.2.2.2.1).1
theorem entry_8_checked : entryAt 8 = entry_8 := by
  rw [entry_chunk_0 2 (by decide)]
  decide +kernel
theorem row_8 : rowAt 8 = data_8 := by
  rw [rowAt, dif_neg (by decide : ¬ 8 < 6), entry_8_checked]
  change forkRow [placeRow ⟨0, 4, 8, 3⟩ (rowAt 0), placeRow ⟨6, 4, 3, 4⟩ (rowAt 6)] = data_8
  rw [row_0, row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_8 : EntryGood 8 := by
  unfold EntryGood
  rw [entry_8_checked]
  decide +kernel
theorem good_8 : Good (rowAt 8) := by
  rw [row_8]
  unfold Good
  decide +kernel

theorem entry_9_checked : entryAt 9 = entry_9 := by
  rw [entry_chunk_0 3 (by decide)]
  decide +kernel
theorem row_9 : rowAt 9 = data_9 := by
  rw [rowAt, dif_neg (by decide : ¬ 9 < 6), entry_9_checked]
  change forkRow [placeRow ⟨0, 4, 5, 4⟩ (rowAt 0), placeRow ⟨6, 4, 0, 5⟩ (rowAt 6)] = data_9
  rw [row_0, row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_9 : EntryGood 9 := by
  unfold EntryGood
  rw [entry_9_checked]
  decide +kernel
theorem good_9 : Good (rowAt 9) := by
  rw [row_9]
  unfold Good
  decide +kernel

theorem entry_10_checked : entryAt 10 = entry_10 := by
  rw [entry_chunk_0 4 (by decide)]
  decide +kernel
theorem row_10 : rowAt 10 = data_10 := by
  rw [rowAt, dif_neg (by decide : ¬ 10 < 6), entry_10_checked]
  change forkRow [placeRow ⟨2, 0, 2, 3⟩ (rowAt 2), placeRow ⟨2, 6, 2, 4⟩ (rowAt 2)] = data_10
  rw [row_2]
  apply row_ext <;> decide +kernel
theorem entry_good_10 : EntryGood 10 := by
  unfold EntryGood
  rw [entry_10_checked]
  decide +kernel
theorem good_10 : Good (rowAt 10) := by
  rw [row_10]
  unfold Good
  decide +kernel

theorem entry_11_checked : entryAt 11 = entry_11 := by
  rw [entry_chunk_0 5 (by decide)]
  decide +kernel
theorem row_11 : rowAt 11 = data_11 := by
  rw [rowAt, dif_neg (by decide : ¬ 11 < 6), entry_11_checked]
  change forkRow [placeRow ⟨6, 4, 2, 5⟩ (rowAt 6), placeRow ⟨6, 6, 2, 3⟩ (rowAt 6)] = data_11
  rw [row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_11 : EntryGood 11 := by
  unfold EntryGood
  rw [entry_11_checked]
  decide +kernel
theorem good_11 : Good (rowAt 11) := by
  rw [row_11]
  unfold Good
  decide +kernel

theorem entry_12_checked : entryAt 12 = entry_12 := by
  rw [entry_chunk_0 6 (by decide)]
  decide +kernel
theorem row_12 : rowAt 12 = data_12 := by
  rw [rowAt, dif_neg (by decide : ¬ 12 < 6), entry_12_checked]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (rowAt 0), placeRow ⟨0, 0, 0, 3⟩ (rowAt 0)] = data_12
  rw [row_0]
  apply row_ext <;> decide +kernel
theorem entry_good_12 : EntryGood 12 := by
  unfold EntryGood
  rw [entry_12_checked]
  decide +kernel
theorem good_12 : Good (rowAt 12) := by
  rw [row_12]
  unfold Good
  decide +kernel

theorem entry_13_checked : entryAt 13 = entry_13 := by
  rw [entry_chunk_0 7 (by decide)]
  decide +kernel
theorem row_13 : rowAt 13 = data_13 := by
  rw [rowAt, dif_neg (by decide : ¬ 13 < 6), entry_13_checked]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (rowAt 6), placeRow ⟨6, 4, 0, 5⟩ (rowAt 6)] = data_13
  rw [row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_13 : EntryGood 13 := by
  unfold EntryGood
  rw [entry_13_checked]
  decide +kernel
theorem good_13 : Good (rowAt 13) := by
  rw [row_13]
  unfold Good
  decide +kernel

theorem entry_14_checked : entryAt 14 = entry_14 := by
  rw [entry_chunk_0 8 (by decide)]
  decide +kernel
theorem row_14 : rowAt 14 = data_14 := by
  rw [rowAt, dif_neg (by decide : ¬ 14 < 6), entry_14_checked]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (rowAt 0), placeRow ⟨3, 6, 1, 4⟩ (rowAt 3)] = data_14
  rw [row_0, row_3]
  apply row_ext <;> decide +kernel
theorem entry_good_14 : EntryGood 14 := by
  unfold EntryGood
  rw [entry_14_checked]
  decide +kernel
theorem good_14 : Good (rowAt 14) := by
  rw [row_14]
  unfold Good
  decide +kernel

theorem entry_15_checked : entryAt 15 = entry_15 := by
  rw [entry_chunk_0 9 (by decide)]
  decide +kernel
theorem row_15 : rowAt 15 = data_15 := by
  rw [rowAt, dif_neg (by decide : ¬ 15 < 6), entry_15_checked]
  change forkRow [placeRow ⟨0, 6, 6, 4⟩ (rowAt 0), placeRow ⟨3, 6, 2, 4⟩ (rowAt 3)] = data_15
  rw [row_0, row_3]
  apply row_ext <;> decide +kernel
theorem entry_good_15 : EntryGood 15 := by
  unfold EntryGood
  rw [entry_15_checked]
  decide +kernel
theorem good_15 : Good (rowAt 15) := by
  rw [row_15]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 8 = data_8 ∧ Good (rowAt 8) ∧ EntryGood 8) ∧ (rowAt 9 = data_9 ∧ Good (rowAt 9) ∧ EntryGood 9) ∧ (rowAt 10 = data_10 ∧ Good (rowAt 10) ∧ EntryGood 10) ∧ (rowAt 11 = data_11 ∧ Good (rowAt 11) ∧ EntryGood 11) ∧ (rowAt 12 = data_12 ∧ Good (rowAt 12) ∧ EntryGood 12) ∧ (rowAt 13 = data_13 ∧ Good (rowAt 13) ∧ EntryGood 13) ∧ (rowAt 14 = data_14 ∧ Good (rowAt 14) ∧ EntryGood 14) ∧ (rowAt 15 = data_15 ∧ Good (rowAt 15) ∧ EntryGood 15) ∧ True := by
  exact ⟨⟨row_8, good_8, entry_good_8⟩, ⟨row_9, good_9, entry_good_9⟩, ⟨row_10, good_10, entry_good_10⟩, ⟨row_11, good_11, entry_good_11⟩, ⟨row_12, good_12, entry_good_12⟩, ⟨row_13, good_13, entry_good_13⟩, ⟨row_14, good_14, entry_good_14⟩, ⟨row_15, good_15, entry_good_15⟩, trivial⟩
