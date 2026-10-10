-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block01_group00_piece00_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T13:58:32.667333+00:00
-- url     : https://prove2.me/submissions/5f022d7e-edca-4734-953a-734f2d0dc4b0

import Definitions.Def_Snaky35Cache01
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_1 (j : ℕ) (hj : j < 20) : entryAt (26 + j) = tableChunk_1[j]?.getD emptyEntry := (chunk_lookups.2.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.1).1
theorem row_1 : rowAt 1 = data_1 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.1).1
theorem row_2 : rowAt 2 = data_2 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.1).1
theorem row_3 : rowAt 3 = data_3 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_14 : rowAt 14 = data_14 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_16 : rowAt 16 = data_16 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_17 : rowAt 17 = data_17 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem entry_32_checked : entryAt 32 = entry_32 := by
  rw [entry_chunk_1 6 (by decide)]
  decide +kernel
theorem row_32 : rowAt 32 = data_32 := by
  rw [rowAt, dif_neg (by decide : ¬ 32 < 6), entry_32_checked]
  change forkRow [placeRow ⟨0, 4, 8, 3⟩ (rowAt 0), placeRow ⟨6, 3, 4, 5⟩ (rowAt 6)] = data_32
  rw [row_0, row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_32 : EntryGood 32 := by
  unfold EntryGood
  rw [entry_32_checked]
  decide +kernel
theorem good_32 : Good (rowAt 32) := by
  rw [row_32]
  unfold Good
  decide +kernel

theorem entry_33_checked : entryAt 33 = entry_33 := by
  rw [entry_chunk_1 7 (by decide)]
  decide +kernel
theorem row_33 : rowAt 33 = data_33 := by
  rw [rowAt, dif_neg (by decide : ¬ 33 < 6), entry_33_checked]
  change forkRow [placeRow ⟨0, 0, 2, 4⟩ (rowAt 0), placeRow ⟨17, 0, 7, 5⟩ (rowAt 17)] = data_33
  rw [row_0, row_17]
  apply row_ext <;> decide +kernel
theorem entry_good_33 : EntryGood 33 := by
  unfold EntryGood
  rw [entry_33_checked]
  decide +kernel
theorem good_33 : Good (rowAt 33) := by
  rw [row_33]
  unfold Good
  decide +kernel

theorem entry_34_checked : entryAt 34 = entry_34 := by
  rw [entry_chunk_1 8 (by decide)]
  decide +kernel
theorem row_34 : rowAt 34 = data_34 := by
  rw [rowAt, dif_neg (by decide : ¬ 34 < 6), entry_34_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨1, 6, 5, 4⟩ (rowAt 1)] = data_34
  rw [row_6, row_1]
  apply row_ext <;> decide +kernel
theorem entry_good_34 : EntryGood 34 := by
  unfold EntryGood
  rw [entry_34_checked]
  decide +kernel
theorem good_34 : Good (rowAt 34) := by
  rw [row_34]
  unfold Good
  decide +kernel

theorem entry_35_checked : entryAt 35 = entry_35 := by
  rw [entry_chunk_1 9 (by decide)]
  decide +kernel
theorem row_35 : rowAt 35 = data_35 := by
  rw [rowAt, dif_neg (by decide : ¬ 35 < 6), entry_35_checked]
  change forkRow [placeRow ⟨0, 0, 2, 4⟩ (rowAt 0), placeRow ⟨14, 0, 7, 5⟩ (rowAt 14)] = data_35
  rw [row_0, row_14]
  apply row_ext <;> decide +kernel
theorem entry_good_35 : EntryGood 35 := by
  unfold EntryGood
  rw [entry_35_checked]
  decide +kernel
theorem good_35 : Good (rowAt 35) := by
  rw [row_35]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 32 = data_32 ∧ Good (rowAt 32) ∧ EntryGood 32) ∧ (rowAt 33 = data_33 ∧ Good (rowAt 33) ∧ EntryGood 33) ∧ (rowAt 34 = data_34 ∧ Good (rowAt 34) ∧ EntryGood 34) ∧ (rowAt 35 = data_35 ∧ Good (rowAt 35) ∧ EntryGood 35) ∧ True := by
  exact ⟨⟨row_32, good_32, entry_good_32⟩, ⟨row_33, good_33, entry_good_33⟩, ⟨row_34, good_34, entry_good_34⟩, ⟨row_35, good_35, entry_good_35⟩, trivial⟩
