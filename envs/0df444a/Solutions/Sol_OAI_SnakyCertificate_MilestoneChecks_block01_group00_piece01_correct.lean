-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block01_group00_piece01_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T13:59:05.844909+00:00
-- url     : https://prove2.me/submissions/cb7a3cb6-2cf4-41c7-87ed-b74695e34878

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
theorem entry_36_checked : entryAt 36 = entry_36 := by
  rw [entry_chunk_1 10 (by decide)]
  decide +kernel
theorem row_36 : rowAt 36 = data_36 := by
  rw [rowAt, dif_neg (by decide : ¬ 36 < 6), entry_36_checked]
  change forkRow [placeRow ⟨0, 0, 3, 4⟩ (rowAt 0), placeRow ⟨17, 0, 8, 5⟩ (rowAt 17)] = data_36
  rw [row_0, row_17]
  apply row_ext <;> decide +kernel
theorem entry_good_36 : EntryGood 36 := by
  unfold EntryGood
  rw [entry_36_checked]
  decide +kernel
theorem good_36 : Good (rowAt 36) := by
  rw [row_36]
  unfold Good
  decide +kernel

theorem entry_37_checked : entryAt 37 = entry_37 := by
  rw [entry_chunk_1 11 (by decide)]
  decide +kernel
theorem row_37 : rowAt 37 = data_37 := by
  rw [rowAt, dif_neg (by decide : ¬ 37 < 6), entry_37_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨2, 4, 6, 3⟩ (rowAt 2)] = data_37
  rw [row_6, row_2]
  apply row_ext <;> decide +kernel
theorem entry_good_37 : EntryGood 37 := by
  unfold EntryGood
  rw [entry_37_checked]
  decide +kernel
theorem good_37 : Good (rowAt 37) := by
  rw [row_37]
  unfold Good
  decide +kernel

theorem entry_38_checked : entryAt 38 = entry_38 := by
  rw [entry_chunk_1 12 (by decide)]
  decide +kernel
theorem row_38 : rowAt 38 = data_38 := by
  rw [rowAt, dif_neg (by decide : ¬ 38 < 6), entry_38_checked]
  change forkRow [placeRow ⟨3, 0, 3, 3⟩ (rowAt 3), placeRow ⟨16, 0, 2, 4⟩ (rowAt 16)] = data_38
  rw [row_3, row_16]
  apply row_ext <;> decide +kernel
theorem entry_good_38 : EntryGood 38 := by
  unfold EntryGood
  rw [entry_38_checked]
  decide +kernel
theorem good_38 : Good (rowAt 38) := by
  rw [row_38]
  unfold Good
  decide +kernel

theorem entry_39_checked : entryAt 39 = entry_39 := by
  rw [entry_chunk_1 13 (by decide)]
  decide +kernel
theorem row_39 : rowAt 39 = data_39 := by
  rw [rowAt, dif_neg (by decide : ¬ 39 < 6), entry_39_checked]
  change forkRow [placeRow ⟨0, 0, 1, 3⟩ (rowAt 0), placeRow ⟨17, 0, 6, 4⟩ (rowAt 17)] = data_39
  rw [row_0, row_17]
  apply row_ext <;> decide +kernel
theorem entry_good_39 : EntryGood 39 := by
  unfold EntryGood
  rw [entry_39_checked]
  decide +kernel
theorem good_39 : Good (rowAt 39) := by
  rw [row_39]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 36 = data_36 ∧ Good (rowAt 36) ∧ EntryGood 36) ∧ (rowAt 37 = data_37 ∧ Good (rowAt 37) ∧ EntryGood 37) ∧ (rowAt 38 = data_38 ∧ Good (rowAt 38) ∧ EntryGood 38) ∧ (rowAt 39 = data_39 ∧ Good (rowAt 39) ∧ EntryGood 39) ∧ True := by
  exact ⟨⟨row_36, good_36, entry_good_36⟩, ⟨row_37, good_37, entry_good_37⟩, ⟨row_38, good_38, entry_good_38⟩, ⟨row_39, good_39, entry_good_39⟩, trivial⟩
