-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block03_group00_piece01_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T07:46:54.963585+00:00
-- url     : https://prove2.me/submissions/108e116b-80fc-47ce-ad0b-f10ba25b469f

import Definitions.Def_Snaky35Cache03
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_group00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks
theorem entry_chunk_4 (j : ℕ) (hj : j < 20) : entryAt (86 + j) = tableChunk_4[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_24 : rowAt 24 = data_24 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_25 : rowAt 25 = data_25 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_48 : rowAt 48 = data_48 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_71 : rowAt 71 = data_71 := (OAI.SnakyCertificate.MilestoneChecks.block02_group00_correct.2.2.2.2.2.2.2.1).1
theorem entry_100_checked : entryAt 100 = entry_100 := by
  rw [entry_chunk_4 14 (by decide)]
  decide +kernel
theorem row_100 : rowAt 100 = data_100 := by
  rw [rowAt, dif_neg (by decide : ¬ 100 < 6), entry_100_checked]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (rowAt 0), placeRow ⟨48, 0, 1, 4⟩ (rowAt 48)] = data_100
  rw [row_0, row_48]
  apply row_ext <;> decide +kernel
theorem entry_good_100 : EntryGood 100 := by
  unfold EntryGood
  rw [entry_100_checked]
  decide +kernel
theorem good_100 : Good (rowAt 100) := by
  rw [row_100]
  unfold Good
  decide +kernel

theorem entry_101_checked : entryAt 101 = entry_101 := by
  rw [entry_chunk_4 15 (by decide)]
  decide +kernel
theorem row_101 : rowAt 101 = data_101 := by
  rw [rowAt, dif_neg (by decide : ¬ 101 < 6), entry_101_checked]
  change forkRow [placeRow ⟨0, 7, 4, 6⟩ (rowAt 0), placeRow ⟨24, 0, 5, 4⟩ (rowAt 24)] = data_101
  rw [row_0, row_24]
  apply row_ext <;> decide +kernel
theorem entry_good_101 : EntryGood 101 := by
  unfold EntryGood
  rw [entry_101_checked]
  decide +kernel
theorem good_101 : Good (rowAt 101) := by
  rw [row_101]
  unfold Good
  decide +kernel

theorem entry_102_checked : entryAt 102 = entry_102 := by
  rw [entry_chunk_4 16 (by decide)]
  decide +kernel
theorem row_102 : rowAt 102 = data_102 := by
  rw [rowAt, dif_neg (by decide : ¬ 102 < 6), entry_102_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨25, 2, 6, 3⟩ (rowAt 25)] = data_102
  rw [row_6, row_25]
  apply row_ext <;> decide +kernel
theorem entry_good_102 : EntryGood 102 := by
  unfold EntryGood
  rw [entry_102_checked]
  decide +kernel
theorem good_102 : Good (rowAt 102) := by
  rw [row_102]
  unfold Good
  decide +kernel

theorem entry_103_checked : entryAt 103 = entry_103 := by
  rw [entry_chunk_4 17 (by decide)]
  decide +kernel
theorem row_103 : rowAt 103 = data_103 := by
  rw [rowAt, dif_neg (by decide : ¬ 103 < 6), entry_103_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨71, 0, 6, 4⟩ (rowAt 71)] = data_103
  rw [row_6, row_71]
  apply row_ext <;> decide +kernel
theorem entry_good_103 : EntryGood 103 := by
  unfold EntryGood
  rw [entry_103_checked]
  decide +kernel
theorem good_103 : Good (rowAt 103) := by
  rw [row_103]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks.S213
theorem solution : (rowAt 100 = data_100 ∧ Good (rowAt 100) ∧ EntryGood 100) ∧ (rowAt 101 = data_101 ∧ Good (rowAt 101) ∧ EntryGood 101) ∧ (rowAt 102 = data_102 ∧ Good (rowAt 102) ∧ EntryGood 102) ∧ (rowAt 103 = data_103 ∧ Good (rowAt 103) ∧ EntryGood 103) ∧ True := by
  exact ⟨⟨row_100, good_100, entry_good_100⟩, ⟨row_101, good_101, entry_good_101⟩, ⟨row_102, good_102, entry_good_102⟩, ⟨row_103, good_103, entry_good_103⟩, trivial⟩
