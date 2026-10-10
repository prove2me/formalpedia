-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block02_group02_piece01_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T14:36:18.744355+00:00
-- url     : https://prove2.me/submissions/ccaaa405-8162-4061-a08a-3a722889a89c

import Definitions.Def_Snaky35Cache02
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_group00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_3 (j : ℕ) (hj : j < 20) : entryAt (66 + j) = tableChunk_3[j]?.getD emptyEntry := (chunk_lookups.2.2.2.1) j hj
theorem entry_chunk_4 (j : ℕ) (hj : j < 20) : entryAt (86 + j) = tableChunk_4[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.1).1
theorem row_4 : rowAt 4 = data_4 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_8 : rowAt 8 = data_8 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.1).1
theorem row_9 : rowAt 9 = data_9 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_13 : rowAt 13 = data_13 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_24 : rowAt 24 = data_24 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_36 : rowAt 36 = data_36 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.1).1
theorem row_43 : rowAt 43 = data_43 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_67 : rowAt 67 = data_67 := (OAI.SnakyCertificate.MilestoneChecks.block02_group00_correct.2.2.2.1).1
theorem entry_84_checked : entryAt 84 = entry_84 := by
  rw [entry_chunk_3 18 (by decide)]
  decide +kernel
theorem row_84 : rowAt 84 = data_84 := by
  rw [rowAt, dif_neg (by decide : ¬ 84 < 6), entry_84_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨67, 0, 6, 4⟩ (rowAt 67)] = data_84
  rw [row_6, row_67]
  apply row_ext <;> decide +kernel
theorem entry_good_84 : EntryGood 84 := by
  unfold EntryGood
  rw [entry_84_checked]
  decide +kernel
theorem good_84 : Good (rowAt 84) := by
  rw [row_84]
  unfold Good
  decide +kernel

theorem entry_85_checked : entryAt 85 = entry_85 := by
  rw [entry_chunk_3 19 (by decide)]
  decide +kernel
theorem row_85 : rowAt 85 = data_85 := by
  rw [rowAt, dif_neg (by decide : ¬ 85 < 6), entry_85_checked]
  change forkRow [placeRow ⟨9, 0, 6, 3⟩ (rowAt 9), placeRow ⟨8, 4, 5, 4⟩ (rowAt 8)] = data_85
  rw [row_9, row_8]
  apply row_ext <;> decide +kernel
theorem entry_good_85 : EntryGood 85 := by
  unfold EntryGood
  rw [entry_85_checked]
  decide +kernel
theorem good_85 : Good (rowAt 85) := by
  rw [row_85]
  unfold Good
  decide +kernel

theorem entry_86_checked : entryAt 86 = entry_86 := by
  rw [entry_chunk_4 0 (by decide)]
  decide +kernel
theorem row_86 : rowAt 86 = data_86 := by
  rw [rowAt, dif_neg (by decide : ¬ 86 < 6), entry_86_checked]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (rowAt 0), placeRow ⟨67, 3, 1, 5⟩ (rowAt 67)] = data_86
  rw [row_0, row_67]
  apply row_ext <;> decide +kernel
theorem entry_good_86 : EntryGood 86 := by
  unfold EntryGood
  rw [entry_86_checked]
  decide +kernel
theorem good_86 : Good (rowAt 86) := by
  rw [row_86]
  unfold Good
  decide +kernel

theorem entry_87_checked : entryAt 87 = entry_87 := by
  rw [entry_chunk_4 1 (by decide)]
  decide +kernel
theorem row_87 : rowAt 87 = data_87 := by
  rw [rowAt, dif_neg (by decide : ¬ 87 < 6), entry_87_checked]
  change forkRow [placeRow ⟨0, 5, 3, 7⟩ (rowAt 0), placeRow ⟨24, 2, 5, 3⟩ (rowAt 24)] = data_87
  rw [row_0, row_24]
  apply row_ext <;> decide +kernel
theorem entry_good_87 : EntryGood 87 := by
  unfold EntryGood
  rw [entry_87_checked]
  decide +kernel
theorem good_87 : Good (rowAt 87) := by
  rw [row_87]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 84 = data_84 ∧ Good (rowAt 84) ∧ EntryGood 84) ∧ (rowAt 85 = data_85 ∧ Good (rowAt 85) ∧ EntryGood 85) ∧ (rowAt 86 = data_86 ∧ Good (rowAt 86) ∧ EntryGood 86) ∧ (rowAt 87 = data_87 ∧ Good (rowAt 87) ∧ EntryGood 87) ∧ True := by
  exact ⟨⟨row_84, good_84, entry_good_84⟩, ⟨row_85, good_85, entry_good_85⟩, ⟨row_86, good_86, entry_good_86⟩, ⟨row_87, good_87, entry_good_87⟩, trivial⟩
