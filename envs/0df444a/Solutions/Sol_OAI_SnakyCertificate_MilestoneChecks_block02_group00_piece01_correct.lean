-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block02_group00_piece01_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T14:27:00.62825+00:00
-- url     : https://prove2.me/submissions/965e10f2-8f26-4a72-b8d7-0059ab1e4938

import Definitions.Def_Snaky35Cache02
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_2 (j : ℕ) (hj : j < 20) : entryAt (46 + j) = tableChunk_2[j]?.getD emptyEntry := (chunk_lookups.2.2.1) j hj
theorem entry_chunk_3 (j : ℕ) (hj : j < 20) : entryAt (66 + j) = tableChunk_3[j]?.getD emptyEntry := (chunk_lookups.2.2.2.1) j hj
theorem row_4 : rowAt 4 = data_4 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_9 : rowAt 9 = data_9 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_23 : rowAt 23 = data_23 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_34 : rowAt 34 = data_34 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.1).1
theorem row_41 : rowAt 41 = data_41 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_44 : rowAt 44 = data_44 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_49 : rowAt 49 = data_49 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_53 : rowAt 53 = data_53 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem entry_68_checked : entryAt 68 = entry_68 := by
  rw [entry_chunk_3 2 (by decide)]
  decide +kernel
theorem row_68 : rowAt 68 = data_68 := by
  rw [rowAt, dif_neg (by decide : ¬ 68 < 6), entry_68_checked]
  change forkRow [placeRow ⟨6, 4, 0, 5⟩ (rowAt 6), placeRow ⟨44, 0, 5, 4⟩ (rowAt 44)] = data_68
  rw [row_6, row_44]
  apply row_ext <;> decide +kernel
theorem entry_good_68 : EntryGood 68 := by
  unfold EntryGood
  rw [entry_68_checked]
  decide +kernel
theorem good_68 : Good (rowAt 68) := by
  rw [row_68]
  unfold Good
  decide +kernel

theorem entry_69_checked : entryAt 69 = entry_69 := by
  rw [entry_chunk_3 3 (by decide)]
  decide +kernel
theorem row_69 : rowAt 69 = data_69 := by
  rw [rowAt, dif_neg (by decide : ¬ 69 < 6), entry_69_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨34, 0, 6, 5⟩ (rowAt 34)] = data_69
  rw [row_6, row_34]
  apply row_ext <;> decide +kernel
theorem entry_good_69 : EntryGood 69 := by
  unfold EntryGood
  rw [entry_69_checked]
  decide +kernel
theorem good_69 : Good (rowAt 69) := by
  rw [row_69]
  unfold Good
  decide +kernel

theorem entry_70_checked : entryAt 70 = entry_70 := by
  rw [entry_chunk_3 4 (by decide)]
  decide +kernel
theorem row_70 : rowAt 70 = data_70 := by
  rw [rowAt, dif_neg (by decide : ¬ 70 < 6), entry_70_checked]
  change forkRow [placeRow ⟨4, 3, 4, 3⟩ (rowAt 4), placeRow ⟨41, 0, 5, 4⟩ (rowAt 41)] = data_70
  rw [row_4, row_41]
  apply row_ext <;> decide +kernel
theorem entry_good_70 : EntryGood 70 := by
  unfold EntryGood
  rw [entry_70_checked]
  decide +kernel
theorem good_70 : Good (rowAt 70) := by
  rw [row_70]
  unfold Good
  decide +kernel

theorem entry_71_checked : entryAt 71 = entry_71 := by
  rw [entry_chunk_3 5 (by decide)]
  decide +kernel
theorem row_71 : rowAt 71 = data_71 := by
  rw [rowAt, dif_neg (by decide : ¬ 71 < 6), entry_71_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨23, 2, 4, 3⟩ (rowAt 23)] = data_71
  rw [row_6, row_23]
  apply row_ext <;> decide +kernel
theorem entry_good_71 : EntryGood 71 := by
  unfold EntryGood
  rw [entry_71_checked]
  decide +kernel
theorem good_71 : Good (rowAt 71) := by
  rw [row_71]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 68 = data_68 ∧ Good (rowAt 68) ∧ EntryGood 68) ∧ (rowAt 69 = data_69 ∧ Good (rowAt 69) ∧ EntryGood 69) ∧ (rowAt 70 = data_70 ∧ Good (rowAt 70) ∧ EntryGood 70) ∧ (rowAt 71 = data_71 ∧ Good (rowAt 71) ∧ EntryGood 71) ∧ True := by
  exact ⟨⟨row_68, good_68, entry_good_68⟩, ⟨row_69, good_69, entry_good_69⟩, ⟨row_70, good_70, entry_good_70⟩, ⟨row_71, good_71, entry_good_71⟩, trivial⟩
