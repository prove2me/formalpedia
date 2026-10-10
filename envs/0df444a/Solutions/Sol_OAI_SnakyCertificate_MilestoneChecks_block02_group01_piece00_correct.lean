-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block02_group01_piece00_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T14:27:03.375535+00:00
-- url     : https://prove2.me/submissions/0b94914c-1423-4ba9-aa15-b61636d887a0

import Definitions.Def_Snaky35Cache02
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_3 (j : ℕ) (hj : j < 20) : entryAt (66 + j) = tableChunk_3[j]?.getD emptyEntry := (chunk_lookups.2.2.2.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.1).1
theorem row_2 : rowAt 2 = data_2 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.1).1
theorem row_4 : rowAt 4 = data_4 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_8 : rowAt 8 = data_8 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.1).1
theorem row_9 : rowAt 9 = data_9 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_12 : rowAt 12 = data_12 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_14 : rowAt 14 = data_14 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_48 : rowAt 48 = data_48 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_50 : rowAt 50 = data_50 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_52 : rowAt 52 = data_52 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_53 : rowAt 53 = data_53 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem entry_72_checked : entryAt 72 = entry_72 := by
  rw [entry_chunk_3 6 (by decide)]
  decide +kernel
theorem row_72 : rowAt 72 = data_72 := by
  rw [rowAt, dif_neg (by decide : ¬ 72 < 6), entry_72_checked]
  change forkRow [placeRow ⟨0, 5, 3, 8⟩ (rowAt 0), placeRow ⟨8, 6, 5, 4⟩ (rowAt 8)] = data_72
  rw [row_0, row_8]
  apply row_ext <;> decide +kernel
theorem entry_good_72 : EntryGood 72 := by
  unfold EntryGood
  rw [entry_72_checked]
  decide +kernel
theorem good_72 : Good (rowAt 72) := by
  rw [row_72]
  unfold Good
  decide +kernel

theorem entry_73_checked : entryAt 73 = entry_73 := by
  rw [entry_chunk_3 7 (by decide)]
  decide +kernel
theorem row_73 : rowAt 73 = data_73 := by
  rw [rowAt, dif_neg (by decide : ¬ 73 < 6), entry_73_checked]
  change forkRow [placeRow ⟨4, 3, 3, 4⟩ (rowAt 4), placeRow ⟨50, 0, 4, 5⟩ (rowAt 50)] = data_73
  rw [row_4, row_50]
  apply row_ext <;> decide +kernel
theorem entry_good_73 : EntryGood 73 := by
  unfold EntryGood
  rw [entry_73_checked]
  decide +kernel
theorem good_73 : Good (rowAt 73) := by
  rw [row_73]
  unfold Good
  decide +kernel

theorem entry_74_checked : entryAt 74 = entry_74 := by
  rw [entry_chunk_3 8 (by decide)]
  decide +kernel
theorem row_74 : rowAt 74 = data_74 := by
  rw [rowAt, dif_neg (by decide : ¬ 74 < 6), entry_74_checked]
  change forkRow [placeRow ⟨2, 7, 4, 3⟩ (rowAt 2), placeRow ⟨53, 0, 3, 3⟩ (rowAt 53)] = data_74
  rw [row_2, row_53]
  apply row_ext <;> decide +kernel
theorem entry_good_74 : EntryGood 74 := by
  unfold EntryGood
  rw [entry_74_checked]
  decide +kernel
theorem good_74 : Good (rowAt 74) := by
  rw [row_74]
  unfold Good
  decide +kernel

theorem entry_75_checked : entryAt 75 = entry_75 := by
  rw [entry_chunk_3 9 (by decide)]
  decide +kernel
theorem row_75 : rowAt 75 = data_75 := by
  rw [rowAt, dif_neg (by decide : ¬ 75 < 6), entry_75_checked]
  change forkRow [placeRow ⟨0, 0, 1, 3⟩ (rowAt 0), placeRow ⟨9, 0, 7, 3⟩ (rowAt 9)] = data_75
  rw [row_0, row_9]
  apply row_ext <;> decide +kernel
theorem entry_good_75 : EntryGood 75 := by
  unfold EntryGood
  rw [entry_75_checked]
  decide +kernel
theorem good_75 : Good (rowAt 75) := by
  rw [row_75]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 72 = data_72 ∧ Good (rowAt 72) ∧ EntryGood 72) ∧ (rowAt 73 = data_73 ∧ Good (rowAt 73) ∧ EntryGood 73) ∧ (rowAt 74 = data_74 ∧ Good (rowAt 74) ∧ EntryGood 74) ∧ (rowAt 75 = data_75 ∧ Good (rowAt 75) ∧ EntryGood 75) ∧ True := by
  exact ⟨⟨row_72, good_72, entry_good_72⟩, ⟨row_73, good_73, entry_good_73⟩, ⟨row_74, good_74, entry_good_74⟩, ⟨row_75, good_75, entry_good_75⟩, trivial⟩
