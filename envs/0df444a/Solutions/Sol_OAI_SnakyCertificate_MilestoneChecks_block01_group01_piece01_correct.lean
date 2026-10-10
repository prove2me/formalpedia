-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block01_group01_piece01_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T13:59:38.984067+00:00
-- url     : https://prove2.me/submissions/3e5d16a2-8a0e-4d9c-a3e1-01244c28f205

import Definitions.Def_Snaky35Cache01
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_1 (j : ℕ) (hj : j < 20) : entryAt (26 + j) = tableChunk_1[j]?.getD emptyEntry := (chunk_lookups.2.1) j hj
theorem entry_chunk_2 (j : ℕ) (hj : j < 20) : entryAt (46 + j) = tableChunk_2[j]?.getD emptyEntry := (chunk_lookups.2.2.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.1).1
theorem row_1 : rowAt 1 = data_1 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.1).1
theorem row_2 : rowAt 2 = data_2 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.1).1
theorem row_3 : rowAt 3 = data_3 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.1).1
theorem row_4 : rowAt 4 = data_4 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_7 : rowAt 7 = data_7 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.1).1
theorem row_16 : rowAt 16 = data_16 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem entry_44_checked : entryAt 44 = entry_44 := by
  rw [entry_chunk_1 18 (by decide)]
  decide +kernel
theorem row_44 : rowAt 44 = data_44 := by
  rw [rowAt, dif_neg (by decide : ¬ 44 < 6), entry_44_checked]
  change forkRow [placeRow ⟨4, 4, 1, 5⟩ (rowAt 4), placeRow ⟨7, 0, 4, 5⟩ (rowAt 7)] = data_44
  rw [row_4, row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_44 : EntryGood 44 := by
  unfold EntryGood
  rw [entry_44_checked]
  decide +kernel
theorem good_44 : Good (rowAt 44) := by
  rw [row_44]
  unfold Good
  decide +kernel

theorem entry_45_checked : entryAt 45 = entry_45 := by
  rw [entry_chunk_1 19 (by decide)]
  decide +kernel
theorem row_45 : rowAt 45 = data_45 := by
  rw [rowAt, dif_neg (by decide : ¬ 45 < 6), entry_45_checked]
  change forkRow [placeRow ⟨6, 4, 0, 5⟩ (rowAt 6), placeRow ⟨7, 0, 4, 5⟩ (rowAt 7)] = data_45
  rw [row_6, row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_45 : EntryGood 45 := by
  unfold EntryGood
  rw [entry_45_checked]
  decide +kernel
theorem good_45 : Good (rowAt 45) := by
  rw [row_45]
  unfold Good
  decide +kernel

theorem entry_46_checked : entryAt 46 = entry_46 := by
  rw [entry_chunk_2 0 (by decide)]
  decide +kernel
theorem row_46 : rowAt 46 = data_46 := by
  rw [rowAt, dif_neg (by decide : ¬ 46 < 6), entry_46_checked]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (rowAt 6), placeRow ⟨7, 0, 4, 5⟩ (rowAt 7)] = data_46
  rw [row_6, row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_46 : EntryGood 46 := by
  unfold EntryGood
  rw [entry_46_checked]
  decide +kernel
theorem good_46 : Good (rowAt 46) := by
  rw [row_46]
  unfold Good
  decide +kernel

theorem entry_47_checked : entryAt 47 = entry_47 := by
  rw [entry_chunk_2 1 (by decide)]
  decide +kernel
theorem row_47 : rowAt 47 = data_47 := by
  rw [rowAt, dif_neg (by decide : ¬ 47 < 6), entry_47_checked]
  change forkRow [placeRow ⟨6, 3, 3, 5⟩ (rowAt 6), placeRow ⟨6, 2, 7, 3⟩ (rowAt 6)] = data_47
  rw [row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_47 : EntryGood 47 := by
  unfold EntryGood
  rw [entry_47_checked]
  decide +kernel
theorem good_47 : Good (rowAt 47) := by
  rw [row_47]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 44 = data_44 ∧ Good (rowAt 44) ∧ EntryGood 44) ∧ (rowAt 45 = data_45 ∧ Good (rowAt 45) ∧ EntryGood 45) ∧ (rowAt 46 = data_46 ∧ Good (rowAt 46) ∧ EntryGood 46) ∧ (rowAt 47 = data_47 ∧ Good (rowAt 47) ∧ EntryGood 47) ∧ True := by
  exact ⟨⟨row_44, good_44, entry_good_44⟩, ⟨row_45, good_45, entry_good_45⟩, ⟨row_46, good_46, entry_good_46⟩, ⟨row_47, good_47, entry_good_47⟩, trivial⟩
