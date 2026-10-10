-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block01_group02_piece01_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T14:06:14.744376+00:00
-- url     : https://prove2.me/submissions/f9f9c34c-c14d-45bf-b6f4-bdc102f6d4c9

import Definitions.Def_Snaky35Cache01
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_2 (j : ℕ) (hj : j < 20) : entryAt (46 + j) = tableChunk_2[j]?.getD emptyEntry := (chunk_lookups.2.2.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.1).1
theorem row_3 : rowAt 3 = data_3 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.1).1
theorem row_4 : rowAt 4 = data_4 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_7 : rowAt 7 = data_7 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.1).1
theorem row_10 : rowAt 10 = data_10 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_22 : rowAt 22 = data_22 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_26 : rowAt 26 = data_26 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem entry_52_checked : entryAt 52 = entry_52 := by
  rw [entry_chunk_2 6 (by decide)]
  decide +kernel
theorem row_52 : rowAt 52 = data_52 := by
  rw [rowAt, dif_neg (by decide : ¬ 52 < 6), entry_52_checked]
  change forkRow [placeRow ⟨0, 0, 0, 3⟩ (rowAt 0), placeRow ⟨0, 4, 7, 3⟩ (rowAt 0)] = data_52
  rw [row_0]
  apply row_ext <;> decide +kernel
theorem entry_good_52 : EntryGood 52 := by
  unfold EntryGood
  rw [entry_52_checked]
  decide +kernel
theorem good_52 : Good (rowAt 52) := by
  rw [row_52]
  unfold Good
  decide +kernel

theorem entry_53_checked : entryAt 53 = entry_53 := by
  rw [entry_chunk_2 7 (by decide)]
  decide +kernel
theorem row_53 : rowAt 53 = data_53 := by
  rw [rowAt, dif_neg (by decide : ¬ 53 < 6), entry_53_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨3, 1, 4, 5⟩ (rowAt 3)] = data_53
  rw [row_6, row_3]
  apply row_ext <;> decide +kernel
theorem entry_good_53 : EntryGood 53 := by
  unfold EntryGood
  rw [entry_53_checked]
  decide +kernel
theorem good_53 : Good (rowAt 53) := by
  rw [row_53]
  unfold Good
  decide +kernel

theorem entry_54_checked : entryAt 54 = entry_54 := by
  rw [entry_chunk_2 8 (by decide)]
  decide +kernel
theorem row_54 : rowAt 54 = data_54 := by
  rw [rowAt, dif_neg (by decide : ¬ 54 < 6), entry_54_checked]
  change forkRow [placeRow ⟨22, 0, 2, 3⟩ (rowAt 22), placeRow ⟨3, 6, 1, 4⟩ (rowAt 3)] = data_54
  rw [row_22, row_3]
  apply row_ext <;> decide +kernel
theorem entry_good_54 : EntryGood 54 := by
  unfold EntryGood
  rw [entry_54_checked]
  decide +kernel
theorem good_54 : Good (rowAt 54) := by
  rw [row_54]
  unfold Good
  decide +kernel

theorem entry_55_checked : entryAt 55 = entry_55 := by
  rw [entry_chunk_2 9 (by decide)]
  decide +kernel
theorem row_55 : rowAt 55 = data_55 := by
  rw [rowAt, dif_neg (by decide : ¬ 55 < 6), entry_55_checked]
  change forkRow [placeRow ⟨7, 4, 0, 5⟩ (rowAt 7), placeRow ⟨7, 0, 4, 5⟩ (rowAt 7)] = data_55
  rw [row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_55 : EntryGood 55 := by
  unfold EntryGood
  rw [entry_55_checked]
  decide +kernel
theorem good_55 : Good (rowAt 55) := by
  rw [row_55]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 52 = data_52 ∧ Good (rowAt 52) ∧ EntryGood 52) ∧ (rowAt 53 = data_53 ∧ Good (rowAt 53) ∧ EntryGood 53) ∧ (rowAt 54 = data_54 ∧ Good (rowAt 54) ∧ EntryGood 54) ∧ (rowAt 55 = data_55 ∧ Good (rowAt 55) ∧ EntryGood 55) ∧ True := by
  exact ⟨⟨row_52, good_52, entry_good_52⟩, ⟨row_53, good_53, entry_good_53⟩, ⟨row_54, good_54, entry_good_54⟩, ⟨row_55, good_55, entry_good_55⟩, trivial⟩
