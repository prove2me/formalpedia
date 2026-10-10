-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block01_group03_piece01_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T14:17:18.897166+00:00
-- url     : https://prove2.me/submissions/355fb1ce-cf42-4336-ade1-cd1393a65b3e

import Definitions.Def_Snaky35Cache01
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_group02_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_2 (j : ℕ) (hj : j < 20) : entryAt (46 + j) = tableChunk_2[j]?.getD emptyEntry := (chunk_lookups.2.2.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.1).1
theorem row_4 : rowAt 4 = data_4 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_7 : rowAt 7 = data_7 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.1).1
theorem row_14 : rowAt 14 = data_14 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_49 : rowAt 49 = data_49 := (OAI.SnakyCertificate.MilestoneChecks.block01_group02_correct.2.1).1
theorem row_50 : rowAt 50 = data_50 := (OAI.SnakyCertificate.MilestoneChecks.block01_group02_correct.2.2.1).1
theorem row_53 : rowAt 53 = data_53 := (OAI.SnakyCertificate.MilestoneChecks.block01_group02_correct.2.2.2.2.2.1).1
theorem entry_60_checked : entryAt 60 = entry_60 := by
  rw [entry_chunk_2 14 (by decide)]
  decide +kernel
theorem row_60 : rowAt 60 = data_60 := by
  rw [rowAt, dif_neg (by decide : ¬ 60 < 6), entry_60_checked]
  change forkRow [placeRow ⟨6, 6, 1, 3⟩ (rowAt 6), placeRow ⟨49, 1, 6, 4⟩ (rowAt 49)] = data_60
  rw [row_6, row_49]
  apply row_ext <;> decide +kernel
theorem entry_good_60 : EntryGood 60 := by
  unfold EntryGood
  rw [entry_60_checked]
  decide +kernel
theorem good_60 : Good (rowAt 60) := by
  rw [row_60]
  unfold Good
  decide +kernel

theorem entry_61_checked : entryAt 61 = entry_61 := by
  rw [entry_chunk_2 15 (by decide)]
  decide +kernel
theorem row_61 : rowAt 61 = data_61 := by
  rw [rowAt, dif_neg (by decide : ¬ 61 < 6), entry_61_checked]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (rowAt 6), placeRow ⟨14, 1, 4, 5⟩ (rowAt 14)] = data_61
  rw [row_6, row_14]
  apply row_ext <;> decide +kernel
theorem entry_good_61 : EntryGood 61 := by
  unfold EntryGood
  rw [entry_61_checked]
  decide +kernel
theorem good_61 : Good (rowAt 61) := by
  rw [row_61]
  unfold Good
  decide +kernel

theorem entry_62_checked : entryAt 62 = entry_62 := by
  rw [entry_chunk_2 16 (by decide)]
  decide +kernel
theorem row_62 : rowAt 62 = data_62 := by
  rw [rowAt, dif_neg (by decide : ¬ 62 < 6), entry_62_checked]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (rowAt 6), placeRow ⟨53, 0, 1, 5⟩ (rowAt 53)] = data_62
  rw [row_6, row_53]
  apply row_ext <;> decide +kernel
theorem entry_good_62 : EntryGood 62 := by
  unfold EntryGood
  rw [entry_62_checked]
  decide +kernel
theorem good_62 : Good (rowAt 62) := by
  rw [row_62]
  unfold Good
  decide +kernel

theorem entry_63_checked : entryAt 63 = entry_63 := by
  rw [entry_chunk_2 17 (by decide)]
  decide +kernel
theorem row_63 : rowAt 63 = data_63 := by
  rw [rowAt, dif_neg (by decide : ¬ 63 < 6), entry_63_checked]
  change forkRow [placeRow ⟨4, 3, 4, 3⟩ (rowAt 4), placeRow ⟨50, 0, 5, 4⟩ (rowAt 50)] = data_63
  rw [row_4, row_50]
  apply row_ext <;> decide +kernel
theorem entry_good_63 : EntryGood 63 := by
  unfold EntryGood
  rw [entry_63_checked]
  decide +kernel
theorem good_63 : Good (rowAt 63) := by
  rw [row_63]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 60 = data_60 ∧ Good (rowAt 60) ∧ EntryGood 60) ∧ (rowAt 61 = data_61 ∧ Good (rowAt 61) ∧ EntryGood 61) ∧ (rowAt 62 = data_62 ∧ Good (rowAt 62) ∧ EntryGood 62) ∧ (rowAt 63 = data_63 ∧ Good (rowAt 63) ∧ EntryGood 63) ∧ True := by
  exact ⟨⟨row_60, good_60, entry_good_60⟩, ⟨row_61, good_61, entry_good_61⟩, ⟨row_62, good_62, entry_good_62⟩, ⟨row_63, good_63, entry_good_63⟩, trivial⟩
