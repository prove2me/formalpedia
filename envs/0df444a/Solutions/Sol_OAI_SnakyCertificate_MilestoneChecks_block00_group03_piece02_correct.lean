-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block00_group03_piece02_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T13:49:27.243056+00:00
-- url     : https://prove2.me/submissions/92974429-60f8-4196-a780-006537917a3b

import Definitions.Def_Snaky35Cache00
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_group00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_group01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_group02_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_0 (j : ℕ) (hj : j < 20) : entryAt (6 + j) = tableChunk_0[j]?.getD emptyEntry := (chunk_lookups.1) j hj
theorem entry_chunk_1 (j : ℕ) (hj : j < 20) : entryAt (26 + j) = tableChunk_1[j]?.getD emptyEntry := (chunk_lookups.2.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_group00_correct.1).1
theorem row_1 : rowAt 1 = data_1 := (OAI.SnakyCertificate.MilestoneChecks.block00_group00_correct.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_group00_correct.2.2.2.2.2.2.1).1
theorem row_14 : rowAt 14 = data_14 := (OAI.SnakyCertificate.MilestoneChecks.block00_group01_correct.2.2.2.2.2.2.1).1
theorem row_17 : rowAt 17 = data_17 := (OAI.SnakyCertificate.MilestoneChecks.block00_group02_correct.2.1).1
theorem entry_28_checked : entryAt 28 = entry_28 := by
  rw [entry_chunk_1 2 (by decide)]
  decide +kernel
theorem row_28 : rowAt 28 = data_28 := by
  rw [rowAt, dif_neg (by decide : ¬ 28 < 6), entry_28_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨0, 6, 6, 4⟩ (rowAt 0)] = data_28
  rw [row_6, row_0]
  apply row_ext <;> decide +kernel
theorem entry_good_28 : EntryGood 28 := by
  unfold EntryGood
  rw [entry_28_checked]
  decide +kernel
theorem good_28 : Good (rowAt 28) := by
  rw [row_28]
  unfold Good
  decide +kernel

theorem entry_29_checked : entryAt 29 = entry_29 := by
  rw [entry_chunk_1 3 (by decide)]
  decide +kernel
theorem row_29 : rowAt 29 = data_29 := by
  rw [rowAt, dif_neg (by decide : ¬ 29 < 6), entry_29_checked]
  change forkRow [placeRow ⟨1, 4, 7, 3⟩ (rowAt 1), placeRow ⟨6, 3, 4, 5⟩ (rowAt 6)] = data_29
  rw [row_1, row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_29 : EntryGood 29 := by
  unfold EntryGood
  rw [entry_29_checked]
  decide +kernel
theorem good_29 : Good (rowAt 29) := by
  rw [row_29]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 28 = data_28 ∧ Good (rowAt 28) ∧ EntryGood 28) ∧ (rowAt 29 = data_29 ∧ Good (rowAt 29) ∧ EntryGood 29) ∧ True := by
  exact ⟨⟨row_28, good_28, entry_good_28⟩, ⟨row_29, good_29, entry_good_29⟩, trivial⟩
