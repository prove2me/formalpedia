-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block00_group03_piece03_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T13:49:48.984983+00:00
-- url     : https://prove2.me/submissions/f4271eac-4d7c-4c9f-8676-832675540ec5

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
theorem entry_30_checked : entryAt 30 = entry_30 := by
  rw [entry_chunk_1 4 (by decide)]
  decide +kernel
theorem row_30 : rowAt 30 = data_30 := by
  rw [rowAt, dif_neg (by decide : ¬ 30 < 6), entry_30_checked]
  change forkRow [placeRow ⟨0, 0, 1, 3⟩ (rowAt 0), placeRow ⟨14, 0, 6, 4⟩ (rowAt 14)] = data_30
  rw [row_0, row_14]
  apply row_ext <;> decide +kernel
theorem entry_good_30 : EntryGood 30 := by
  unfold EntryGood
  rw [entry_30_checked]
  decide +kernel
theorem good_30 : Good (rowAt 30) := by
  rw [row_30]
  unfold Good
  decide +kernel

theorem entry_31_checked : entryAt 31 = entry_31 := by
  rw [entry_chunk_1 5 (by decide)]
  decide +kernel
theorem row_31 : rowAt 31 = data_31 := by
  rw [rowAt, dif_neg (by decide : ¬ 31 < 6), entry_31_checked]
  change forkRow [placeRow ⟨0, 0, 1, 4⟩ (rowAt 0), placeRow ⟨17, 0, 6, 5⟩ (rowAt 17)] = data_31
  rw [row_0, row_17]
  apply row_ext <;> decide +kernel
theorem entry_good_31 : EntryGood 31 := by
  unfold EntryGood
  rw [entry_31_checked]
  decide +kernel
theorem good_31 : Good (rowAt 31) := by
  rw [row_31]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 30 = data_30 ∧ Good (rowAt 30) ∧ EntryGood 30) ∧ (rowAt 31 = data_31 ∧ Good (rowAt 31) ∧ EntryGood 31) ∧ True := by
  exact ⟨⟨row_30, good_30, entry_good_30⟩, ⟨row_31, good_31, entry_good_31⟩, trivial⟩
