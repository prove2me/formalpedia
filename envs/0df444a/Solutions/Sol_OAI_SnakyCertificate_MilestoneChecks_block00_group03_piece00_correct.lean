-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block00_group03_piece00_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T13:50:52.654447+00:00
-- url     : https://prove2.me/submissions/b5f63578-f468-488c-82c4-2e4126c6b3d6

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
theorem entry_24_checked : entryAt 24 = entry_24 := by
  rw [entry_chunk_0 18 (by decide)]
  decide +kernel
theorem row_24 : rowAt 24 = data_24 := by
  rw [rowAt, dif_neg (by decide : ¬ 24 < 6), entry_24_checked]
  change forkRow [placeRow ⟨0, 0, 0, 3⟩ (rowAt 0), placeRow ⟨17, 0, 5, 4⟩ (rowAt 17)] = data_24
  rw [row_0, row_17]
  apply row_ext <;> decide +kernel
theorem entry_good_24 : EntryGood 24 := by
  unfold EntryGood
  rw [entry_24_checked]
  decide +kernel
theorem good_24 : Good (rowAt 24) := by
  rw [row_24]
  unfold Good
  decide +kernel

theorem entry_25_checked : entryAt 25 = entry_25 := by
  rw [entry_chunk_0 19 (by decide)]
  decide +kernel
theorem row_25 : rowAt 25 = data_25 := by
  rw [rowAt, dif_neg (by decide : ¬ 25 < 6), entry_25_checked]
  change forkRow [placeRow ⟨0, 0, 0, 3⟩ (rowAt 0), placeRow ⟨14, 0, 5, 4⟩ (rowAt 14)] = data_25
  rw [row_0, row_14]
  apply row_ext <;> decide +kernel
theorem entry_good_25 : EntryGood 25 := by
  unfold EntryGood
  rw [entry_25_checked]
  decide +kernel
theorem good_25 : Good (rowAt 25) := by
  rw [row_25]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 24 = data_24 ∧ Good (rowAt 24) ∧ EntryGood 24) ∧ (rowAt 25 = data_25 ∧ Good (rowAt 25) ∧ EntryGood 25) ∧ True := by
  exact ⟨⟨row_24, good_24, entry_good_24⟩, ⟨row_25, good_25, entry_good_25⟩, trivial⟩
