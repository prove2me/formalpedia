-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block00_group03_piece01_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T13:49:27.297918+00:00
-- url     : https://prove2.me/submissions/7e85f7a1-6a4d-4515-a509-fbbab655f501

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
theorem entry_26_checked : entryAt 26 = entry_26 := by
  rw [entry_chunk_1 0 (by decide)]
  decide +kernel
theorem row_26 : rowAt 26 = data_26 := by
  rw [rowAt, dif_neg (by decide : ¬ 26 < 6), entry_26_checked]
  change forkRow [placeRow ⟨0, 4, 6, 4⟩ (rowAt 0), placeRow ⟨6, 0, 6, 5⟩ (rowAt 6)] = data_26
  rw [row_0, row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_26 : EntryGood 26 := by
  unfold EntryGood
  rw [entry_26_checked]
  decide +kernel
theorem good_26 : Good (rowAt 26) := by
  rw [row_26]
  unfold Good
  decide +kernel

theorem entry_27_checked : entryAt 27 = entry_27 := by
  rw [entry_chunk_1 1 (by decide)]
  decide +kernel
theorem row_27 : rowAt 27 = data_27 := by
  rw [rowAt, dif_neg (by decide : ¬ 27 < 6), entry_27_checked]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (rowAt 0), placeRow ⟨6, 4, 0, 5⟩ (rowAt 6)] = data_27
  rw [row_0, row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_27 : EntryGood 27 := by
  unfold EntryGood
  rw [entry_27_checked]
  decide +kernel
theorem good_27 : Good (rowAt 27) := by
  rw [row_27]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 26 = data_26 ∧ Good (rowAt 26) ∧ EntryGood 26) ∧ (rowAt 27 = data_27 ∧ Good (rowAt 27) ∧ EntryGood 27) ∧ True := by
  exact ⟨⟨row_26, good_26, entry_good_26⟩, ⟨row_27, good_27, entry_good_27⟩, trivial⟩
