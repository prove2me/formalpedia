-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block04_group01_piece01_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T08:21:01.082804+00:00
-- url     : https://prove2.me/submissions/1a18204c-2339-4390-9914-a2713d34febe

import Definitions.Def_Snaky35Cache04
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_group01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_group02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_group01_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks
theorem entry_chunk_6 (j : ℕ) (hj : j < 20) : entryAt (126 + j) = tableChunk_6[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.1) j hj
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_7 : rowAt 7 = data_7 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.1).1
theorem row_32 : rowAt 32 = data_32 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.1).1
theorem row_55 : rowAt 55 = data_55 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_72 : rowAt 72 = data_72 := (OAI.SnakyCertificate.MilestoneChecks.block02_group01_correct.1).1
theorem row_78 : rowAt 78 = data_78 := (OAI.SnakyCertificate.MilestoneChecks.block02_group01_correct.2.2.2.2.2.2.1).1
theorem row_82 : rowAt 82 = data_82 := (OAI.SnakyCertificate.MilestoneChecks.block02_group02_correct.2.2.1).1
theorem row_108 : rowAt 108 = data_108 := (OAI.SnakyCertificate.MilestoneChecks.block03_group01_piece01_correct.1).1
theorem entry_140_checked : entryAt 140 = entry_140 := by
  rw [entry_chunk_6 14 (by decide)]
  decide +kernel
theorem row_140 : rowAt 140 = data_140 := by
  rw [rowAt, dif_neg (by decide : ¬ 140 < 6), entry_140_checked]
  change forkRow [placeRow ⟨6, 7, 3, 2⟩ (rowAt 6), placeRow ⟨82, 0, 5, 6⟩ (rowAt 82)] = data_140
  rw [row_6, row_82]
  apply row_ext <;> decide +kernel
theorem entry_good_140 : EntryGood 140 := by
  unfold EntryGood
  rw [entry_140_checked]
  decide +kernel
theorem good_140 : Good (rowAt 140) := by
  rw [row_140]
  unfold Good
  decide +kernel

theorem entry_141_checked : entryAt 141 = entry_141 := by
  rw [entry_chunk_6 15 (by decide)]
  decide +kernel
theorem row_141 : rowAt 141 = data_141 := by
  rw [rowAt, dif_neg (by decide : ¬ 141 < 6), entry_141_checked]
  change forkRow [placeRow ⟨7, 0, 4, 5⟩ (rowAt 7), placeRow ⟨78, 2, 1, 3⟩ (rowAt 78)] = data_141
  rw [row_7, row_78]
  apply row_ext <;> decide +kernel
theorem entry_good_141 : EntryGood 141 := by
  unfold EntryGood
  rw [entry_141_checked]
  decide +kernel
theorem good_141 : Good (rowAt 141) := by
  rw [row_141]
  unfold Good
  decide +kernel

theorem entry_142_checked : entryAt 142 = entry_142 := by
  rw [entry_chunk_6 16 (by decide)]
  decide +kernel
theorem row_142 : rowAt 142 = data_142 := by
  rw [rowAt, dif_neg (by decide : ¬ 142 < 6), entry_142_checked]
  change forkRow [placeRow ⟨72, 4, 2, 3⟩ (rowAt 72), placeRow ⟨32, 1, 4, 3⟩ (rowAt 32), placeRow ⟨55, 2, 5, 4⟩ (rowAt 55)] = data_142
  rw [row_72, row_32, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_142 : EntryGood 142 := by
  unfold EntryGood
  rw [entry_142_checked]
  decide +kernel
theorem good_142 : Good (rowAt 142) := by
  rw [row_142]
  unfold Good
  decide +kernel

theorem entry_143_checked : entryAt 143 = entry_143 := by
  rw [entry_chunk_6 17 (by decide)]
  decide +kernel
theorem row_143 : rowAt 143 = data_143 := by
  rw [rowAt, dif_neg (by decide : ¬ 143 < 6), entry_143_checked]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (rowAt 6), placeRow ⟨108, 0, 8, 5⟩ (rowAt 108)] = data_143
  rw [row_6, row_108]
  apply row_ext <;> decide +kernel
theorem entry_good_143 : EntryGood 143 := by
  unfold EntryGood
  rw [entry_143_checked]
  decide +kernel
theorem good_143 : Good (rowAt 143) := by
  rw [row_143]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks.S213
theorem solution : (rowAt 140 = data_140 ∧ Good (rowAt 140) ∧ EntryGood 140) ∧ (rowAt 141 = data_141 ∧ Good (rowAt 141) ∧ EntryGood 141) ∧ (rowAt 142 = data_142 ∧ Good (rowAt 142) ∧ EntryGood 142) ∧ (rowAt 143 = data_143 ∧ Good (rowAt 143) ∧ EntryGood 143) ∧ True := by
  exact ⟨⟨row_140, good_140, entry_good_140⟩, ⟨row_141, good_141, entry_good_141⟩, ⟨row_142, good_142, entry_good_142⟩, ⟨row_143, good_143, entry_good_143⟩, trivial⟩
