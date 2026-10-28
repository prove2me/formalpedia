-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block03_group02_piece00_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T07:51:43.28879+00:00
-- url     : https://prove2.me/submissions/68c35a3a-ee69-4ec5-ac4e-efb4dc69ea56

import Definitions.Def_Snaky35Cache03
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_group00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_group03_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks
theorem entry_chunk_5 (j : ℕ) (hj : j < 20) : entryAt (106 + j) = tableChunk_5[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.1) j hj
theorem row_1 : rowAt 1 = data_1 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.1).1
theorem row_4 : rowAt 4 = data_4 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_36 : rowAt 36 = data_36 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.1).1
theorem row_67 : rowAt 67 = data_67 := (OAI.SnakyCertificate.MilestoneChecks.block02_group00_correct.2.2.2.1).1
theorem row_70 : rowAt 70 = data_70 := (OAI.SnakyCertificate.MilestoneChecks.block02_group00_correct.2.2.2.2.2.2.1).1
theorem row_93 : rowAt 93 = data_93 := (OAI.SnakyCertificate.MilestoneChecks.block02_group03_correct.2.2.2.2.2.1).1
theorem entry_112_checked : entryAt 112 = entry_112 := by
  rw [entry_chunk_5 6 (by decide)]
  decide +kernel
theorem row_112 : rowAt 112 = data_112 := by
  rw [rowAt, dif_neg (by decide : ¬ 112 < 6), entry_112_checked]
  change forkRow [placeRow ⟨4, 1, 5, 4⟩ (rowAt 4), placeRow ⟨93, 0, 3, 5⟩ (rowAt 93)] = data_112
  rw [row_4, row_93]
  apply row_ext <;> decide +kernel
theorem entry_good_112 : EntryGood 112 := by
  unfold EntryGood
  rw [entry_112_checked]
  decide +kernel
theorem good_112 : Good (rowAt 112) := by
  rw [row_112]
  unfold Good
  decide +kernel

theorem entry_113_checked : entryAt 113 = entry_113 := by
  rw [entry_chunk_5 7 (by decide)]
  decide +kernel
theorem row_113 : rowAt 113 = data_113 := by
  rw [rowAt, dif_neg (by decide : ¬ 113 < 6), entry_113_checked]
  change forkRow [placeRow ⟨1, 6, 6, 4⟩ (rowAt 1), placeRow ⟨36, 6, 7, 5⟩ (rowAt 36)] = data_113
  rw [row_1, row_36]
  apply row_ext <;> decide +kernel
theorem entry_good_113 : EntryGood 113 := by
  unfold EntryGood
  rw [entry_113_checked]
  decide +kernel
theorem good_113 : Good (rowAt 113) := by
  rw [row_113]
  unfold Good
  decide +kernel

theorem entry_114_checked : entryAt 114 = entry_114 := by
  rw [entry_chunk_5 8 (by decide)]
  decide +kernel
theorem row_114 : rowAt 114 = data_114 := by
  rw [rowAt, dif_neg (by decide : ¬ 114 < 6), entry_114_checked]
  change forkRow [placeRow ⟨6, 0, 6, 5⟩ (rowAt 6), placeRow ⟨67, 3, 2, 5⟩ (rowAt 67)] = data_114
  rw [row_6, row_67]
  apply row_ext <;> decide +kernel
theorem entry_good_114 : EntryGood 114 := by
  unfold EntryGood
  rw [entry_114_checked]
  decide +kernel
theorem good_114 : Good (rowAt 114) := by
  rw [row_114]
  unfold Good
  decide +kernel

theorem entry_115_checked : entryAt 115 = entry_115 := by
  rw [entry_chunk_5 9 (by decide)]
  decide +kernel
theorem row_115 : rowAt 115 = data_115 := by
  rw [rowAt, dif_neg (by decide : ¬ 115 < 6), entry_115_checked]
  change forkRow [placeRow ⟨6, 2, 7, 3⟩ (rowAt 6), placeRow ⟨70, 7, 2, 5⟩ (rowAt 70)] = data_115
  rw [row_6, row_70]
  apply row_ext <;> decide +kernel
theorem entry_good_115 : EntryGood 115 := by
  unfold EntryGood
  rw [entry_115_checked]
  decide +kernel
theorem good_115 : Good (rowAt 115) := by
  rw [row_115]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks.S213
theorem solution : (rowAt 112 = data_112 ∧ Good (rowAt 112) ∧ EntryGood 112) ∧ (rowAt 113 = data_113 ∧ Good (rowAt 113) ∧ EntryGood 113) ∧ (rowAt 114 = data_114 ∧ Good (rowAt 114) ∧ EntryGood 114) ∧ (rowAt 115 = data_115 ∧ Good (rowAt 115) ∧ EntryGood 115) ∧ True := by
  exact ⟨⟨row_112, good_112, entry_good_112⟩, ⟨row_113, good_113, entry_good_113⟩, ⟨row_114, good_114, entry_good_114⟩, ⟨row_115, good_115, entry_good_115⟩, trivial⟩
