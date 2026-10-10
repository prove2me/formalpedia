-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block02_group02_piece00_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T14:35:57.714069+00:00
-- url     : https://prove2.me/submissions/515fc678-0501-40ea-9e0c-6f56fbc97a64

import Definitions.Def_Snaky35Cache02
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_group00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_3 (j : ℕ) (hj : j < 20) : entryAt (66 + j) = tableChunk_3[j]?.getD emptyEntry := (chunk_lookups.2.2.2.1) j hj
theorem entry_chunk_4 (j : ℕ) (hj : j < 20) : entryAt (86 + j) = tableChunk_4[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.1).1
theorem row_4 : rowAt 4 = data_4 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_8 : rowAt 8 = data_8 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.1).1
theorem row_9 : rowAt 9 = data_9 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_13 : rowAt 13 = data_13 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_24 : rowAt 24 = data_24 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_36 : rowAt 36 = data_36 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.1).1
theorem row_43 : rowAt 43 = data_43 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_67 : rowAt 67 = data_67 := (OAI.SnakyCertificate.MilestoneChecks.block02_group00_correct.2.2.2.1).1
theorem entry_80_checked : entryAt 80 = entry_80 := by
  rw [entry_chunk_3 14 (by decide)]
  decide +kernel
theorem row_80 : rowAt 80 = data_80 := by
  rw [rowAt, dif_neg (by decide : ¬ 80 < 6), entry_80_checked]
  change forkRow [placeRow ⟨0, 6, 6, 4⟩ (rowAt 0), placeRow ⟨13, 4, 2, 4⟩ (rowAt 13)] = data_80
  rw [row_0, row_13]
  apply row_ext <;> decide +kernel
theorem entry_good_80 : EntryGood 80 := by
  unfold EntryGood
  rw [entry_80_checked]
  decide +kernel
theorem good_80 : Good (rowAt 80) := by
  rw [row_80]
  unfold Good
  decide +kernel

theorem entry_81_checked : entryAt 81 = entry_81 := by
  rw [entry_chunk_3 15 (by decide)]
  decide +kernel
theorem row_81 : rowAt 81 = data_81 := by
  rw [rowAt, dif_neg (by decide : ¬ 81 < 6), entry_81_checked]
  change forkRow [placeRow ⟨4, 3, 4, 3⟩ (rowAt 4), placeRow ⟨43, 0, 5, 4⟩ (rowAt 43)] = data_81
  rw [row_4, row_43]
  apply row_ext <;> decide +kernel
theorem entry_good_81 : EntryGood 81 := by
  unfold EntryGood
  rw [entry_81_checked]
  decide +kernel
theorem good_81 : Good (rowAt 81) := by
  rw [row_81]
  unfold Good
  decide +kernel

theorem entry_82_checked : entryAt 82 = entry_82 := by
  rw [entry_chunk_3 16 (by decide)]
  decide +kernel
theorem row_82 : rowAt 82 = data_82 := by
  rw [rowAt, dif_neg (by decide : ¬ 82 < 6), entry_82_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨36, 0, 1, 3⟩ (rowAt 36)] = data_82
  rw [row_6, row_36]
  apply row_ext <;> decide +kernel
theorem entry_good_82 : EntryGood 82 := by
  unfold EntryGood
  rw [entry_82_checked]
  decide +kernel
theorem good_82 : Good (rowAt 82) := by
  rw [row_82]
  unfold Good
  decide +kernel

theorem entry_83_checked : entryAt 83 = entry_83 := by
  rw [entry_chunk_3 17 (by decide)]
  decide +kernel
theorem row_83 : rowAt 83 = data_83 := by
  rw [rowAt, dif_neg (by decide : ¬ 83 < 6), entry_83_checked]
  change forkRow [placeRow ⟨0, 7, 5, 7⟩ (rowAt 0), placeRow ⟨67, 2, 6, 3⟩ (rowAt 67)] = data_83
  rw [row_0, row_67]
  apply row_ext <;> decide +kernel
theorem entry_good_83 : EntryGood 83 := by
  unfold EntryGood
  rw [entry_83_checked]
  decide +kernel
theorem good_83 : Good (rowAt 83) := by
  rw [row_83]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 80 = data_80 ∧ Good (rowAt 80) ∧ EntryGood 80) ∧ (rowAt 81 = data_81 ∧ Good (rowAt 81) ∧ EntryGood 81) ∧ (rowAt 82 = data_82 ∧ Good (rowAt 82) ∧ EntryGood 82) ∧ (rowAt 83 = data_83 ∧ Good (rowAt 83) ∧ EntryGood 83) ∧ True := by
  exact ⟨⟨row_80, good_80, entry_good_80⟩, ⟨row_81, good_81, entry_good_81⟩, ⟨row_82, good_82, entry_good_82⟩, ⟨row_83, good_83, entry_good_83⟩, trivial⟩
