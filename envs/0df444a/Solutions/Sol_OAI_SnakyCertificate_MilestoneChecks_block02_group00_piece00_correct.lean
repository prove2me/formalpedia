-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block02_group00_piece00_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T14:26:39.488597+00:00
-- url     : https://prove2.me/submissions/193cb524-e1e1-4fe6-89c9-a0bb4f16365e

import Definitions.Def_Snaky35Cache02
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_2 (j : ℕ) (hj : j < 20) : entryAt (46 + j) = tableChunk_2[j]?.getD emptyEntry := (chunk_lookups.2.2.1) j hj
theorem entry_chunk_3 (j : ℕ) (hj : j < 20) : entryAt (66 + j) = tableChunk_3[j]?.getD emptyEntry := (chunk_lookups.2.2.2.1) j hj
theorem row_4 : rowAt 4 = data_4 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_9 : rowAt 9 = data_9 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_23 : rowAt 23 = data_23 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_34 : rowAt 34 = data_34 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.1).1
theorem row_41 : rowAt 41 = data_41 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_44 : rowAt 44 = data_44 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_49 : rowAt 49 = data_49 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_53 : rowAt 53 = data_53 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem entry_64_checked : entryAt 64 = entry_64 := by
  rw [entry_chunk_2 18 (by decide)]
  decide +kernel
theorem row_64 : rowAt 64 = data_64 := by
  rw [rowAt, dif_neg (by decide : ¬ 64 < 6), entry_64_checked]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (rowAt 6), placeRow ⟨49, 1, 8, 5⟩ (rowAt 49)] = data_64
  rw [row_6, row_49]
  apply row_ext <;> decide +kernel
theorem entry_good_64 : EntryGood 64 := by
  unfold EntryGood
  rw [entry_64_checked]
  decide +kernel
theorem good_64 : Good (rowAt 64) := by
  rw [row_64]
  unfold Good
  decide +kernel

theorem entry_65_checked : entryAt 65 = entry_65 := by
  rw [entry_chunk_2 19 (by decide)]
  decide +kernel
theorem row_65 : rowAt 65 = data_65 := by
  rw [rowAt, dif_neg (by decide : ¬ 65 < 6), entry_65_checked]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (rowAt 6), placeRow ⟨49, 1, 5, 4⟩ (rowAt 49)] = data_65
  rw [row_6, row_49]
  apply row_ext <;> decide +kernel
theorem entry_good_65 : EntryGood 65 := by
  unfold EntryGood
  rw [entry_65_checked]
  decide +kernel
theorem good_65 : Good (rowAt 65) := by
  rw [row_65]
  unfold Good
  decide +kernel

theorem entry_66_checked : entryAt 66 = entry_66 := by
  rw [entry_chunk_3 0 (by decide)]
  decide +kernel
theorem row_66 : rowAt 66 = data_66 := by
  rw [rowAt, dif_neg (by decide : ¬ 66 < 6), entry_66_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨53, 5, 6, 4⟩ (rowAt 53)] = data_66
  rw [row_6, row_53]
  apply row_ext <;> decide +kernel
theorem entry_good_66 : EntryGood 66 := by
  unfold EntryGood
  rw [entry_66_checked]
  decide +kernel
theorem good_66 : Good (rowAt 66) := by
  rw [row_66]
  unfold Good
  decide +kernel

theorem entry_67_checked : entryAt 67 = entry_67 := by
  rw [entry_chunk_3 1 (by decide)]
  decide +kernel
theorem row_67 : rowAt 67 = data_67 := by
  rw [rowAt, dif_neg (by decide : ¬ 67 < 6), entry_67_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨9, 2, 5, 4⟩ (rowAt 9)] = data_67
  rw [row_6, row_9]
  apply row_ext <;> decide +kernel
theorem entry_good_67 : EntryGood 67 := by
  unfold EntryGood
  rw [entry_67_checked]
  decide +kernel
theorem good_67 : Good (rowAt 67) := by
  rw [row_67]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 64 = data_64 ∧ Good (rowAt 64) ∧ EntryGood 64) ∧ (rowAt 65 = data_65 ∧ Good (rowAt 65) ∧ EntryGood 65) ∧ (rowAt 66 = data_66 ∧ Good (rowAt 66) ∧ EntryGood 66) ∧ (rowAt 67 = data_67 ∧ Good (rowAt 67) ∧ EntryGood 67) ∧ True := by
  exact ⟨⟨row_64, good_64, entry_good_64⟩, ⟨row_65, good_65, entry_good_65⟩, ⟨row_66, good_66, entry_good_66⟩, ⟨row_67, good_67, entry_good_67⟩, trivial⟩
