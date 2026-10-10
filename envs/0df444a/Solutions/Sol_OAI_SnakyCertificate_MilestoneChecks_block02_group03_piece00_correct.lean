-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block02_group03_piece00_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T14:36:31.017983+00:00
-- url     : https://prove2.me/submissions/065f0c6b-fbaf-443a-8eec-191ee72d4589

import Definitions.Def_Snaky35Cache02
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_group00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_group01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_4 (j : ℕ) (hj : j < 20) : entryAt (86 + j) = tableChunk_4[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.1).1
theorem row_4 : rowAt 4 = data_4 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_7 : rowAt 7 = data_7 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.1).1
theorem row_8 : rowAt 8 = data_8 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.1).1
theorem row_27 : rowAt 27 = data_27 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_29 : rowAt 29 = data_29 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_31 : rowAt 31 = data_31 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_33 : rowAt 33 = data_33 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.1).1
theorem row_47 : rowAt 47 = data_47 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_54 : rowAt 54 = data_54 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_67 : rowAt 67 = data_67 := (OAI.SnakyCertificate.MilestoneChecks.block02_group00_correct.2.2.2.1).1
theorem row_74 : rowAt 74 = data_74 := (OAI.SnakyCertificate.MilestoneChecks.block02_group01_correct.2.2.1).1
theorem entry_88_checked : entryAt 88 = entry_88 := by
  rw [entry_chunk_4 2 (by decide)]
  decide +kernel
theorem row_88 : rowAt 88 = data_88 := by
  rw [rowAt, dif_neg (by decide : ¬ 88 < 6), entry_88_checked]
  change forkRow [placeRow ⟨0, 6, 6, 4⟩ (rowAt 0), placeRow ⟨67, 3, 2, 5⟩ (rowAt 67)] = data_88
  rw [row_0, row_67]
  apply row_ext <;> decide +kernel
theorem entry_good_88 : EntryGood 88 := by
  unfold EntryGood
  rw [entry_88_checked]
  decide +kernel
theorem good_88 : Good (rowAt 88) := by
  rw [row_88]
  unfold Good
  decide +kernel

theorem entry_89_checked : entryAt 89 = entry_89 := by
  rw [entry_chunk_4 3 (by decide)]
  decide +kernel
theorem row_89 : rowAt 89 = data_89 := by
  rw [rowAt, dif_neg (by decide : ¬ 89 < 6), entry_89_checked]
  change forkRow [placeRow ⟨8, 3, 3, 1⟩ (rowAt 8), placeRow ⟨7, 1, 5, 4⟩ (rowAt 7)] = data_89
  rw [row_8, row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_89 : EntryGood 89 := by
  unfold EntryGood
  rw [entry_89_checked]
  decide +kernel
theorem good_89 : Good (rowAt 89) := by
  rw [row_89]
  unfold Good
  decide +kernel

theorem entry_90_checked : entryAt 90 = entry_90 := by
  rw [entry_chunk_4 4 (by decide)]
  decide +kernel
theorem row_90 : rowAt 90 = data_90 := by
  rw [rowAt, dif_neg (by decide : ¬ 90 < 6), entry_90_checked]
  change forkRow [placeRow ⟨31, 0, 3, 3⟩ (rowAt 31), placeRow ⟨54, 6, 0, 3⟩ (rowAt 54), placeRow ⟨54, 0, 5, 4⟩ (rowAt 54), placeRow ⟨31, 6, 2, 4⟩ (rowAt 31)] = data_90
  rw [row_31, row_54]
  apply row_ext <;> decide +kernel
theorem entry_good_90 : EntryGood 90 := by
  unfold EntryGood
  rw [entry_90_checked]
  decide +kernel
theorem good_90 : Good (rowAt 90) := by
  rw [row_90]
  unfold Good
  decide +kernel

theorem entry_91_checked : entryAt 91 = entry_91 := by
  rw [entry_chunk_4 5 (by decide)]
  decide +kernel
theorem row_91 : rowAt 91 = data_91 := by
  rw [rowAt, dif_neg (by decide : ¬ 91 < 6), entry_91_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨74, 5, 7, 3⟩ (rowAt 74)] = data_91
  rw [row_6, row_74]
  apply row_ext <;> decide +kernel
theorem entry_good_91 : EntryGood 91 := by
  unfold EntryGood
  rw [entry_91_checked]
  decide +kernel
theorem good_91 : Good (rowAt 91) := by
  rw [row_91]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 88 = data_88 ∧ Good (rowAt 88) ∧ EntryGood 88) ∧ (rowAt 89 = data_89 ∧ Good (rowAt 89) ∧ EntryGood 89) ∧ (rowAt 90 = data_90 ∧ Good (rowAt 90) ∧ EntryGood 90) ∧ (rowAt 91 = data_91 ∧ Good (rowAt 91) ∧ EntryGood 91) ∧ True := by
  exact ⟨⟨row_88, good_88, entry_good_88⟩, ⟨row_89, good_89, entry_good_89⟩, ⟨row_90, good_90, entry_good_90⟩, ⟨row_91, good_91, entry_good_91⟩, trivial⟩
