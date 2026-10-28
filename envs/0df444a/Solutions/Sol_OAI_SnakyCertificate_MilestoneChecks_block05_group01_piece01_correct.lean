-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block05_group01_piece01_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T08:35:30.652449+00:00
-- url     : https://prove2.me/submissions/cb7ac28f-9031-4be5-ade0-676429eeb80f

import Definitions.Def_Snaky35Cache05
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_group00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_group02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_group01_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks
theorem entry_chunk_8 (j : ℕ) (hj : j < 20) : entryAt (166 + j) = tableChunk_8[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.1) j hj
theorem row_7 : rowAt 7 = data_7 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.1).1
theorem row_55 : rowAt 55 = data_55 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_57 : rowAt 57 = data_57 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_58 : rowAt 58 = data_58 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_64 : rowAt 64 = data_64 := (OAI.SnakyCertificate.MilestoneChecks.block02_group00_correct.1).1
theorem row_84 : rowAt 84 = data_84 := (OAI.SnakyCertificate.MilestoneChecks.block02_group02_correct.2.2.2.2.1).1
theorem row_141 : rowAt 141 = data_141 := (OAI.SnakyCertificate.MilestoneChecks.block04_group01_piece01_correct.2.1).1
theorem entry_172_checked : entryAt 172 = entry_172 := by
  rw [entry_chunk_8 6 (by decide)]
  decide +kernel
theorem row_172 : rowAt 172 = data_172 := by
  rw [rowAt, dif_neg (by decide : ¬ 172 < 6), entry_172_checked]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨55, 6, 0, 4⟩ (rowAt 55), placeRow ⟨64, 0, 1, 3⟩ (rowAt 64)] = data_172
  rw [row_63, row_55, row_64]
  apply row_ext <;> decide +kernel
theorem entry_good_172 : EntryGood 172 := by
  unfold EntryGood
  rw [entry_172_checked]
  decide +kernel
theorem good_172 : Good (rowAt 172) := by
  rw [row_172]
  unfold Good
  decide +kernel

theorem entry_173_checked : entryAt 173 = entry_173 := by
  rw [entry_chunk_8 7 (by decide)]
  decide +kernel
theorem row_173 : rowAt 173 = data_173 := by
  rw [rowAt, dif_neg (by decide : ¬ 173 < 6), entry_173_checked]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨64, 6, 4, 5⟩ (rowAt 64), placeRow ⟨55, 6, 0, 4⟩ (rowAt 55)] = data_173
  rw [row_63, row_64, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_173 : EntryGood 173 := by
  unfold EntryGood
  rw [entry_173_checked]
  decide +kernel
theorem good_173 : Good (rowAt 173) := by
  rw [row_173]
  unfold Good
  decide +kernel

theorem entry_174_checked : entryAt 174 = entry_174 := by
  rw [entry_chunk_8 8 (by decide)]
  decide +kernel
theorem row_174 : rowAt 174 = data_174 := by
  rw [rowAt, dif_neg (by decide : ¬ 174 < 6), entry_174_checked]
  change forkRow [placeRow ⟨58, 3, 4, 5⟩ (rowAt 58), placeRow ⟨57, 1, 4, 5⟩ (rowAt 57), placeRow ⟨84, 0, 3, 4⟩ (rowAt 84)] = data_174
  rw [row_58, row_57, row_84]
  apply row_ext <;> decide +kernel
theorem entry_good_174 : EntryGood 174 := by
  unfold EntryGood
  rw [entry_174_checked]
  decide +kernel
theorem good_174 : Good (rowAt 174) := by
  rw [row_174]
  unfold Good
  decide +kernel

theorem entry_175_checked : entryAt 175 = entry_175 := by
  rw [entry_chunk_8 9 (by decide)]
  decide +kernel
theorem row_175 : rowAt 175 = data_175 := by
  rw [rowAt, dif_neg (by decide : ¬ 175 < 6), entry_175_checked]
  change forkRow [placeRow ⟨141, 0, 5, 4⟩ (rowAt 141), placeRow ⟨7, 2, 4, 3⟩ (rowAt 7), placeRow ⟨63, 1, 5, 3⟩ (rowAt 63)] = data_175
  rw [row_141, row_7, row_63]
  apply row_ext <;> decide +kernel
theorem entry_good_175 : EntryGood 175 := by
  unfold EntryGood
  rw [entry_175_checked]
  decide +kernel
theorem good_175 : Good (rowAt 175) := by
  rw [row_175]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks.S213
theorem solution : (rowAt 172 = data_172 ∧ Good (rowAt 172) ∧ EntryGood 172) ∧ (rowAt 173 = data_173 ∧ Good (rowAt 173) ∧ EntryGood 173) ∧ (rowAt 174 = data_174 ∧ Good (rowAt 174) ∧ EntryGood 174) ∧ (rowAt 175 = data_175 ∧ Good (rowAt 175) ∧ EntryGood 175) ∧ True := by
  exact ⟨⟨row_172, good_172, entry_good_172⟩, ⟨row_173, good_173, entry_good_173⟩, ⟨row_174, good_174, entry_good_174⟩, ⟨row_175, good_175, entry_good_175⟩, trivial⟩
