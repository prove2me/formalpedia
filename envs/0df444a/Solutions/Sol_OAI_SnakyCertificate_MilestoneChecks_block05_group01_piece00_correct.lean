-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block05_group01_piece00_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T08:33:23.090261+00:00
-- url     : https://prove2.me/submissions/24b9f1a0-0878-4a89-a6af-41ad555f3e7e

import Definitions.Def_Snaky35Cache05
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_group03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_group03_piece01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_group03_piece00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks
theorem entry_chunk_8 (j : ℕ) (hj : j < 20) : entryAt (166 + j) = tableChunk_8[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.1) j hj
theorem row_4 : rowAt 4 = data_4 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_28 : rowAt 28 = data_28 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_91 : rowAt 91 = data_91 := (OAI.SnakyCertificate.MilestoneChecks.block02_group03_correct.2.2.2.1).1
theorem row_127 : rowAt 127 = data_127 := (OAI.SnakyCertificate.MilestoneChecks.block03_group03_piece01_correct.2.2.2.1).1
theorem row_152 : rowAt 152 = data_152 := (OAI.SnakyCertificate.MilestoneChecks.block04_group03_piece00_correct.1).1
theorem entry_168_checked : entryAt 168 = entry_168 := by
  rw [entry_chunk_8 2 (by decide)]
  decide +kernel
theorem row_168 : rowAt 168 = data_168 := by
  rw [rowAt, dif_neg (by decide : ¬ 168 < 6), entry_168_checked]
  change forkRow [placeRow ⟨6, 1, 5, 5⟩ (rowAt 6), placeRow ⟨152, 0, 3, 4⟩ (rowAt 152)] = data_168
  rw [row_6, row_152]
  apply row_ext <;> decide +kernel
theorem entry_good_168 : EntryGood 168 := by
  unfold EntryGood
  rw [entry_168_checked]
  decide +kernel
theorem good_168 : Good (rowAt 168) := by
  rw [row_168]
  unfold Good
  decide +kernel

theorem entry_169_checked : entryAt 169 = entry_169 := by
  rw [entry_chunk_8 3 (by decide)]
  decide +kernel
theorem row_169 : rowAt 169 = data_169 := by
  rw [rowAt, dif_neg (by decide : ¬ 169 < 6), entry_169_checked]
  change forkRow [placeRow ⟨28, 3, 4, 5⟩ (rowAt 28), placeRow ⟨63, 1, 8, 3⟩ (rowAt 63)] = data_169
  rw [row_28, row_63]
  apply row_ext <;> decide +kernel
theorem entry_good_169 : EntryGood 169 := by
  unfold EntryGood
  rw [entry_169_checked]
  decide +kernel
theorem good_169 : Good (rowAt 169) := by
  rw [row_169]
  unfold Good
  decide +kernel

theorem entry_170_checked : entryAt 170 = entry_170 := by
  rw [entry_chunk_8 4 (by decide)]
  decide +kernel
theorem row_170 : rowAt 170 = data_170 := by
  rw [rowAt, dif_neg (by decide : ¬ 170 < 6), entry_170_checked]
  change forkRow [placeRow ⟨4, 6, 1, 3⟩ (rowAt 4), placeRow ⟨127, 2, 5, 4⟩ (rowAt 127)] = data_170
  rw [row_4, row_127]
  apply row_ext <;> decide +kernel
theorem entry_good_170 : EntryGood 170 := by
  unfold EntryGood
  rw [entry_170_checked]
  decide +kernel
theorem good_170 : Good (rowAt 170) := by
  rw [row_170]
  unfold Good
  decide +kernel

theorem entry_171_checked : entryAt 171 = entry_171 := by
  rw [entry_chunk_8 5 (by decide)]
  decide +kernel
theorem row_171 : rowAt 171 = data_171 := by
  rw [rowAt, dif_neg (by decide : ¬ 171 < 6), entry_171_checked]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (rowAt 6), placeRow ⟨91, 0, 0, 5⟩ (rowAt 91)] = data_171
  rw [row_6, row_91]
  apply row_ext <;> decide +kernel
theorem entry_good_171 : EntryGood 171 := by
  unfold EntryGood
  rw [entry_171_checked]
  decide +kernel
theorem good_171 : Good (rowAt 171) := by
  rw [row_171]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks.S213
theorem solution : (rowAt 168 = data_168 ∧ Good (rowAt 168) ∧ EntryGood 168) ∧ (rowAt 169 = data_169 ∧ Good (rowAt 169) ∧ EntryGood 169) ∧ (rowAt 170 = data_170 ∧ Good (rowAt 170) ∧ EntryGood 170) ∧ (rowAt 171 = data_171 ∧ Good (rowAt 171) ∧ EntryGood 171) ∧ True := by
  exact ⟨⟨row_168, good_168, entry_good_168⟩, ⟨row_169, good_169, entry_good_169⟩, ⟨row_170, good_170, entry_good_170⟩, ⟨row_171, good_171, entry_good_171⟩, trivial⟩
