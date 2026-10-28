-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block05_group00_piece00_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T08:29:22.984636+00:00
-- url     : https://prove2.me/submissions/0c103112-8858-49ca-b0dc-09e8de90e0e7

import Definitions.Def_Snaky35Cache04
import Definitions.Def_Snaky35Cache05
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_group02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_group03_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks
theorem entry_chunk_7 (j : ℕ) (hj : j < 20) : entryAt (146 + j) = tableChunk_7[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.1) j hj
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_7 : rowAt 7 = data_7 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.1).1
theorem row_15 : rowAt 15 = data_15 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_32 : rowAt 32 = data_32 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.1).1
theorem row_44 : rowAt 44 = data_44 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_49 : rowAt 49 = data_49 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_56 : rowAt 56 = data_56 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_57 : rowAt 57 = data_57 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_86 : rowAt 86 = data_86 := (OAI.SnakyCertificate.MilestoneChecks.block02_group02_correct.2.2.2.2.2.2.1).1
theorem row_127 : rowAt 127 = data_127 := (OAI.SnakyCertificate.MilestoneChecks.block03_group03_piece01_correct.2.2.2.1).1
theorem entry_157_checked : entryAt 157 = entry_157 := by
  rw [entry_chunk_7 11 (by decide)]
  decide +kernel
theorem row_157 : rowAt 157 = data_157 := by
  rw [rowAt, dif_neg (by decide : ¬ 157 < 6), entry_157_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨57, 1, 5, 6⟩ (rowAt 57)] = data_157
  rw [row_6, row_57]
  apply row_ext <;> decide +kernel

theorem entry_160_checked : entryAt 160 = entry_160 := by
  rw [entry_chunk_7 14 (by decide)]
  decide +kernel
theorem row_160 : rowAt 160 = data_160 := by
  rw [rowAt, dif_neg (by decide : ¬ 160 < 6), entry_160_checked]
  change forkRow [placeRow ⟨63, 1, 8, 3⟩ (rowAt 63), placeRow ⟨32, 3, 4, 3⟩ (rowAt 32)] = data_160
  rw [row_63, row_32]
  apply row_ext <;> decide +kernel
theorem entry_good_160 : EntryGood 160 := by
  unfold EntryGood
  rw [entry_160_checked]
  decide +kernel
theorem good_160 : Good (rowAt 160) := by
  rw [row_160]
  unfold Good
  decide +kernel

theorem entry_161_checked : entryAt 161 = entry_161 := by
  rw [entry_chunk_7 15 (by decide)]
  decide +kernel
theorem row_161 : rowAt 161 = data_161 := by
  rw [rowAt, dif_neg (by decide : ¬ 161 < 6), entry_161_checked]
  change forkRow [placeRow ⟨15, 1, 4, 5⟩ (rowAt 15), placeRow ⟨86, 0, 5, 4⟩ (rowAt 86)] = data_161
  rw [row_15, row_86]
  apply row_ext <;> decide +kernel
theorem entry_good_161 : EntryGood 161 := by
  unfold EntryGood
  rw [entry_161_checked]
  decide +kernel
theorem good_161 : Good (rowAt 161) := by
  rw [row_161]
  unfold Good
  decide +kernel

theorem entry_162_checked : entryAt 162 = entry_162 := by
  rw [entry_chunk_7 16 (by decide)]
  decide +kernel
theorem row_162 : rowAt 162 = data_162 := by
  rw [rowAt, dif_neg (by decide : ¬ 162 < 6), entry_162_checked]
  change forkRow [placeRow ⟨7, 3, 3, 4⟩ (rowAt 7), placeRow ⟨127, 1, 4, 5⟩ (rowAt 127), placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨157, 0, 3, 3⟩ (rowAt 157)] = data_162
  rw [row_7, row_127, row_63, row_157]
  apply row_ext <;> decide +kernel
theorem entry_good_162 : EntryGood 162 := by
  unfold EntryGood
  rw [entry_162_checked]
  decide +kernel
theorem good_162 : Good (rowAt 162) := by
  rw [row_162]
  unfold Good
  decide +kernel

theorem entry_163_checked : entryAt 163 = entry_163 := by
  rw [entry_chunk_7 17 (by decide)]
  decide +kernel
theorem row_163 : rowAt 163 = data_163 := by
  rw [rowAt, dif_neg (by decide : ¬ 163 < 6), entry_163_checked]
  change forkRow [placeRow ⟨44, 2, 5, 4⟩ (rowAt 44), placeRow ⟨49, 1, 5, 4⟩ (rowAt 49), placeRow ⟨56, 4, 0, 4⟩ (rowAt 56)] = data_163
  rw [row_44, row_49, row_56]
  apply row_ext <;> decide +kernel
theorem entry_good_163 : EntryGood 163 := by
  unfold EntryGood
  rw [entry_163_checked]
  decide +kernel
theorem good_163 : Good (rowAt 163) := by
  rw [row_163]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks.S213
theorem solution : (rowAt 160 = data_160 ∧ Good (rowAt 160) ∧ EntryGood 160) ∧ (rowAt 161 = data_161 ∧ Good (rowAt 161) ∧ EntryGood 161) ∧ (rowAt 162 = data_162 ∧ Good (rowAt 162) ∧ EntryGood 162) ∧ (rowAt 163 = data_163 ∧ Good (rowAt 163) ∧ EntryGood 163) ∧ True := by
  exact ⟨⟨row_160, good_160, entry_good_160⟩, ⟨row_161, good_161, entry_good_161⟩, ⟨row_162, good_162, entry_good_162⟩, ⟨row_163, good_163, entry_good_163⟩, trivial⟩
