-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block04_group02_piece00_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T08:22:40.853402+00:00
-- url     : https://prove2.me/submissions/f457477a-62f1-4a40-8897-e63ddeb2640d

import Definitions.Def_Snaky35Cache04
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_group03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_group01_piece00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks
theorem entry_chunk_6 (j : ℕ) (hj : j < 20) : entryAt (126 + j) = tableChunk_6[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.1) j hj
theorem entry_chunk_7 (j : ℕ) (hj : j < 20) : entryAt (146 + j) = tableChunk_7[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.1).1
theorem row_7 : rowAt 7 = data_7 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.1).1
theorem row_24 : rowAt 24 = data_24 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_36 : rowAt 36 = data_36 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.1).1
theorem row_44 : rowAt 44 = data_44 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_53 : rowAt 53 = data_53 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_55 : rowAt 55 = data_55 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_91 : rowAt 91 = data_91 := (OAI.SnakyCertificate.MilestoneChecks.block02_group03_correct.2.2.2.1).1
theorem row_104 : rowAt 104 = data_104 := (OAI.SnakyCertificate.MilestoneChecks.block03_group01_piece00_correct.1).1
theorem entry_144_checked : entryAt 144 = entry_144 := by
  rw [entry_chunk_6 18 (by decide)]
  decide +kernel
theorem row_144 : rowAt 144 = data_144 := by
  rw [rowAt, dif_neg (by decide : ¬ 144 < 6), entry_144_checked]
  change forkRow [placeRow ⟨7, 0, 4, 5⟩ (rowAt 7), placeRow ⟨104, 4, 1, 5⟩ (rowAt 104), placeRow ⟨55, 0, 5, 4⟩ (rowAt 55)] = data_144
  rw [row_7, row_104, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_144 : EntryGood 144 := by
  unfold EntryGood
  rw [entry_144_checked]
  decide +kernel
theorem good_144 : Good (rowAt 144) := by
  rw [row_144]
  unfold Good
  decide +kernel

theorem entry_145_checked : entryAt 145 = entry_145 := by
  rw [entry_chunk_6 19 (by decide)]
  decide +kernel
theorem row_145 : rowAt 145 = data_145 := by
  rw [rowAt, dif_neg (by decide : ¬ 145 < 6), entry_145_checked]
  change forkRow [placeRow ⟨0, 5, 4, 5⟩ (rowAt 0), placeRow ⟨91, 0, 3, 4⟩ (rowAt 91)] = data_145
  rw [row_0, row_91]
  apply row_ext <;> decide +kernel
theorem entry_good_145 : EntryGood 145 := by
  unfold EntryGood
  rw [entry_145_checked]
  decide +kernel
theorem good_145 : Good (rowAt 145) := by
  rw [row_145]
  unfold Good
  decide +kernel

theorem entry_146_checked : entryAt 146 = entry_146 := by
  rw [entry_chunk_7 0 (by decide)]
  decide +kernel
theorem row_146 : rowAt 146 = data_146 := by
  rw [rowAt, dif_neg (by decide : ¬ 146 < 6), entry_146_checked]
  change forkRow [placeRow ⟨36, 6, 5, 4⟩ (rowAt 36), placeRow ⟨24, 1, 4, 5⟩ (rowAt 24)] = data_146
  rw [row_36, row_24]
  apply row_ext <;> decide +kernel
theorem entry_good_146 : EntryGood 146 := by
  unfold EntryGood
  rw [entry_146_checked]
  decide +kernel
theorem good_146 : Good (rowAt 146) := by
  rw [row_146]
  unfold Good
  decide +kernel

theorem entry_147_checked : entryAt 147 = entry_147 := by
  rw [entry_chunk_7 1 (by decide)]
  decide +kernel
theorem row_147 : rowAt 147 = data_147 := by
  rw [rowAt, dif_neg (by decide : ¬ 147 < 6), entry_147_checked]
  change forkRow [placeRow ⟨53, 0, 1, 5⟩ (rowAt 53), placeRow ⟨44, 2, 5, 4⟩ (rowAt 44)] = data_147
  rw [row_53, row_44]
  apply row_ext <;> decide +kernel
theorem entry_good_147 : EntryGood 147 := by
  unfold EntryGood
  rw [entry_147_checked]
  decide +kernel
theorem good_147 : Good (rowAt 147) := by
  rw [row_147]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks.S213
theorem solution : (rowAt 144 = data_144 ∧ Good (rowAt 144) ∧ EntryGood 144) ∧ (rowAt 145 = data_145 ∧ Good (rowAt 145) ∧ EntryGood 145) ∧ (rowAt 146 = data_146 ∧ Good (rowAt 146) ∧ EntryGood 146) ∧ (rowAt 147 = data_147 ∧ Good (rowAt 147) ∧ EntryGood 147) ∧ True := by
  exact ⟨⟨row_144, good_144, entry_good_144⟩, ⟨row_145, good_145, entry_good_145⟩, ⟨row_146, good_146, entry_good_146⟩, ⟨row_147, good_147, entry_good_147⟩, trivial⟩
