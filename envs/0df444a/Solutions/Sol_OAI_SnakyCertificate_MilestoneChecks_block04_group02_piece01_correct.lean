-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block04_group02_piece01_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T08:24:18.096119+00:00
-- url     : https://prove2.me/submissions/3e24a4b5-a35f-454f-a0bb-412d1dbdb21f

import Definitions.Def_Snaky35Cache04
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_group03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_group00_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_group00_piece01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_group03_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks
theorem entry_chunk_7 (j : ℕ) (hj : j < 20) : entryAt (146 + j) = tableChunk_7[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.1) j hj
theorem row_2 : rowAt 2 = data_2 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.1).1
theorem row_4 : rowAt 4 = data_4 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.1).1
theorem row_7 : rowAt 7 = data_7 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.1).1
theorem row_16 : rowAt 16 = data_16 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_24 : rowAt 24 = data_24 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_46 : rowAt 46 = data_46 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_94 : rowAt 94 = data_94 := (OAI.SnakyCertificate.MilestoneChecks.block02_group03_correct.2.2.2.2.2.2.1).1
theorem row_97 : rowAt 97 = data_97 := (OAI.SnakyCertificate.MilestoneChecks.block03_group00_piece00_correct.2.1).1
theorem row_101 : rowAt 101 = data_101 := (OAI.SnakyCertificate.MilestoneChecks.block03_group00_piece01_correct.2.1).1
theorem row_126 : rowAt 126 = data_126 := (OAI.SnakyCertificate.MilestoneChecks.block03_group03_piece01_correct.2.2.1).1
theorem entry_148_checked : entryAt 148 = entry_148 := by
  rw [entry_chunk_7 2 (by decide)]
  decide +kernel
theorem row_148 : rowAt 148 = data_148 := by
  rw [rowAt, dif_neg (by decide : ¬ 148 < 6), entry_148_checked]
  change forkRow [placeRow ⟨7, 1, 5, 4⟩ (rowAt 7), placeRow ⟨46, 1, 4, 5⟩ (rowAt 46), placeRow ⟨94, 0, 5, 3⟩ (rowAt 94), placeRow ⟨97, 1, 4, 5⟩ (rowAt 97)] = data_148
  rw [row_7, row_46, row_94, row_97]
  apply row_ext <;> decide +kernel
theorem entry_good_148 : EntryGood 148 := by
  unfold EntryGood
  rw [entry_148_checked]
  decide +kernel
theorem good_148 : Good (rowAt 148) := by
  rw [row_148]
  unfold Good
  decide +kernel

theorem entry_149_checked : entryAt 149 = entry_149 := by
  rw [entry_chunk_7 3 (by decide)]
  decide +kernel
theorem row_149 : rowAt 149 = data_149 := by
  rw [rowAt, dif_neg (by decide : ¬ 149 < 6), entry_149_checked]
  change forkRow [placeRow ⟨16, 1, 4, 3⟩ (rowAt 16), placeRow ⟨24, 2, 5, 4⟩ (rowAt 24)] = data_149
  rw [row_16, row_24]
  apply row_ext <;> decide +kernel
theorem entry_good_149 : EntryGood 149 := by
  unfold EntryGood
  rw [entry_149_checked]
  decide +kernel
theorem good_149 : Good (rowAt 149) := by
  rw [row_149]
  unfold Good
  decide +kernel

theorem entry_150_checked : entryAt 150 = entry_150 := by
  rw [entry_chunk_7 4 (by decide)]
  decide +kernel
theorem row_150 : rowAt 150 = data_150 := by
  rw [rowAt, dif_neg (by decide : ¬ 150 < 6), entry_150_checked]
  change forkRow [placeRow ⟨4, 6, 1, 3⟩ (rowAt 4), placeRow ⟨126, 5, 2, 5⟩ (rowAt 126)] = data_150
  rw [row_4, row_126]
  apply row_ext <;> decide +kernel
theorem entry_good_150 : EntryGood 150 := by
  unfold EntryGood
  rw [entry_150_checked]
  decide +kernel
theorem good_150 : Good (rowAt 150) := by
  rw [row_150]
  unfold Good
  decide +kernel

theorem entry_151_checked : entryAt 151 = entry_151 := by
  rw [entry_chunk_7 5 (by decide)]
  decide +kernel
theorem row_151 : rowAt 151 = data_151 := by
  rw [rowAt, dif_neg (by decide : ¬ 151 < 6), entry_151_checked]
  change forkRow [placeRow ⟨2, 1, 4, 3⟩ (rowAt 2), placeRow ⟨101, 2, 6, 3⟩ (rowAt 101)] = data_151
  rw [row_2, row_101]
  apply row_ext <;> decide +kernel
theorem entry_good_151 : EntryGood 151 := by
  unfold EntryGood
  rw [entry_151_checked]
  decide +kernel
theorem good_151 : Good (rowAt 151) := by
  rw [row_151]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks.S213
theorem solution : (rowAt 148 = data_148 ∧ Good (rowAt 148) ∧ EntryGood 148) ∧ (rowAt 149 = data_149 ∧ Good (rowAt 149) ∧ EntryGood 149) ∧ (rowAt 150 = data_150 ∧ Good (rowAt 150) ∧ EntryGood 150) ∧ (rowAt 151 = data_151 ∧ Good (rowAt 151) ∧ EntryGood 151) ∧ True := by
  exact ⟨⟨row_148, good_148, entry_good_148⟩, ⟨row_149, good_149, entry_good_149⟩, ⟨row_150, good_150, entry_good_150⟩, ⟨row_151, good_151, entry_good_151⟩, trivial⟩
