-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block04_group00_piece01_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T08:15:08.880381+00:00
-- url     : https://prove2.me/submissions/6553556d-d6c1-45d4-b505-a354fcab772f

import Definitions.Def_Snaky35Cache04
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_group01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_group02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_group03_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks
theorem entry_chunk_6 (j : ℕ) (hj : j < 20) : entryAt (126 + j) = tableChunk_6[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.1) j hj
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_7 : rowAt 7 = data_7 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.1).1
theorem row_44 : rowAt 44 = data_44 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_75 : rowAt 75 = data_75 := (OAI.SnakyCertificate.MilestoneChecks.block02_group01_correct.2.2.2.1).1
theorem row_82 : rowAt 82 = data_82 := (OAI.SnakyCertificate.MilestoneChecks.block02_group02_correct.2.2.1).1
theorem row_89 : rowAt 89 = data_89 := (OAI.SnakyCertificate.MilestoneChecks.block02_group03_correct.2.1).1
theorem row_92 : rowAt 92 = data_92 := (OAI.SnakyCertificate.MilestoneChecks.block02_group03_correct.2.2.2.2.1).1
theorem entry_132_checked : entryAt 132 = entry_132 := by
  rw [entry_chunk_6 6 (by decide)]
  decide +kernel
theorem row_132 : rowAt 132 = data_132 := by
  rw [rowAt, dif_neg (by decide : ¬ 132 < 6), entry_132_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨89, 0, 5, 6⟩ (rowAt 89)] = data_132
  rw [row_6, row_89]
  apply row_ext <;> decide +kernel
theorem entry_good_132 : EntryGood 132 := by
  unfold EntryGood
  rw [entry_132_checked]
  decide +kernel
theorem good_132 : Good (rowAt 132) := by
  rw [row_132]
  unfold Good
  decide +kernel

theorem entry_133_checked : entryAt 133 = entry_133 := by
  rw [entry_chunk_6 7 (by decide)]
  decide +kernel
theorem row_133 : rowAt 133 = data_133 := by
  rw [rowAt, dif_neg (by decide : ¬ 133 < 6), entry_133_checked]
  change forkRow [placeRow ⟨6, 7, 3, 1⟩ (rowAt 6), placeRow ⟨92, 0, 5, 5⟩ (rowAt 92)] = data_133
  rw [row_6, row_92]
  apply row_ext <;> decide +kernel
theorem entry_good_133 : EntryGood 133 := by
  unfold EntryGood
  rw [entry_133_checked]
  decide +kernel
theorem good_133 : Good (rowAt 133) := by
  rw [row_133]
  unfold Good
  decide +kernel

theorem entry_134_checked : entryAt 134 = entry_134 := by
  rw [entry_chunk_6 8 (by decide)]
  decide +kernel
theorem row_134 : rowAt 134 = data_134 := by
  rw [rowAt, dif_neg (by decide : ¬ 134 < 6), entry_134_checked]
  change forkRow [placeRow ⟨6, 7, 3, 0⟩ (rowAt 6), placeRow ⟨82, 0, 5, 4⟩ (rowAt 82)] = data_134
  rw [row_6, row_82]
  apply row_ext <;> decide +kernel
theorem entry_good_134 : EntryGood 134 := by
  unfold EntryGood
  rw [entry_134_checked]
  decide +kernel
theorem good_134 : Good (rowAt 134) := by
  rw [row_134]
  unfold Good
  decide +kernel

theorem entry_135_checked : entryAt 135 = entry_135 := by
  rw [entry_chunk_6 9 (by decide)]
  decide +kernel
theorem row_135 : rowAt 135 = data_135 := by
  rw [rowAt, dif_neg (by decide : ¬ 135 < 6), entry_135_checked]
  change forkRow [placeRow ⟨7, 0, 4, 5⟩ (rowAt 7), placeRow ⟨75, 4, 2, 5⟩ (rowAt 75), placeRow ⟨44, 0, 5, 4⟩ (rowAt 44)] = data_135
  rw [row_7, row_75, row_44]
  apply row_ext <;> decide +kernel
theorem entry_good_135 : EntryGood 135 := by
  unfold EntryGood
  rw [entry_135_checked]
  decide +kernel
theorem good_135 : Good (rowAt 135) := by
  rw [row_135]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks.S213
theorem solution : (rowAt 132 = data_132 ∧ Good (rowAt 132) ∧ EntryGood 132) ∧ (rowAt 133 = data_133 ∧ Good (rowAt 133) ∧ EntryGood 133) ∧ (rowAt 134 = data_134 ∧ Good (rowAt 134) ∧ EntryGood 134) ∧ (rowAt 135 = data_135 ∧ Good (rowAt 135) ∧ EntryGood 135) ∧ True := by
  exact ⟨⟨row_132, good_132, entry_good_132⟩, ⟨row_133, good_133, entry_good_133⟩, ⟨row_134, good_134, entry_good_134⟩, ⟨row_135, good_135, entry_good_135⟩, trivial⟩
