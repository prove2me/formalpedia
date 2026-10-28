-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block03_group01_piece01_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T07:50:05.549995+00:00
-- url     : https://prove2.me/submissions/4b77c2c2-e3ae-4aa9-83ca-f72487f3296e

import Definitions.Def_Snaky35Cache03
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_group02_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks
theorem entry_chunk_5 (j : ℕ) (hj : j < 20) : entryAt (106 + j) = tableChunk_5[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.1) j hj
theorem row_4 : rowAt 4 = data_4 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_55 : rowAt 55 = data_55 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_83 : rowAt 83 = data_83 := (OAI.SnakyCertificate.MilestoneChecks.block02_group02_correct.2.2.2.1).1
theorem entry_108_checked : entryAt 108 = entry_108 := by
  rw [entry_chunk_5 2 (by decide)]
  decide +kernel
theorem row_108 : rowAt 108 = data_108 := by
  rw [rowAt, dif_neg (by decide : ¬ 108 < 6), entry_108_checked]
  change forkRow [placeRow ⟨4, 6, 1, 3⟩ (rowAt 4), placeRow ⟨63, 1, 5, 3⟩ (rowAt 63)] = data_108
  rw [row_4, row_63]
  apply row_ext <;> decide +kernel
theorem entry_good_108 : EntryGood 108 := by
  unfold EntryGood
  rw [entry_108_checked]
  decide +kernel
theorem good_108 : Good (rowAt 108) := by
  rw [row_108]
  unfold Good
  decide +kernel

theorem entry_109_checked : entryAt 109 = entry_109 := by
  rw [entry_chunk_5 3 (by decide)]
  decide +kernel
theorem row_109 : rowAt 109 = data_109 := by
  rw [rowAt, dif_neg (by decide : ¬ 109 < 6), entry_109_checked]
  change forkRow [placeRow ⟨4, 6, 1, 3⟩ (rowAt 4), placeRow ⟨55, 0, 5, 4⟩ (rowAt 55)] = data_109
  rw [row_4, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_109 : EntryGood 109 := by
  unfold EntryGood
  rw [entry_109_checked]
  decide +kernel
theorem good_109 : Good (rowAt 109) := by
  rw [row_109]
  unfold Good
  decide +kernel

theorem entry_110_checked : entryAt 110 = entry_110 := by
  rw [entry_chunk_5 4 (by decide)]
  decide +kernel
theorem row_110 : rowAt 110 = data_110 := by
  rw [rowAt, dif_neg (by decide : ¬ 110 < 6), entry_110_checked]
  change forkRow [placeRow ⟨6, 6, 1, 3⟩ (rowAt 6), placeRow ⟨63, 1, 6, 3⟩ (rowAt 63)] = data_110
  rw [row_6, row_63]
  apply row_ext <;> decide +kernel
theorem entry_good_110 : EntryGood 110 := by
  unfold EntryGood
  rw [entry_110_checked]
  decide +kernel
theorem good_110 : Good (rowAt 110) := by
  rw [row_110]
  unfold Good
  decide +kernel

theorem entry_111_checked : entryAt 111 = entry_111 := by
  rw [entry_chunk_5 5 (by decide)]
  decide +kernel
theorem row_111 : rowAt 111 = data_111 := by
  rw [rowAt, dif_neg (by decide : ¬ 111 < 6), entry_111_checked]
  change forkRow [placeRow ⟨6, 7, 4, 3⟩ (rowAt 6), placeRow ⟨83, 0, 4, 5⟩ (rowAt 83)] = data_111
  rw [row_6, row_83]
  apply row_ext <;> decide +kernel
theorem entry_good_111 : EntryGood 111 := by
  unfold EntryGood
  rw [entry_111_checked]
  decide +kernel
theorem good_111 : Good (rowAt 111) := by
  rw [row_111]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks.S213
theorem solution : (rowAt 108 = data_108 ∧ Good (rowAt 108) ∧ EntryGood 108) ∧ (rowAt 109 = data_109 ∧ Good (rowAt 109) ∧ EntryGood 109) ∧ (rowAt 110 = data_110 ∧ Good (rowAt 110) ∧ EntryGood 110) ∧ (rowAt 111 = data_111 ∧ Good (rowAt 111) ∧ EntryGood 111) ∧ True := by
  exact ⟨⟨row_108, good_108, entry_good_108⟩, ⟨row_109, good_109, entry_good_109⟩, ⟨row_110, good_110, entry_good_110⟩, ⟨row_111, good_111, entry_good_111⟩, trivial⟩
