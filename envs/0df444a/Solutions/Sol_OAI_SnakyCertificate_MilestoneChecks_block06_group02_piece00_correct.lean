-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block06_group02_piece00_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T08:53:42.894994+00:00
-- url     : https://prove2.me/submissions/12b7d011-f298-4200-86b6-745163d61eb5

import Definitions.Def_Snaky35Cache06
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_group02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_group02_piece01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_group03_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks
theorem entry_chunk_10 (j : ℕ) (hj : j < 20) : entryAt (206 + j) = tableChunk_10[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_7 : rowAt 7 = data_7 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.1).1
theorem row_25 : rowAt 25 = data_25 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_49 : rowAt 49 = data_49 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_57 : rowAt 57 = data_57 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_58 : rowAt 58 = data_58 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_81 : rowAt 81 = data_81 := (OAI.SnakyCertificate.MilestoneChecks.block02_group02_correct.2.1).1
theorem row_117 : rowAt 117 = data_117 := (OAI.SnakyCertificate.MilestoneChecks.block03_group02_piece01_correct.2.1).1
theorem row_127 : rowAt 127 = data_127 := (OAI.SnakyCertificate.MilestoneChecks.block03_group03_piece01_correct.2.2.2.1).1
theorem entry_208_checked : entryAt 208 = entry_208 := by
  rw [entry_chunk_10 2 (by decide)]
  decide +kernel
theorem row_208 : rowAt 208 = data_208 := by
  rw [rowAt, dif_neg (by decide : ¬ 208 < 6), entry_208_checked]
  change forkRow [placeRow ⟨7, 4, 0, 5⟩ (rowAt 7), placeRow ⟨127, 0, 5, 4⟩ (rowAt 127)] = data_208
  rw [row_7, row_127]
  apply row_ext <;> decide +kernel
theorem entry_good_208 : EntryGood 208 := by
  unfold EntryGood
  rw [entry_208_checked]
  decide +kernel
theorem good_208 : Good (rowAt 208) := by
  rw [row_208]
  unfold Good
  decide +kernel

theorem entry_209_checked : entryAt 209 = entry_209 := by
  rw [entry_chunk_10 3 (by decide)]
  decide +kernel
theorem row_209 : rowAt 209 = data_209 := by
  rw [rowAt, dif_neg (by decide : ¬ 209 < 6), entry_209_checked]
  change forkRow [placeRow ⟨25, 0, 5, 4⟩ (rowAt 25), placeRow ⟨81, 5, 5, 7⟩ (rowAt 81)] = data_209
  rw [row_25, row_81]
  apply row_ext <;> decide +kernel
theorem entry_good_209 : EntryGood 209 := by
  unfold EntryGood
  rw [entry_209_checked]
  decide +kernel
theorem good_209 : Good (rowAt 209) := by
  rw [row_209]
  unfold Good
  decide +kernel

theorem entry_210_checked : entryAt 210 = entry_210 := by
  rw [entry_chunk_10 4 (by decide)]
  decide +kernel
theorem row_210 : rowAt 210 = data_210 := by
  rw [rowAt, dif_neg (by decide : ¬ 210 < 6), entry_210_checked]
  change forkRow [placeRow ⟨58, 2, 5, 4⟩ (rowAt 58), placeRow ⟨57, 0, 5, 4⟩ (rowAt 57), placeRow ⟨117, 1, 4, 5⟩ (rowAt 117)] = data_210
  rw [row_58, row_57, row_117]
  apply row_ext <;> decide +kernel
theorem entry_good_210 : EntryGood 210 := by
  unfold EntryGood
  rw [entry_210_checked]
  decide +kernel
theorem good_210 : Good (rowAt 210) := by
  rw [row_210]
  unfold Good
  decide +kernel

theorem entry_211_checked : entryAt 211 = entry_211 := by
  rw [entry_chunk_10 5 (by decide)]
  decide +kernel
theorem row_211 : rowAt 211 = data_211 := by
  rw [rowAt, dif_neg (by decide : ¬ 211 < 6), entry_211_checked]
  change forkRow [placeRow ⟨49, 5, 5, 4⟩ (rowAt 49), placeRow ⟨6, 6, 0, 3⟩ (rowAt 6)] = data_211
  rw [row_49, row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_211 : EntryGood 211 := by
  unfold EntryGood
  rw [entry_211_checked]
  decide +kernel
theorem good_211 : Good (rowAt 211) := by
  rw [row_211]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks.S213
theorem solution : (rowAt 208 = data_208 ∧ Good (rowAt 208) ∧ EntryGood 208) ∧ (rowAt 209 = data_209 ∧ Good (rowAt 209) ∧ EntryGood 209) ∧ (rowAt 210 = data_210 ∧ Good (rowAt 210) ∧ EntryGood 210) ∧ (rowAt 211 = data_211 ∧ Good (rowAt 211) ∧ EntryGood 211) ∧ True := by
  exact ⟨⟨row_208, good_208, entry_good_208⟩, ⟨row_209, good_209, entry_good_209⟩, ⟨row_210, good_210, entry_good_210⟩, ⟨row_211, good_211, entry_good_211⟩, trivial⟩
