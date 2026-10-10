-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block00_group00_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T13:13:20.245824+00:00
-- url     : https://prove2.me/submissions/dc50de1d-1bad-40ee-99b0-9a738f4efe3f

import Definitions.Def_Snaky35Cache00
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_0 (j : ℕ) (hj : j < 20) : entryAt (6 + j) = tableChunk_0[j]?.getD emptyEntry := (chunk_lookups.1) j hj
theorem row_0 : rowAt 0 = data_0 := by apply row_ext <;> decide +kernel
theorem good_0 : Good (rowAt 0) := by
  rw [row_0]
  unfold Good
  decide +kernel

theorem row_1 : rowAt 1 = data_1 := by apply row_ext <;> decide +kernel
theorem good_1 : Good (rowAt 1) := by
  rw [row_1]
  unfold Good
  decide +kernel

theorem row_2 : rowAt 2 = data_2 := by apply row_ext <;> decide +kernel
theorem good_2 : Good (rowAt 2) := by
  rw [row_2]
  unfold Good
  decide +kernel

theorem row_3 : rowAt 3 = data_3 := by apply row_ext <;> decide +kernel
theorem good_3 : Good (rowAt 3) := by
  rw [row_3]
  unfold Good
  decide +kernel

theorem row_4 : rowAt 4 = data_4 := by apply row_ext <;> decide +kernel
theorem good_4 : Good (rowAt 4) := by
  rw [row_4]
  unfold Good
  decide +kernel

theorem row_5 : rowAt 5 = data_5 := by apply row_ext <;> decide +kernel
theorem good_5 : Good (rowAt 5) := by
  rw [row_5]
  unfold Good
  decide +kernel

theorem entry_6_checked : entryAt 6 = entry_6 := by
  rw [entry_chunk_0 0 (by decide)]
  decide +kernel
theorem row_6 : rowAt 6 = data_6 := by
  rw [rowAt, dif_neg (by decide : ¬ 6 < 6), entry_6_checked]
  change forkRow [placeRow ⟨0, 0, 0, 3⟩ (rowAt 0)] = data_6
  rw [row_0]
  apply row_ext <;> decide +kernel
theorem entry_good_6 : EntryGood 6 := by
  unfold EntryGood
  rw [entry_6_checked]
  decide +kernel
theorem good_6 : Good (rowAt 6) := by
  rw [row_6]
  unfold Good
  decide +kernel

theorem entry_7_checked : entryAt 7 = entry_7 := by
  rw [entry_chunk_0 1 (by decide)]
  decide +kernel
theorem row_7 : rowAt 7 = data_7 := by
  rw [rowAt, dif_neg (by decide : ¬ 7 < 6), entry_7_checked]
  change forkRow [placeRow ⟨4, 0, 3, 4⟩ (rowAt 4), placeRow ⟨6, 0, 5, 4⟩ (rowAt 6)] = data_7
  rw [row_4, row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_7 : EntryGood 7 := by
  unfold EntryGood
  rw [entry_7_checked]
  decide +kernel
theorem good_7 : Good (rowAt 7) := by
  rw [row_7]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 0 = data_0 ∧ Good (rowAt 0) ∧ True) ∧ (rowAt 1 = data_1 ∧ Good (rowAt 1) ∧ True) ∧ (rowAt 2 = data_2 ∧ Good (rowAt 2) ∧ True) ∧ (rowAt 3 = data_3 ∧ Good (rowAt 3) ∧ True) ∧ (rowAt 4 = data_4 ∧ Good (rowAt 4) ∧ True) ∧ (rowAt 5 = data_5 ∧ Good (rowAt 5) ∧ True) ∧ (rowAt 6 = data_6 ∧ Good (rowAt 6) ∧ EntryGood 6) ∧ (rowAt 7 = data_7 ∧ Good (rowAt 7) ∧ EntryGood 7) ∧ True := by
  exact ⟨⟨row_0, good_0, trivial⟩, ⟨row_1, good_1, trivial⟩, ⟨row_2, good_2, trivial⟩, ⟨row_3, good_3, trivial⟩, ⟨row_4, good_4, trivial⟩, ⟨row_5, good_5, trivial⟩, ⟨row_6, good_6, entry_good_6⟩, ⟨row_7, good_7, entry_good_7⟩, trivial⟩
