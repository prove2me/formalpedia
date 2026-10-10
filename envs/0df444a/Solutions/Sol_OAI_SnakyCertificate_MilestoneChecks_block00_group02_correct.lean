-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block00_group02_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T13:26:08.913634+00:00
-- url     : https://prove2.me/submissions/0527719c-fb76-4dca-bf1d-f7c9381e2dea

import Definitions.Def_Snaky35Cache00
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_group00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_0 (j : ℕ) (hj : j < 20) : entryAt (6 + j) = tableChunk_0[j]?.getD emptyEntry := (chunk_lookups.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_group00_correct.1).1
theorem row_3 : rowAt 3 = data_3 := (OAI.SnakyCertificate.MilestoneChecks.block00_group00_correct.2.2.2.1).1
theorem row_4 : rowAt 4 = data_4 := (OAI.SnakyCertificate.MilestoneChecks.block00_group00_correct.2.2.2.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_group00_correct.2.2.2.2.2.2.1).1
theorem entry_16_checked : entryAt 16 = entry_16 := by
  rw [entry_chunk_0 10 (by decide)]
  decide +kernel
theorem row_16 : rowAt 16 = data_16 := by
  rw [rowAt, dif_neg (by decide : ¬ 16 < 6), entry_16_checked]
  change forkRow [placeRow ⟨3, 6, 3, 4⟩ (rowAt 3), placeRow ⟨0, 6, 7, 4⟩ (rowAt 0)] = data_16
  rw [row_3, row_0]
  apply row_ext <;> decide +kernel
theorem entry_good_16 : EntryGood 16 := by
  unfold EntryGood
  rw [entry_16_checked]
  decide +kernel
theorem good_16 : Good (rowAt 16) := by
  rw [row_16]
  unfold Good
  decide +kernel

theorem entry_17_checked : entryAt 17 = entry_17 := by
  rw [entry_chunk_0 11 (by decide)]
  decide +kernel
theorem row_17 : rowAt 17 = data_17 := by
  rw [rowAt, dif_neg (by decide : ¬ 17 < 6), entry_17_checked]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (rowAt 0), placeRow ⟨3, 0, 3, 3⟩ (rowAt 3)] = data_17
  rw [row_0, row_3]
  apply row_ext <;> decide +kernel
theorem entry_good_17 : EntryGood 17 := by
  unfold EntryGood
  rw [entry_17_checked]
  decide +kernel
theorem good_17 : Good (rowAt 17) := by
  rw [row_17]
  unfold Good
  decide +kernel

theorem entry_18_checked : entryAt 18 = entry_18 := by
  rw [entry_chunk_0 12 (by decide)]
  decide +kernel
theorem row_18 : rowAt 18 = data_18 := by
  rw [rowAt, dif_neg (by decide : ¬ 18 < 6), entry_18_checked]
  change forkRow [placeRow ⟨3, 6, 2, 4⟩ (rowAt 3), placeRow ⟨3, 0, 4, 3⟩ (rowAt 3)] = data_18
  rw [row_3]
  apply row_ext <;> decide +kernel
theorem entry_good_18 : EntryGood 18 := by
  unfold EntryGood
  rw [entry_18_checked]
  decide +kernel
theorem good_18 : Good (rowAt 18) := by
  rw [row_18]
  unfold Good
  decide +kernel

theorem entry_19_checked : entryAt 19 = entry_19 := by
  rw [entry_chunk_0 13 (by decide)]
  decide +kernel
theorem row_19 : rowAt 19 = data_19 := by
  rw [rowAt, dif_neg (by decide : ¬ 19 < 6), entry_19_checked]
  change forkRow [placeRow ⟨6, 4, 1, 5⟩ (rowAt 6), placeRow ⟨6, 0, 6, 5⟩ (rowAt 6)] = data_19
  rw [row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_19 : EntryGood 19 := by
  unfold EntryGood
  rw [entry_19_checked]
  decide +kernel
theorem good_19 : Good (rowAt 19) := by
  rw [row_19]
  unfold Good
  decide +kernel

theorem entry_20_checked : entryAt 20 = entry_20 := by
  rw [entry_chunk_0 14 (by decide)]
  decide +kernel
theorem row_20 : rowAt 20 = data_20 := by
  rw [rowAt, dif_neg (by decide : ¬ 20 < 6), entry_20_checked]
  change forkRow [placeRow ⟨6, 4, 0, 5⟩ (rowAt 6), placeRow ⟨6, 0, 5, 5⟩ (rowAt 6)] = data_20
  rw [row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_20 : EntryGood 20 := by
  unfold EntryGood
  rw [entry_20_checked]
  decide +kernel
theorem good_20 : Good (rowAt 20) := by
  rw [row_20]
  unfold Good
  decide +kernel

theorem entry_21_checked : entryAt 21 = entry_21 := by
  rw [entry_chunk_0 15 (by decide)]
  decide +kernel
theorem row_21 : rowAt 21 = data_21 := by
  rw [rowAt, dif_neg (by decide : ¬ 21 < 6), entry_21_checked]
  change forkRow [placeRow ⟨4, 6, 2, 3⟩ (rowAt 4), placeRow ⟨6, 0, 6, 5⟩ (rowAt 6)] = data_21
  rw [row_4, row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_21 : EntryGood 21 := by
  unfold EntryGood
  rw [entry_21_checked]
  decide +kernel
theorem good_21 : Good (rowAt 21) := by
  rw [row_21]
  unfold Good
  decide +kernel

theorem entry_22_checked : entryAt 22 = entry_22 := by
  rw [entry_chunk_0 16 (by decide)]
  decide +kernel
theorem row_22 : rowAt 22 = data_22 := by
  rw [rowAt, dif_neg (by decide : ¬ 22 < 6), entry_22_checked]
  change forkRow [placeRow ⟨0, 6, 7, 5⟩ (rowAt 0), placeRow ⟨3, 0, 5, 4⟩ (rowAt 3)] = data_22
  rw [row_0, row_3]
  apply row_ext <;> decide +kernel
theorem entry_good_22 : EntryGood 22 := by
  unfold EntryGood
  rw [entry_22_checked]
  decide +kernel
theorem good_22 : Good (rowAt 22) := by
  rw [row_22]
  unfold Good
  decide +kernel

theorem entry_23_checked : entryAt 23 = entry_23 := by
  rw [entry_chunk_0 17 (by decide)]
  decide +kernel
theorem row_23 : rowAt 23 = data_23 := by
  rw [rowAt, dif_neg (by decide : ¬ 23 < 6), entry_23_checked]
  change forkRow [placeRow ⟨0, 6, 6, 4⟩ (rowAt 0), placeRow ⟨0, 0, 1, 3⟩ (rowAt 0)] = data_23
  rw [row_0]
  apply row_ext <;> decide +kernel
theorem entry_good_23 : EntryGood 23 := by
  unfold EntryGood
  rw [entry_23_checked]
  decide +kernel
theorem good_23 : Good (rowAt 23) := by
  rw [row_23]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 16 = data_16 ∧ Good (rowAt 16) ∧ EntryGood 16) ∧ (rowAt 17 = data_17 ∧ Good (rowAt 17) ∧ EntryGood 17) ∧ (rowAt 18 = data_18 ∧ Good (rowAt 18) ∧ EntryGood 18) ∧ (rowAt 19 = data_19 ∧ Good (rowAt 19) ∧ EntryGood 19) ∧ (rowAt 20 = data_20 ∧ Good (rowAt 20) ∧ EntryGood 20) ∧ (rowAt 21 = data_21 ∧ Good (rowAt 21) ∧ EntryGood 21) ∧ (rowAt 22 = data_22 ∧ Good (rowAt 22) ∧ EntryGood 22) ∧ (rowAt 23 = data_23 ∧ Good (rowAt 23) ∧ EntryGood 23) ∧ True := by
  exact ⟨⟨row_16, good_16, entry_good_16⟩, ⟨row_17, good_17, entry_good_17⟩, ⟨row_18, good_18, entry_good_18⟩, ⟨row_19, good_19, entry_good_19⟩, ⟨row_20, good_20, entry_good_20⟩, ⟨row_21, good_21, entry_good_21⟩, ⟨row_22, good_22, entry_good_22⟩, ⟨row_23, good_23, entry_good_23⟩, trivial⟩
