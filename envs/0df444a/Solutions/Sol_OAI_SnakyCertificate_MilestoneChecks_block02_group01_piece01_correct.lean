-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block02_group01_piece01_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T14:27:12.36329+00:00
-- url     : https://prove2.me/submissions/0c9dc54d-686b-42eb-827f-cc49bbb68a81

import Definitions.Def_Snaky35Cache02
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_3 (j : ℕ) (hj : j < 20) : entryAt (66 + j) = tableChunk_3[j]?.getD emptyEntry := (chunk_lookups.2.2.2.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.1).1
theorem row_2 : rowAt 2 = data_2 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.1).1
theorem row_4 : rowAt 4 = data_4 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_8 : rowAt 8 = data_8 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.1).1
theorem row_9 : rowAt 9 = data_9 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_12 : rowAt 12 = data_12 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_14 : rowAt 14 = data_14 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_48 : rowAt 48 = data_48 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_50 : rowAt 50 = data_50 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_52 : rowAt 52 = data_52 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_53 : rowAt 53 = data_53 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem entry_76_checked : entryAt 76 = entry_76 := by
  rw [entry_chunk_3 10 (by decide)]
  decide +kernel
theorem row_76 : rowAt 76 = data_76 := by
  rw [rowAt, dif_neg (by decide : ¬ 76 < 6), entry_76_checked]
  change forkRow [placeRow ⟨0, 7, 5, 7⟩ (rowAt 0), placeRow ⟨14, 0, 7, 5⟩ (rowAt 14)] = data_76
  rw [row_0, row_14]
  apply row_ext <;> decide +kernel
theorem entry_good_76 : EntryGood 76 := by
  unfold EntryGood
  rw [entry_76_checked]
  decide +kernel
theorem good_76 : Good (rowAt 76) := by
  rw [row_76]
  unfold Good
  decide +kernel

theorem entry_77_checked : entryAt 77 = entry_77 := by
  rw [entry_chunk_3 11 (by decide)]
  decide +kernel
theorem row_77 : rowAt 77 = data_77 := by
  rw [rowAt, dif_neg (by decide : ¬ 77 < 6), entry_77_checked]
  change forkRow [placeRow ⟨0, 5, 3, 7⟩ (rowAt 0), placeRow ⟨12, 0, 5, 4⟩ (rowAt 12)] = data_77
  rw [row_0, row_12]
  apply row_ext <;> decide +kernel
theorem entry_good_77 : EntryGood 77 := by
  unfold EntryGood
  rw [entry_77_checked]
  decide +kernel
theorem good_77 : Good (rowAt 77) := by
  rw [row_77]
  unfold Good
  decide +kernel

theorem entry_78_checked : entryAt 78 = entry_78 := by
  rw [entry_chunk_3 12 (by decide)]
  decide +kernel
theorem row_78 : rowAt 78 = data_78 := by
  rw [rowAt, dif_neg (by decide : ¬ 78 < 6), entry_78_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨52, 0, 5, 4⟩ (rowAt 52)] = data_78
  rw [row_6, row_52]
  apply row_ext <;> decide +kernel
theorem entry_good_78 : EntryGood 78 := by
  unfold EntryGood
  rw [entry_78_checked]
  decide +kernel
theorem good_78 : Good (rowAt 78) := by
  rw [row_78]
  unfold Good
  decide +kernel

theorem entry_79_checked : entryAt 79 = entry_79 := by
  rw [entry_chunk_3 13 (by decide)]
  decide +kernel
theorem row_79 : rowAt 79 = data_79 := by
  rw [rowAt, dif_neg (by decide : ¬ 79 < 6), entry_79_checked]
  change forkRow [placeRow ⟨6, 1, 5, 5⟩ (rowAt 6), placeRow ⟨48, 0, 3, 4⟩ (rowAt 48)] = data_79
  rw [row_6, row_48]
  apply row_ext <;> decide +kernel
theorem entry_good_79 : EntryGood 79 := by
  unfold EntryGood
  rw [entry_79_checked]
  decide +kernel
theorem good_79 : Good (rowAt 79) := by
  rw [row_79]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 76 = data_76 ∧ Good (rowAt 76) ∧ EntryGood 76) ∧ (rowAt 77 = data_77 ∧ Good (rowAt 77) ∧ EntryGood 77) ∧ (rowAt 78 = data_78 ∧ Good (rowAt 78) ∧ EntryGood 78) ∧ (rowAt 79 = data_79 ∧ Good (rowAt 79) ∧ EntryGood 79) ∧ True := by
  exact ⟨⟨row_76, good_76, entry_good_76⟩, ⟨row_77, good_77, entry_good_77⟩, ⟨row_78, good_78, entry_good_78⟩, ⟨row_79, good_79, entry_good_79⟩, trivial⟩
