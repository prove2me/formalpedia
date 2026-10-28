-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block03_group01_piece00_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T07:48:29.432137+00:00
-- url     : https://prove2.me/submissions/2ddfd1ad-1cf3-4bd3-a65e-f61cf163a499

import Definitions.Def_Snaky35Cache03
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_group01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks
theorem entry_chunk_4 (j : ℕ) (hj : j < 20) : entryAt (86 + j) = tableChunk_4[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.1) j hj
theorem entry_chunk_5 (j : ℕ) (hj : j < 20) : entryAt (106 + j) = tableChunk_5[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.1) j hj
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_36 : rowAt 36 = data_36 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_75 : rowAt 75 = data_75 := (OAI.SnakyCertificate.MilestoneChecks.block02_group01_correct.2.2.2.1).1
theorem row_77 : rowAt 77 = data_77 := (OAI.SnakyCertificate.MilestoneChecks.block02_group01_correct.2.2.2.2.2.1).1
theorem entry_104_checked : entryAt 104 = entry_104 := by
  rw [entry_chunk_4 18 (by decide)]
  decide +kernel
theorem row_104 : rowAt 104 = data_104 := by
  rw [rowAt, dif_neg (by decide : ¬ 104 < 6), entry_104_checked]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (rowAt 6), placeRow ⟨75, 0, 3, 4⟩ (rowAt 75)] = data_104
  rw [row_6, row_75]
  apply row_ext <;> decide +kernel
theorem entry_good_104 : EntryGood 104 := by
  unfold EntryGood
  rw [entry_104_checked]
  decide +kernel
theorem good_104 : Good (rowAt 104) := by
  rw [row_104]
  unfold Good
  decide +kernel

theorem entry_105_checked : entryAt 105 = entry_105 := by
  rw [entry_chunk_4 19 (by decide)]
  decide +kernel
theorem row_105 : rowAt 105 = data_105 := by
  rw [rowAt, dif_neg (by decide : ¬ 105 < 6), entry_105_checked]
  change forkRow [placeRow ⟨6, 5, 4, 3⟩ (rowAt 6), placeRow ⟨77, 0, 4, 5⟩ (rowAt 77)] = data_105
  rw [row_6, row_77]
  apply row_ext <;> decide +kernel
theorem entry_good_105 : EntryGood 105 := by
  unfold EntryGood
  rw [entry_105_checked]
  decide +kernel
theorem good_105 : Good (rowAt 105) := by
  rw [row_105]
  unfold Good
  decide +kernel

theorem entry_106_checked : entryAt 106 = entry_106 := by
  rw [entry_chunk_5 0 (by decide)]
  decide +kernel
theorem row_106 : rowAt 106 = data_106 := by
  rw [rowAt, dif_neg (by decide : ¬ 106 < 6), entry_106_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨36, 6, 5, 4⟩ (rowAt 36)] = data_106
  rw [row_6, row_36]
  apply row_ext <;> decide +kernel
theorem entry_good_106 : EntryGood 106 := by
  unfold EntryGood
  rw [entry_106_checked]
  decide +kernel
theorem good_106 : Good (rowAt 106) := by
  rw [row_106]
  unfold Good
  decide +kernel

theorem entry_107_checked : entryAt 107 = entry_107 := by
  rw [entry_chunk_5 1 (by decide)]
  decide +kernel
theorem row_107 : rowAt 107 = data_107 := by
  rw [rowAt, dif_neg (by decide : ¬ 107 < 6), entry_107_checked]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (rowAt 6), placeRow ⟨63, 1, 5, 3⟩ (rowAt 63)] = data_107
  rw [row_6, row_63]
  apply row_ext <;> decide +kernel
theorem entry_good_107 : EntryGood 107 := by
  unfold EntryGood
  rw [entry_107_checked]
  decide +kernel
theorem good_107 : Good (rowAt 107) := by
  rw [row_107]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks.S213
theorem solution : (rowAt 104 = data_104 ∧ Good (rowAt 104) ∧ EntryGood 104) ∧ (rowAt 105 = data_105 ∧ Good (rowAt 105) ∧ EntryGood 105) ∧ (rowAt 106 = data_106 ∧ Good (rowAt 106) ∧ EntryGood 106) ∧ (rowAt 107 = data_107 ∧ Good (rowAt 107) ∧ EntryGood 107) ∧ True := by
  exact ⟨⟨row_104, good_104, entry_good_104⟩, ⟨row_105, good_105, entry_good_105⟩, ⟨row_106, good_106, entry_good_106⟩, ⟨row_107, good_107, entry_good_107⟩, trivial⟩
