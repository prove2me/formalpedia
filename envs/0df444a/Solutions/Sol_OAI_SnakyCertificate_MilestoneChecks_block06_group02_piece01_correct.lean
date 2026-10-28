-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block06_group02_piece01_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T08:56:17.035006+00:00
-- url     : https://prove2.me/submissions/e8af601f-0a88-4d02-b901-d97a501aaab3

import Definitions.Def_Snaky35Cache06
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_group03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_group01_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_group01_piece01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_group03_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks
theorem entry_chunk_10 (j : ℕ) (hj : j < 20) : entryAt (206 + j) = tableChunk_10[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_7 : rowAt 7 = data_7 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.1).1
theorem row_24 : rowAt 24 = data_24 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_95 : rowAt 95 = data_95 := (OAI.SnakyCertificate.MilestoneChecks.block02_group03_correct.2.2.2.2.2.2.2.1).1
theorem row_107 : rowAt 107 = data_107 := (OAI.SnakyCertificate.MilestoneChecks.block03_group01_piece00_correct.2.2.2.1).1
theorem row_108 : rowAt 108 = data_108 := (OAI.SnakyCertificate.MilestoneChecks.block03_group01_piece01_correct.1).1
theorem row_188 : rowAt 188 = data_188 := (OAI.SnakyCertificate.MilestoneChecks.block05_group03_piece01_correct.1).1
theorem row_191 : rowAt 191 = data_191 := (OAI.SnakyCertificate.MilestoneChecks.block05_group03_piece01_correct.2.2.2.1).1
theorem entry_212_checked : entryAt 212 = entry_212 := by
  rw [entry_chunk_10 6 (by decide)]
  decide +kernel
theorem row_212 : rowAt 212 = data_212 := by
  rw [rowAt, dif_neg (by decide : ¬ 212 < 6), entry_212_checked]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (rowAt 6), placeRow ⟨188, 0, 0, 5⟩ (rowAt 188)] = data_212
  rw [row_6, row_188]
  apply row_ext <;> decide +kernel
theorem entry_good_212 : EntryGood 212 := by
  unfold EntryGood
  rw [entry_212_checked]
  decide +kernel
theorem good_212 : Good (rowAt 212) := by
  rw [row_212]
  unfold Good
  decide +kernel

theorem entry_213_checked : entryAt 213 = entry_213 := by
  rw [entry_chunk_10 7 (by decide)]
  decide +kernel
theorem row_213 : rowAt 213 = data_213 := by
  rw [rowAt, dif_neg (by decide : ¬ 213 < 6), entry_213_checked]
  change forkRow [placeRow ⟨6, 0, 7, 5⟩ (rowAt 6), placeRow ⟨191, 0, 3, 5⟩ (rowAt 191)] = data_213
  rw [row_6, row_191]
  apply row_ext <;> decide +kernel
theorem entry_good_213 : EntryGood 213 := by
  unfold EntryGood
  rw [entry_213_checked]
  decide +kernel
theorem good_213 : Good (rowAt 213) := by
  rw [row_213]
  unfold Good
  decide +kernel

theorem entry_214_checked : entryAt 214 = entry_214 := by
  rw [entry_chunk_10 8 (by decide)]
  decide +kernel
theorem row_214 : rowAt 214 = data_214 := by
  rw [rowAt, dif_neg (by decide : ¬ 214 < 6), entry_214_checked]
  change forkRow [placeRow ⟨7, 3, 3, 4⟩ (rowAt 7), placeRow ⟨108, 3, 4, 5⟩ (rowAt 108), placeRow ⟨95, 0, 5, 2⟩ (rowAt 95)] = data_214
  rw [row_7, row_108, row_95]
  apply row_ext <;> decide +kernel
theorem entry_good_214 : EntryGood 214 := by
  unfold EntryGood
  rw [entry_214_checked]
  decide +kernel
theorem good_214 : Good (rowAt 214) := by
  rw [row_214]
  unfold Good
  decide +kernel

theorem entry_215_checked : entryAt 215 = entry_215 := by
  rw [entry_chunk_10 9 (by decide)]
  decide +kernel
theorem row_215 : rowAt 215 = data_215 := by
  rw [rowAt, dif_neg (by decide : ¬ 215 < 6), entry_215_checked]
  change forkRow [placeRow ⟨107, 1, 4, 6⟩ (rowAt 107), placeRow ⟨24, 0, 5, 4⟩ (rowAt 24)] = data_215
  rw [row_107, row_24]
  apply row_ext <;> decide +kernel
theorem entry_good_215 : EntryGood 215 := by
  unfold EntryGood
  rw [entry_215_checked]
  decide +kernel
theorem good_215 : Good (rowAt 215) := by
  rw [row_215]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks.S213
theorem solution : (rowAt 212 = data_212 ∧ Good (rowAt 212) ∧ EntryGood 212) ∧ (rowAt 213 = data_213 ∧ Good (rowAt 213) ∧ EntryGood 213) ∧ (rowAt 214 = data_214 ∧ Good (rowAt 214) ∧ EntryGood 214) ∧ (rowAt 215 = data_215 ∧ Good (rowAt 215) ∧ EntryGood 215) ∧ True := by
  exact ⟨⟨row_212, good_212, entry_good_212⟩, ⟨row_213, good_213, entry_good_213⟩, ⟨row_214, good_214, entry_good_214⟩, ⟨row_215, good_215, entry_good_215⟩, trivial⟩
