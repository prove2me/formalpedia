-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block06_group00_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T09:21:50.008369+00:00
-- url     : https://prove2.me/submissions/6a569ae2-1b60-43a7-9c10-d29019bd7506

import Definitions.Def_Snaky35Cache06
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_group00_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_group00_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks
theorem triple_192 : rowAt 192 = data_192 ∧ Good (rowAt 192) ∧ EntryGood 192 := (OAI.SnakyCertificate.MilestoneChecks.block06_group00_piece00_correct.1)
theorem triple_193 : rowAt 193 = data_193 ∧ Good (rowAt 193) ∧ EntryGood 193 := (OAI.SnakyCertificate.MilestoneChecks.block06_group00_piece00_correct.2.1)
theorem triple_194 : rowAt 194 = data_194 ∧ Good (rowAt 194) ∧ EntryGood 194 := (OAI.SnakyCertificate.MilestoneChecks.block06_group00_piece00_correct.2.2.1)
theorem triple_195 : rowAt 195 = data_195 ∧ Good (rowAt 195) ∧ EntryGood 195 := (OAI.SnakyCertificate.MilestoneChecks.block06_group00_piece00_correct.2.2.2.1)
theorem triple_196 : rowAt 196 = data_196 ∧ Good (rowAt 196) ∧ EntryGood 196 := (OAI.SnakyCertificate.MilestoneChecks.block06_group00_piece01_correct.1)
theorem triple_197 : rowAt 197 = data_197 ∧ Good (rowAt 197) ∧ EntryGood 197 := (OAI.SnakyCertificate.MilestoneChecks.block06_group00_piece01_correct.2.1)
theorem triple_198 : rowAt 198 = data_198 ∧ Good (rowAt 198) ∧ EntryGood 198 := (OAI.SnakyCertificate.MilestoneChecks.block06_group00_piece01_correct.2.2.1)
theorem triple_199 : rowAt 199 = data_199 ∧ Good (rowAt 199) ∧ EntryGood 199 := (OAI.SnakyCertificate.MilestoneChecks.block06_group00_piece01_correct.2.2.2.1)
end OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks.S213
theorem solution : (rowAt 192 = data_192 ∧ Good (rowAt 192) ∧ EntryGood 192) ∧ (rowAt 193 = data_193 ∧ Good (rowAt 193) ∧ EntryGood 193) ∧ (rowAt 194 = data_194 ∧ Good (rowAt 194) ∧ EntryGood 194) ∧ (rowAt 195 = data_195 ∧ Good (rowAt 195) ∧ EntryGood 195) ∧ (rowAt 196 = data_196 ∧ Good (rowAt 196) ∧ EntryGood 196) ∧ (rowAt 197 = data_197 ∧ Good (rowAt 197) ∧ EntryGood 197) ∧ (rowAt 198 = data_198 ∧ Good (rowAt 198) ∧ EntryGood 198) ∧ (rowAt 199 = data_199 ∧ Good (rowAt 199) ∧ EntryGood 199) ∧ True := by
  exact ⟨triple_192, triple_193, triple_194, triple_195, triple_196, triple_197, triple_198, triple_199, trivial⟩
