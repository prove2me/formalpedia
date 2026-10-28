-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block05_group00_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T09:20:10.606032+00:00
-- url     : https://prove2.me/submissions/3d093c99-3b8c-40cf-93a1-d5ce507dd96a

import Definitions.Def_Snaky35Cache05
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_group00_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_group00_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks
theorem triple_160 : rowAt 160 = data_160 ∧ Good (rowAt 160) ∧ EntryGood 160 := (OAI.SnakyCertificate.MilestoneChecks.block05_group00_piece00_correct.1)
theorem triple_161 : rowAt 161 = data_161 ∧ Good (rowAt 161) ∧ EntryGood 161 := (OAI.SnakyCertificate.MilestoneChecks.block05_group00_piece00_correct.2.1)
theorem triple_162 : rowAt 162 = data_162 ∧ Good (rowAt 162) ∧ EntryGood 162 := (OAI.SnakyCertificate.MilestoneChecks.block05_group00_piece00_correct.2.2.1)
theorem triple_163 : rowAt 163 = data_163 ∧ Good (rowAt 163) ∧ EntryGood 163 := (OAI.SnakyCertificate.MilestoneChecks.block05_group00_piece00_correct.2.2.2.1)
theorem triple_164 : rowAt 164 = data_164 ∧ Good (rowAt 164) ∧ EntryGood 164 := (OAI.SnakyCertificate.MilestoneChecks.block05_group00_piece01_correct.1)
theorem triple_165 : rowAt 165 = data_165 ∧ Good (rowAt 165) ∧ EntryGood 165 := (OAI.SnakyCertificate.MilestoneChecks.block05_group00_piece01_correct.2.1)
theorem triple_166 : rowAt 166 = data_166 ∧ Good (rowAt 166) ∧ EntryGood 166 := (OAI.SnakyCertificate.MilestoneChecks.block05_group00_piece01_correct.2.2.1)
theorem triple_167 : rowAt 167 = data_167 ∧ Good (rowAt 167) ∧ EntryGood 167 := (OAI.SnakyCertificate.MilestoneChecks.block05_group00_piece01_correct.2.2.2.1)
end OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks.S213
theorem solution : (rowAt 160 = data_160 ∧ Good (rowAt 160) ∧ EntryGood 160) ∧ (rowAt 161 = data_161 ∧ Good (rowAt 161) ∧ EntryGood 161) ∧ (rowAt 162 = data_162 ∧ Good (rowAt 162) ∧ EntryGood 162) ∧ (rowAt 163 = data_163 ∧ Good (rowAt 163) ∧ EntryGood 163) ∧ (rowAt 164 = data_164 ∧ Good (rowAt 164) ∧ EntryGood 164) ∧ (rowAt 165 = data_165 ∧ Good (rowAt 165) ∧ EntryGood 165) ∧ (rowAt 166 = data_166 ∧ Good (rowAt 166) ∧ EntryGood 166) ∧ (rowAt 167 = data_167 ∧ Good (rowAt 167) ∧ EntryGood 167) ∧ True := by
  exact ⟨triple_160, triple_161, triple_162, triple_163, triple_164, triple_165, triple_166, triple_167, trivial⟩
