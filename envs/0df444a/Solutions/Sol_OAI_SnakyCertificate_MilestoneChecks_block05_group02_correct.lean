-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block05_group02_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T09:20:48.154963+00:00
-- url     : https://prove2.me/submissions/70c3f254-59fc-45b3-8bd1-4814b7a2f891

import Definitions.Def_Snaky35Cache05
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_group02_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_group02_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks
theorem triple_176 : rowAt 176 = data_176 ∧ Good (rowAt 176) ∧ EntryGood 176 := (OAI.SnakyCertificate.MilestoneChecks.block05_group02_piece00_correct.1)
theorem triple_177 : rowAt 177 = data_177 ∧ Good (rowAt 177) ∧ EntryGood 177 := (OAI.SnakyCertificate.MilestoneChecks.block05_group02_piece00_correct.2.1)
theorem triple_178 : rowAt 178 = data_178 ∧ Good (rowAt 178) ∧ EntryGood 178 := (OAI.SnakyCertificate.MilestoneChecks.block05_group02_piece00_correct.2.2.1)
theorem triple_179 : rowAt 179 = data_179 ∧ Good (rowAt 179) ∧ EntryGood 179 := (OAI.SnakyCertificate.MilestoneChecks.block05_group02_piece00_correct.2.2.2.1)
theorem triple_180 : rowAt 180 = data_180 ∧ Good (rowAt 180) ∧ EntryGood 180 := (OAI.SnakyCertificate.MilestoneChecks.block05_group02_piece01_correct.1)
theorem triple_181 : rowAt 181 = data_181 ∧ Good (rowAt 181) ∧ EntryGood 181 := (OAI.SnakyCertificate.MilestoneChecks.block05_group02_piece01_correct.2.1)
theorem triple_182 : rowAt 182 = data_182 ∧ Good (rowAt 182) ∧ EntryGood 182 := (OAI.SnakyCertificate.MilestoneChecks.block05_group02_piece01_correct.2.2.1)
theorem triple_183 : rowAt 183 = data_183 ∧ Good (rowAt 183) ∧ EntryGood 183 := (OAI.SnakyCertificate.MilestoneChecks.block05_group02_piece01_correct.2.2.2.1)
end OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks.S213
theorem solution : (rowAt 176 = data_176 ∧ Good (rowAt 176) ∧ EntryGood 176) ∧ (rowAt 177 = data_177 ∧ Good (rowAt 177) ∧ EntryGood 177) ∧ (rowAt 178 = data_178 ∧ Good (rowAt 178) ∧ EntryGood 178) ∧ (rowAt 179 = data_179 ∧ Good (rowAt 179) ∧ EntryGood 179) ∧ (rowAt 180 = data_180 ∧ Good (rowAt 180) ∧ EntryGood 180) ∧ (rowAt 181 = data_181 ∧ Good (rowAt 181) ∧ EntryGood 181) ∧ (rowAt 182 = data_182 ∧ Good (rowAt 182) ∧ EntryGood 182) ∧ (rowAt 183 = data_183 ∧ Good (rowAt 183) ∧ EntryGood 183) ∧ True := by
  exact ⟨triple_176, triple_177, triple_178, triple_179, triple_180, triple_181, triple_182, triple_183, trivial⟩
