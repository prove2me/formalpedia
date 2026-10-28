-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block04_group03_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T09:19:39.535353+00:00
-- url     : https://prove2.me/submissions/a3503416-47aa-4c70-add5-9faea6ddb812

import Definitions.Def_Snaky35Cache04
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_group03_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_group03_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks
theorem triple_152 : rowAt 152 = data_152 ∧ Good (rowAt 152) ∧ EntryGood 152 := (OAI.SnakyCertificate.MilestoneChecks.block04_group03_piece00_correct.1)
theorem triple_153 : rowAt 153 = data_153 ∧ Good (rowAt 153) ∧ EntryGood 153 := (OAI.SnakyCertificate.MilestoneChecks.block04_group03_piece00_correct.2.1)
theorem triple_154 : rowAt 154 = data_154 ∧ Good (rowAt 154) ∧ EntryGood 154 := (OAI.SnakyCertificate.MilestoneChecks.block04_group03_piece00_correct.2.2.1)
theorem triple_155 : rowAt 155 = data_155 ∧ Good (rowAt 155) ∧ EntryGood 155 := (OAI.SnakyCertificate.MilestoneChecks.block04_group03_piece00_correct.2.2.2.1)
theorem triple_156 : rowAt 156 = data_156 ∧ Good (rowAt 156) ∧ EntryGood 156 := (OAI.SnakyCertificate.MilestoneChecks.block04_group03_piece01_correct.1)
theorem triple_157 : rowAt 157 = data_157 ∧ Good (rowAt 157) ∧ EntryGood 157 := (OAI.SnakyCertificate.MilestoneChecks.block04_group03_piece01_correct.2.1)
theorem triple_158 : rowAt 158 = data_158 ∧ Good (rowAt 158) ∧ EntryGood 158 := (OAI.SnakyCertificate.MilestoneChecks.block04_group03_piece01_correct.2.2.1)
theorem triple_159 : rowAt 159 = data_159 ∧ Good (rowAt 159) ∧ EntryGood 159 := (OAI.SnakyCertificate.MilestoneChecks.block04_group03_piece01_correct.2.2.2.1)
end OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks.S213
theorem solution : (rowAt 152 = data_152 ∧ Good (rowAt 152) ∧ EntryGood 152) ∧ (rowAt 153 = data_153 ∧ Good (rowAt 153) ∧ EntryGood 153) ∧ (rowAt 154 = data_154 ∧ Good (rowAt 154) ∧ EntryGood 154) ∧ (rowAt 155 = data_155 ∧ Good (rowAt 155) ∧ EntryGood 155) ∧ (rowAt 156 = data_156 ∧ Good (rowAt 156) ∧ EntryGood 156) ∧ (rowAt 157 = data_157 ∧ Good (rowAt 157) ∧ EntryGood 157) ∧ (rowAt 158 = data_158 ∧ Good (rowAt 158) ∧ EntryGood 158) ∧ (rowAt 159 = data_159 ∧ Good (rowAt 159) ∧ EntryGood 159) ∧ True := by
  exact ⟨triple_152, triple_153, triple_154, triple_155, triple_156, triple_157, triple_158, triple_159, trivial⟩
