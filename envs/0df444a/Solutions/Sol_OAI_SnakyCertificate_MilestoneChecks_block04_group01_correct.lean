-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block04_group01_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T09:19:05.706165+00:00
-- url     : https://prove2.me/submissions/6871e12b-89f9-45c1-84c6-d1ae321d02ff

import Definitions.Def_Snaky35Cache04
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_group01_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_group01_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks
theorem triple_136 : rowAt 136 = data_136 ∧ Good (rowAt 136) ∧ EntryGood 136 := (OAI.SnakyCertificate.MilestoneChecks.block04_group01_piece00_correct.1)
theorem triple_137 : rowAt 137 = data_137 ∧ Good (rowAt 137) ∧ EntryGood 137 := (OAI.SnakyCertificate.MilestoneChecks.block04_group01_piece00_correct.2.1)
theorem triple_138 : rowAt 138 = data_138 ∧ Good (rowAt 138) ∧ EntryGood 138 := (OAI.SnakyCertificate.MilestoneChecks.block04_group01_piece00_correct.2.2.1)
theorem triple_139 : rowAt 139 = data_139 ∧ Good (rowAt 139) ∧ EntryGood 139 := (OAI.SnakyCertificate.MilestoneChecks.block04_group01_piece00_correct.2.2.2.1)
theorem triple_140 : rowAt 140 = data_140 ∧ Good (rowAt 140) ∧ EntryGood 140 := (OAI.SnakyCertificate.MilestoneChecks.block04_group01_piece01_correct.1)
theorem triple_141 : rowAt 141 = data_141 ∧ Good (rowAt 141) ∧ EntryGood 141 := (OAI.SnakyCertificate.MilestoneChecks.block04_group01_piece01_correct.2.1)
theorem triple_142 : rowAt 142 = data_142 ∧ Good (rowAt 142) ∧ EntryGood 142 := (OAI.SnakyCertificate.MilestoneChecks.block04_group01_piece01_correct.2.2.1)
theorem triple_143 : rowAt 143 = data_143 ∧ Good (rowAt 143) ∧ EntryGood 143 := (OAI.SnakyCertificate.MilestoneChecks.block04_group01_piece01_correct.2.2.2.1)
end OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks.S213
theorem solution : (rowAt 136 = data_136 ∧ Good (rowAt 136) ∧ EntryGood 136) ∧ (rowAt 137 = data_137 ∧ Good (rowAt 137) ∧ EntryGood 137) ∧ (rowAt 138 = data_138 ∧ Good (rowAt 138) ∧ EntryGood 138) ∧ (rowAt 139 = data_139 ∧ Good (rowAt 139) ∧ EntryGood 139) ∧ (rowAt 140 = data_140 ∧ Good (rowAt 140) ∧ EntryGood 140) ∧ (rowAt 141 = data_141 ∧ Good (rowAt 141) ∧ EntryGood 141) ∧ (rowAt 142 = data_142 ∧ Good (rowAt 142) ∧ EntryGood 142) ∧ (rowAt 143 = data_143 ∧ Good (rowAt 143) ∧ EntryGood 143) ∧ True := by
  exact ⟨triple_136, triple_137, triple_138, triple_139, triple_140, triple_141, triple_142, triple_143, trivial⟩
