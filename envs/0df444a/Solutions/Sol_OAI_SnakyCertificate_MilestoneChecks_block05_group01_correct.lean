-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block05_group01_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T09:20:31.792104+00:00
-- url     : https://prove2.me/submissions/a9b858d0-56a9-448e-919a-a1d8494998aa

import Definitions.Def_Snaky35Cache05
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_group01_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_group01_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks
theorem triple_168 : rowAt 168 = data_168 ∧ Good (rowAt 168) ∧ EntryGood 168 := (OAI.SnakyCertificate.MilestoneChecks.block05_group01_piece00_correct.1)
theorem triple_169 : rowAt 169 = data_169 ∧ Good (rowAt 169) ∧ EntryGood 169 := (OAI.SnakyCertificate.MilestoneChecks.block05_group01_piece00_correct.2.1)
theorem triple_170 : rowAt 170 = data_170 ∧ Good (rowAt 170) ∧ EntryGood 170 := (OAI.SnakyCertificate.MilestoneChecks.block05_group01_piece00_correct.2.2.1)
theorem triple_171 : rowAt 171 = data_171 ∧ Good (rowAt 171) ∧ EntryGood 171 := (OAI.SnakyCertificate.MilestoneChecks.block05_group01_piece00_correct.2.2.2.1)
theorem triple_172 : rowAt 172 = data_172 ∧ Good (rowAt 172) ∧ EntryGood 172 := (OAI.SnakyCertificate.MilestoneChecks.block05_group01_piece01_correct.1)
theorem triple_173 : rowAt 173 = data_173 ∧ Good (rowAt 173) ∧ EntryGood 173 := (OAI.SnakyCertificate.MilestoneChecks.block05_group01_piece01_correct.2.1)
theorem triple_174 : rowAt 174 = data_174 ∧ Good (rowAt 174) ∧ EntryGood 174 := (OAI.SnakyCertificate.MilestoneChecks.block05_group01_piece01_correct.2.2.1)
theorem triple_175 : rowAt 175 = data_175 ∧ Good (rowAt 175) ∧ EntryGood 175 := (OAI.SnakyCertificate.MilestoneChecks.block05_group01_piece01_correct.2.2.2.1)
end OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks.S213
theorem solution : (rowAt 168 = data_168 ∧ Good (rowAt 168) ∧ EntryGood 168) ∧ (rowAt 169 = data_169 ∧ Good (rowAt 169) ∧ EntryGood 169) ∧ (rowAt 170 = data_170 ∧ Good (rowAt 170) ∧ EntryGood 170) ∧ (rowAt 171 = data_171 ∧ Good (rowAt 171) ∧ EntryGood 171) ∧ (rowAt 172 = data_172 ∧ Good (rowAt 172) ∧ EntryGood 172) ∧ (rowAt 173 = data_173 ∧ Good (rowAt 173) ∧ EntryGood 173) ∧ (rowAt 174 = data_174 ∧ Good (rowAt 174) ∧ EntryGood 174) ∧ (rowAt 175 = data_175 ∧ Good (rowAt 175) ∧ EntryGood 175) ∧ True := by
  exact ⟨triple_168, triple_169, triple_170, triple_171, triple_172, triple_173, triple_174, triple_175, trivial⟩
