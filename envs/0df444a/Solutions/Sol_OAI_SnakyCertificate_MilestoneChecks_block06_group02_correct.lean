-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block06_group02_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T09:22:40.351718+00:00
-- url     : https://prove2.me/submissions/c2b42a45-6280-4538-ae18-5c75686fcc29

import Definitions.Def_Snaky35Cache06
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_group02_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_group02_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks
theorem triple_208 : rowAt 208 = data_208 ∧ Good (rowAt 208) ∧ EntryGood 208 := (OAI.SnakyCertificate.MilestoneChecks.block06_group02_piece00_correct.1)
theorem triple_209 : rowAt 209 = data_209 ∧ Good (rowAt 209) ∧ EntryGood 209 := (OAI.SnakyCertificate.MilestoneChecks.block06_group02_piece00_correct.2.1)
theorem triple_210 : rowAt 210 = data_210 ∧ Good (rowAt 210) ∧ EntryGood 210 := (OAI.SnakyCertificate.MilestoneChecks.block06_group02_piece00_correct.2.2.1)
theorem triple_211 : rowAt 211 = data_211 ∧ Good (rowAt 211) ∧ EntryGood 211 := (OAI.SnakyCertificate.MilestoneChecks.block06_group02_piece00_correct.2.2.2.1)
theorem triple_212 : rowAt 212 = data_212 ∧ Good (rowAt 212) ∧ EntryGood 212 := (OAI.SnakyCertificate.MilestoneChecks.block06_group02_piece01_correct.1)
theorem triple_213 : rowAt 213 = data_213 ∧ Good (rowAt 213) ∧ EntryGood 213 := (OAI.SnakyCertificate.MilestoneChecks.block06_group02_piece01_correct.2.1)
theorem triple_214 : rowAt 214 = data_214 ∧ Good (rowAt 214) ∧ EntryGood 214 := (OAI.SnakyCertificate.MilestoneChecks.block06_group02_piece01_correct.2.2.1)
theorem triple_215 : rowAt 215 = data_215 ∧ Good (rowAt 215) ∧ EntryGood 215 := (OAI.SnakyCertificate.MilestoneChecks.block06_group02_piece01_correct.2.2.2.1)
end OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks.S213
theorem solution : (rowAt 208 = data_208 ∧ Good (rowAt 208) ∧ EntryGood 208) ∧ (rowAt 209 = data_209 ∧ Good (rowAt 209) ∧ EntryGood 209) ∧ (rowAt 210 = data_210 ∧ Good (rowAt 210) ∧ EntryGood 210) ∧ (rowAt 211 = data_211 ∧ Good (rowAt 211) ∧ EntryGood 211) ∧ (rowAt 212 = data_212 ∧ Good (rowAt 212) ∧ EntryGood 212) ∧ (rowAt 213 = data_213 ∧ Good (rowAt 213) ∧ EntryGood 213) ∧ (rowAt 214 = data_214 ∧ Good (rowAt 214) ∧ EntryGood 214) ∧ (rowAt 215 = data_215 ∧ Good (rowAt 215) ∧ EntryGood 215) ∧ True := by
  exact ⟨triple_208, triple_209, triple_210, triple_211, triple_212, triple_213, triple_214, triple_215, trivial⟩
