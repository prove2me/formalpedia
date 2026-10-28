-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block05_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T09:21:25.834511+00:00
-- url     : https://prove2.me/submissions/117a7de5-9f21-402f-952e-2e446db04fbe

import Definitions.Def_Snaky35Cache05
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_group00_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_group00_piece01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_group01_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_group01_piece01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_group02_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_group02_piece01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_group03_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_group03_piece01_correct
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
theorem triple_168 : rowAt 168 = data_168 ∧ Good (rowAt 168) ∧ EntryGood 168 := (OAI.SnakyCertificate.MilestoneChecks.block05_group01_piece00_correct.1)
theorem triple_169 : rowAt 169 = data_169 ∧ Good (rowAt 169) ∧ EntryGood 169 := (OAI.SnakyCertificate.MilestoneChecks.block05_group01_piece00_correct.2.1)
theorem triple_170 : rowAt 170 = data_170 ∧ Good (rowAt 170) ∧ EntryGood 170 := (OAI.SnakyCertificate.MilestoneChecks.block05_group01_piece00_correct.2.2.1)
theorem triple_171 : rowAt 171 = data_171 ∧ Good (rowAt 171) ∧ EntryGood 171 := (OAI.SnakyCertificate.MilestoneChecks.block05_group01_piece00_correct.2.2.2.1)
theorem triple_172 : rowAt 172 = data_172 ∧ Good (rowAt 172) ∧ EntryGood 172 := (OAI.SnakyCertificate.MilestoneChecks.block05_group01_piece01_correct.1)
theorem triple_173 : rowAt 173 = data_173 ∧ Good (rowAt 173) ∧ EntryGood 173 := (OAI.SnakyCertificate.MilestoneChecks.block05_group01_piece01_correct.2.1)
theorem triple_174 : rowAt 174 = data_174 ∧ Good (rowAt 174) ∧ EntryGood 174 := (OAI.SnakyCertificate.MilestoneChecks.block05_group01_piece01_correct.2.2.1)
theorem triple_175 : rowAt 175 = data_175 ∧ Good (rowAt 175) ∧ EntryGood 175 := (OAI.SnakyCertificate.MilestoneChecks.block05_group01_piece01_correct.2.2.2.1)
theorem triple_176 : rowAt 176 = data_176 ∧ Good (rowAt 176) ∧ EntryGood 176 := (OAI.SnakyCertificate.MilestoneChecks.block05_group02_piece00_correct.1)
theorem triple_177 : rowAt 177 = data_177 ∧ Good (rowAt 177) ∧ EntryGood 177 := (OAI.SnakyCertificate.MilestoneChecks.block05_group02_piece00_correct.2.1)
theorem triple_178 : rowAt 178 = data_178 ∧ Good (rowAt 178) ∧ EntryGood 178 := (OAI.SnakyCertificate.MilestoneChecks.block05_group02_piece00_correct.2.2.1)
theorem triple_179 : rowAt 179 = data_179 ∧ Good (rowAt 179) ∧ EntryGood 179 := (OAI.SnakyCertificate.MilestoneChecks.block05_group02_piece00_correct.2.2.2.1)
theorem triple_180 : rowAt 180 = data_180 ∧ Good (rowAt 180) ∧ EntryGood 180 := (OAI.SnakyCertificate.MilestoneChecks.block05_group02_piece01_correct.1)
theorem triple_181 : rowAt 181 = data_181 ∧ Good (rowAt 181) ∧ EntryGood 181 := (OAI.SnakyCertificate.MilestoneChecks.block05_group02_piece01_correct.2.1)
theorem triple_182 : rowAt 182 = data_182 ∧ Good (rowAt 182) ∧ EntryGood 182 := (OAI.SnakyCertificate.MilestoneChecks.block05_group02_piece01_correct.2.2.1)
theorem triple_183 : rowAt 183 = data_183 ∧ Good (rowAt 183) ∧ EntryGood 183 := (OAI.SnakyCertificate.MilestoneChecks.block05_group02_piece01_correct.2.2.2.1)
theorem triple_184 : rowAt 184 = data_184 ∧ Good (rowAt 184) ∧ EntryGood 184 := (OAI.SnakyCertificate.MilestoneChecks.block05_group03_piece00_correct.1)
theorem triple_185 : rowAt 185 = data_185 ∧ Good (rowAt 185) ∧ EntryGood 185 := (OAI.SnakyCertificate.MilestoneChecks.block05_group03_piece00_correct.2.1)
theorem triple_186 : rowAt 186 = data_186 ∧ Good (rowAt 186) ∧ EntryGood 186 := (OAI.SnakyCertificate.MilestoneChecks.block05_group03_piece00_correct.2.2.1)
theorem triple_187 : rowAt 187 = data_187 ∧ Good (rowAt 187) ∧ EntryGood 187 := (OAI.SnakyCertificate.MilestoneChecks.block05_group03_piece00_correct.2.2.2.1)
theorem triple_188 : rowAt 188 = data_188 ∧ Good (rowAt 188) ∧ EntryGood 188 := (OAI.SnakyCertificate.MilestoneChecks.block05_group03_piece01_correct.1)
theorem triple_189 : rowAt 189 = data_189 ∧ Good (rowAt 189) ∧ EntryGood 189 := (OAI.SnakyCertificate.MilestoneChecks.block05_group03_piece01_correct.2.1)
theorem triple_190 : rowAt 190 = data_190 ∧ Good (rowAt 190) ∧ EntryGood 190 := (OAI.SnakyCertificate.MilestoneChecks.block05_group03_piece01_correct.2.2.1)
theorem triple_191 : rowAt 191 = data_191 ∧ Good (rowAt 191) ∧ EntryGood 191 := (OAI.SnakyCertificate.MilestoneChecks.block05_group03_piece01_correct.2.2.2.1)
end OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks.S213
theorem solution : (rowAt 160 = data_160 ∧ Good (rowAt 160) ∧ EntryGood 160) ∧ (rowAt 161 = data_161 ∧ Good (rowAt 161) ∧ EntryGood 161) ∧ (rowAt 162 = data_162 ∧ Good (rowAt 162) ∧ EntryGood 162) ∧ (rowAt 163 = data_163 ∧ Good (rowAt 163) ∧ EntryGood 163) ∧ (rowAt 164 = data_164 ∧ Good (rowAt 164) ∧ EntryGood 164) ∧ (rowAt 165 = data_165 ∧ Good (rowAt 165) ∧ EntryGood 165) ∧ (rowAt 166 = data_166 ∧ Good (rowAt 166) ∧ EntryGood 166) ∧ (rowAt 167 = data_167 ∧ Good (rowAt 167) ∧ EntryGood 167) ∧ (rowAt 168 = data_168 ∧ Good (rowAt 168) ∧ EntryGood 168) ∧ (rowAt 169 = data_169 ∧ Good (rowAt 169) ∧ EntryGood 169) ∧ (rowAt 170 = data_170 ∧ Good (rowAt 170) ∧ EntryGood 170) ∧ (rowAt 171 = data_171 ∧ Good (rowAt 171) ∧ EntryGood 171) ∧ (rowAt 172 = data_172 ∧ Good (rowAt 172) ∧ EntryGood 172) ∧ (rowAt 173 = data_173 ∧ Good (rowAt 173) ∧ EntryGood 173) ∧ (rowAt 174 = data_174 ∧ Good (rowAt 174) ∧ EntryGood 174) ∧ (rowAt 175 = data_175 ∧ Good (rowAt 175) ∧ EntryGood 175) ∧ (rowAt 176 = data_176 ∧ Good (rowAt 176) ∧ EntryGood 176) ∧ (rowAt 177 = data_177 ∧ Good (rowAt 177) ∧ EntryGood 177) ∧ (rowAt 178 = data_178 ∧ Good (rowAt 178) ∧ EntryGood 178) ∧ (rowAt 179 = data_179 ∧ Good (rowAt 179) ∧ EntryGood 179) ∧ (rowAt 180 = data_180 ∧ Good (rowAt 180) ∧ EntryGood 180) ∧ (rowAt 181 = data_181 ∧ Good (rowAt 181) ∧ EntryGood 181) ∧ (rowAt 182 = data_182 ∧ Good (rowAt 182) ∧ EntryGood 182) ∧ (rowAt 183 = data_183 ∧ Good (rowAt 183) ∧ EntryGood 183) ∧ (rowAt 184 = data_184 ∧ Good (rowAt 184) ∧ EntryGood 184) ∧ (rowAt 185 = data_185 ∧ Good (rowAt 185) ∧ EntryGood 185) ∧ (rowAt 186 = data_186 ∧ Good (rowAt 186) ∧ EntryGood 186) ∧ (rowAt 187 = data_187 ∧ Good (rowAt 187) ∧ EntryGood 187) ∧ (rowAt 188 = data_188 ∧ Good (rowAt 188) ∧ EntryGood 188) ∧ (rowAt 189 = data_189 ∧ Good (rowAt 189) ∧ EntryGood 189) ∧ (rowAt 190 = data_190 ∧ Good (rowAt 190) ∧ EntryGood 190) ∧ (rowAt 191 = data_191 ∧ Good (rowAt 191) ∧ EntryGood 191) ∧ True := by
  exact ⟨triple_160, triple_161, triple_162, triple_163, triple_164, triple_165, triple_166, triple_167, triple_168, triple_169, triple_170, triple_171, triple_172, triple_173, triple_174, triple_175, triple_176, triple_177, triple_178, triple_179, triple_180, triple_181, triple_182, triple_183, triple_184, triple_185, triple_186, triple_187, triple_188, triple_189, triple_190, triple_191, trivial⟩
