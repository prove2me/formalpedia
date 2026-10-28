-- Prove2me | solution 1 for OAI.SnakyCertificate.MilestoneChecks.block04_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T09:19:55.584736+00:00
-- url     : https://prove2.me/submissions/eadb9da9-ac0d-4426-9290-690c9a641061

import Definitions.Def_Snaky35Cache04
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_group00_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_group00_piece01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_group01_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_group01_piece01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_group02_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_group02_piece01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_group03_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_group03_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks.S213
open OAI.SnakyCertificate OAI.SnakyCertificate.MilestoneChecks
theorem triple_128 : rowAt 128 = data_128 ∧ Good (rowAt 128) ∧ EntryGood 128 := (OAI.SnakyCertificate.MilestoneChecks.block04_group00_piece00_correct.1)
theorem triple_129 : rowAt 129 = data_129 ∧ Good (rowAt 129) ∧ EntryGood 129 := (OAI.SnakyCertificate.MilestoneChecks.block04_group00_piece00_correct.2.1)
theorem triple_130 : rowAt 130 = data_130 ∧ Good (rowAt 130) ∧ EntryGood 130 := (OAI.SnakyCertificate.MilestoneChecks.block04_group00_piece00_correct.2.2.1)
theorem triple_131 : rowAt 131 = data_131 ∧ Good (rowAt 131) ∧ EntryGood 131 := (OAI.SnakyCertificate.MilestoneChecks.block04_group00_piece00_correct.2.2.2.1)
theorem triple_132 : rowAt 132 = data_132 ∧ Good (rowAt 132) ∧ EntryGood 132 := (OAI.SnakyCertificate.MilestoneChecks.block04_group00_piece01_correct.1)
theorem triple_133 : rowAt 133 = data_133 ∧ Good (rowAt 133) ∧ EntryGood 133 := (OAI.SnakyCertificate.MilestoneChecks.block04_group00_piece01_correct.2.1)
theorem triple_134 : rowAt 134 = data_134 ∧ Good (rowAt 134) ∧ EntryGood 134 := (OAI.SnakyCertificate.MilestoneChecks.block04_group00_piece01_correct.2.2.1)
theorem triple_135 : rowAt 135 = data_135 ∧ Good (rowAt 135) ∧ EntryGood 135 := (OAI.SnakyCertificate.MilestoneChecks.block04_group00_piece01_correct.2.2.2.1)
theorem triple_136 : rowAt 136 = data_136 ∧ Good (rowAt 136) ∧ EntryGood 136 := (OAI.SnakyCertificate.MilestoneChecks.block04_group01_piece00_correct.1)
theorem triple_137 : rowAt 137 = data_137 ∧ Good (rowAt 137) ∧ EntryGood 137 := (OAI.SnakyCertificate.MilestoneChecks.block04_group01_piece00_correct.2.1)
theorem triple_138 : rowAt 138 = data_138 ∧ Good (rowAt 138) ∧ EntryGood 138 := (OAI.SnakyCertificate.MilestoneChecks.block04_group01_piece00_correct.2.2.1)
theorem triple_139 : rowAt 139 = data_139 ∧ Good (rowAt 139) ∧ EntryGood 139 := (OAI.SnakyCertificate.MilestoneChecks.block04_group01_piece00_correct.2.2.2.1)
theorem triple_140 : rowAt 140 = data_140 ∧ Good (rowAt 140) ∧ EntryGood 140 := (OAI.SnakyCertificate.MilestoneChecks.block04_group01_piece01_correct.1)
theorem triple_141 : rowAt 141 = data_141 ∧ Good (rowAt 141) ∧ EntryGood 141 := (OAI.SnakyCertificate.MilestoneChecks.block04_group01_piece01_correct.2.1)
theorem triple_142 : rowAt 142 = data_142 ∧ Good (rowAt 142) ∧ EntryGood 142 := (OAI.SnakyCertificate.MilestoneChecks.block04_group01_piece01_correct.2.2.1)
theorem triple_143 : rowAt 143 = data_143 ∧ Good (rowAt 143) ∧ EntryGood 143 := (OAI.SnakyCertificate.MilestoneChecks.block04_group01_piece01_correct.2.2.2.1)
theorem triple_144 : rowAt 144 = data_144 ∧ Good (rowAt 144) ∧ EntryGood 144 := (OAI.SnakyCertificate.MilestoneChecks.block04_group02_piece00_correct.1)
theorem triple_145 : rowAt 145 = data_145 ∧ Good (rowAt 145) ∧ EntryGood 145 := (OAI.SnakyCertificate.MilestoneChecks.block04_group02_piece00_correct.2.1)
theorem triple_146 : rowAt 146 = data_146 ∧ Good (rowAt 146) ∧ EntryGood 146 := (OAI.SnakyCertificate.MilestoneChecks.block04_group02_piece00_correct.2.2.1)
theorem triple_147 : rowAt 147 = data_147 ∧ Good (rowAt 147) ∧ EntryGood 147 := (OAI.SnakyCertificate.MilestoneChecks.block04_group02_piece00_correct.2.2.2.1)
theorem triple_148 : rowAt 148 = data_148 ∧ Good (rowAt 148) ∧ EntryGood 148 := (OAI.SnakyCertificate.MilestoneChecks.block04_group02_piece01_correct.1)
theorem triple_149 : rowAt 149 = data_149 ∧ Good (rowAt 149) ∧ EntryGood 149 := (OAI.SnakyCertificate.MilestoneChecks.block04_group02_piece01_correct.2.1)
theorem triple_150 : rowAt 150 = data_150 ∧ Good (rowAt 150) ∧ EntryGood 150 := (OAI.SnakyCertificate.MilestoneChecks.block04_group02_piece01_correct.2.2.1)
theorem triple_151 : rowAt 151 = data_151 ∧ Good (rowAt 151) ∧ EntryGood 151 := (OAI.SnakyCertificate.MilestoneChecks.block04_group02_piece01_correct.2.2.2.1)
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
theorem solution : (rowAt 128 = data_128 ∧ Good (rowAt 128) ∧ EntryGood 128) ∧ (rowAt 129 = data_129 ∧ Good (rowAt 129) ∧ EntryGood 129) ∧ (rowAt 130 = data_130 ∧ Good (rowAt 130) ∧ EntryGood 130) ∧ (rowAt 131 = data_131 ∧ Good (rowAt 131) ∧ EntryGood 131) ∧ (rowAt 132 = data_132 ∧ Good (rowAt 132) ∧ EntryGood 132) ∧ (rowAt 133 = data_133 ∧ Good (rowAt 133) ∧ EntryGood 133) ∧ (rowAt 134 = data_134 ∧ Good (rowAt 134) ∧ EntryGood 134) ∧ (rowAt 135 = data_135 ∧ Good (rowAt 135) ∧ EntryGood 135) ∧ (rowAt 136 = data_136 ∧ Good (rowAt 136) ∧ EntryGood 136) ∧ (rowAt 137 = data_137 ∧ Good (rowAt 137) ∧ EntryGood 137) ∧ (rowAt 138 = data_138 ∧ Good (rowAt 138) ∧ EntryGood 138) ∧ (rowAt 139 = data_139 ∧ Good (rowAt 139) ∧ EntryGood 139) ∧ (rowAt 140 = data_140 ∧ Good (rowAt 140) ∧ EntryGood 140) ∧ (rowAt 141 = data_141 ∧ Good (rowAt 141) ∧ EntryGood 141) ∧ (rowAt 142 = data_142 ∧ Good (rowAt 142) ∧ EntryGood 142) ∧ (rowAt 143 = data_143 ∧ Good (rowAt 143) ∧ EntryGood 143) ∧ (rowAt 144 = data_144 ∧ Good (rowAt 144) ∧ EntryGood 144) ∧ (rowAt 145 = data_145 ∧ Good (rowAt 145) ∧ EntryGood 145) ∧ (rowAt 146 = data_146 ∧ Good (rowAt 146) ∧ EntryGood 146) ∧ (rowAt 147 = data_147 ∧ Good (rowAt 147) ∧ EntryGood 147) ∧ (rowAt 148 = data_148 ∧ Good (rowAt 148) ∧ EntryGood 148) ∧ (rowAt 149 = data_149 ∧ Good (rowAt 149) ∧ EntryGood 149) ∧ (rowAt 150 = data_150 ∧ Good (rowAt 150) ∧ EntryGood 150) ∧ (rowAt 151 = data_151 ∧ Good (rowAt 151) ∧ EntryGood 151) ∧ (rowAt 152 = data_152 ∧ Good (rowAt 152) ∧ EntryGood 152) ∧ (rowAt 153 = data_153 ∧ Good (rowAt 153) ∧ EntryGood 153) ∧ (rowAt 154 = data_154 ∧ Good (rowAt 154) ∧ EntryGood 154) ∧ (rowAt 155 = data_155 ∧ Good (rowAt 155) ∧ EntryGood 155) ∧ (rowAt 156 = data_156 ∧ Good (rowAt 156) ∧ EntryGood 156) ∧ (rowAt 157 = data_157 ∧ Good (rowAt 157) ∧ EntryGood 157) ∧ (rowAt 158 = data_158 ∧ Good (rowAt 158) ∧ EntryGood 158) ∧ (rowAt 159 = data_159 ∧ Good (rowAt 159) ∧ EntryGood 159) ∧ True := by
  exact ⟨triple_128, triple_129, triple_130, triple_131, triple_132, triple_133, triple_134, triple_135, triple_136, triple_137, triple_138, triple_139, triple_140, triple_141, triple_142, triple_143, triple_144, triple_145, triple_146, triple_147, triple_148, triple_149, triple_150, triple_151, triple_152, triple_153, triple_154, triple_155, triple_156, triple_157, triple_158, triple_159, trivial⟩
