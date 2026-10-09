-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block11_part01_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T07:53:53.453283+00:00
-- url     : https://prove2.me/submissions/8dc441a4-bd78-4ac6-8539-cc7f851a03be

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block03_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block08_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_valid
import Definitions.Def_Snaky21Calc11Part00
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block10_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part00_valid
open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate
namespace OAI.Snaky21
theorem base_valid (i : Fin 6) : Valid (baseCard i) := claim_calculus.1 i
theorem placed_valid (r : Fin 8) (t : Cell) {c : Card} (h : Valid c) : Valid (placed r t c) := claim_calculus.2.1 r t c h
end OAI.Snaky21

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace OAI.Snaky21.Certificate
theorem computed_card_ext {c d : Card} (hA : c.required = d.required) (hT : c.envelope = d.envelope) (hh : c.height = d.height) : c = d := by
  cases c
  cases d
  cases hA
  cases hT
  cases hh
  rfl
theorem valid_14 : Valid card_14 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_52 : Valid card_52 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_59 : Valid card_59 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_79 : Valid card_79 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_105 : Valid card_105 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_181 : Valid card_181 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_189 : Valid card_189 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_242 : Valid card_242 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_243 : Valid card_243 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_323 : Valid card_323 := block05_valid.2.2.2.1
theorem valid_367 : Valid card_367 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_422 : Valid card_422 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_430 : Valid card_430 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_431 : Valid card_431 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_450 : Valid card_450 := block07_valid.2.2.1
theorem valid_474 : Valid card_474 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_503 : Valid card_503 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_518 : Valid card_518 := block08_valid.2.2.2.2.2.2.1
theorem valid_592 : Valid card_592 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_642 : Valid card_642 := block10_valid.2.2.1
theorem valid_680 : Valid card_680 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_681 : Valid card_681 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem calc11_card_81_eq : placed 6 (6, 8) card_14 = calc11_card_81 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_82_eq : placed 2 (2, 7) card_79 = calc11_card_82 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_83_eq : placed 1 (3, 3) card_181 = calc11_card_83 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_84_eq : placed 4 (6, 2) card_189 = calc11_card_84 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_85_eq : placed 2 (4, 8) card_367 = calc11_card_85 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_86_eq : placed 1 (3, 3) card_474 = calc11_card_86 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_87_eq : calc11_card_86.required ∪ ∅ = calc11_set_87 := by decide +kernel

theorem calc11_set_88_eq : calc11_card_86.envelope ∪ ∅ = calc11_set_88 := by decide +kernel

theorem calc11_set_89_eq : calc11_card_85.required ∪ calc11_set_87 = calc11_set_89 := by decide +kernel

theorem calc11_set_90_eq : calc11_card_85.envelope ∪ calc11_set_88 = calc11_set_90 := by decide +kernel

theorem calc11_set_91_eq : calc11_card_84.required ∪ calc11_set_89 = calc11_set_91 := by decide +kernel

theorem calc11_set_92_eq : calc11_card_84.envelope ∪ calc11_set_90 = calc11_set_92 := by decide +kernel

theorem calc11_set_93_eq : calc11_card_83.required ∪ calc11_set_91 = calc11_set_93 := by decide +kernel

theorem calc11_set_94_eq : calc11_card_83.envelope ∪ calc11_set_92 = calc11_set_94 := by decide +kernel

theorem calc11_set_95_eq : calc11_card_82.required ∪ calc11_set_93 = calc11_set_95 := by decide +kernel

theorem calc11_set_96_eq : calc11_card_82.envelope ∪ calc11_set_94 = calc11_set_96 := by decide +kernel

theorem calc11_set_97_eq : calc11_card_81.required ∪ calc11_set_95 = calc11_set_97 := by decide +kernel

theorem calc11_set_98_eq : calc11_card_81.envelope ∪ calc11_set_96 = calc11_set_98 := by decide +kernel

theorem calc11_set_99_eq : calc11_card_86.envelope ∩ calc11_card_81.envelope = calc11_set_99 := by decide +kernel

theorem calc11_set_100_eq : calc11_card_85.envelope ∩ calc11_set_99 = calc11_set_100 := by decide +kernel

theorem calc11_set_101_eq : calc11_card_84.envelope ∩ calc11_set_100 = calc11_set_101 := by decide +kernel

theorem calc11_set_102_eq : calc11_card_83.envelope ∩ calc11_set_101 = calc11_set_102 := by decide +kernel

theorem calc11_set_103_eq : calc11_card_82.envelope ∩ calc11_set_102 = calc11_set_103 := by decide +kernel

theorem calc11_set_104_eq : calc11_set_97 ∪ calc11_set_103 = calc11_set_104 := by decide +kernel

theorem calc11_finishA_105 : calc11_set_104.erase (5, 6) = inline_800.required := by decide +kernel

theorem calc11_finishT_105 : insert (5, 6) calc11_set_98 = inline_800.envelope := by decide +kernel

theorem eq_inline_800 : inline_800 = combine (5, 6) [placed 6 (6, 8) card_14, placed 2 (2, 7) card_79, placed 1 (3, 3) card_181, placed 4 (6, 2) card_189, placed 2 (4, 8) card_367, placed 1 (3, 3) card_474] := by
  rw [calc11_card_81_eq, calc11_card_82_eq, calc11_card_83_eq, calc11_card_84_eq, calc11_card_85_eq, calc11_card_86_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_87_eq, calc11_set_89_eq, calc11_set_91_eq, calc11_set_93_eq, calc11_set_95_eq, calc11_set_97_eq, calc11_set_99_eq, calc11_set_100_eq, calc11_set_101_eq, calc11_set_102_eq, calc11_set_103_eq, calc11_set_104_eq, calc11_finishA_105]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_88_eq, calc11_set_90_eq, calc11_set_92_eq, calc11_set_94_eq, calc11_set_96_eq, calc11_set_98_eq, calc11_finishT_105]
  · decide +kernel

theorem valid_inline_800 : Valid inline_800 := by
  rw [eq_inline_800]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 8) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_79
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 3) valid_181
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 2) valid_189
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 8) valid_367
  subst c
  exact placed_valid 1 (3, 3) valid_474

theorem calc11_card_106_eq : placed 2 (2, 8) card_59 = calc11_card_106 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_107_eq : placed 5 (1, 5) card_105 = calc11_card_107 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_108_eq : placed 4 (6, 1) card_323 = calc11_card_108 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_109_eq : inline_800.required ∪ ∅ = calc11_set_109 := by decide +kernel

theorem calc11_set_110_eq : inline_800.envelope ∪ ∅ = calc11_set_110 := by decide +kernel

theorem calc11_set_111_eq : calc11_card_108.required ∪ calc11_set_109 = calc11_set_111 := by decide +kernel

theorem calc11_set_112_eq : calc11_card_108.envelope ∪ calc11_set_110 = calc11_set_112 := by decide +kernel

theorem calc11_set_113_eq : calc11_card_107.required ∪ calc11_set_111 = calc11_set_113 := by decide +kernel

theorem calc11_set_114_eq : calc11_card_107.envelope ∪ calc11_set_112 = calc11_set_114 := by decide +kernel

theorem calc11_set_115_eq : calc11_card_106.required ∪ calc11_set_113 = calc11_set_115 := by decide +kernel

theorem calc11_set_116_eq : calc11_card_106.envelope ∪ calc11_set_114 = calc11_set_116 := by decide +kernel

theorem calc11_set_117_eq : inline_800.envelope ∩ calc11_card_106.envelope = calc11_set_117 := by decide +kernel

theorem calc11_set_118_eq : calc11_card_108.envelope ∩ calc11_set_117 = calc11_set_118 := by decide +kernel

theorem calc11_set_119_eq : calc11_card_107.envelope ∩ calc11_set_118 = calc11_set_119 := by decide +kernel

theorem calc11_set_120_eq : calc11_set_115 ∪ calc11_set_119 = calc11_set_120 := by decide +kernel

theorem calc11_finishA_121 : calc11_set_120.erase (5, 5) = inline_801.required := by decide +kernel

theorem calc11_finishT_121 : insert (5, 5) calc11_set_116 = inline_801.envelope := by decide +kernel

theorem eq_inline_801 : inline_801 = combine (5, 5) [placed 2 (2, 8) card_59, placed 5 (1, 5) card_105, placed 4 (6, 1) card_323, inline_800] := by
  rw [calc11_card_106_eq, calc11_card_107_eq, calc11_card_108_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_109_eq, calc11_set_111_eq, calc11_set_113_eq, calc11_set_115_eq, calc11_set_117_eq, calc11_set_118_eq, calc11_set_119_eq, calc11_set_120_eq, calc11_finishA_121]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_110_eq, calc11_set_112_eq, calc11_set_114_eq, calc11_set_116_eq, calc11_finishT_121]
  · decide +kernel

theorem valid_inline_801 : Valid inline_801 := by
  rw [eq_inline_801]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 8) valid_59
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_105
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 1) valid_323
  subst c
  exact valid_inline_800

theorem calc11_card_122_eq : placed 6 (5, 7) card_52 = calc11_card_122 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_123_eq : placed 4 (6, 2) card_242 = calc11_card_123 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_124_eq : calc11_card_123.required ∪ ∅ = calc11_set_124 := by decide +kernel

theorem calc11_set_125_eq : calc11_card_123.envelope ∪ ∅ = calc11_set_125 := by decide +kernel

theorem calc11_set_126_eq : calc11_card_122.required ∪ calc11_set_124 = calc11_set_126 := by decide +kernel

theorem calc11_set_127_eq : calc11_card_122.envelope ∪ calc11_set_125 = calc11_set_127 := by decide +kernel

theorem calc11_set_128_eq : calc11_card_123.envelope ∩ calc11_card_122.envelope = calc11_set_128 := by decide +kernel

theorem calc11_set_129_eq : calc11_set_126 ∪ calc11_set_128 = calc11_set_129 := by decide +kernel

theorem calc11_finishA_130 : calc11_set_129.erase (4, 4) = inline_802.required := by decide +kernel

theorem calc11_finishT_130 : insert (4, 4) calc11_set_127 = inline_802.envelope := by decide +kernel

theorem eq_inline_802 : inline_802 = combine (4, 4) [placed 6 (5, 7) card_52, placed 4 (6, 2) card_242] := by
  rw [calc11_card_122_eq, calc11_card_123_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_124_eq, calc11_set_126_eq, calc11_set_128_eq, calc11_set_129_eq, calc11_finishA_130]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_125_eq, calc11_set_127_eq, calc11_finishT_130]
  · decide +kernel

theorem valid_inline_802 : Valid inline_802 := by
  rw [eq_inline_802]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 7) valid_52
  subst c
  exact placed_valid 4 (6, 2) valid_242

theorem calc11_card_131_eq : placed 2 (2, 7) card_79 = calc11_card_131 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_132_eq : placed 4 (6, 2) card_243 = calc11_card_132 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_133_eq : placed 4 (8, 1) card_518 = calc11_card_133 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_134_eq : inline_802.required ∪ ∅ = calc11_set_134 := by decide +kernel

theorem calc11_set_135_eq : inline_802.envelope ∪ ∅ = calc11_set_135 := by decide +kernel

theorem calc11_set_136_eq : calc11_card_133.required ∪ calc11_set_134 = calc11_set_136 := by decide +kernel

theorem calc11_set_137_eq : calc11_card_133.envelope ∪ calc11_set_135 = calc11_set_137 := by decide +kernel

theorem calc11_set_138_eq : calc11_card_132.required ∪ calc11_set_136 = calc11_set_138 := by decide +kernel

theorem calc11_set_139_eq : calc11_card_132.envelope ∪ calc11_set_137 = calc11_set_139 := by decide +kernel

theorem calc11_set_140_eq : calc11_card_131.required ∪ calc11_set_138 = calc11_set_140 := by decide +kernel

theorem calc11_set_141_eq : calc11_card_131.envelope ∪ calc11_set_139 = calc11_set_141 := by decide +kernel

theorem calc11_set_142_eq : inline_802.envelope ∩ calc11_card_131.envelope = calc11_set_142 := by decide +kernel

theorem calc11_set_143_eq : calc11_card_133.envelope ∩ calc11_set_142 = calc11_set_143 := by decide +kernel

theorem calc11_set_144_eq : calc11_card_132.envelope ∩ calc11_set_143 = calc11_set_144 := by decide +kernel

theorem calc11_set_145_eq : calc11_set_140 ∪ calc11_set_144 = calc11_set_145 := by decide +kernel

theorem calc11_finishA_146 : calc11_set_145.erase (5, 6) = inline_803.required := by decide +kernel

theorem calc11_finishT_146 : insert (5, 6) calc11_set_141 = inline_803.envelope := by decide +kernel

theorem eq_inline_803 : inline_803 = combine (5, 6) [placed 2 (2, 7) card_79, placed 4 (6, 2) card_243, placed 4 (8, 1) card_518, inline_802] := by
  rw [calc11_card_131_eq, calc11_card_132_eq, calc11_card_133_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_134_eq, calc11_set_136_eq, calc11_set_138_eq, calc11_set_140_eq, calc11_set_142_eq, calc11_set_143_eq, calc11_set_144_eq, calc11_set_145_eq, calc11_finishA_146]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_135_eq, calc11_set_137_eq, calc11_set_139_eq, calc11_set_141_eq, calc11_finishT_146]
  · decide +kernel

theorem valid_inline_803 : Valid inline_803 := by
  rw [eq_inline_803]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_79
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 2) valid_243
  rcases hc with rfl | hc
  · exact placed_valid 4 (8, 1) valid_518
  subst c
  exact valid_inline_802

theorem calc11_card_147_eq : placed 4 (6, 1) card_323 = calc11_card_147 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_148_eq : placed 0 (2, 1) card_430 = calc11_card_148 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_149_eq : placed 0 (1, 2) card_431 = calc11_card_149 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_150_eq : placed 7 (6, 5) card_592 = calc11_card_150 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_151_eq : placed 2 (1, 9) card_681 = calc11_card_151 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_152_eq : inline_803.required ∪ ∅ = calc11_set_152 := by decide +kernel

theorem calc11_set_153_eq : inline_803.envelope ∪ ∅ = calc11_set_153 := by decide +kernel

theorem calc11_set_154_eq : calc11_card_151.required ∪ calc11_set_152 = calc11_set_154 := by decide +kernel

theorem calc11_set_155_eq : calc11_card_151.envelope ∪ calc11_set_153 = calc11_set_155 := by decide +kernel

theorem calc11_set_156_eq : calc11_card_150.required ∪ calc11_set_154 = calc11_set_156 := by decide +kernel

theorem calc11_set_157_eq : calc11_card_150.envelope ∪ calc11_set_155 = calc11_set_157 := by decide +kernel

theorem calc11_set_158_eq : calc11_card_149.required ∪ calc11_set_156 = calc11_set_158 := by decide +kernel

theorem calc11_set_159_eq : calc11_card_149.envelope ∪ calc11_set_157 = calc11_set_159 := by decide +kernel

theorem calc11_set_160_eq : calc11_card_148.required ∪ calc11_set_158 = calc11_set_160 := by decide +kernel

theorem calc11_set_161_eq : calc11_card_148.envelope ∪ calc11_set_159 = calc11_set_161 := by decide +kernel

theorem calc11_set_162_eq : calc11_card_147.required ∪ calc11_set_160 = calc11_set_162 := by decide +kernel

theorem calc11_set_163_eq : calc11_card_147.envelope ∪ calc11_set_161 = calc11_set_163 := by decide +kernel

theorem calc11_set_164_eq : inline_803.envelope ∩ calc11_card_147.envelope = calc11_set_164 := by decide +kernel

theorem calc11_set_165_eq : calc11_card_151.envelope ∩ calc11_set_164 = calc11_set_165 := by decide +kernel

theorem calc11_set_166_eq : calc11_card_150.envelope ∩ calc11_set_165 = calc11_set_166 := by decide +kernel

theorem calc11_set_167_eq : calc11_card_149.envelope ∩ calc11_set_166 = calc11_set_167 := by decide +kernel

theorem calc11_set_168_eq : calc11_card_148.envelope ∩ calc11_set_167 = calc11_set_168 := by decide +kernel

theorem calc11_set_169_eq : calc11_set_162 ∪ calc11_set_168 = calc11_set_169 := by decide +kernel

theorem calc11_finishA_170 : calc11_set_169.erase (5, 5) = inline_804.required := by decide +kernel

theorem calc11_finishT_170 : insert (5, 5) calc11_set_163 = inline_804.envelope := by decide +kernel

theorem eq_inline_804 : inline_804 = combine (5, 5) [placed 4 (6, 1) card_323, placed 0 (2, 1) card_430, placed 0 (1, 2) card_431, placed 7 (6, 5) card_592, placed 2 (1, 9) card_681, inline_803] := by
  rw [calc11_card_147_eq, calc11_card_148_eq, calc11_card_149_eq, calc11_card_150_eq, calc11_card_151_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_152_eq, calc11_set_154_eq, calc11_set_156_eq, calc11_set_158_eq, calc11_set_160_eq, calc11_set_162_eq, calc11_set_164_eq, calc11_set_165_eq, calc11_set_166_eq, calc11_set_167_eq, calc11_set_168_eq, calc11_set_169_eq, calc11_finishA_170]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_153_eq, calc11_set_155_eq, calc11_set_157_eq, calc11_set_159_eq, calc11_set_161_eq, calc11_set_163_eq, calc11_finishT_170]
  · decide +kernel

theorem valid_inline_804 : Valid inline_804 := by
  rw [eq_inline_804]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 1) valid_323
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_430
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_431
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 5) valid_592
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 9) valid_681
  subst c
  exact valid_inline_803

theorem calc11_card_171_eq : placed 4 (6, 2) card_422 = calc11_card_171 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_172_eq : placed 2 (1, 8) card_450 = calc11_card_172 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_173_eq : placed 6 (6, 7) card_503 = calc11_card_173 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_174_eq : placed 0 (2, 0) card_642 = calc11_card_174 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_175_eq : placed 2 (1, 7) card_680 = calc11_card_175 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_176_eq : inline_804.required ∪ ∅ = calc11_set_176 := by decide +kernel

theorem calc11_set_177_eq : inline_804.envelope ∪ ∅ = calc11_set_177 := by decide +kernel

theorem calc11_set_178_eq : inline_801.required ∪ calc11_set_176 = calc11_set_178 := by decide +kernel

theorem calc11_set_179_eq : inline_801.envelope ∪ calc11_set_177 = calc11_set_179 := by decide +kernel

theorem calc11_set_180_eq : calc11_card_175.required ∪ calc11_set_178 = calc11_set_180 := by decide +kernel

theorem calc11_set_181_eq : calc11_card_175.envelope ∪ calc11_set_179 = calc11_set_181 := by decide +kernel

theorem calc11_set_182_eq : calc11_card_174.required ∪ calc11_set_180 = calc11_set_182 := by decide +kernel

theorem calc11_set_183_eq : calc11_card_174.envelope ∪ calc11_set_181 = calc11_set_183 := by decide +kernel

theorem calc11_set_184_eq : calc11_card_173.required ∪ calc11_set_182 = calc11_set_184 := by decide +kernel

theorem calc11_set_185_eq : calc11_card_173.envelope ∪ calc11_set_183 = calc11_set_185 := by decide +kernel

theorem calc11_set_186_eq : calc11_card_172.required ∪ calc11_set_184 = calc11_set_186 := by decide +kernel

theorem calc11_set_187_eq : calc11_card_172.envelope ∪ calc11_set_185 = calc11_set_187 := by decide +kernel

theorem calc11_set_188_eq : calc11_card_171.required ∪ calc11_set_186 = calc11_set_188 := by decide +kernel

theorem calc11_set_189_eq : calc11_card_171.envelope ∪ calc11_set_187 = calc11_set_189 := by decide +kernel

theorem calc11_set_190_eq : inline_804.envelope ∩ calc11_card_171.envelope = calc11_set_190 := by decide +kernel

theorem calc11_set_191_eq : inline_801.envelope ∩ calc11_set_190 = calc11_set_191 := by decide +kernel

theorem calc11_set_192_eq : calc11_card_175.envelope ∩ calc11_set_191 = calc11_set_192 := by decide +kernel

theorem calc11_set_193_eq : calc11_card_174.envelope ∩ calc11_set_192 = calc11_set_193 := by decide +kernel

theorem calc11_set_194_eq : calc11_card_173.envelope ∩ calc11_set_193 = calc11_set_194 := by decide +kernel

theorem calc11_set_195_eq : calc11_card_172.envelope ∩ calc11_set_194 = calc11_set_195 := by decide +kernel

theorem calc11_set_196_eq : calc11_set_188 ∪ calc11_set_195 = calc11_set_196 := by decide +kernel

theorem calc11_finishA_197 : calc11_set_196.erase (5, 4) = card_705.required := by decide +kernel

theorem calc11_finishT_197 : insert (5, 4) calc11_set_189 = card_705.envelope := by decide +kernel

theorem eq_card_705 : card_705 = combine (5, 4) [placed 4 (6, 2) card_422, placed 2 (1, 8) card_450, placed 6 (6, 7) card_503, placed 0 (2, 0) card_642, placed 2 (1, 7) card_680, inline_801, inline_804] := by
  rw [calc11_card_171_eq, calc11_card_172_eq, calc11_card_173_eq, calc11_card_174_eq, calc11_card_175_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_176_eq, calc11_set_178_eq, calc11_set_180_eq, calc11_set_182_eq, calc11_set_184_eq, calc11_set_186_eq, calc11_set_188_eq, calc11_set_190_eq, calc11_set_191_eq, calc11_set_192_eq, calc11_set_193_eq, calc11_set_194_eq, calc11_set_195_eq, calc11_set_196_eq, calc11_finishA_197]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_177_eq, calc11_set_179_eq, calc11_set_181_eq, calc11_set_183_eq, calc11_set_185_eq, calc11_set_187_eq, calc11_set_189_eq, calc11_finishT_197]
  · decide +kernel

theorem valid_705 : Valid card_705 := by
  rw [eq_card_705]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 2) valid_422
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 8) valid_450
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 7) valid_503
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_642
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_680
  rcases hc with rfl | hc
  · exact valid_inline_801
  subst c
  exact valid_inline_804


end OAI.Snaky21.Certificate

theorem solution : Valid card_705 ∧ True :=
  ⟨valid_705, True.intro⟩
