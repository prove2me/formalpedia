-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block11_part08_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:08:04.557024+00:00
-- url     : https://prove2.me/submissions/a7125362-dbb0-444b-bdf1-907a58939c9f

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block08_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part06_valid
import Definitions.Def_Snaky21Calc11Part04
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block10_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part07_valid
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
theorem valid_44 : Valid card_44 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_116 : Valid card_116 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_174 : Valid card_174 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_297 : Valid card_297 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_435 : Valid card_435 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_508 : Valid card_508 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_545 : Valid card_545 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_566 : Valid card_566 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_605 : Valid card_605 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_647 : Valid card_647 := block10_valid.2.2.2.2.2.2.2.1
theorem valid_649 : Valid card_649 := block10_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_650 : Valid card_650 := block10_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_655 : Valid card_655 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_661 : Valid card_661 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_710 : Valid card_710 := block11_part06_valid.1
theorem valid_711 : Valid card_711 := block11_part07_valid.1

theorem calc11_card_1000_eq : placed 2 (5, 7) card_44 = calc11_card_1000 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1001_eq : placed 3 (10, 3) card_545 = calc11_card_1001 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1002_eq : placed 7 (10, 7) card_655 = calc11_card_1002 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1003_eq : calc11_card_1002.required ∪ ∅ = calc11_set_1003 := by decide +kernel

theorem calc11_set_1004_eq : calc11_card_1002.envelope ∪ ∅ = calc11_set_1004 := by decide +kernel

theorem calc11_set_1005_eq : calc11_card_1001.required ∪ calc11_set_1003 = calc11_set_1005 := by decide +kernel

theorem calc11_set_1006_eq : calc11_card_1001.envelope ∪ calc11_set_1004 = calc11_set_1006 := by decide +kernel

theorem calc11_set_1007_eq : calc11_card_1000.required ∪ calc11_set_1005 = calc11_set_1007 := by decide +kernel

theorem calc11_set_1008_eq : calc11_card_1000.envelope ∪ calc11_set_1006 = calc11_set_1008 := by decide +kernel

theorem calc11_set_1009_eq : calc11_card_1002.envelope ∩ calc11_card_1000.envelope = calc11_set_1009 := by decide +kernel

theorem calc11_set_1010_eq : calc11_card_1001.envelope ∩ calc11_set_1009 = calc11_set_1010 := by decide +kernel

theorem calc11_set_1011_eq : calc11_set_1007 ∪ calc11_set_1010 = calc11_set_1011 := by decide +kernel

theorem calc11_finishA_1012 : calc11_set_1011.erase (6, 4) = inline_840.required := by decide +kernel

theorem calc11_finishT_1012 : insert (6, 4) calc11_set_1008 = inline_840.envelope := by decide +kernel

theorem eq_inline_840 : inline_840 = combine (6, 4) [placed 2 (5, 7) card_44, placed 3 (10, 3) card_545, placed 7 (10, 7) card_655] := by
  rw [calc11_card_1000_eq, calc11_card_1001_eq, calc11_card_1002_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1003_eq, calc11_set_1005_eq, calc11_set_1007_eq, calc11_set_1009_eq, calc11_set_1010_eq, calc11_set_1011_eq, calc11_finishA_1012]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1004_eq, calc11_set_1006_eq, calc11_set_1008_eq, calc11_finishT_1012]
  · decide +kernel

theorem valid_inline_840 : Valid inline_840 := by
  rw [eq_inline_840]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 7) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 3 (10, 3) valid_545
  subst c
  exact placed_valid 7 (10, 7) valid_655

theorem calc11_card_1013_eq : placed 5 (2, 7) card_116 = calc11_card_1013 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1014_eq : placed 5 (2, 8) card_297 = calc11_card_1014 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1015_eq : placed 3 (8, 3) card_435 = calc11_card_1015 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1016_eq : placed 1 (2, 3) card_435 = calc11_card_1016 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1017_eq : placed 7 (10, 8) card_649 = calc11_card_1017 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1018_eq : inline_840.required ∪ ∅ = calc11_set_1018 := by decide +kernel

theorem calc11_set_1019_eq : inline_840.envelope ∪ ∅ = calc11_set_1019 := by decide +kernel

theorem calc11_set_1020_eq : calc11_card_1017.required ∪ calc11_set_1018 = calc11_set_1020 := by decide +kernel

theorem calc11_set_1021_eq : calc11_card_1017.envelope ∪ calc11_set_1019 = calc11_set_1021 := by decide +kernel

theorem calc11_set_1022_eq : calc11_card_1016.required ∪ calc11_set_1020 = calc11_set_1022 := by decide +kernel

theorem calc11_set_1023_eq : calc11_card_1016.envelope ∪ calc11_set_1021 = calc11_set_1023 := by decide +kernel

theorem calc11_set_1024_eq : calc11_card_1015.required ∪ calc11_set_1022 = calc11_set_1024 := by decide +kernel

theorem calc11_set_1025_eq : calc11_card_1015.envelope ∪ calc11_set_1023 = calc11_set_1025 := by decide +kernel

theorem calc11_set_1026_eq : calc11_card_1014.required ∪ calc11_set_1024 = calc11_set_1026 := by decide +kernel

theorem calc11_set_1027_eq : calc11_card_1014.envelope ∪ calc11_set_1025 = calc11_set_1027 := by decide +kernel

theorem calc11_set_1028_eq : calc11_card_1013.required ∪ calc11_set_1026 = calc11_set_1028 := by decide +kernel

theorem calc11_set_1029_eq : calc11_card_1013.envelope ∪ calc11_set_1027 = calc11_set_1029 := by decide +kernel

theorem calc11_set_1030_eq : inline_840.envelope ∩ calc11_card_1013.envelope = calc11_set_1030 := by decide +kernel

theorem calc11_set_1031_eq : calc11_card_1017.envelope ∩ calc11_set_1030 = calc11_set_1031 := by decide +kernel

theorem calc11_set_1032_eq : calc11_card_1016.envelope ∩ calc11_set_1031 = calc11_set_1032 := by decide +kernel

theorem calc11_set_1033_eq : calc11_card_1015.envelope ∩ calc11_set_1032 = calc11_set_1033 := by decide +kernel

theorem calc11_set_1034_eq : calc11_card_1014.envelope ∩ calc11_set_1033 = calc11_set_1034 := by decide +kernel

theorem calc11_set_1035_eq : calc11_set_1028 ∪ calc11_set_1034 = calc11_set_1035 := by decide +kernel

theorem calc11_finishA_1036 : calc11_set_1035.erase (5, 4) = inline_841.required := by decide +kernel

theorem calc11_finishT_1036 : insert (5, 4) calc11_set_1029 = inline_841.envelope := by decide +kernel

theorem eq_inline_841 : inline_841 = combine (5, 4) [placed 5 (2, 7) card_116, placed 5 (2, 8) card_297, placed 3 (8, 3) card_435, placed 1 (2, 3) card_435, placed 7 (10, 8) card_649, inline_840] := by
  rw [calc11_card_1013_eq, calc11_card_1014_eq, calc11_card_1015_eq, calc11_card_1016_eq, calc11_card_1017_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1018_eq, calc11_set_1020_eq, calc11_set_1022_eq, calc11_set_1024_eq, calc11_set_1026_eq, calc11_set_1028_eq, calc11_set_1030_eq, calc11_set_1031_eq, calc11_set_1032_eq, calc11_set_1033_eq, calc11_set_1034_eq, calc11_set_1035_eq, calc11_finishA_1036]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1019_eq, calc11_set_1021_eq, calc11_set_1023_eq, calc11_set_1025_eq, calc11_set_1027_eq, calc11_set_1029_eq, calc11_finishT_1036]
  · decide +kernel

theorem valid_inline_841 : Valid inline_841 := by
  rw [eq_inline_841]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 7) valid_116
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 8) valid_297
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 3) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 7 (10, 8) valid_649
  subst c
  exact valid_inline_840

theorem calc11_card_1037_eq : placed 2 (2, 9) card_174 = calc11_card_1037 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1038_eq : placed 1 (2, 3) card_508 = calc11_card_1038 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1039_eq : placed 3 (8, 3) card_508 = calc11_card_1039 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1040_eq : placed 2 (2, 9) card_566 = calc11_card_1040 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1041_eq : placed 1 (2, 3) card_605 = calc11_card_1041 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1042_eq : placed 3 (8, 3) card_605 = calc11_card_1042 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1043_eq : placed 2 (1, 10) card_647 = calc11_card_1043 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1044_eq : placed 1 (0, 2) card_650 = calc11_card_1044 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1045_eq : placed 3 (10, 2) card_650 = calc11_card_1045 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1046_eq : placed 4 (9, 1) card_661 = calc11_card_1046 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1047_eq : placed 0 (2, 1) card_710 = calc11_card_1047 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1048_eq : placed 0 (1, 0) card_711 = calc11_card_1048 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1049_eq : calc11_card_1048.required ∪ ∅ = calc11_set_1049 := by decide +kernel

theorem calc11_set_1050_eq : calc11_card_1048.envelope ∪ ∅ = calc11_set_1050 := by decide +kernel

theorem calc11_set_1051_eq : calc11_card_1047.required ∪ calc11_set_1049 = calc11_set_1051 := by decide +kernel

theorem calc11_set_1052_eq : calc11_card_1047.envelope ∪ calc11_set_1050 = calc11_set_1052 := by decide +kernel

theorem calc11_set_1053_eq : calc11_card_1046.required ∪ calc11_set_1051 = calc11_set_1053 := by decide +kernel

theorem calc11_set_1054_eq : calc11_card_1046.envelope ∪ calc11_set_1052 = calc11_set_1054 := by decide +kernel

theorem calc11_set_1055_eq : inline_841.required ∪ calc11_set_1053 = calc11_set_1055 := by decide +kernel

theorem calc11_set_1056_eq : inline_841.envelope ∪ calc11_set_1054 = calc11_set_1056 := by decide +kernel

theorem calc11_set_1057_eq : calc11_card_1045.required ∪ calc11_set_1055 = calc11_set_1057 := by decide +kernel

theorem calc11_set_1058_eq : calc11_card_1045.envelope ∪ calc11_set_1056 = calc11_set_1058 := by decide +kernel

theorem calc11_set_1059_eq : calc11_card_1044.required ∪ calc11_set_1057 = calc11_set_1059 := by decide +kernel

theorem calc11_set_1060_eq : calc11_card_1044.envelope ∪ calc11_set_1058 = calc11_set_1060 := by decide +kernel

theorem calc11_set_1061_eq : calc11_card_1043.required ∪ calc11_set_1059 = calc11_set_1061 := by decide +kernel

theorem calc11_set_1062_eq : calc11_card_1043.envelope ∪ calc11_set_1060 = calc11_set_1062 := by decide +kernel

theorem calc11_set_1063_eq : calc11_card_1042.required ∪ calc11_set_1061 = calc11_set_1063 := by decide +kernel

theorem calc11_set_1064_eq : calc11_card_1042.envelope ∪ calc11_set_1062 = calc11_set_1064 := by decide +kernel

theorem calc11_set_1065_eq : calc11_card_1041.required ∪ calc11_set_1063 = calc11_set_1065 := by decide +kernel

theorem calc11_set_1066_eq : calc11_card_1041.envelope ∪ calc11_set_1064 = calc11_set_1066 := by decide +kernel

theorem calc11_set_1067_eq : calc11_card_1040.required ∪ calc11_set_1065 = calc11_set_1067 := by decide +kernel

theorem calc11_set_1068_eq : calc11_card_1040.envelope ∪ calc11_set_1066 = calc11_set_1068 := by decide +kernel

theorem calc11_set_1069_eq : calc11_card_1039.required ∪ calc11_set_1067 = calc11_set_1069 := by decide +kernel

theorem calc11_set_1070_eq : calc11_card_1039.envelope ∪ calc11_set_1068 = calc11_set_1070 := by decide +kernel

theorem calc11_set_1071_eq : calc11_card_1038.required ∪ calc11_set_1069 = calc11_set_1071 := by decide +kernel

theorem calc11_set_1072_eq : calc11_card_1038.envelope ∪ calc11_set_1070 = calc11_set_1072 := by decide +kernel

theorem calc11_set_1073_eq : calc11_card_1037.required ∪ calc11_set_1071 = calc11_set_1073 := by decide +kernel

theorem calc11_set_1074_eq : calc11_card_1037.envelope ∪ calc11_set_1072 = calc11_set_1074 := by decide +kernel

theorem calc11_set_1075_eq : calc11_card_1048.envelope ∩ calc11_card_1037.envelope = calc11_set_1075 := by decide +kernel

theorem calc11_set_1076_eq : calc11_card_1047.envelope ∩ calc11_set_1075 = calc11_set_1076 := by decide +kernel

theorem calc11_set_1077_eq : calc11_card_1046.envelope ∩ calc11_set_1076 = calc11_set_1077 := by decide +kernel

theorem calc11_set_1078_eq : inline_841.envelope ∩ calc11_set_1077 = calc11_set_1078 := by decide +kernel

theorem calc11_set_1079_eq : calc11_card_1045.envelope ∩ calc11_set_1078 = calc11_set_1079 := by decide +kernel

theorem calc11_set_1080_eq : calc11_card_1044.envelope ∩ calc11_set_1079 = calc11_set_1080 := by decide +kernel

theorem calc11_set_1081_eq : calc11_card_1043.envelope ∩ calc11_set_1080 = calc11_set_1081 := by decide +kernel

theorem calc11_set_1082_eq : calc11_card_1042.envelope ∩ calc11_set_1081 = calc11_set_1082 := by decide +kernel

theorem calc11_set_1083_eq : calc11_card_1041.envelope ∩ calc11_set_1082 = calc11_set_1083 := by decide +kernel

theorem calc11_set_1084_eq : calc11_card_1040.envelope ∩ calc11_set_1083 = calc11_set_1084 := by decide +kernel

theorem calc11_set_1085_eq : calc11_card_1039.envelope ∩ calc11_set_1084 = calc11_set_1085 := by decide +kernel

theorem calc11_set_1086_eq : calc11_card_1038.envelope ∩ calc11_set_1085 = calc11_set_1086 := by decide +kernel

theorem calc11_set_1087_eq : calc11_set_1073 ∪ calc11_set_1086 = calc11_set_1087 := by decide +kernel

theorem calc11_finishA_1088 : calc11_set_1087.erase (5, 6) = card_712.required := by decide +kernel

theorem calc11_finishT_1088 : insert (5, 6) calc11_set_1074 = card_712.envelope := by decide +kernel

theorem eq_card_712 : card_712 = combine (5, 6) [placed 2 (2, 9) card_174, placed 1 (2, 3) card_508, placed 3 (8, 3) card_508, placed 2 (2, 9) card_566, placed 1 (2, 3) card_605, placed 3 (8, 3) card_605, placed 2 (1, 10) card_647, placed 1 (0, 2) card_650, placed 3 (10, 2) card_650, inline_841, placed 4 (9, 1) card_661, placed 0 (2, 1) card_710, placed 0 (1, 0) card_711] := by
  rw [calc11_card_1037_eq, calc11_card_1038_eq, calc11_card_1039_eq, calc11_card_1040_eq, calc11_card_1041_eq, calc11_card_1042_eq, calc11_card_1043_eq, calc11_card_1044_eq, calc11_card_1045_eq, calc11_card_1046_eq, calc11_card_1047_eq, calc11_card_1048_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1049_eq, calc11_set_1051_eq, calc11_set_1053_eq, calc11_set_1055_eq, calc11_set_1057_eq, calc11_set_1059_eq, calc11_set_1061_eq, calc11_set_1063_eq, calc11_set_1065_eq, calc11_set_1067_eq, calc11_set_1069_eq, calc11_set_1071_eq, calc11_set_1073_eq, calc11_set_1075_eq, calc11_set_1076_eq, calc11_set_1077_eq, calc11_set_1078_eq, calc11_set_1079_eq, calc11_set_1080_eq, calc11_set_1081_eq, calc11_set_1082_eq, calc11_set_1083_eq, calc11_set_1084_eq, calc11_set_1085_eq, calc11_set_1086_eq, calc11_set_1087_eq, calc11_finishA_1088]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1050_eq, calc11_set_1052_eq, calc11_set_1054_eq, calc11_set_1056_eq, calc11_set_1058_eq, calc11_set_1060_eq, calc11_set_1062_eq, calc11_set_1064_eq, calc11_set_1066_eq, calc11_set_1068_eq, calc11_set_1070_eq, calc11_set_1072_eq, calc11_set_1074_eq, calc11_finishT_1088]
  · decide +kernel

theorem valid_712 : Valid card_712 := by
  rw [eq_card_712]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 9) valid_174
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_508
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 3) valid_508
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 9) valid_566
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_605
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 3) valid_605
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 10) valid_647
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_650
  rcases hc with rfl | hc
  · exact placed_valid 3 (10, 2) valid_650
  rcases hc with rfl | hc
  · exact valid_inline_841
  rcases hc with rfl | hc
  · exact placed_valid 4 (9, 1) valid_661
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_710
  subst c
  exact placed_valid 0 (1, 0) valid_711


end OAI.Snaky21.Certificate

theorem solution : Valid card_712 ∧ True :=
  ⟨valid_712, True.intro⟩
