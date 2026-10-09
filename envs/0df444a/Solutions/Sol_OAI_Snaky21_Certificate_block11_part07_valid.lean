-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block11_part07_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:11:08.92212+00:00
-- url     : https://prove2.me/submissions/efdab77b-0f6d-46c5-acdd-60b11d010952

import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block08_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_valid
import Definitions.Def_Snaky21Calc11Part03
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block10_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part06_valid
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
theorem valid_104 : Valid card_104 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_120 : Valid card_120 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_338 : Valid card_338 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_359 : Valid card_359 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_437 : Valid card_437 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_452 : Valid card_452 := block07_valid.2.2.2.2.1
theorem valid_476 : Valid card_476 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_479 : Valid card_479 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_520 : Valid card_520 := block08_valid.2.2.2.2.2.2.2.2.1
theorem valid_611 : Valid card_611 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_613 : Valid card_613 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_634 : Valid card_634 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_642 : Valid card_642 := block10_valid.2.2.1
theorem valid_643 : Valid card_643 := block10_valid.2.2.2.1

theorem calc11_card_939_eq : placed 5 (1, 6) card_104 = calc11_card_939 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_940_eq : placed 5 (1, 6) card_359 = calc11_card_940 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_941_eq : placed 2 (1, 9) card_452 = calc11_card_941 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_942_eq : placed 0 (3, 2) card_476 = calc11_card_942 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_943_eq : placed 2 (3, 9) card_479 = calc11_card_943 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_944_eq : placed 4 (9, 0) card_520 = calc11_card_944 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_945_eq : calc11_card_944.required ∪ ∅ = calc11_set_945 := by decide +kernel

theorem calc11_set_946_eq : calc11_card_944.envelope ∪ ∅ = calc11_set_946 := by decide +kernel

theorem calc11_set_947_eq : calc11_card_943.required ∪ calc11_set_945 = calc11_set_947 := by decide +kernel

theorem calc11_set_948_eq : calc11_card_943.envelope ∪ calc11_set_946 = calc11_set_948 := by decide +kernel

theorem calc11_set_949_eq : calc11_card_942.required ∪ calc11_set_947 = calc11_set_949 := by decide +kernel

theorem calc11_set_950_eq : calc11_card_942.envelope ∪ calc11_set_948 = calc11_set_950 := by decide +kernel

theorem calc11_set_951_eq : calc11_card_941.required ∪ calc11_set_949 = calc11_set_951 := by decide +kernel

theorem calc11_set_952_eq : calc11_card_941.envelope ∪ calc11_set_950 = calc11_set_952 := by decide +kernel

theorem calc11_set_953_eq : calc11_card_940.required ∪ calc11_set_951 = calc11_set_953 := by decide +kernel

theorem calc11_set_954_eq : calc11_card_940.envelope ∪ calc11_set_952 = calc11_set_954 := by decide +kernel

theorem calc11_set_955_eq : calc11_card_939.required ∪ calc11_set_953 = calc11_set_955 := by decide +kernel

theorem calc11_set_956_eq : calc11_card_939.envelope ∪ calc11_set_954 = calc11_set_956 := by decide +kernel

theorem calc11_set_957_eq : calc11_card_944.envelope ∩ calc11_card_939.envelope = calc11_set_957 := by decide +kernel

theorem calc11_set_958_eq : calc11_card_943.envelope ∩ calc11_set_957 = calc11_set_958 := by decide +kernel

theorem calc11_set_959_eq : calc11_card_942.envelope ∩ calc11_set_958 = calc11_set_959 := by decide +kernel

theorem calc11_set_960_eq : calc11_card_941.envelope ∩ calc11_set_959 = calc11_set_960 := by decide +kernel

theorem calc11_set_961_eq : calc11_card_940.envelope ∩ calc11_set_960 = calc11_set_961 := by decide +kernel

theorem calc11_set_962_eq : calc11_set_955 ∪ calc11_set_961 = calc11_set_962 := by decide +kernel

theorem calc11_finishA_963 : calc11_set_962.erase (6, 5) = inline_839.required := by decide +kernel

theorem calc11_finishT_963 : insert (6, 5) calc11_set_956 = inline_839.envelope := by decide +kernel

theorem eq_inline_839 : inline_839 = combine (6, 5) [placed 5 (1, 6) card_104, placed 5 (1, 6) card_359, placed 2 (1, 9) card_452, placed 0 (3, 2) card_476, placed 2 (3, 9) card_479, placed 4 (9, 0) card_520] := by
  rw [calc11_card_939_eq, calc11_card_940_eq, calc11_card_941_eq, calc11_card_942_eq, calc11_card_943_eq, calc11_card_944_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_945_eq, calc11_set_947_eq, calc11_set_949_eq, calc11_set_951_eq, calc11_set_953_eq, calc11_set_955_eq, calc11_set_957_eq, calc11_set_958_eq, calc11_set_959_eq, calc11_set_960_eq, calc11_set_961_eq, calc11_set_962_eq, calc11_finishA_963]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_946_eq, calc11_set_948_eq, calc11_set_950_eq, calc11_set_952_eq, calc11_set_954_eq, calc11_set_956_eq, calc11_finishT_963]
  · decide +kernel

theorem valid_inline_839 : Valid inline_839 := by
  rw [eq_inline_839]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_104
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_359
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 9) valid_452
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_476
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 9) valid_479
  subst c
  exact placed_valid 4 (9, 0) valid_520

theorem calc11_card_964_eq : placed 4 (7, 3) card_120 = calc11_card_964 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_965_eq : placed 1 (1, 4) card_338 = calc11_card_965 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_966_eq : placed 1 (1, 3) card_437 = calc11_card_966 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_967_eq : placed 1 (0, 4) card_611 = calc11_card_967 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_968_eq : placed 5 (1, 7) card_613 = calc11_card_968 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_969_eq : placed 2 (1, 10) card_634 = calc11_card_969 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_970_eq : placed 2 (3, 10) card_642 = calc11_card_970 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_971_eq : placed 2 (3, 10) card_643 = calc11_card_971 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_972_eq : inline_839.required ∪ ∅ = calc11_set_972 := by decide +kernel

theorem calc11_set_973_eq : inline_839.envelope ∪ ∅ = calc11_set_973 := by decide +kernel

theorem calc11_set_974_eq : calc11_card_971.required ∪ calc11_set_972 = calc11_set_974 := by decide +kernel

theorem calc11_set_975_eq : calc11_card_971.envelope ∪ calc11_set_973 = calc11_set_975 := by decide +kernel

theorem calc11_set_976_eq : calc11_card_970.required ∪ calc11_set_974 = calc11_set_976 := by decide +kernel

theorem calc11_set_977_eq : calc11_card_970.envelope ∪ calc11_set_975 = calc11_set_977 := by decide +kernel

theorem calc11_set_978_eq : calc11_card_969.required ∪ calc11_set_976 = calc11_set_978 := by decide +kernel

theorem calc11_set_979_eq : calc11_card_969.envelope ∪ calc11_set_977 = calc11_set_979 := by decide +kernel

theorem calc11_set_980_eq : calc11_card_968.required ∪ calc11_set_978 = calc11_set_980 := by decide +kernel

theorem calc11_set_981_eq : calc11_card_968.envelope ∪ calc11_set_979 = calc11_set_981 := by decide +kernel

theorem calc11_set_982_eq : calc11_card_967.required ∪ calc11_set_980 = calc11_set_982 := by decide +kernel

theorem calc11_set_983_eq : calc11_card_967.envelope ∪ calc11_set_981 = calc11_set_983 := by decide +kernel

theorem calc11_set_984_eq : calc11_card_966.required ∪ calc11_set_982 = calc11_set_984 := by decide +kernel

theorem calc11_set_985_eq : calc11_card_966.envelope ∪ calc11_set_983 = calc11_set_985 := by decide +kernel

theorem calc11_set_986_eq : calc11_card_965.required ∪ calc11_set_984 = calc11_set_986 := by decide +kernel

theorem calc11_set_987_eq : calc11_card_965.envelope ∪ calc11_set_985 = calc11_set_987 := by decide +kernel

theorem calc11_set_988_eq : calc11_card_964.required ∪ calc11_set_986 = calc11_set_988 := by decide +kernel

theorem calc11_set_989_eq : calc11_card_964.envelope ∪ calc11_set_987 = calc11_set_989 := by decide +kernel

theorem calc11_set_990_eq : inline_839.envelope ∩ calc11_card_964.envelope = calc11_set_990 := by decide +kernel

theorem calc11_set_991_eq : calc11_card_971.envelope ∩ calc11_set_990 = calc11_set_991 := by decide +kernel

theorem calc11_set_992_eq : calc11_card_970.envelope ∩ calc11_set_991 = calc11_set_992 := by decide +kernel

theorem calc11_set_993_eq : calc11_card_969.envelope ∩ calc11_set_992 = calc11_set_993 := by decide +kernel

theorem calc11_set_994_eq : calc11_card_968.envelope ∩ calc11_set_993 = calc11_set_994 := by decide +kernel

theorem calc11_set_995_eq : calc11_card_967.envelope ∩ calc11_set_994 = calc11_set_995 := by decide +kernel

theorem calc11_set_996_eq : calc11_card_966.envelope ∩ calc11_set_995 = calc11_set_996 := by decide +kernel

theorem calc11_set_997_eq : calc11_card_965.envelope ∩ calc11_set_996 = calc11_set_997 := by decide +kernel

theorem calc11_set_998_eq : calc11_set_988 ∪ calc11_set_997 = calc11_set_998 := by decide +kernel

theorem calc11_finishA_999 : calc11_set_998.erase (6, 6) = card_711.required := by decide +kernel

theorem calc11_finishT_999 : insert (6, 6) calc11_set_989 = card_711.envelope := by decide +kernel

theorem eq_card_711 : card_711 = combine (6, 6) [placed 4 (7, 3) card_120, placed 1 (1, 4) card_338, placed 1 (1, 3) card_437, placed 1 (0, 4) card_611, placed 5 (1, 7) card_613, placed 2 (1, 10) card_634, placed 2 (3, 10) card_642, placed 2 (3, 10) card_643, inline_839] := by
  rw [calc11_card_964_eq, calc11_card_965_eq, calc11_card_966_eq, calc11_card_967_eq, calc11_card_968_eq, calc11_card_969_eq, calc11_card_970_eq, calc11_card_971_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_972_eq, calc11_set_974_eq, calc11_set_976_eq, calc11_set_978_eq, calc11_set_980_eq, calc11_set_982_eq, calc11_set_984_eq, calc11_set_986_eq, calc11_set_988_eq, calc11_set_990_eq, calc11_set_991_eq, calc11_set_992_eq, calc11_set_993_eq, calc11_set_994_eq, calc11_set_995_eq, calc11_set_996_eq, calc11_set_997_eq, calc11_set_998_eq, calc11_finishA_999]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_973_eq, calc11_set_975_eq, calc11_set_977_eq, calc11_set_979_eq, calc11_set_981_eq, calc11_set_983_eq, calc11_set_985_eq, calc11_set_987_eq, calc11_set_989_eq, calc11_finishT_999]
  · decide +kernel

theorem valid_711 : Valid card_711 := by
  rw [eq_card_711]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_120
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 4) valid_338
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_437
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 4) valid_611
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 7) valid_613
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 10) valid_634
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 10) valid_642
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 10) valid_643
  subst c
  exact valid_inline_839


end OAI.Snaky21.Certificate

theorem solution : Valid card_711 ∧ True :=
  ⟨valid_711, True.intro⟩
