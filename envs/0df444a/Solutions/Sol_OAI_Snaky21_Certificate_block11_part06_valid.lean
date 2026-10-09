-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block11_part06_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:05:36.230002+00:00
-- url     : https://prove2.me/submissions/9f123e85-ed1e-4382-a758-b8dd39aa698f

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block03_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_valid
import Definitions.Def_Snaky21Calc11Part03
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block10_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part05_valid
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
theorem valid_6 : Valid card_6 := block00_valid.2.2.2.2.2.2.1
theorem valid_7 : Valid card_7 := block00_valid.2.2.2.2.2.2.2.1
theorem valid_13 : Valid card_13 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_14 : Valid card_14 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_115 : Valid card_115 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_117 : Valid card_117 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_196 : Valid card_196 := block03_valid.2.2.2.2.1
theorem valid_577 : Valid card_577 := block09_valid.2.1

theorem calc11_card_898_eq : placed 0 (3, 2) card_6 = calc11_card_898 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_899_eq : placed 5 (2, 6) card_196 = calc11_card_899 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_900_eq : calc11_card_899.required ∪ ∅ = calc11_set_900 := by decide +kernel

theorem calc11_set_901_eq : calc11_card_899.envelope ∪ ∅ = calc11_set_901 := by decide +kernel

theorem calc11_set_902_eq : calc11_card_898.required ∪ calc11_set_900 = calc11_set_902 := by decide +kernel

theorem calc11_set_903_eq : calc11_card_898.envelope ∪ calc11_set_901 = calc11_set_903 := by decide +kernel

theorem calc11_set_904_eq : calc11_card_899.envelope ∩ calc11_card_898.envelope = calc11_set_904 := by decide +kernel

theorem calc11_set_905_eq : calc11_set_902 ∪ calc11_set_904 = calc11_set_905 := by decide +kernel

theorem calc11_finishA_906 : calc11_set_905.erase (3, 2) = inline_837.required := by decide +kernel

theorem calc11_finishT_906 : insert (3, 2) calc11_set_903 = inline_837.envelope := by decide +kernel

theorem eq_inline_837 : inline_837 = combine (3, 2) [placed 0 (3, 2) card_6, placed 5 (2, 6) card_196] := by
  rw [calc11_card_898_eq, calc11_card_899_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_900_eq, calc11_set_902_eq, calc11_set_904_eq, calc11_set_905_eq, calc11_finishA_906]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_901_eq, calc11_set_903_eq, calc11_finishT_906]
  · decide +kernel

theorem valid_inline_837 : Valid inline_837 := by
  rw [eq_inline_837]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_6
  subst c
  exact placed_valid 5 (2, 6) valid_196

theorem calc11_card_907_eq : placed 2 (3, 7) card_7 = calc11_card_907 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_908_eq : placed 5 (0, 6) card_115 = calc11_card_908 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_909_eq : placed 1 (1, 2) card_577 = calc11_card_909 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_910_eq : calc11_card_909.required ∪ ∅ = calc11_set_910 := by decide +kernel

theorem calc11_set_911_eq : calc11_card_909.envelope ∪ ∅ = calc11_set_911 := by decide +kernel

theorem calc11_set_912_eq : inline_837.required ∪ calc11_set_910 = calc11_set_912 := by decide +kernel

theorem calc11_set_913_eq : inline_837.envelope ∪ calc11_set_911 = calc11_set_913 := by decide +kernel

theorem calc11_set_914_eq : calc11_card_908.required ∪ calc11_set_912 = calc11_set_914 := by decide +kernel

theorem calc11_set_915_eq : calc11_card_908.envelope ∪ calc11_set_913 = calc11_set_915 := by decide +kernel

theorem calc11_set_916_eq : calc11_card_907.required ∪ calc11_set_914 = calc11_set_916 := by decide +kernel

theorem calc11_set_917_eq : calc11_card_907.envelope ∪ calc11_set_915 = calc11_set_917 := by decide +kernel

theorem calc11_set_918_eq : calc11_card_909.envelope ∩ calc11_card_907.envelope = calc11_set_918 := by decide +kernel

theorem calc11_set_919_eq : inline_837.envelope ∩ calc11_set_918 = calc11_set_919 := by decide +kernel

theorem calc11_set_920_eq : calc11_card_908.envelope ∩ calc11_set_919 = calc11_set_920 := by decide +kernel

theorem calc11_set_921_eq : calc11_set_916 ∪ calc11_set_920 = calc11_set_921 := by decide +kernel

theorem calc11_finishA_922 : calc11_set_921.erase (3, 3) = inline_838.required := by decide +kernel

theorem calc11_finishT_922 : insert (3, 3) calc11_set_917 = inline_838.envelope := by decide +kernel

theorem eq_inline_838 : inline_838 = combine (3, 3) [placed 2 (3, 7) card_7, placed 5 (0, 6) card_115, inline_837, placed 1 (1, 2) card_577] := by
  rw [calc11_card_907_eq, calc11_card_908_eq, calc11_card_909_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_910_eq, calc11_set_912_eq, calc11_set_914_eq, calc11_set_916_eq, calc11_set_918_eq, calc11_set_919_eq, calc11_set_920_eq, calc11_set_921_eq, calc11_finishA_922]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_911_eq, calc11_set_913_eq, calc11_set_915_eq, calc11_set_917_eq, calc11_finishT_922]
  · decide +kernel

theorem valid_inline_838 : Valid inline_838 := by
  rw [eq_inline_838]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_115
  rcases hc with rfl | hc
  · exact valid_inline_837
  subst c
  exact placed_valid 1 (1, 2) valid_577

theorem calc11_card_923_eq : placed 0 (2, 2) card_13 = calc11_card_923 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_924_eq : placed 4 (4, 2) card_14 = calc11_card_924 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_925_eq : placed 1 (0, 3) card_117 = calc11_card_925 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_926_eq : inline_838.required ∪ ∅ = calc11_set_926 := by decide +kernel

theorem calc11_set_927_eq : inline_838.envelope ∪ ∅ = calc11_set_927 := by decide +kernel

theorem calc11_set_928_eq : calc11_card_925.required ∪ calc11_set_926 = calc11_set_928 := by decide +kernel

theorem calc11_set_929_eq : calc11_card_925.envelope ∪ calc11_set_927 = calc11_set_929 := by decide +kernel

theorem calc11_set_930_eq : calc11_card_924.required ∪ calc11_set_928 = calc11_set_930 := by decide +kernel

theorem calc11_set_931_eq : calc11_card_924.envelope ∪ calc11_set_929 = calc11_set_931 := by decide +kernel

theorem calc11_set_932_eq : calc11_card_923.required ∪ calc11_set_930 = calc11_set_932 := by decide +kernel

theorem calc11_set_933_eq : calc11_card_923.envelope ∪ calc11_set_931 = calc11_set_933 := by decide +kernel

theorem calc11_set_934_eq : inline_838.envelope ∩ calc11_card_923.envelope = calc11_set_934 := by decide +kernel

theorem calc11_set_935_eq : calc11_card_925.envelope ∩ calc11_set_934 = calc11_set_935 := by decide +kernel

theorem calc11_set_936_eq : calc11_card_924.envelope ∩ calc11_set_935 = calc11_set_936 := by decide +kernel

theorem calc11_set_937_eq : calc11_set_932 ∪ calc11_set_936 = calc11_set_937 := by decide +kernel

theorem calc11_finishA_938 : calc11_set_937.erase (3, 6) = card_710.required := by decide +kernel

theorem calc11_finishT_938 : insert (3, 6) calc11_set_933 = card_710.envelope := by decide +kernel

theorem eq_card_710 : card_710 = combine (3, 6) [placed 0 (2, 2) card_13, placed 4 (4, 2) card_14, placed 1 (0, 3) card_117, inline_838] := by
  rw [calc11_card_923_eq, calc11_card_924_eq, calc11_card_925_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_926_eq, calc11_set_928_eq, calc11_set_930_eq, calc11_set_932_eq, calc11_set_934_eq, calc11_set_935_eq, calc11_set_936_eq, calc11_set_937_eq, calc11_finishA_938]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_927_eq, calc11_set_929_eq, calc11_set_931_eq, calc11_set_933_eq, calc11_finishT_938]
  · decide +kernel

theorem valid_710 : Valid card_710 := by
  rw [eq_card_710]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_117
  subst c
  exact valid_inline_838


end OAI.Snaky21.Certificate

theorem solution : Valid card_710 ∧ True :=
  ⟨valid_710, True.intro⟩
