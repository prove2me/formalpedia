-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block11_part04_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T07:59:02.863992+00:00
-- url     : https://prove2.me/submissions/7f033cf6-4bc2-4289-b3d7-4e0d8d080a62

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block03_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block08_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_valid
import Definitions.Def_Snaky21Calc11Part02
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block10_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part03_valid
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
theorem valid_7 : Valid card_7 := block00_valid.2.2.2.2.2.2.2.1
theorem valid_9 : Valid card_9 := block00_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_12 : Valid card_12 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_44 : Valid card_44 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_52 : Valid card_52 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_57 : Valid card_57 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_88 : Valid card_88 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_92 : Valid card_92 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_111 : Valid card_111 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_117 : Valid card_117 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_135 : Valid card_135 := block02_valid.2.2.2.2.2.2.2.1
theorem valid_137 : Valid card_137 := block02_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_181 : Valid card_181 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_186 : Valid card_186 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_213 : Valid card_213 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_234 : Valid card_234 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_241 : Valid card_241 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_257 : Valid card_257 := block04_valid.2.1
theorem valid_292 : Valid card_292 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_435 : Valid card_435 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_459 : Valid card_459 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_475 : Valid card_475 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_490 : Valid card_490 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_565 : Valid card_565 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_587 : Valid card_587 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_603 : Valid card_603 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_605 : Valid card_605 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_650 : Valid card_650 := block10_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_684 : Valid card_684 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_687 : Valid card_687 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_689 : Valid card_689 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_694 : Valid card_694 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_695 : Valid card_695 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_696 : Valid card_696 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_698 : Valid card_698 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_701 : Valid card_701 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_707 : Valid card_707 := block11_part03_valid.1

theorem calc11_card_592_eq : placed 3 (9, 8) card_7 = calc11_card_592 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_593_eq : placed 1 (4, 7) card_234 = calc11_card_593 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_594_eq : placed 3 (9, 7) card_241 = calc11_card_594 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_595_eq : calc11_card_594.required ∪ ∅ = calc11_set_595 := by decide +kernel

theorem calc11_set_596_eq : calc11_card_594.envelope ∪ ∅ = calc11_set_596 := by decide +kernel

theorem calc11_set_597_eq : calc11_card_593.required ∪ calc11_set_595 = calc11_set_597 := by decide +kernel

theorem calc11_set_598_eq : calc11_card_593.envelope ∪ calc11_set_596 = calc11_set_598 := by decide +kernel

theorem calc11_set_599_eq : calc11_card_592.required ∪ calc11_set_597 = calc11_set_599 := by decide +kernel

theorem calc11_set_600_eq : calc11_card_592.envelope ∪ calc11_set_598 = calc11_set_600 := by decide +kernel

theorem calc11_set_601_eq : calc11_card_594.envelope ∩ calc11_card_592.envelope = calc11_set_601 := by decide +kernel

theorem calc11_set_602_eq : calc11_card_593.envelope ∩ calc11_set_601 = calc11_set_602 := by decide +kernel

theorem calc11_set_603_eq : calc11_set_599 ∪ calc11_set_602 = calc11_set_603 := by decide +kernel

theorem calc11_finishA_604 : calc11_set_603.erase (5, 8) = inline_824.required := by decide +kernel

theorem calc11_finishT_604 : insert (5, 8) calc11_set_600 = inline_824.envelope := by decide +kernel

theorem eq_inline_824 : inline_824 = combine (5, 8) [placed 3 (9, 8) card_7, placed 1 (4, 7) card_234, placed 3 (9, 7) card_241] := by
  rw [calc11_card_592_eq, calc11_card_593_eq, calc11_card_594_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_595_eq, calc11_set_597_eq, calc11_set_599_eq, calc11_set_601_eq, calc11_set_602_eq, calc11_set_603_eq, calc11_finishA_604]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_596_eq, calc11_set_598_eq, calc11_set_600_eq, calc11_finishT_604]
  · decide +kernel

theorem valid_inline_824 : Valid inline_824 := by
  rw [eq_inline_824]
  apply combination_rule (5, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (9, 8) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 7) valid_234
  subst c
  exact placed_valid 3 (9, 7) valid_241

theorem calc11_card_605_eq : placed 4 (7, 5) card_7 = calc11_card_605 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_606_eq : placed 0 (6, 5) card_9 = calc11_card_606 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_607_eq : placed 3 (9, 6) card_92 = calc11_card_607 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_608_eq : calc11_card_607.required ∪ ∅ = calc11_set_608 := by decide +kernel

theorem calc11_set_609_eq : calc11_card_607.envelope ∪ ∅ = calc11_set_609 := by decide +kernel

theorem calc11_set_610_eq : calc11_card_606.required ∪ calc11_set_608 = calc11_set_610 := by decide +kernel

theorem calc11_set_611_eq : calc11_card_606.envelope ∪ calc11_set_609 = calc11_set_611 := by decide +kernel

theorem calc11_set_612_eq : calc11_card_605.required ∪ calc11_set_610 = calc11_set_612 := by decide +kernel

theorem calc11_set_613_eq : calc11_card_605.envelope ∪ calc11_set_611 = calc11_set_613 := by decide +kernel

theorem calc11_set_614_eq : calc11_card_607.envelope ∩ calc11_card_605.envelope = calc11_set_614 := by decide +kernel

theorem calc11_set_615_eq : calc11_card_606.envelope ∩ calc11_set_614 = calc11_set_615 := by decide +kernel

theorem calc11_set_616_eq : calc11_set_612 ∪ calc11_set_615 = calc11_set_616 := by decide +kernel

theorem calc11_finishA_617 : calc11_set_616.erase (7, 9) = inline_825.required := by decide +kernel

theorem calc11_finishT_617 : insert (7, 9) calc11_set_613 = inline_825.envelope := by decide +kernel

theorem eq_inline_825 : inline_825 = combine (7, 9) [placed 4 (7, 5) card_7, placed 0 (6, 5) card_9, placed 3 (9, 6) card_92] := by
  rw [calc11_card_605_eq, calc11_card_606_eq, calc11_card_607_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_608_eq, calc11_set_610_eq, calc11_set_612_eq, calc11_set_614_eq, calc11_set_615_eq, calc11_set_616_eq, calc11_finishA_617]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_609_eq, calc11_set_611_eq, calc11_set_613_eq, calc11_finishT_617]
  · decide +kernel

theorem valid_inline_825 : Valid inline_825 := by
  rw [eq_inline_825]
  apply combination_rule (7, 9) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 5) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 0 (6, 5) valid_9
  subst c
  exact placed_valid 3 (9, 6) valid_92

theorem calc11_card_618_eq : placed 4 (7, 5) card_44 = calc11_card_618 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_619_eq : placed 0 (7, 5) card_52 = calc11_card_619 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_620_eq : inline_825.required ∪ ∅ = calc11_set_620 := by decide +kernel

theorem calc11_set_621_eq : inline_825.envelope ∪ ∅ = calc11_set_621 := by decide +kernel

theorem calc11_set_622_eq : calc11_card_619.required ∪ calc11_set_620 = calc11_set_622 := by decide +kernel

theorem calc11_set_623_eq : calc11_card_619.envelope ∪ calc11_set_621 = calc11_set_623 := by decide +kernel

theorem calc11_set_624_eq : calc11_card_618.required ∪ calc11_set_622 = calc11_set_624 := by decide +kernel

theorem calc11_set_625_eq : calc11_card_618.envelope ∪ calc11_set_623 = calc11_set_625 := by decide +kernel

theorem calc11_set_626_eq : inline_825.envelope ∩ calc11_card_618.envelope = calc11_set_626 := by decide +kernel

theorem calc11_set_627_eq : calc11_card_619.envelope ∩ calc11_set_626 = calc11_set_627 := by decide +kernel

theorem calc11_set_628_eq : calc11_set_624 ∪ calc11_set_627 = calc11_set_628 := by decide +kernel

theorem calc11_finishA_629 : calc11_set_628.erase (7, 6) = inline_826.required := by decide +kernel

theorem calc11_finishT_629 : insert (7, 6) calc11_set_625 = inline_826.envelope := by decide +kernel

theorem eq_inline_826 : inline_826 = combine (7, 6) [placed 4 (7, 5) card_44, placed 0 (7, 5) card_52, inline_825] := by
  rw [calc11_card_618_eq, calc11_card_619_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_620_eq, calc11_set_622_eq, calc11_set_624_eq, calc11_set_626_eq, calc11_set_627_eq, calc11_set_628_eq, calc11_finishA_629]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_621_eq, calc11_set_623_eq, calc11_set_625_eq, calc11_finishT_629]
  · decide +kernel

theorem valid_inline_826 : Valid inline_826 := by
  rw [eq_inline_826]
  apply combination_rule (7, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 5) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 0 (7, 5) valid_52
  subst c
  exact valid_inline_825

theorem calc11_card_630_eq : placed 4 (9, 5) card_57 = calc11_card_630 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_631_eq : placed 4 (9, 5) card_88 = calc11_card_631 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_632_eq : placed 4 (9, 5) card_111 = calc11_card_632 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_633_eq : placed 0 (5, 5) card_213 = calc11_card_633 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_634_eq : inline_826.required ∪ ∅ = calc11_set_634 := by decide +kernel

theorem calc11_set_635_eq : inline_826.envelope ∪ ∅ = calc11_set_635 := by decide +kernel

theorem calc11_set_636_eq : inline_824.required ∪ calc11_set_634 = calc11_set_636 := by decide +kernel

theorem calc11_set_637_eq : inline_824.envelope ∪ calc11_set_635 = calc11_set_637 := by decide +kernel

theorem calc11_set_638_eq : calc11_card_633.required ∪ calc11_set_636 = calc11_set_638 := by decide +kernel

theorem calc11_set_639_eq : calc11_card_633.envelope ∪ calc11_set_637 = calc11_set_639 := by decide +kernel

theorem calc11_set_640_eq : calc11_card_632.required ∪ calc11_set_638 = calc11_set_640 := by decide +kernel

theorem calc11_set_641_eq : calc11_card_632.envelope ∪ calc11_set_639 = calc11_set_641 := by decide +kernel

theorem calc11_set_642_eq : calc11_card_631.required ∪ calc11_set_640 = calc11_set_642 := by decide +kernel

theorem calc11_set_643_eq : calc11_card_631.envelope ∪ calc11_set_641 = calc11_set_643 := by decide +kernel

theorem calc11_set_644_eq : calc11_card_630.required ∪ calc11_set_642 = calc11_set_644 := by decide +kernel

theorem calc11_set_645_eq : calc11_card_630.envelope ∪ calc11_set_643 = calc11_set_645 := by decide +kernel

theorem calc11_set_646_eq : inline_826.envelope ∩ calc11_card_630.envelope = calc11_set_646 := by decide +kernel

theorem calc11_set_647_eq : inline_824.envelope ∩ calc11_set_646 = calc11_set_647 := by decide +kernel

theorem calc11_set_648_eq : calc11_card_633.envelope ∩ calc11_set_647 = calc11_set_648 := by decide +kernel

theorem calc11_set_649_eq : calc11_card_632.envelope ∩ calc11_set_648 = calc11_set_649 := by decide +kernel

theorem calc11_set_650_eq : calc11_card_631.envelope ∩ calc11_set_649 = calc11_set_650 := by decide +kernel

theorem calc11_set_651_eq : calc11_set_644 ∪ calc11_set_650 = calc11_set_651 := by decide +kernel

theorem calc11_finishA_652 : calc11_set_651.erase (7, 7) = inline_827.required := by decide +kernel

theorem calc11_finishT_652 : insert (7, 7) calc11_set_645 = inline_827.envelope := by decide +kernel

theorem eq_inline_827 : inline_827 = combine (7, 7) [placed 4 (9, 5) card_57, placed 4 (9, 5) card_88, placed 4 (9, 5) card_111, placed 0 (5, 5) card_213, inline_824, inline_826] := by
  rw [calc11_card_630_eq, calc11_card_631_eq, calc11_card_632_eq, calc11_card_633_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_634_eq, calc11_set_636_eq, calc11_set_638_eq, calc11_set_640_eq, calc11_set_642_eq, calc11_set_644_eq, calc11_set_646_eq, calc11_set_647_eq, calc11_set_648_eq, calc11_set_649_eq, calc11_set_650_eq, calc11_set_651_eq, calc11_finishA_652]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_635_eq, calc11_set_637_eq, calc11_set_639_eq, calc11_set_641_eq, calc11_set_643_eq, calc11_set_645_eq, calc11_finishT_652]
  · decide +kernel

theorem valid_inline_827 : Valid inline_827 := by
  rw [eq_inline_827]
  apply combination_rule (7, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (9, 5) valid_57
  rcases hc with rfl | hc
  · exact placed_valid 4 (9, 5) valid_88
  rcases hc with rfl | hc
  · exact placed_valid 4 (9, 5) valid_111
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 5) valid_213
  rcases hc with rfl | hc
  · exact valid_inline_824
  subst c
  exact valid_inline_826

theorem calc11_card_653_eq : placed 5 (5, 8) card_7 = calc11_card_653 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_654_eq : placed 3 (11, 7) card_186 = calc11_card_654 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_655_eq : placed 6 (9, 11) card_292 = calc11_card_655 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_656_eq : calc11_card_655.required ∪ ∅ = calc11_set_656 := by decide +kernel

theorem calc11_set_657_eq : calc11_card_655.envelope ∪ ∅ = calc11_set_657 := by decide +kernel

theorem calc11_set_658_eq : calc11_card_654.required ∪ calc11_set_656 = calc11_set_658 := by decide +kernel

theorem calc11_set_659_eq : calc11_card_654.envelope ∪ calc11_set_657 = calc11_set_659 := by decide +kernel

theorem calc11_set_660_eq : calc11_card_653.required ∪ calc11_set_658 = calc11_set_660 := by decide +kernel

theorem calc11_set_661_eq : calc11_card_653.envelope ∪ calc11_set_659 = calc11_set_661 := by decide +kernel

theorem calc11_set_662_eq : calc11_card_655.envelope ∩ calc11_card_653.envelope = calc11_set_662 := by decide +kernel

theorem calc11_set_663_eq : calc11_card_654.envelope ∩ calc11_set_662 = calc11_set_663 := by decide +kernel

theorem calc11_set_664_eq : calc11_set_660 ∪ calc11_set_663 = calc11_set_664 := by decide +kernel

theorem calc11_finishA_665 : calc11_set_664.erase (9, 8) = inline_828.required := by decide +kernel

theorem calc11_finishT_665 : insert (9, 8) calc11_set_661 = inline_828.envelope := by decide +kernel

theorem eq_inline_828 : inline_828 = combine (9, 8) [placed 5 (5, 8) card_7, placed 3 (11, 7) card_186, placed 6 (9, 11) card_292] := by
  rw [calc11_card_653_eq, calc11_card_654_eq, calc11_card_655_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_656_eq, calc11_set_658_eq, calc11_set_660_eq, calc11_set_662_eq, calc11_set_663_eq, calc11_set_664_eq, calc11_finishA_665]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_657_eq, calc11_set_659_eq, calc11_set_661_eq, calc11_finishT_665]
  · decide +kernel

theorem valid_inline_828 : Valid inline_828 := by
  rw [eq_inline_828]
  apply combination_rule (9, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (5, 8) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 3 (11, 7) valid_186
  subst c
  exact placed_valid 6 (9, 11) valid_292

theorem calc11_card_666_eq : placed 0 (5, 5) card_117 = calc11_card_666 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_667_eq : placed 4 (9, 6) card_137 = calc11_card_667 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_668_eq : placed 4 (9, 6) card_181 = calc11_card_668 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_669_eq : placed 4 (9, 5) card_257 = calc11_card_669 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_670_eq : placed 4 (9, 5) card_435 = calc11_card_670 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_671_eq : inline_828.required ∪ ∅ = calc11_set_671 := by decide +kernel

theorem calc11_set_672_eq : inline_828.envelope ∪ ∅ = calc11_set_672 := by decide +kernel

theorem calc11_set_673_eq : inline_827.required ∪ calc11_set_671 = calc11_set_673 := by decide +kernel

theorem calc11_set_674_eq : inline_827.envelope ∪ calc11_set_672 = calc11_set_674 := by decide +kernel

theorem calc11_set_675_eq : calc11_card_670.required ∪ calc11_set_673 = calc11_set_675 := by decide +kernel

theorem calc11_set_676_eq : calc11_card_670.envelope ∪ calc11_set_674 = calc11_set_676 := by decide +kernel

theorem calc11_set_677_eq : calc11_card_669.required ∪ calc11_set_675 = calc11_set_677 := by decide +kernel

theorem calc11_set_678_eq : calc11_card_669.envelope ∪ calc11_set_676 = calc11_set_678 := by decide +kernel

theorem calc11_set_679_eq : calc11_card_668.required ∪ calc11_set_677 = calc11_set_679 := by decide +kernel

theorem calc11_set_680_eq : calc11_card_668.envelope ∪ calc11_set_678 = calc11_set_680 := by decide +kernel

theorem calc11_set_681_eq : calc11_card_667.required ∪ calc11_set_679 = calc11_set_681 := by decide +kernel

theorem calc11_set_682_eq : calc11_card_667.envelope ∪ calc11_set_680 = calc11_set_682 := by decide +kernel

theorem calc11_set_683_eq : calc11_card_666.required ∪ calc11_set_681 = calc11_set_683 := by decide +kernel

theorem calc11_set_684_eq : calc11_card_666.envelope ∪ calc11_set_682 = calc11_set_684 := by decide +kernel

theorem calc11_set_685_eq : inline_828.envelope ∩ calc11_card_666.envelope = calc11_set_685 := by decide +kernel

theorem calc11_set_686_eq : inline_827.envelope ∩ calc11_set_685 = calc11_set_686 := by decide +kernel

theorem calc11_set_687_eq : calc11_card_670.envelope ∩ calc11_set_686 = calc11_set_687 := by decide +kernel

theorem calc11_set_688_eq : calc11_card_669.envelope ∩ calc11_set_687 = calc11_set_688 := by decide +kernel

theorem calc11_set_689_eq : calc11_card_668.envelope ∩ calc11_set_688 = calc11_set_689 := by decide +kernel

theorem calc11_set_690_eq : calc11_card_667.envelope ∩ calc11_set_689 = calc11_set_690 := by decide +kernel

theorem calc11_set_691_eq : calc11_set_683 ∪ calc11_set_690 = calc11_set_691 := by decide +kernel

theorem calc11_finishA_692 : calc11_set_691.erase (6, 8) = inline_829.required := by decide +kernel

theorem calc11_finishT_692 : insert (6, 8) calc11_set_684 = inline_829.envelope := by decide +kernel

theorem eq_inline_829 : inline_829 = combine (6, 8) [placed 0 (5, 5) card_117, placed 4 (9, 6) card_137, placed 4 (9, 6) card_181, placed 4 (9, 5) card_257, placed 4 (9, 5) card_435, inline_827, inline_828] := by
  rw [calc11_card_666_eq, calc11_card_667_eq, calc11_card_668_eq, calc11_card_669_eq, calc11_card_670_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_671_eq, calc11_set_673_eq, calc11_set_675_eq, calc11_set_677_eq, calc11_set_679_eq, calc11_set_681_eq, calc11_set_683_eq, calc11_set_685_eq, calc11_set_686_eq, calc11_set_687_eq, calc11_set_688_eq, calc11_set_689_eq, calc11_set_690_eq, calc11_set_691_eq, calc11_finishA_692]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_672_eq, calc11_set_674_eq, calc11_set_676_eq, calc11_set_678_eq, calc11_set_680_eq, calc11_set_682_eq, calc11_set_684_eq, calc11_finishT_692]
  · decide +kernel

theorem valid_inline_829 : Valid inline_829 := by
  rw [eq_inline_829]
  apply combination_rule (6, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 5) valid_117
  rcases hc with rfl | hc
  · exact placed_valid 4 (9, 6) valid_137
  rcases hc with rfl | hc
  · exact placed_valid 4 (9, 6) valid_181
  rcases hc with rfl | hc
  · exact placed_valid 4 (9, 5) valid_257
  rcases hc with rfl | hc
  · exact placed_valid 4 (9, 5) valid_435
  rcases hc with rfl | hc
  · exact valid_inline_827
  subst c
  exact valid_inline_828

theorem calc11_card_693_eq : placed 5 (5, 9) card_12 = calc11_card_693 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_694_eq : placed 3 (11, 6) card_135 = calc11_card_694 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_695_eq : placed 0 (6, 6) card_181 = calc11_card_695 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_696_eq : placed 2 (6, 11) card_435 = calc11_card_696 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_697_eq : placed 2 (5, 11) card_565 = calc11_card_697 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_698_eq : placed 4 (12, 4) card_687 = calc11_card_698 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_699_eq : placed 0 (5, 4) card_689 = calc11_card_699 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_700_eq : calc11_card_699.required ∪ ∅ = calc11_set_700 := by decide +kernel

theorem calc11_set_701_eq : calc11_card_699.envelope ∪ ∅ = calc11_set_701 := by decide +kernel

theorem calc11_set_702_eq : calc11_card_698.required ∪ calc11_set_700 = calc11_set_702 := by decide +kernel

theorem calc11_set_703_eq : calc11_card_698.envelope ∪ calc11_set_701 = calc11_set_703 := by decide +kernel

theorem calc11_set_704_eq : calc11_card_697.required ∪ calc11_set_702 = calc11_set_704 := by decide +kernel

theorem calc11_set_705_eq : calc11_card_697.envelope ∪ calc11_set_703 = calc11_set_705 := by decide +kernel

theorem calc11_set_706_eq : calc11_card_696.required ∪ calc11_set_704 = calc11_set_706 := by decide +kernel

theorem calc11_set_707_eq : calc11_card_696.envelope ∪ calc11_set_705 = calc11_set_707 := by decide +kernel

theorem calc11_set_708_eq : calc11_card_695.required ∪ calc11_set_706 = calc11_set_708 := by decide +kernel

theorem calc11_set_709_eq : calc11_card_695.envelope ∪ calc11_set_707 = calc11_set_709 := by decide +kernel

theorem calc11_set_710_eq : calc11_card_694.required ∪ calc11_set_708 = calc11_set_710 := by decide +kernel

theorem calc11_set_711_eq : calc11_card_694.envelope ∪ calc11_set_709 = calc11_set_711 := by decide +kernel

theorem calc11_set_712_eq : calc11_card_693.required ∪ calc11_set_710 = calc11_set_712 := by decide +kernel

theorem calc11_set_713_eq : calc11_card_693.envelope ∪ calc11_set_711 = calc11_set_713 := by decide +kernel

theorem calc11_set_714_eq : calc11_card_699.envelope ∩ calc11_card_693.envelope = calc11_set_714 := by decide +kernel

theorem calc11_set_715_eq : calc11_card_698.envelope ∩ calc11_set_714 = calc11_set_715 := by decide +kernel

theorem calc11_set_716_eq : calc11_card_697.envelope ∩ calc11_set_715 = calc11_set_716 := by decide +kernel

theorem calc11_set_717_eq : calc11_card_696.envelope ∩ calc11_set_716 = calc11_set_717 := by decide +kernel

theorem calc11_set_718_eq : calc11_card_695.envelope ∩ calc11_set_717 = calc11_set_718 := by decide +kernel

theorem calc11_set_719_eq : calc11_card_694.envelope ∩ calc11_set_718 = calc11_set_719 := by decide +kernel

theorem calc11_set_720_eq : calc11_set_712 ∪ calc11_set_719 = calc11_set_720 := by decide +kernel

theorem calc11_finishA_721 : calc11_set_720.erase (9, 8) = inline_830.required := by decide +kernel

theorem calc11_finishT_721 : insert (9, 8) calc11_set_713 = inline_830.envelope := by decide +kernel

theorem eq_inline_830 : inline_830 = combine (9, 8) [placed 5 (5, 9) card_12, placed 3 (11, 6) card_135, placed 0 (6, 6) card_181, placed 2 (6, 11) card_435, placed 2 (5, 11) card_565, placed 4 (12, 4) card_687, placed 0 (5, 4) card_689] := by
  rw [calc11_card_693_eq, calc11_card_694_eq, calc11_card_695_eq, calc11_card_696_eq, calc11_card_697_eq, calc11_card_698_eq, calc11_card_699_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_700_eq, calc11_set_702_eq, calc11_set_704_eq, calc11_set_706_eq, calc11_set_708_eq, calc11_set_710_eq, calc11_set_712_eq, calc11_set_714_eq, calc11_set_715_eq, calc11_set_716_eq, calc11_set_717_eq, calc11_set_718_eq, calc11_set_719_eq, calc11_set_720_eq, calc11_finishA_721]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_701_eq, calc11_set_703_eq, calc11_set_705_eq, calc11_set_707_eq, calc11_set_709_eq, calc11_set_711_eq, calc11_set_713_eq, calc11_finishT_721]
  · decide +kernel

theorem valid_inline_830 : Valid inline_830 := by
  rw [eq_inline_830]
  apply combination_rule (9, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (5, 9) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 3 (11, 6) valid_135
  rcases hc with rfl | hc
  · exact placed_valid 0 (6, 6) valid_181
  rcases hc with rfl | hc
  · exact placed_valid 2 (6, 11) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 11) valid_565
  rcases hc with rfl | hc
  · exact placed_valid 4 (12, 4) valid_687
  subst c
  exact placed_valid 0 (5, 4) valid_689

theorem calc11_card_722_eq : placed 1 (5, 7) card_12 = calc11_card_722 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_723_eq : placed 5 (5, 9) card_12 = calc11_card_723 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_724_eq : placed 3 (11, 7) card_12 = calc11_card_724 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_725_eq : placed 7 (11, 9) card_12 = calc11_card_725 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_726_eq : placed 0 (5, 1) card_490 = calc11_card_726 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_727_eq : placed 4 (11, 1) card_490 = calc11_card_727 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_728_eq : calc11_card_727.required ∪ ∅ = calc11_set_728 := by decide +kernel

theorem calc11_set_729_eq : calc11_card_727.envelope ∪ ∅ = calc11_set_729 := by decide +kernel

theorem calc11_set_730_eq : calc11_card_726.required ∪ calc11_set_728 = calc11_set_730 := by decide +kernel

theorem calc11_set_731_eq : calc11_card_726.envelope ∪ calc11_set_729 = calc11_set_731 := by decide +kernel

theorem calc11_set_732_eq : calc11_card_725.required ∪ calc11_set_730 = calc11_set_732 := by decide +kernel

theorem calc11_set_733_eq : calc11_card_725.envelope ∪ calc11_set_731 = calc11_set_733 := by decide +kernel

theorem calc11_set_734_eq : calc11_card_724.required ∪ calc11_set_732 = calc11_set_734 := by decide +kernel

theorem calc11_set_735_eq : calc11_card_724.envelope ∪ calc11_set_733 = calc11_set_735 := by decide +kernel

theorem calc11_set_736_eq : calc11_card_723.required ∪ calc11_set_734 = calc11_set_736 := by decide +kernel

theorem calc11_set_737_eq : calc11_card_723.envelope ∪ calc11_set_735 = calc11_set_737 := by decide +kernel

theorem calc11_set_738_eq : calc11_card_722.required ∪ calc11_set_736 = calc11_set_738 := by decide +kernel

theorem calc11_set_739_eq : calc11_card_722.envelope ∪ calc11_set_737 = calc11_set_739 := by decide +kernel

theorem calc11_set_740_eq : calc11_card_727.envelope ∩ calc11_card_722.envelope = calc11_set_740 := by decide +kernel

theorem calc11_set_741_eq : calc11_card_726.envelope ∩ calc11_set_740 = calc11_set_741 := by decide +kernel

theorem calc11_set_742_eq : calc11_card_725.envelope ∩ calc11_set_741 = calc11_set_742 := by decide +kernel

theorem calc11_set_743_eq : calc11_card_724.envelope ∩ calc11_set_742 = calc11_set_743 := by decide +kernel

theorem calc11_set_744_eq : calc11_card_723.envelope ∩ calc11_set_743 = calc11_set_744 := by decide +kernel

theorem calc11_set_745_eq : calc11_set_738 ∪ calc11_set_744 = calc11_set_745 := by decide +kernel

theorem calc11_finishA_746 : calc11_set_745.erase (9, 8) = inline_831.required := by decide +kernel

theorem calc11_finishT_746 : insert (9, 8) calc11_set_739 = inline_831.envelope := by decide +kernel

theorem eq_inline_831 : inline_831 = combine (9, 8) [placed 1 (5, 7) card_12, placed 5 (5, 9) card_12, placed 3 (11, 7) card_12, placed 7 (11, 9) card_12, placed 0 (5, 1) card_490, placed 4 (11, 1) card_490] := by
  rw [calc11_card_722_eq, calc11_card_723_eq, calc11_card_724_eq, calc11_card_725_eq, calc11_card_726_eq, calc11_card_727_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_728_eq, calc11_set_730_eq, calc11_set_732_eq, calc11_set_734_eq, calc11_set_736_eq, calc11_set_738_eq, calc11_set_740_eq, calc11_set_741_eq, calc11_set_742_eq, calc11_set_743_eq, calc11_set_744_eq, calc11_set_745_eq, calc11_finishA_746]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_729_eq, calc11_set_731_eq, calc11_set_733_eq, calc11_set_735_eq, calc11_set_737_eq, calc11_set_739_eq, calc11_finishT_746]
  · decide +kernel

theorem valid_inline_831 : Valid inline_831 := by
  rw [eq_inline_831]
  apply combination_rule (9, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (5, 7) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 5 (5, 9) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 3 (11, 7) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 7 (11, 9) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 1) valid_490
  subst c
  exact placed_valid 4 (11, 1) valid_490

theorem calc11_card_747_eq : placed 3 (12, 7) card_459 = calc11_card_747 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_748_eq : placed 3 (11, 6) card_475 = calc11_card_748 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_749_eq : placed 5 (4, 10) card_587 = calc11_card_749 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_750_eq : placed 1 (4, 7) card_603 = calc11_card_750 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_751_eq : placed 0 (5, 5) card_605 = calc11_card_751 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_752_eq : placed 6 (11, 13) card_650 = calc11_card_752 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_753_eq : placed 0 (1, 1) card_684 = calc11_card_753 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_754_eq : placed 7 (13, 13) card_694 = calc11_card_754 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_755_eq : placed 0 (5, 3) card_695 = calc11_card_755 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_756_eq : placed 3 (13, 3) card_696 = calc11_card_756 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_757_eq : placed 1 (3, 4) card_698 = calc11_card_757 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_758_eq : placed 4 (13, 1) card_701 = calc11_card_758 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_759_eq : placed 4 (12, 3) card_707 = calc11_card_759 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_760_eq : calc11_card_759.required ∪ ∅ = calc11_set_760 := by decide +kernel

theorem calc11_set_761_eq : calc11_card_759.envelope ∪ ∅ = calc11_set_761 := by decide +kernel

theorem calc11_set_762_eq : inline_831.required ∪ calc11_set_760 = calc11_set_762 := by decide +kernel

theorem calc11_set_763_eq : inline_831.envelope ∪ calc11_set_761 = calc11_set_763 := by decide +kernel

theorem calc11_set_764_eq : calc11_card_758.required ∪ calc11_set_762 = calc11_set_764 := by decide +kernel

theorem calc11_set_765_eq : calc11_card_758.envelope ∪ calc11_set_763 = calc11_set_765 := by decide +kernel

theorem calc11_set_766_eq : calc11_card_757.required ∪ calc11_set_764 = calc11_set_766 := by decide +kernel

theorem calc11_set_767_eq : calc11_card_757.envelope ∪ calc11_set_765 = calc11_set_767 := by decide +kernel

theorem calc11_set_768_eq : calc11_card_756.required ∪ calc11_set_766 = calc11_set_768 := by decide +kernel

theorem calc11_set_769_eq : calc11_card_756.envelope ∪ calc11_set_767 = calc11_set_769 := by decide +kernel

theorem calc11_set_770_eq : calc11_card_755.required ∪ calc11_set_768 = calc11_set_770 := by decide +kernel

theorem calc11_set_771_eq : calc11_card_755.envelope ∪ calc11_set_769 = calc11_set_771 := by decide +kernel

theorem calc11_set_772_eq : calc11_card_754.required ∪ calc11_set_770 = calc11_set_772 := by decide +kernel

theorem calc11_set_773_eq : calc11_card_754.envelope ∪ calc11_set_771 = calc11_set_773 := by decide +kernel

theorem calc11_set_774_eq : inline_830.required ∪ calc11_set_772 = calc11_set_774 := by decide +kernel

theorem calc11_set_775_eq : inline_830.envelope ∪ calc11_set_773 = calc11_set_775 := by decide +kernel

theorem calc11_set_776_eq : inline_829.required ∪ calc11_set_774 = calc11_set_776 := by decide +kernel

theorem calc11_set_777_eq : inline_829.envelope ∪ calc11_set_775 = calc11_set_777 := by decide +kernel

theorem calc11_set_778_eq : calc11_card_753.required ∪ calc11_set_776 = calc11_set_778 := by decide +kernel

theorem calc11_set_779_eq : calc11_card_753.envelope ∪ calc11_set_777 = calc11_set_779 := by decide +kernel

theorem calc11_set_780_eq : calc11_card_752.required ∪ calc11_set_778 = calc11_set_780 := by decide +kernel

theorem calc11_set_781_eq : calc11_card_752.envelope ∪ calc11_set_779 = calc11_set_781 := by decide +kernel

theorem calc11_set_782_eq : calc11_card_751.required ∪ calc11_set_780 = calc11_set_782 := by decide +kernel

theorem calc11_set_783_eq : calc11_card_751.envelope ∪ calc11_set_781 = calc11_set_783 := by decide +kernel

theorem calc11_set_784_eq : calc11_card_750.required ∪ calc11_set_782 = calc11_set_784 := by decide +kernel

theorem calc11_set_785_eq : calc11_card_750.envelope ∪ calc11_set_783 = calc11_set_785 := by decide +kernel

theorem calc11_set_786_eq : calc11_card_749.required ∪ calc11_set_784 = calc11_set_786 := by decide +kernel

theorem calc11_set_787_eq : calc11_card_749.envelope ∪ calc11_set_785 = calc11_set_787 := by decide +kernel

theorem calc11_set_788_eq : calc11_card_748.required ∪ calc11_set_786 = calc11_set_788 := by decide +kernel

theorem calc11_set_789_eq : calc11_card_748.envelope ∪ calc11_set_787 = calc11_set_789 := by decide +kernel

theorem calc11_set_790_eq : calc11_card_747.required ∪ calc11_set_788 = calc11_set_790 := by decide +kernel

theorem calc11_set_791_eq : calc11_card_747.envelope ∪ calc11_set_789 = calc11_set_791 := by decide +kernel

theorem calc11_set_792_eq : calc11_card_759.envelope ∩ calc11_card_747.envelope = calc11_set_792 := by decide +kernel

theorem calc11_set_793_eq : inline_831.envelope ∩ calc11_set_792 = calc11_set_793 := by decide +kernel

theorem calc11_set_794_eq : calc11_card_758.envelope ∩ calc11_set_793 = calc11_set_794 := by decide +kernel

theorem calc11_set_795_eq : calc11_card_757.envelope ∩ calc11_set_794 = calc11_set_795 := by decide +kernel

theorem calc11_set_796_eq : calc11_card_756.envelope ∩ calc11_set_795 = calc11_set_796 := by decide +kernel

theorem calc11_set_797_eq : calc11_card_755.envelope ∩ calc11_set_796 = calc11_set_797 := by decide +kernel

theorem calc11_set_798_eq : calc11_card_754.envelope ∩ calc11_set_797 = calc11_set_798 := by decide +kernel

theorem calc11_set_799_eq : inline_830.envelope ∩ calc11_set_798 = calc11_set_799 := by decide +kernel

theorem calc11_set_800_eq : inline_829.envelope ∩ calc11_set_799 = calc11_set_800 := by decide +kernel

theorem calc11_set_801_eq : calc11_card_753.envelope ∩ calc11_set_800 = calc11_set_801 := by decide +kernel

theorem calc11_set_802_eq : calc11_card_752.envelope ∩ calc11_set_801 = calc11_set_802 := by decide +kernel

theorem calc11_set_803_eq : calc11_card_751.envelope ∩ calc11_set_802 = calc11_set_803 := by decide +kernel

theorem calc11_set_804_eq : calc11_card_750.envelope ∩ calc11_set_803 = calc11_set_804 := by decide +kernel

theorem calc11_set_805_eq : calc11_card_749.envelope ∩ calc11_set_804 = calc11_set_805 := by decide +kernel

theorem calc11_set_806_eq : calc11_card_748.envelope ∩ calc11_set_805 = calc11_set_806 := by decide +kernel

theorem calc11_set_807_eq : calc11_set_790 ∪ calc11_set_806 = calc11_set_807 := by decide +kernel

theorem calc11_finishA_808 : calc11_set_807.erase (7, 8) = card_708.required := by decide +kernel

theorem calc11_finishT_808 : insert (7, 8) calc11_set_791 = card_708.envelope := by decide +kernel

theorem eq_card_708 : card_708 = combine (7, 8) [placed 3 (12, 7) card_459, placed 3 (11, 6) card_475, placed 5 (4, 10) card_587, placed 1 (4, 7) card_603, placed 0 (5, 5) card_605, placed 6 (11, 13) card_650, placed 0 (1, 1) card_684, inline_829, inline_830, placed 7 (13, 13) card_694, placed 0 (5, 3) card_695, placed 3 (13, 3) card_696, placed 1 (3, 4) card_698, placed 4 (13, 1) card_701, inline_831, placed 4 (12, 3) card_707] := by
  rw [calc11_card_747_eq, calc11_card_748_eq, calc11_card_749_eq, calc11_card_750_eq, calc11_card_751_eq, calc11_card_752_eq, calc11_card_753_eq, calc11_card_754_eq, calc11_card_755_eq, calc11_card_756_eq, calc11_card_757_eq, calc11_card_758_eq, calc11_card_759_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_760_eq, calc11_set_762_eq, calc11_set_764_eq, calc11_set_766_eq, calc11_set_768_eq, calc11_set_770_eq, calc11_set_772_eq, calc11_set_774_eq, calc11_set_776_eq, calc11_set_778_eq, calc11_set_780_eq, calc11_set_782_eq, calc11_set_784_eq, calc11_set_786_eq, calc11_set_788_eq, calc11_set_790_eq, calc11_set_792_eq, calc11_set_793_eq, calc11_set_794_eq, calc11_set_795_eq, calc11_set_796_eq, calc11_set_797_eq, calc11_set_798_eq, calc11_set_799_eq, calc11_set_800_eq, calc11_set_801_eq, calc11_set_802_eq, calc11_set_803_eq, calc11_set_804_eq, calc11_set_805_eq, calc11_set_806_eq, calc11_set_807_eq, calc11_finishA_808]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_761_eq, calc11_set_763_eq, calc11_set_765_eq, calc11_set_767_eq, calc11_set_769_eq, calc11_set_771_eq, calc11_set_773_eq, calc11_set_775_eq, calc11_set_777_eq, calc11_set_779_eq, calc11_set_781_eq, calc11_set_783_eq, calc11_set_785_eq, calc11_set_787_eq, calc11_set_789_eq, calc11_set_791_eq, calc11_finishT_808]
  · decide +kernel

theorem valid_708 : Valid card_708 := by
  rw [eq_card_708]
  apply combination_rule (7, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (12, 7) valid_459
  rcases hc with rfl | hc
  · exact placed_valid 3 (11, 6) valid_475
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 10) valid_587
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 7) valid_603
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 5) valid_605
  rcases hc with rfl | hc
  · exact placed_valid 6 (11, 13) valid_650
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_684
  rcases hc with rfl | hc
  · exact valid_inline_829
  rcases hc with rfl | hc
  · exact valid_inline_830
  rcases hc with rfl | hc
  · exact placed_valid 7 (13, 13) valid_694
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 3) valid_695
  rcases hc with rfl | hc
  · exact placed_valid 3 (13, 3) valid_696
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 4) valid_698
  rcases hc with rfl | hc
  · exact placed_valid 4 (13, 1) valid_701
  rcases hc with rfl | hc
  · exact valid_inline_831
  subst c
  exact placed_valid 4 (12, 3) valid_707


end OAI.Snaky21.Certificate

theorem solution : Valid card_708 ∧ True :=
  ⟨valid_708, True.intro⟩
