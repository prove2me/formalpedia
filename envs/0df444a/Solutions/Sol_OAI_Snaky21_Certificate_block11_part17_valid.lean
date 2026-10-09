-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block11_part17_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:26:09.918333+00:00
-- url     : https://prove2.me/submissions/67736873-7a20-4edb-a827-ee64092ce719

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block03_valid
import Definitions.Def_Snaky21Calc11Part08
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block10_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part16_valid
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
theorem valid_5 : Valid card_5 := block00_valid.2.2.2.2.2.1
theorem valid_7 : Valid card_7 := block00_valid.2.2.2.2.2.2.2.1
theorem valid_8 : Valid card_8 := block00_valid.2.2.2.2.2.2.2.2.1
theorem valid_14 : Valid card_14 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_22 : Valid card_22 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_25 : Valid card_25 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_176 : Valid card_176 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_208 : Valid card_208 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_216 : Valid card_216 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_218 : Valid card_218 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem calc11_card_1697_eq : placed 2 (2, 6) card_5 = calc11_card_1697 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1698_eq : placed 6 (5, 7) card_208 = calc11_card_1698 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1699_eq : calc11_card_1698.required ∪ ∅ = calc11_set_1699 := by decide +kernel

theorem calc11_set_1700_eq : calc11_card_1698.envelope ∪ ∅ = calc11_set_1700 := by decide +kernel

theorem calc11_set_1701_eq : calc11_card_1697.required ∪ calc11_set_1699 = calc11_set_1701 := by decide +kernel

theorem calc11_set_1702_eq : calc11_card_1697.envelope ∪ calc11_set_1700 = calc11_set_1702 := by decide +kernel

theorem calc11_set_1703_eq : calc11_card_1698.envelope ∩ calc11_card_1697.envelope = calc11_set_1703 := by decide +kernel

theorem calc11_set_1704_eq : calc11_set_1701 ∪ calc11_set_1703 = calc11_set_1704 := by decide +kernel

theorem calc11_finishA_1705 : calc11_set_1704.erase (2, 6) = inline_870.required := by decide +kernel

theorem calc11_finishT_1705 : insert (2, 6) calc11_set_1702 = inline_870.envelope := by decide +kernel

theorem eq_inline_870 : inline_870 = combine (2, 6) [placed 2 (2, 6) card_5, placed 6 (5, 7) card_208] := by
  rw [calc11_card_1697_eq, calc11_card_1698_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1699_eq, calc11_set_1701_eq, calc11_set_1703_eq, calc11_set_1704_eq, calc11_finishA_1705]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1700_eq, calc11_set_1702_eq, calc11_finishT_1705]
  · decide +kernel

theorem valid_inline_870 : Valid inline_870 := by
  rw [eq_inline_870]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 6) valid_5
  subst c
  exact placed_valid 6 (5, 7) valid_208

theorem calc11_card_1706_eq : placed 3 (5, 3) card_5 = calc11_card_1706 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1707_eq : inline_870.required ∪ ∅ = calc11_set_1707 := by decide +kernel

theorem calc11_set_1708_eq : inline_870.envelope ∪ ∅ = calc11_set_1708 := by decide +kernel

theorem calc11_set_1709_eq : calc11_card_1706.required ∪ calc11_set_1707 = calc11_set_1709 := by decide +kernel

theorem calc11_set_1710_eq : calc11_card_1706.envelope ∪ calc11_set_1708 = calc11_set_1710 := by decide +kernel

theorem calc11_set_1711_eq : inline_870.envelope ∩ calc11_card_1706.envelope = calc11_set_1711 := by decide +kernel

theorem calc11_set_1712_eq : calc11_set_1709 ∪ calc11_set_1711 = calc11_set_1712 := by decide +kernel

theorem calc11_finishA_1713 : calc11_set_1712.erase (4, 6) = inline_871.required := by decide +kernel

theorem calc11_finishT_1713 : insert (4, 6) calc11_set_1710 = inline_871.envelope := by decide +kernel

theorem eq_inline_871 : inline_871 = combine (4, 6) [placed 3 (5, 3) card_5, inline_870] := by
  rw [calc11_card_1706_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1707_eq, calc11_set_1709_eq, calc11_set_1711_eq, calc11_set_1712_eq, calc11_finishA_1713]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1708_eq, calc11_set_1710_eq, calc11_finishT_1713]
  · decide +kernel

theorem valid_inline_871 : Valid inline_871 := by
  rw [eq_inline_871]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 3) valid_5
  subst c
  exact valid_inline_870

theorem calc11_card_1714_eq : placed 4 (3, 2) card_22 = calc11_card_1714 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1715_eq : inline_871.required ∪ ∅ = calc11_set_1715 := by decide +kernel

theorem calc11_set_1716_eq : inline_871.envelope ∪ ∅ = calc11_set_1716 := by decide +kernel

theorem calc11_set_1717_eq : calc11_card_1714.required ∪ calc11_set_1715 = calc11_set_1717 := by decide +kernel

theorem calc11_set_1718_eq : calc11_card_1714.envelope ∪ calc11_set_1716 = calc11_set_1718 := by decide +kernel

theorem calc11_set_1719_eq : inline_871.envelope ∩ calc11_card_1714.envelope = calc11_set_1719 := by decide +kernel

theorem calc11_set_1720_eq : calc11_set_1717 ∪ calc11_set_1719 = calc11_set_1720 := by decide +kernel

theorem calc11_finishA_1721 : calc11_set_1720.erase (3, 6) = inline_872.required := by decide +kernel

theorem calc11_finishT_1721 : insert (3, 6) calc11_set_1718 = inline_872.envelope := by decide +kernel

theorem eq_inline_872 : inline_872 = combine (3, 6) [placed 4 (3, 2) card_22, inline_871] := by
  rw [calc11_card_1714_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1715_eq, calc11_set_1717_eq, calc11_set_1719_eq, calc11_set_1720_eq, calc11_finishA_1721]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1716_eq, calc11_set_1718_eq, calc11_finishT_1721]
  · decide +kernel

theorem valid_inline_872 : Valid inline_872 := by
  rw [eq_inline_872]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 2) valid_22
  subst c
  exact valid_inline_871

theorem calc11_card_1722_eq : placed 7 (6, 6) card_25 = calc11_card_1722 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1723_eq : inline_872.required ∪ ∅ = calc11_set_1723 := by decide +kernel

theorem calc11_set_1724_eq : inline_872.envelope ∪ ∅ = calc11_set_1724 := by decide +kernel

theorem calc11_set_1725_eq : calc11_card_1722.required ∪ calc11_set_1723 = calc11_set_1725 := by decide +kernel

theorem calc11_set_1726_eq : calc11_card_1722.envelope ∪ calc11_set_1724 = calc11_set_1726 := by decide +kernel

theorem calc11_set_1727_eq : inline_872.envelope ∩ calc11_card_1722.envelope = calc11_set_1727 := by decide +kernel

theorem calc11_set_1728_eq : calc11_set_1725 ∪ calc11_set_1727 = calc11_set_1728 := by decide +kernel

theorem calc11_finishA_1729 : calc11_set_1728.erase (2, 4) = inline_873.required := by decide +kernel

theorem calc11_finishT_1729 : insert (2, 4) calc11_set_1726 = inline_873.envelope := by decide +kernel

theorem eq_inline_873 : inline_873 = combine (2, 4) [placed 7 (6, 6) card_25, inline_872] := by
  rw [calc11_card_1722_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1723_eq, calc11_set_1725_eq, calc11_set_1727_eq, calc11_set_1728_eq, calc11_finishA_1729]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1724_eq, calc11_set_1726_eq, calc11_finishT_1729]
  · decide +kernel

theorem valid_inline_873 : Valid inline_873 := by
  rw [eq_inline_873]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 6) valid_25
  subst c
  exact valid_inline_872

theorem calc11_card_1730_eq : placed 2 (5, 7) card_7 = calc11_card_1730 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1731_eq : placed 3 (6, 3) card_8 = calc11_card_1731 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1732_eq : inline_873.required ∪ ∅ = calc11_set_1732 := by decide +kernel

theorem calc11_set_1733_eq : inline_873.envelope ∪ ∅ = calc11_set_1733 := by decide +kernel

theorem calc11_set_1734_eq : calc11_card_1731.required ∪ calc11_set_1732 = calc11_set_1734 := by decide +kernel

theorem calc11_set_1735_eq : calc11_card_1731.envelope ∪ calc11_set_1733 = calc11_set_1735 := by decide +kernel

theorem calc11_set_1736_eq : calc11_card_1730.required ∪ calc11_set_1734 = calc11_set_1736 := by decide +kernel

theorem calc11_set_1737_eq : calc11_card_1730.envelope ∪ calc11_set_1735 = calc11_set_1737 := by decide +kernel

theorem calc11_set_1738_eq : inline_873.envelope ∩ calc11_card_1730.envelope = calc11_set_1738 := by decide +kernel

theorem calc11_set_1739_eq : calc11_card_1731.envelope ∩ calc11_set_1738 = calc11_set_1739 := by decide +kernel

theorem calc11_set_1740_eq : calc11_set_1736 ∪ calc11_set_1739 = calc11_set_1740 := by decide +kernel

theorem calc11_finishA_1741 : calc11_set_1740.erase (5, 6) = inline_874.required := by decide +kernel

theorem calc11_finishT_1741 : insert (5, 6) calc11_set_1737 = inline_874.envelope := by decide +kernel

theorem eq_inline_874 : inline_874 = combine (5, 6) [placed 2 (5, 7) card_7, placed 3 (6, 3) card_8, inline_873] := by
  rw [calc11_card_1730_eq, calc11_card_1731_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1732_eq, calc11_set_1734_eq, calc11_set_1736_eq, calc11_set_1738_eq, calc11_set_1739_eq, calc11_set_1740_eq, calc11_finishA_1741]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1733_eq, calc11_set_1735_eq, calc11_set_1737_eq, calc11_finishT_1741]
  · decide +kernel

theorem valid_inline_874 : Valid inline_874 := by
  rw [eq_inline_874]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 7) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 3) valid_8
  subst c
  exact valid_inline_873

theorem calc11_card_1742_eq : placed 4 (6, 1) card_14 = calc11_card_1742 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1743_eq : placed 2 (2, 6) card_176 = calc11_card_1743 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1744_eq : placed 0 (2, 2) card_216 = calc11_card_1744 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1745_eq : placed 1 (2, 3) card_218 = calc11_card_1745 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1746_eq : inline_874.required ∪ ∅ = calc11_set_1746 := by decide +kernel

theorem calc11_set_1747_eq : inline_874.envelope ∪ ∅ = calc11_set_1747 := by decide +kernel

theorem calc11_set_1748_eq : calc11_card_1745.required ∪ calc11_set_1746 = calc11_set_1748 := by decide +kernel

theorem calc11_set_1749_eq : calc11_card_1745.envelope ∪ calc11_set_1747 = calc11_set_1749 := by decide +kernel

theorem calc11_set_1750_eq : calc11_card_1744.required ∪ calc11_set_1748 = calc11_set_1750 := by decide +kernel

theorem calc11_set_1751_eq : calc11_card_1744.envelope ∪ calc11_set_1749 = calc11_set_1751 := by decide +kernel

theorem calc11_set_1752_eq : calc11_card_1743.required ∪ calc11_set_1750 = calc11_set_1752 := by decide +kernel

theorem calc11_set_1753_eq : calc11_card_1743.envelope ∪ calc11_set_1751 = calc11_set_1753 := by decide +kernel

theorem calc11_set_1754_eq : calc11_card_1742.required ∪ calc11_set_1752 = calc11_set_1754 := by decide +kernel

theorem calc11_set_1755_eq : calc11_card_1742.envelope ∪ calc11_set_1753 = calc11_set_1755 := by decide +kernel

theorem calc11_set_1756_eq : inline_874.envelope ∩ calc11_card_1742.envelope = calc11_set_1756 := by decide +kernel

theorem calc11_set_1757_eq : calc11_card_1745.envelope ∩ calc11_set_1756 = calc11_set_1757 := by decide +kernel

theorem calc11_set_1758_eq : calc11_card_1744.envelope ∩ calc11_set_1757 = calc11_set_1758 := by decide +kernel

theorem calc11_set_1759_eq : calc11_card_1743.envelope ∩ calc11_set_1758 = calc11_set_1759 := by decide +kernel

theorem calc11_set_1760_eq : calc11_set_1754 ∪ calc11_set_1759 = calc11_set_1760 := by decide +kernel

theorem calc11_finishA_1761 : calc11_set_1760.erase (5, 4) = card_721.required := by decide +kernel

theorem calc11_finishT_1761 : insert (5, 4) calc11_set_1755 = card_721.envelope := by decide +kernel

theorem eq_card_721 : card_721 = combine (5, 4) [placed 4 (6, 1) card_14, placed 2 (2, 6) card_176, placed 0 (2, 2) card_216, placed 1 (2, 3) card_218, inline_874] := by
  rw [calc11_card_1742_eq, calc11_card_1743_eq, calc11_card_1744_eq, calc11_card_1745_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1746_eq, calc11_set_1748_eq, calc11_set_1750_eq, calc11_set_1752_eq, calc11_set_1754_eq, calc11_set_1756_eq, calc11_set_1757_eq, calc11_set_1758_eq, calc11_set_1759_eq, calc11_set_1760_eq, calc11_finishA_1761]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1747_eq, calc11_set_1749_eq, calc11_set_1751_eq, calc11_set_1753_eq, calc11_set_1755_eq, calc11_finishT_1761]
  · decide +kernel

theorem valid_721 : Valid card_721 := by
  rw [eq_card_721]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 1) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 6) valid_176
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_216
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_218
  subst c
  exact valid_inline_874


end OAI.Snaky21.Certificate

theorem solution : Valid card_721 ∧ True :=
  ⟨valid_721, True.intro⟩
