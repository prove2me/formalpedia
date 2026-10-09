-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block11_part18_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:24:43.159882+00:00
-- url     : https://prove2.me/submissions/e9c52b1c-bb7e-4e74-9668-6658f4c4596c

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Definitions.Def_Snaky21Calc11Part09
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block10_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part17_valid
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
theorem valid_0 : Valid card_0 := block00_valid.1
theorem valid_2 : Valid card_2 := block00_valid.2.2.1
theorem valid_8 : Valid card_8 := block00_valid.2.2.2.2.2.2.2.2.1
theorem valid_9 : Valid card_9 := block00_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_13 : Valid card_13 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_17 : Valid card_17 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_32 : Valid card_32 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_176 : Valid card_176 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_267 : Valid card_267 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_307 : Valid card_307 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_345 : Valid card_345 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_366 : Valid card_366 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem calc11_card_1762_eq : placed 0 (3, 3) card_17 = calc11_card_1762 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1763_eq : placed 7 (5, 6) card_32 = calc11_card_1763 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1764_eq : calc11_card_1763.required ∪ ∅ = calc11_set_1764 := by decide +kernel

theorem calc11_set_1765_eq : calc11_card_1763.envelope ∪ ∅ = calc11_set_1765 := by decide +kernel

theorem calc11_set_1766_eq : calc11_card_1762.required ∪ calc11_set_1764 = calc11_set_1766 := by decide +kernel

theorem calc11_set_1767_eq : calc11_card_1762.envelope ∪ calc11_set_1765 = calc11_set_1767 := by decide +kernel

theorem calc11_set_1768_eq : calc11_card_1763.envelope ∩ calc11_card_1762.envelope = calc11_set_1768 := by decide +kernel

theorem calc11_set_1769_eq : calc11_set_1766 ∪ calc11_set_1768 = calc11_set_1769 := by decide +kernel

theorem calc11_finishA_1770 : calc11_set_1769.erase (3, 4) = inline_875.required := by decide +kernel

theorem calc11_finishT_1770 : insert (3, 4) calc11_set_1767 = inline_875.envelope := by decide +kernel

theorem eq_inline_875 : inline_875 = combine (3, 4) [placed 0 (3, 3) card_17, placed 7 (5, 6) card_32] := by
  rw [calc11_card_1762_eq, calc11_card_1763_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1764_eq, calc11_set_1766_eq, calc11_set_1768_eq, calc11_set_1769_eq, calc11_finishA_1770]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1765_eq, calc11_set_1767_eq, calc11_finishT_1770]
  · decide +kernel

theorem valid_inline_875 : Valid inline_875 := by
  rw [eq_inline_875]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_17
  subst c
  exact placed_valid 7 (5, 6) valid_32

theorem calc11_card_1771_eq : placed 3 (5, 3) card_8 = calc11_card_1771 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1772_eq : placed 2 (3, 7) card_9 = calc11_card_1772 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1773_eq : placed 6 (5, 8) card_366 = calc11_card_1773 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1774_eq : inline_875.required ∪ ∅ = calc11_set_1774 := by decide +kernel

theorem calc11_set_1775_eq : inline_875.envelope ∪ ∅ = calc11_set_1775 := by decide +kernel

theorem calc11_set_1776_eq : calc11_card_1773.required ∪ calc11_set_1774 = calc11_set_1776 := by decide +kernel

theorem calc11_set_1777_eq : calc11_card_1773.envelope ∪ calc11_set_1775 = calc11_set_1777 := by decide +kernel

theorem calc11_set_1778_eq : calc11_card_1772.required ∪ calc11_set_1776 = calc11_set_1778 := by decide +kernel

theorem calc11_set_1779_eq : calc11_card_1772.envelope ∪ calc11_set_1777 = calc11_set_1779 := by decide +kernel

theorem calc11_set_1780_eq : calc11_card_1771.required ∪ calc11_set_1778 = calc11_set_1780 := by decide +kernel

theorem calc11_set_1781_eq : calc11_card_1771.envelope ∪ calc11_set_1779 = calc11_set_1781 := by decide +kernel

theorem calc11_set_1782_eq : inline_875.envelope ∩ calc11_card_1771.envelope = calc11_set_1782 := by decide +kernel

theorem calc11_set_1783_eq : calc11_card_1773.envelope ∩ calc11_set_1782 = calc11_set_1783 := by decide +kernel

theorem calc11_set_1784_eq : calc11_card_1772.envelope ∩ calc11_set_1783 = calc11_set_1784 := by decide +kernel

theorem calc11_set_1785_eq : calc11_set_1780 ∪ calc11_set_1784 = calc11_set_1785 := by decide +kernel

theorem calc11_finishA_1786 : calc11_set_1785.erase (4, 6) = inline_876.required := by decide +kernel

theorem calc11_finishT_1786 : insert (4, 6) calc11_set_1781 = inline_876.envelope := by decide +kernel

theorem eq_inline_876 : inline_876 = combine (4, 6) [placed 3 (5, 3) card_8, placed 2 (3, 7) card_9, placed 6 (5, 8) card_366, inline_875] := by
  rw [calc11_card_1771_eq, calc11_card_1772_eq, calc11_card_1773_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1774_eq, calc11_set_1776_eq, calc11_set_1778_eq, calc11_set_1780_eq, calc11_set_1782_eq, calc11_set_1783_eq, calc11_set_1784_eq, calc11_set_1785_eq, calc11_finishA_1786]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1775_eq, calc11_set_1777_eq, calc11_set_1779_eq, calc11_set_1781_eq, calc11_finishT_1786]
  · decide +kernel

theorem valid_inline_876 : Valid inline_876 := by
  rw [eq_inline_876]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 3) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_9
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 8) valid_366
  subst c
  exact valid_inline_875

theorem calc11_card_1787_eq : placed 6 (5, 4) card_2 = calc11_card_1787 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1788_eq : placed 1 (2, 2) card_345 = calc11_card_1788 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1789_eq : calc11_card_1788.required ∪ ∅ = calc11_set_1789 := by decide +kernel

theorem calc11_set_1790_eq : calc11_card_1788.envelope ∪ ∅ = calc11_set_1790 := by decide +kernel

theorem calc11_set_1791_eq : calc11_card_1787.required ∪ calc11_set_1789 = calc11_set_1791 := by decide +kernel

theorem calc11_set_1792_eq : calc11_card_1787.envelope ∪ calc11_set_1790 = calc11_set_1792 := by decide +kernel

theorem calc11_set_1793_eq : calc11_card_1788.envelope ∩ calc11_card_1787.envelope = calc11_set_1793 := by decide +kernel

theorem calc11_set_1794_eq : calc11_set_1791 ∪ calc11_set_1793 = calc11_set_1794 := by decide +kernel

theorem calc11_finishA_1795 : calc11_set_1794.erase (5, 4) = inline_877.required := by decide +kernel

theorem calc11_finishT_1795 : insert (5, 4) calc11_set_1792 = inline_877.envelope := by decide +kernel

theorem eq_inline_877 : inline_877 = combine (5, 4) [placed 6 (5, 4) card_2, placed 1 (2, 2) card_345] := by
  rw [calc11_card_1787_eq, calc11_card_1788_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1789_eq, calc11_set_1791_eq, calc11_set_1793_eq, calc11_set_1794_eq, calc11_finishA_1795]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1790_eq, calc11_set_1792_eq, calc11_finishT_1795]
  · decide +kernel

theorem valid_inline_877 : Valid inline_877 := by
  rw [eq_inline_877]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 4) valid_2
  subst c
  exact placed_valid 1 (2, 2) valid_345

theorem calc11_card_1796_eq : placed 6 (5, 4) card_0 = calc11_card_1796 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1797_eq : placed 4 (5, 2) card_307 = calc11_card_1797 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1798_eq : calc11_card_1797.required ∪ ∅ = calc11_set_1798 := by decide +kernel

theorem calc11_set_1799_eq : calc11_card_1797.envelope ∪ ∅ = calc11_set_1799 := by decide +kernel

theorem calc11_set_1800_eq : calc11_card_1796.required ∪ calc11_set_1798 = calc11_set_1800 := by decide +kernel

theorem calc11_set_1801_eq : calc11_card_1796.envelope ∪ calc11_set_1799 = calc11_set_1801 := by decide +kernel

theorem calc11_set_1802_eq : calc11_card_1797.envelope ∩ calc11_card_1796.envelope = calc11_set_1802 := by decide +kernel

theorem calc11_set_1803_eq : calc11_set_1800 ∪ calc11_set_1802 = calc11_set_1803 := by decide +kernel

theorem calc11_finishA_1804 : calc11_set_1803.erase (3, 4) = inline_878.required := by decide +kernel

theorem calc11_finishT_1804 : insert (3, 4) calc11_set_1801 = inline_878.envelope := by decide +kernel

theorem eq_inline_878 : inline_878 = combine (3, 4) [placed 6 (5, 4) card_0, placed 4 (5, 2) card_307] := by
  rw [calc11_card_1796_eq, calc11_card_1797_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1798_eq, calc11_set_1800_eq, calc11_set_1802_eq, calc11_set_1803_eq, calc11_finishA_1804]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1799_eq, calc11_set_1801_eq, calc11_finishT_1804]
  · decide +kernel

theorem valid_inline_878 : Valid inline_878 := by
  rw [eq_inline_878]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 4) valid_0
  subst c
  exact placed_valid 4 (5, 2) valid_307

theorem calc11_card_1805_eq : placed 6 (5, 4) card_0 = calc11_card_1805 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1806_eq : placed 0 (2, 1) card_267 = calc11_card_1806 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1807_eq : calc11_card_1806.required ∪ ∅ = calc11_set_1807 := by decide +kernel

theorem calc11_set_1808_eq : calc11_card_1806.envelope ∪ ∅ = calc11_set_1808 := by decide +kernel

theorem calc11_set_1809_eq : calc11_card_1805.required ∪ calc11_set_1807 = calc11_set_1809 := by decide +kernel

theorem calc11_set_1810_eq : calc11_card_1805.envelope ∪ calc11_set_1808 = calc11_set_1810 := by decide +kernel

theorem calc11_set_1811_eq : calc11_card_1806.envelope ∩ calc11_card_1805.envelope = calc11_set_1811 := by decide +kernel

theorem calc11_set_1812_eq : calc11_set_1809 ∪ calc11_set_1811 = calc11_set_1812 := by decide +kernel

theorem calc11_finishA_1813 : calc11_set_1812.erase (3, 4) = inline_879.required := by decide +kernel

theorem calc11_finishT_1813 : insert (3, 4) calc11_set_1810 = inline_879.envelope := by decide +kernel

theorem eq_inline_879 : inline_879 = combine (3, 4) [placed 6 (5, 4) card_0, placed 0 (2, 1) card_267] := by
  rw [calc11_card_1805_eq, calc11_card_1806_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1807_eq, calc11_set_1809_eq, calc11_set_1811_eq, calc11_set_1812_eq, calc11_finishA_1813]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1808_eq, calc11_set_1810_eq, calc11_finishT_1813]
  · decide +kernel

theorem valid_inline_879 : Valid inline_879 := by
  rw [eq_inline_879]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 4) valid_0
  subst c
  exact placed_valid 0 (2, 1) valid_267

theorem calc11_card_1814_eq : placed 4 (5, 1) card_13 = calc11_card_1814 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1815_eq : placed 2 (1, 6) card_176 = calc11_card_1815 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1816_eq : inline_879.required ∪ ∅ = calc11_set_1816 := by decide +kernel

theorem calc11_set_1817_eq : inline_879.envelope ∪ ∅ = calc11_set_1817 := by decide +kernel

theorem calc11_set_1818_eq : inline_878.required ∪ calc11_set_1816 = calc11_set_1818 := by decide +kernel

theorem calc11_set_1819_eq : inline_878.envelope ∪ calc11_set_1817 = calc11_set_1819 := by decide +kernel

theorem calc11_set_1820_eq : inline_877.required ∪ calc11_set_1818 = calc11_set_1820 := by decide +kernel

theorem calc11_set_1821_eq : inline_877.envelope ∪ calc11_set_1819 = calc11_set_1821 := by decide +kernel

theorem calc11_set_1822_eq : inline_876.required ∪ calc11_set_1820 = calc11_set_1822 := by decide +kernel

theorem calc11_set_1823_eq : inline_876.envelope ∪ calc11_set_1821 = calc11_set_1823 := by decide +kernel

theorem calc11_set_1824_eq : calc11_card_1815.required ∪ calc11_set_1822 = calc11_set_1824 := by decide +kernel

theorem calc11_set_1825_eq : calc11_card_1815.envelope ∪ calc11_set_1823 = calc11_set_1825 := by decide +kernel

theorem calc11_set_1826_eq : calc11_card_1814.required ∪ calc11_set_1824 = calc11_set_1826 := by decide +kernel

theorem calc11_set_1827_eq : calc11_card_1814.envelope ∪ calc11_set_1825 = calc11_set_1827 := by decide +kernel

theorem calc11_set_1828_eq : inline_879.envelope ∩ calc11_card_1814.envelope = calc11_set_1828 := by decide +kernel

theorem calc11_set_1829_eq : inline_878.envelope ∩ calc11_set_1828 = calc11_set_1829 := by decide +kernel

theorem calc11_set_1830_eq : inline_877.envelope ∩ calc11_set_1829 = calc11_set_1830 := by decide +kernel

theorem calc11_set_1831_eq : inline_876.envelope ∩ calc11_set_1830 = calc11_set_1831 := by decide +kernel

theorem calc11_set_1832_eq : calc11_card_1815.envelope ∩ calc11_set_1831 = calc11_set_1832 := by decide +kernel

theorem calc11_set_1833_eq : calc11_set_1826 ∪ calc11_set_1832 = calc11_set_1833 := by decide +kernel

theorem calc11_finishA_1834 : calc11_set_1833.erase (4, 4) = card_722.required := by decide +kernel

theorem calc11_finishT_1834 : insert (4, 4) calc11_set_1827 = card_722.envelope := by decide +kernel

theorem eq_card_722 : card_722 = combine (4, 4) [placed 4 (5, 1) card_13, placed 2 (1, 6) card_176, inline_876, inline_877, inline_878, inline_879] := by
  rw [calc11_card_1814_eq, calc11_card_1815_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1816_eq, calc11_set_1818_eq, calc11_set_1820_eq, calc11_set_1822_eq, calc11_set_1824_eq, calc11_set_1826_eq, calc11_set_1828_eq, calc11_set_1829_eq, calc11_set_1830_eq, calc11_set_1831_eq, calc11_set_1832_eq, calc11_set_1833_eq, calc11_finishA_1834]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1817_eq, calc11_set_1819_eq, calc11_set_1821_eq, calc11_set_1823_eq, calc11_set_1825_eq, calc11_set_1827_eq, calc11_finishT_1834]
  · decide +kernel

theorem valid_722 : Valid card_722 := by
  rw [eq_card_722]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 1) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_176
  rcases hc with rfl | hc
  · exact valid_inline_876
  rcases hc with rfl | hc
  · exact valid_inline_877
  rcases hc with rfl | hc
  · exact valid_inline_878
  subst c
  exact valid_inline_879


end OAI.Snaky21.Certificate

theorem solution : Valid card_722 ∧ True :=
  ⟨valid_722, True.intro⟩
