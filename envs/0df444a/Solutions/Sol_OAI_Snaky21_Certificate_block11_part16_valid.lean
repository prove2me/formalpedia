-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block11_part16_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:20:01.210058+00:00
-- url     : https://prove2.me/submissions/c340db4f-c5c6-44ce-b4ed-81007067d5b0

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block03_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Definitions.Def_Snaky21Calc11Part08
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block10_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part15_valid
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
theorem valid_10 : Valid card_10 := block00_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_12 : Valid card_12 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_13 : Valid card_13 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_40 : Valid card_40 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_52 : Valid card_52 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_54 : Valid card_54 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_64 : Valid card_64 := block01_valid.1
theorem valid_180 : Valid card_180 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_197 : Valid card_197 := block03_valid.2.2.2.2.2.1
theorem valid_200 : Valid card_200 := block03_valid.2.2.2.2.2.2.2.2.1
theorem valid_201 : Valid card_201 := block03_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_310 : Valid card_310 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_315 : Valid card_315 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_369 : Valid card_369 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_474 : Valid card_474 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem calc11_card_1608_eq : placed 7 (6, 6) card_10 = calc11_card_1608 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1609_eq : placed 4 (6, 3) card_180 = calc11_card_1609 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1610_eq : placed 1 (3, 5) card_200 = calc11_card_1610 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1611_eq : calc11_card_1610.required ∪ ∅ = calc11_set_1611 := by decide +kernel

theorem calc11_set_1612_eq : calc11_card_1610.envelope ∪ ∅ = calc11_set_1612 := by decide +kernel

theorem calc11_set_1613_eq : calc11_card_1609.required ∪ calc11_set_1611 = calc11_set_1613 := by decide +kernel

theorem calc11_set_1614_eq : calc11_card_1609.envelope ∪ calc11_set_1612 = calc11_set_1614 := by decide +kernel

theorem calc11_set_1615_eq : calc11_card_1608.required ∪ calc11_set_1613 = calc11_set_1615 := by decide +kernel

theorem calc11_set_1616_eq : calc11_card_1608.envelope ∪ calc11_set_1614 = calc11_set_1616 := by decide +kernel

theorem calc11_set_1617_eq : calc11_card_1610.envelope ∩ calc11_card_1608.envelope = calc11_set_1617 := by decide +kernel

theorem calc11_set_1618_eq : calc11_card_1609.envelope ∩ calc11_set_1617 = calc11_set_1618 := by decide +kernel

theorem calc11_set_1619_eq : calc11_set_1615 ∪ calc11_set_1618 = calc11_set_1619 := by decide +kernel

theorem calc11_finishA_1620 : calc11_set_1619.erase (3, 5) = inline_864.required := by decide +kernel

theorem calc11_finishT_1620 : insert (3, 5) calc11_set_1616 = inline_864.envelope := by decide +kernel

theorem eq_inline_864 : inline_864 = combine (3, 5) [placed 7 (6, 6) card_10, placed 4 (6, 3) card_180, placed 1 (3, 5) card_200] := by
  rw [calc11_card_1608_eq, calc11_card_1609_eq, calc11_card_1610_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1611_eq, calc11_set_1613_eq, calc11_set_1615_eq, calc11_set_1617_eq, calc11_set_1618_eq, calc11_set_1619_eq, calc11_finishA_1620]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1612_eq, calc11_set_1614_eq, calc11_set_1616_eq, calc11_finishT_1620]
  · decide +kernel

theorem valid_inline_864 : Valid inline_864 := by
  rw [eq_inline_864]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 6) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 3) valid_180
  subst c
  exact placed_valid 1 (3, 5) valid_200

theorem calc11_card_1621_eq : placed 4 (7, 4) card_52 = calc11_card_1621 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1622_eq : placed 1 (4, 6) card_315 = calc11_card_1622 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1623_eq : calc11_card_1622.required ∪ ∅ = calc11_set_1623 := by decide +kernel

theorem calc11_set_1624_eq : calc11_card_1622.envelope ∪ ∅ = calc11_set_1624 := by decide +kernel

theorem calc11_set_1625_eq : calc11_card_1621.required ∪ calc11_set_1623 = calc11_set_1625 := by decide +kernel

theorem calc11_set_1626_eq : calc11_card_1621.envelope ∪ calc11_set_1624 = calc11_set_1626 := by decide +kernel

theorem calc11_set_1627_eq : calc11_card_1622.envelope ∩ calc11_card_1621.envelope = calc11_set_1627 := by decide +kernel

theorem calc11_set_1628_eq : calc11_set_1625 ∪ calc11_set_1627 = calc11_set_1628 := by decide +kernel

theorem calc11_finishA_1629 : calc11_set_1628.erase (6, 7) = inline_865.required := by decide +kernel

theorem calc11_finishT_1629 : insert (6, 7) calc11_set_1626 = inline_865.envelope := by decide +kernel

theorem eq_inline_865 : inline_865 = combine (6, 7) [placed 4 (7, 4) card_52, placed 1 (4, 6) card_315] := by
  rw [calc11_card_1621_eq, calc11_card_1622_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1623_eq, calc11_set_1625_eq, calc11_set_1627_eq, calc11_set_1628_eq, calc11_finishA_1629]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1624_eq, calc11_set_1626_eq, calc11_finishT_1629]
  · decide +kernel

theorem valid_inline_865 : Valid inline_865 := by
  rw [eq_inline_865]
  apply combination_rule (6, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 4) valid_52
  subst c
  exact placed_valid 1 (4, 6) valid_315

theorem calc11_card_1630_eq : placed 7 (8, 7) card_197 = calc11_card_1630 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1631_eq : placed 3 (8, 4) card_201 = calc11_card_1631 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1632_eq : calc11_card_1631.required ∪ ∅ = calc11_set_1632 := by decide +kernel

theorem calc11_set_1633_eq : calc11_card_1631.envelope ∪ ∅ = calc11_set_1633 := by decide +kernel

theorem calc11_set_1634_eq : calc11_card_1630.required ∪ calc11_set_1632 = calc11_set_1634 := by decide +kernel

theorem calc11_set_1635_eq : calc11_card_1630.envelope ∪ calc11_set_1633 = calc11_set_1635 := by decide +kernel

theorem calc11_set_1636_eq : calc11_card_1631.envelope ∩ calc11_card_1630.envelope = calc11_set_1636 := by decide +kernel

theorem calc11_set_1637_eq : calc11_set_1634 ∪ calc11_set_1636 = calc11_set_1637 := by decide +kernel

theorem calc11_finishA_1638 : calc11_set_1637.erase (7, 4) = inline_866.required := by decide +kernel

theorem calc11_finishT_1638 : insert (7, 4) calc11_set_1635 = inline_866.envelope := by decide +kernel

theorem eq_inline_866 : inline_866 = combine (7, 4) [placed 7 (8, 7) card_197, placed 3 (8, 4) card_201] := by
  rw [calc11_card_1630_eq, calc11_card_1631_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1632_eq, calc11_set_1634_eq, calc11_set_1636_eq, calc11_set_1637_eq, calc11_finishA_1638]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1633_eq, calc11_set_1635_eq, calc11_finishT_1638]
  · decide +kernel

theorem valid_inline_866 : Valid inline_866 := by
  rw [eq_inline_866]
  apply combination_rule (7, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 7) valid_197
  subst c
  exact placed_valid 3 (8, 4) valid_201

theorem calc11_card_1639_eq : placed 4 (8, 3) card_12 = calc11_card_1639 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1640_eq : placed 4 (8, 3) card_13 = calc11_card_1640 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1641_eq : placed 6 (8, 10) card_369 = calc11_card_1641 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1642_eq : placed 1 (5, 4) card_474 = calc11_card_1642 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1643_eq : inline_866.required ∪ ∅ = calc11_set_1643 := by decide +kernel

theorem calc11_set_1644_eq : inline_866.envelope ∪ ∅ = calc11_set_1644 := by decide +kernel

theorem calc11_set_1645_eq : inline_865.required ∪ calc11_set_1643 = calc11_set_1645 := by decide +kernel

theorem calc11_set_1646_eq : inline_865.envelope ∪ calc11_set_1644 = calc11_set_1646 := by decide +kernel

theorem calc11_set_1647_eq : calc11_card_1642.required ∪ calc11_set_1645 = calc11_set_1647 := by decide +kernel

theorem calc11_set_1648_eq : calc11_card_1642.envelope ∪ calc11_set_1646 = calc11_set_1648 := by decide +kernel

theorem calc11_set_1649_eq : calc11_card_1641.required ∪ calc11_set_1647 = calc11_set_1649 := by decide +kernel

theorem calc11_set_1650_eq : calc11_card_1641.envelope ∪ calc11_set_1648 = calc11_set_1650 := by decide +kernel

theorem calc11_set_1651_eq : calc11_card_1640.required ∪ calc11_set_1649 = calc11_set_1651 := by decide +kernel

theorem calc11_set_1652_eq : calc11_card_1640.envelope ∪ calc11_set_1650 = calc11_set_1652 := by decide +kernel

theorem calc11_set_1653_eq : calc11_card_1639.required ∪ calc11_set_1651 = calc11_set_1653 := by decide +kernel

theorem calc11_set_1654_eq : calc11_card_1639.envelope ∪ calc11_set_1652 = calc11_set_1654 := by decide +kernel

theorem calc11_set_1655_eq : inline_866.envelope ∩ calc11_card_1639.envelope = calc11_set_1655 := by decide +kernel

theorem calc11_set_1656_eq : inline_865.envelope ∩ calc11_set_1655 = calc11_set_1656 := by decide +kernel

theorem calc11_set_1657_eq : calc11_card_1642.envelope ∩ calc11_set_1656 = calc11_set_1657 := by decide +kernel

theorem calc11_set_1658_eq : calc11_card_1641.envelope ∩ calc11_set_1657 = calc11_set_1658 := by decide +kernel

theorem calc11_set_1659_eq : calc11_card_1640.envelope ∩ calc11_set_1658 = calc11_set_1659 := by decide +kernel

theorem calc11_set_1660_eq : calc11_set_1653 ∪ calc11_set_1659 = calc11_set_1660 := by decide +kernel

theorem calc11_finishA_1661 : calc11_set_1660.erase (7, 7) = inline_867.required := by decide +kernel

theorem calc11_finishT_1661 : insert (7, 7) calc11_set_1654 = inline_867.envelope := by decide +kernel

theorem eq_inline_867 : inline_867 = combine (7, 7) [placed 4 (8, 3) card_12, placed 4 (8, 3) card_13, placed 6 (8, 10) card_369, placed 1 (5, 4) card_474, inline_865, inline_866] := by
  rw [calc11_card_1639_eq, calc11_card_1640_eq, calc11_card_1641_eq, calc11_card_1642_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1643_eq, calc11_set_1645_eq, calc11_set_1647_eq, calc11_set_1649_eq, calc11_set_1651_eq, calc11_set_1653_eq, calc11_set_1655_eq, calc11_set_1656_eq, calc11_set_1657_eq, calc11_set_1658_eq, calc11_set_1659_eq, calc11_set_1660_eq, calc11_finishA_1661]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1644_eq, calc11_set_1646_eq, calc11_set_1648_eq, calc11_set_1650_eq, calc11_set_1652_eq, calc11_set_1654_eq, calc11_finishT_1661]
  · decide +kernel

theorem valid_inline_867 : Valid inline_867 := by
  rw [eq_inline_867]
  apply combination_rule (7, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (8, 3) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 4 (8, 3) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 10) valid_369
  rcases hc with rfl | hc
  · exact placed_valid 1 (5, 4) valid_474
  rcases hc with rfl | hc
  · exact valid_inline_865
  subst c
  exact valid_inline_866

theorem calc11_card_1662_eq : placed 7 (5, 8) card_0 = calc11_card_1662 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1663_eq : inline_867.required ∪ ∅ = calc11_set_1663 := by decide +kernel

theorem calc11_set_1664_eq : inline_867.envelope ∪ ∅ = calc11_set_1664 := by decide +kernel

theorem calc11_set_1665_eq : calc11_card_1662.required ∪ calc11_set_1663 = calc11_set_1665 := by decide +kernel

theorem calc11_set_1666_eq : calc11_card_1662.envelope ∪ calc11_set_1664 = calc11_set_1666 := by decide +kernel

theorem calc11_set_1667_eq : inline_867.envelope ∩ calc11_card_1662.envelope = calc11_set_1667 := by decide +kernel

theorem calc11_set_1668_eq : calc11_set_1665 ∪ calc11_set_1667 = calc11_set_1668 := by decide +kernel

theorem calc11_finishA_1669 : calc11_set_1668.erase (5, 7) = inline_868.required := by decide +kernel

theorem calc11_finishT_1669 : insert (5, 7) calc11_set_1666 = inline_868.envelope := by decide +kernel

theorem eq_inline_868 : inline_868 = combine (5, 7) [placed 7 (5, 8) card_0, inline_867] := by
  rw [calc11_card_1662_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1663_eq, calc11_set_1665_eq, calc11_set_1667_eq, calc11_set_1668_eq, calc11_finishA_1669]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1664_eq, calc11_set_1666_eq, calc11_finishT_1669]
  · decide +kernel

theorem valid_inline_868 : Valid inline_868 := by
  rw [eq_inline_868]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 8) valid_0
  subst c
  exact valid_inline_867

theorem calc11_card_1670_eq : placed 1 (3, 4) card_40 = calc11_card_1670 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1671_eq : placed 1 (3, 4) card_310 = calc11_card_1671 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1672_eq : inline_868.required ∪ ∅ = calc11_set_1672 := by decide +kernel

theorem calc11_set_1673_eq : inline_868.envelope ∪ ∅ = calc11_set_1673 := by decide +kernel

theorem calc11_set_1674_eq : calc11_card_1671.required ∪ calc11_set_1672 = calc11_set_1674 := by decide +kernel

theorem calc11_set_1675_eq : calc11_card_1671.envelope ∪ calc11_set_1673 = calc11_set_1675 := by decide +kernel

theorem calc11_set_1676_eq : calc11_card_1670.required ∪ calc11_set_1674 = calc11_set_1676 := by decide +kernel

theorem calc11_set_1677_eq : calc11_card_1670.envelope ∪ calc11_set_1675 = calc11_set_1677 := by decide +kernel

theorem calc11_set_1678_eq : inline_868.envelope ∩ calc11_card_1670.envelope = calc11_set_1678 := by decide +kernel

theorem calc11_set_1679_eq : calc11_card_1671.envelope ∩ calc11_set_1678 = calc11_set_1679 := by decide +kernel

theorem calc11_set_1680_eq : calc11_set_1676 ∪ calc11_set_1679 = calc11_set_1680 := by decide +kernel

theorem calc11_finishA_1681 : calc11_set_1680.erase (7, 5) = inline_869.required := by decide +kernel

theorem calc11_finishT_1681 : insert (7, 5) calc11_set_1677 = inline_869.envelope := by decide +kernel

theorem eq_inline_869 : inline_869 = combine (7, 5) [placed 1 (3, 4) card_40, placed 1 (3, 4) card_310, inline_868] := by
  rw [calc11_card_1670_eq, calc11_card_1671_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1672_eq, calc11_set_1674_eq, calc11_set_1676_eq, calc11_set_1678_eq, calc11_set_1679_eq, calc11_set_1680_eq, calc11_finishA_1681]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1673_eq, calc11_set_1675_eq, calc11_set_1677_eq, calc11_finishT_1681]
  · decide +kernel

theorem valid_inline_869 : Valid inline_869 := by
  rw [eq_inline_869]
  apply combination_rule (7, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 4) valid_40
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 4) valid_310
  subst c
  exact valid_inline_868

theorem calc11_card_1682_eq : placed 7 (8, 6) card_54 = calc11_card_1682 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1683_eq : placed 7 (8, 6) card_64 = calc11_card_1683 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1684_eq : inline_869.required ∪ ∅ = calc11_set_1684 := by decide +kernel

theorem calc11_set_1685_eq : inline_869.envelope ∪ ∅ = calc11_set_1685 := by decide +kernel

theorem calc11_set_1686_eq : inline_864.required ∪ calc11_set_1684 = calc11_set_1686 := by decide +kernel

theorem calc11_set_1687_eq : inline_864.envelope ∪ calc11_set_1685 = calc11_set_1687 := by decide +kernel

theorem calc11_set_1688_eq : calc11_card_1683.required ∪ calc11_set_1686 = calc11_set_1688 := by decide +kernel

theorem calc11_set_1689_eq : calc11_card_1683.envelope ∪ calc11_set_1687 = calc11_set_1689 := by decide +kernel

theorem calc11_set_1690_eq : calc11_card_1682.required ∪ calc11_set_1688 = calc11_set_1690 := by decide +kernel

theorem calc11_set_1691_eq : calc11_card_1682.envelope ∪ calc11_set_1689 = calc11_set_1691 := by decide +kernel

theorem calc11_set_1692_eq : inline_869.envelope ∩ calc11_card_1682.envelope = calc11_set_1692 := by decide +kernel

theorem calc11_set_1693_eq : inline_864.envelope ∩ calc11_set_1692 = calc11_set_1693 := by decide +kernel

theorem calc11_set_1694_eq : calc11_card_1683.envelope ∩ calc11_set_1693 = calc11_set_1694 := by decide +kernel

theorem calc11_set_1695_eq : calc11_set_1690 ∪ calc11_set_1694 = calc11_set_1695 := by decide +kernel

theorem calc11_finishA_1696 : calc11_set_1695.erase (7, 6) = card_720.required := by decide +kernel

theorem calc11_finishT_1696 : insert (7, 6) calc11_set_1691 = card_720.envelope := by decide +kernel

theorem eq_card_720 : card_720 = combine (7, 6) [placed 7 (8, 6) card_54, placed 7 (8, 6) card_64, inline_864, inline_869] := by
  rw [calc11_card_1682_eq, calc11_card_1683_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1684_eq, calc11_set_1686_eq, calc11_set_1688_eq, calc11_set_1690_eq, calc11_set_1692_eq, calc11_set_1693_eq, calc11_set_1694_eq, calc11_set_1695_eq, calc11_finishA_1696]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1685_eq, calc11_set_1687_eq, calc11_set_1689_eq, calc11_set_1691_eq, calc11_finishT_1696]
  · decide +kernel

theorem valid_720 : Valid card_720 := by
  rw [eq_card_720]
  apply combination_rule (7, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 6) valid_54
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 6) valid_64
  rcases hc with rfl | hc
  · exact valid_inline_864
  subst c
  exact valid_inline_869


end OAI.Snaky21.Certificate

theorem solution : Valid card_720 ∧ True :=
  ⟨valid_720, True.intro⟩
