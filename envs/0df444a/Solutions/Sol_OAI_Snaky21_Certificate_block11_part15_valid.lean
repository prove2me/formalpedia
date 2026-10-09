-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block11_part15_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:19:30.08231+00:00
-- url     : https://prove2.me/submissions/d0f61438-0b6d-4aba-b53f-fcdb560ba224

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block03_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Definitions.Def_Snaky21Calc11Part07
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block10_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part14_valid
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
theorem valid_1 : Valid card_1 := block00_valid.2.1
theorem valid_5 : Valid card_5 := block00_valid.2.2.2.2.2.1
theorem valid_15 : Valid card_15 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_45 : Valid card_45 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_53 : Valid card_53 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_65 : Valid card_65 := block01_valid.2.1
theorem valid_72 : Valid card_72 := block01_valid.2.2.2.2.2.2.2.2.1
theorem valid_209 : Valid card_209 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_301 : Valid card_301 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_318 : Valid card_318 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_334 : Valid card_334 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_343 : Valid card_343 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_412 : Valid card_412 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_417 : Valid card_417 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem calc11_card_1495_eq : placed 3 (4, 5) card_5 = calc11_card_1495 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1496_eq : placed 0 (3, 4) card_412 = calc11_card_1496 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1497_eq : calc11_card_1496.required ∪ ∅ = calc11_set_1497 := by decide +kernel

theorem calc11_set_1498_eq : calc11_card_1496.envelope ∪ ∅ = calc11_set_1498 := by decide +kernel

theorem calc11_set_1499_eq : calc11_card_1495.required ∪ calc11_set_1497 = calc11_set_1499 := by decide +kernel

theorem calc11_set_1500_eq : calc11_card_1495.envelope ∪ calc11_set_1498 = calc11_set_1500 := by decide +kernel

theorem calc11_set_1501_eq : calc11_card_1496.envelope ∩ calc11_card_1495.envelope = calc11_set_1501 := by decide +kernel

theorem calc11_set_1502_eq : calc11_set_1499 ∪ calc11_set_1501 = calc11_set_1502 := by decide +kernel

theorem calc11_finishA_1503 : calc11_set_1502.erase (3, 8) = inline_856.required := by decide +kernel

theorem calc11_finishT_1503 : insert (3, 8) calc11_set_1500 = inline_856.envelope := by decide +kernel

theorem eq_inline_856 : inline_856 = combine (3, 8) [placed 3 (4, 5) card_5, placed 0 (3, 4) card_412] := by
  rw [calc11_card_1495_eq, calc11_card_1496_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1497_eq, calc11_set_1499_eq, calc11_set_1501_eq, calc11_set_1502_eq, calc11_finishA_1503]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1498_eq, calc11_set_1500_eq, calc11_finishT_1503]
  · decide +kernel

theorem valid_inline_856 : Valid inline_856 := by
  rw [eq_inline_856]
  apply combination_rule (3, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 5) valid_5
  subst c
  exact placed_valid 0 (3, 4) valid_412

theorem calc11_card_1504_eq : placed 5 (2, 8) card_45 = calc11_card_1504 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1505_eq : placed 3 (6, 5) card_343 = calc11_card_1505 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1506_eq : inline_856.required ∪ ∅ = calc11_set_1506 := by decide +kernel

theorem calc11_set_1507_eq : inline_856.envelope ∪ ∅ = calc11_set_1507 := by decide +kernel

theorem calc11_set_1508_eq : calc11_card_1505.required ∪ calc11_set_1506 = calc11_set_1508 := by decide +kernel

theorem calc11_set_1509_eq : calc11_card_1505.envelope ∪ calc11_set_1507 = calc11_set_1509 := by decide +kernel

theorem calc11_set_1510_eq : calc11_card_1504.required ∪ calc11_set_1508 = calc11_set_1510 := by decide +kernel

theorem calc11_set_1511_eq : calc11_card_1504.envelope ∪ calc11_set_1509 = calc11_set_1511 := by decide +kernel

theorem calc11_set_1512_eq : inline_856.envelope ∩ calc11_card_1504.envelope = calc11_set_1512 := by decide +kernel

theorem calc11_set_1513_eq : calc11_card_1505.envelope ∩ calc11_set_1512 = calc11_set_1513 := by decide +kernel

theorem calc11_set_1514_eq : calc11_set_1510 ∪ calc11_set_1513 = calc11_set_1514 := by decide +kernel

theorem calc11_finishA_1515 : calc11_set_1514.erase (4, 5) = inline_857.required := by decide +kernel

theorem calc11_finishT_1515 : insert (4, 5) calc11_set_1511 = inline_857.envelope := by decide +kernel

theorem eq_inline_857 : inline_857 = combine (4, 5) [placed 5 (2, 8) card_45, placed 3 (6, 5) card_343, inline_856] := by
  rw [calc11_card_1504_eq, calc11_card_1505_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1506_eq, calc11_set_1508_eq, calc11_set_1510_eq, calc11_set_1512_eq, calc11_set_1513_eq, calc11_set_1514_eq, calc11_finishA_1515]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1507_eq, calc11_set_1509_eq, calc11_set_1511_eq, calc11_finishT_1515]
  · decide +kernel

theorem valid_inline_857 : Valid inline_857 := by
  rw [eq_inline_857]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 8) valid_45
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 5) valid_343
  subst c
  exact valid_inline_856

theorem calc11_card_1516_eq : placed 7 (4, 9) card_0 = calc11_card_1516 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1517_eq : inline_857.required ∪ ∅ = calc11_set_1517 := by decide +kernel

theorem calc11_set_1518_eq : inline_857.envelope ∪ ∅ = calc11_set_1518 := by decide +kernel

theorem calc11_set_1519_eq : calc11_card_1516.required ∪ calc11_set_1517 = calc11_set_1519 := by decide +kernel

theorem calc11_set_1520_eq : calc11_card_1516.envelope ∪ calc11_set_1518 = calc11_set_1520 := by decide +kernel

theorem calc11_set_1521_eq : inline_857.envelope ∩ calc11_card_1516.envelope = calc11_set_1521 := by decide +kernel

theorem calc11_set_1522_eq : calc11_set_1519 ∪ calc11_set_1521 = calc11_set_1522 := by decide +kernel

theorem calc11_finishA_1523 : calc11_set_1522.erase (4, 8) = inline_858.required := by decide +kernel

theorem calc11_finishT_1523 : insert (4, 8) calc11_set_1520 = inline_858.envelope := by decide +kernel

theorem eq_inline_858 : inline_858 = combine (4, 8) [placed 7 (4, 9) card_0, inline_857] := by
  rw [calc11_card_1516_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1517_eq, calc11_set_1519_eq, calc11_set_1521_eq, calc11_set_1522_eq, calc11_finishA_1523]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1518_eq, calc11_set_1520_eq, calc11_finishT_1523]
  · decide +kernel

theorem valid_inline_858 : Valid inline_858 := by
  rw [eq_inline_858]
  apply combination_rule (4, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 9) valid_0
  subst c
  exact valid_inline_857

theorem calc11_card_1524_eq : placed 1 (3, 3) card_1 = calc11_card_1524 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1525_eq : inline_858.required ∪ ∅ = calc11_set_1525 := by decide +kernel

theorem calc11_set_1526_eq : inline_858.envelope ∪ ∅ = calc11_set_1526 := by decide +kernel

theorem calc11_set_1527_eq : calc11_card_1524.required ∪ calc11_set_1525 = calc11_set_1527 := by decide +kernel

theorem calc11_set_1528_eq : calc11_card_1524.envelope ∪ calc11_set_1526 = calc11_set_1528 := by decide +kernel

theorem calc11_set_1529_eq : inline_858.envelope ∩ calc11_card_1524.envelope = calc11_set_1529 := by decide +kernel

theorem calc11_set_1530_eq : calc11_set_1527 ∪ calc11_set_1529 = calc11_set_1530 := by decide +kernel

theorem calc11_finishA_1531 : calc11_set_1530.erase (4, 7) = inline_859.required := by decide +kernel

theorem calc11_finishT_1531 : insert (4, 7) calc11_set_1528 = inline_859.envelope := by decide +kernel

theorem eq_inline_859 : inline_859 = combine (4, 7) [placed 1 (3, 3) card_1, inline_858] := by
  rw [calc11_card_1524_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1525_eq, calc11_set_1527_eq, calc11_set_1529_eq, calc11_set_1530_eq, calc11_finishA_1531]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1526_eq, calc11_set_1528_eq, calc11_finishT_1531]
  · decide +kernel

theorem valid_inline_859 : Valid inline_859 := by
  rw [eq_inline_859]
  apply combination_rule (4, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 3) valid_1
  subst c
  exact valid_inline_858

theorem calc11_card_1532_eq : placed 1 (0, 5) card_53 = calc11_card_1532 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1533_eq : placed 7 (6, 6) card_53 = calc11_card_1533 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1534_eq : placed 7 (5, 6) card_209 = calc11_card_1534 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1535_eq : inline_859.required ∪ ∅ = calc11_set_1535 := by decide +kernel

theorem calc11_set_1536_eq : inline_859.envelope ∪ ∅ = calc11_set_1536 := by decide +kernel

theorem calc11_set_1537_eq : calc11_card_1534.required ∪ calc11_set_1535 = calc11_set_1537 := by decide +kernel

theorem calc11_set_1538_eq : calc11_card_1534.envelope ∪ calc11_set_1536 = calc11_set_1538 := by decide +kernel

theorem calc11_set_1539_eq : calc11_card_1533.required ∪ calc11_set_1537 = calc11_set_1539 := by decide +kernel

theorem calc11_set_1540_eq : calc11_card_1533.envelope ∪ calc11_set_1538 = calc11_set_1540 := by decide +kernel

theorem calc11_set_1541_eq : calc11_card_1532.required ∪ calc11_set_1539 = calc11_set_1541 := by decide +kernel

theorem calc11_set_1542_eq : calc11_card_1532.envelope ∪ calc11_set_1540 = calc11_set_1542 := by decide +kernel

theorem calc11_set_1543_eq : inline_859.envelope ∩ calc11_card_1532.envelope = calc11_set_1543 := by decide +kernel

theorem calc11_set_1544_eq : calc11_card_1534.envelope ∩ calc11_set_1543 = calc11_set_1544 := by decide +kernel

theorem calc11_set_1545_eq : calc11_card_1533.envelope ∩ calc11_set_1544 = calc11_set_1545 := by decide +kernel

theorem calc11_set_1546_eq : calc11_set_1541 ∪ calc11_set_1545 = calc11_set_1546 := by decide +kernel

theorem calc11_finishA_1547 : calc11_set_1546.erase (4, 6) = inline_860.required := by decide +kernel

theorem calc11_finishT_1547 : insert (4, 6) calc11_set_1542 = inline_860.envelope := by decide +kernel

theorem eq_inline_860 : inline_860 = combine (4, 6) [placed 1 (0, 5) card_53, placed 7 (6, 6) card_53, placed 7 (5, 6) card_209, inline_859] := by
  rw [calc11_card_1532_eq, calc11_card_1533_eq, calc11_card_1534_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1535_eq, calc11_set_1537_eq, calc11_set_1539_eq, calc11_set_1541_eq, calc11_set_1543_eq, calc11_set_1544_eq, calc11_set_1545_eq, calc11_set_1546_eq, calc11_finishA_1547]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1536_eq, calc11_set_1538_eq, calc11_set_1540_eq, calc11_set_1542_eq, calc11_finishT_1547]
  · decide +kernel

theorem valid_inline_860 : Valid inline_860 := by
  rw [eq_inline_860]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 5) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 6) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 6) valid_209
  subst c
  exact valid_inline_859

theorem calc11_card_1548_eq : placed 0 (2, 2) card_53 = calc11_card_1548 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1549_eq : placed 6 (3, 8) card_53 = calc11_card_1549 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1550_eq : placed 6 (3, 7) card_209 = calc11_card_1550 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1551_eq : inline_860.required ∪ ∅ = calc11_set_1551 := by decide +kernel

theorem calc11_set_1552_eq : inline_860.envelope ∪ ∅ = calc11_set_1552 := by decide +kernel

theorem calc11_set_1553_eq : calc11_card_1550.required ∪ calc11_set_1551 = calc11_set_1553 := by decide +kernel

theorem calc11_set_1554_eq : calc11_card_1550.envelope ∪ calc11_set_1552 = calc11_set_1554 := by decide +kernel

theorem calc11_set_1555_eq : calc11_card_1549.required ∪ calc11_set_1553 = calc11_set_1555 := by decide +kernel

theorem calc11_set_1556_eq : calc11_card_1549.envelope ∪ calc11_set_1554 = calc11_set_1556 := by decide +kernel

theorem calc11_set_1557_eq : calc11_card_1548.required ∪ calc11_set_1555 = calc11_set_1557 := by decide +kernel

theorem calc11_set_1558_eq : calc11_card_1548.envelope ∪ calc11_set_1556 = calc11_set_1558 := by decide +kernel

theorem calc11_set_1559_eq : inline_860.envelope ∩ calc11_card_1548.envelope = calc11_set_1559 := by decide +kernel

theorem calc11_set_1560_eq : calc11_card_1550.envelope ∩ calc11_set_1559 = calc11_set_1560 := by decide +kernel

theorem calc11_set_1561_eq : calc11_card_1549.envelope ∩ calc11_set_1560 = calc11_set_1561 := by decide +kernel

theorem calc11_set_1562_eq : calc11_set_1557 ∪ calc11_set_1561 = calc11_set_1562 := by decide +kernel

theorem calc11_finishA_1563 : calc11_set_1562.erase (3, 6) = inline_861.required := by decide +kernel

theorem calc11_finishT_1563 : insert (3, 6) calc11_set_1558 = inline_861.envelope := by decide +kernel

theorem eq_inline_861 : inline_861 = combine (3, 6) [placed 0 (2, 2) card_53, placed 6 (3, 8) card_53, placed 6 (3, 7) card_209, inline_860] := by
  rw [calc11_card_1548_eq, calc11_card_1549_eq, calc11_card_1550_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1551_eq, calc11_set_1553_eq, calc11_set_1555_eq, calc11_set_1557_eq, calc11_set_1559_eq, calc11_set_1560_eq, calc11_set_1561_eq, calc11_set_1562_eq, calc11_finishA_1563]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1552_eq, calc11_set_1554_eq, calc11_set_1556_eq, calc11_set_1558_eq, calc11_finishT_1563]
  · decide +kernel

theorem valid_inline_861 : Valid inline_861 := by
  rw [eq_inline_861]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 8) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 7) valid_209
  subst c
  exact valid_inline_860

theorem calc11_card_1564_eq : placed 0 (2, 1) card_65 = calc11_card_1564 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1565_eq : placed 1 (0, 3) card_301 = calc11_card_1565 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1566_eq : placed 7 (5, 5) card_417 = calc11_card_1566 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1567_eq : calc11_card_1566.required ∪ ∅ = calc11_set_1567 := by decide +kernel

theorem calc11_set_1568_eq : calc11_card_1566.envelope ∪ ∅ = calc11_set_1568 := by decide +kernel

theorem calc11_set_1569_eq : calc11_card_1565.required ∪ calc11_set_1567 = calc11_set_1569 := by decide +kernel

theorem calc11_set_1570_eq : calc11_card_1565.envelope ∪ calc11_set_1568 = calc11_set_1570 := by decide +kernel

theorem calc11_set_1571_eq : calc11_card_1564.required ∪ calc11_set_1569 = calc11_set_1571 := by decide +kernel

theorem calc11_set_1572_eq : calc11_card_1564.envelope ∪ calc11_set_1570 = calc11_set_1572 := by decide +kernel

theorem calc11_set_1573_eq : calc11_card_1566.envelope ∩ calc11_card_1564.envelope = calc11_set_1573 := by decide +kernel

theorem calc11_set_1574_eq : calc11_card_1565.envelope ∩ calc11_set_1573 = calc11_set_1574 := by decide +kernel

theorem calc11_set_1575_eq : calc11_set_1571 ∪ calc11_set_1574 = calc11_set_1575 := by decide +kernel

theorem calc11_finishA_1576 : calc11_set_1575.erase (3, 4) = inline_862.required := by decide +kernel

theorem calc11_finishT_1576 : insert (3, 4) calc11_set_1572 = inline_862.envelope := by decide +kernel

theorem eq_inline_862 : inline_862 = combine (3, 4) [placed 0 (2, 1) card_65, placed 1 (0, 3) card_301, placed 7 (5, 5) card_417] := by
  rw [calc11_card_1564_eq, calc11_card_1565_eq, calc11_card_1566_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1567_eq, calc11_set_1569_eq, calc11_set_1571_eq, calc11_set_1573_eq, calc11_set_1574_eq, calc11_set_1575_eq, calc11_finishA_1576]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1568_eq, calc11_set_1570_eq, calc11_set_1572_eq, calc11_finishT_1576]
  · decide +kernel

theorem valid_inline_862 : Valid inline_862 := by
  rw [eq_inline_862]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_65
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_301
  subst c
  exact placed_valid 7 (5, 5) valid_417

theorem calc11_card_1577_eq : placed 4 (3, 2) card_15 = calc11_card_1577 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1578_eq : placed 0 (2, 1) card_65 = calc11_card_1578 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1579_eq : placed 1 (1, 3) card_72 = calc11_card_1579 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1580_eq : calc11_card_1579.required ∪ ∅ = calc11_set_1580 := by decide +kernel

theorem calc11_set_1581_eq : calc11_card_1579.envelope ∪ ∅ = calc11_set_1581 := by decide +kernel

theorem calc11_set_1582_eq : calc11_card_1578.required ∪ calc11_set_1580 = calc11_set_1582 := by decide +kernel

theorem calc11_set_1583_eq : calc11_card_1578.envelope ∪ calc11_set_1581 = calc11_set_1583 := by decide +kernel

theorem calc11_set_1584_eq : calc11_card_1577.required ∪ calc11_set_1582 = calc11_set_1584 := by decide +kernel

theorem calc11_set_1585_eq : calc11_card_1577.envelope ∪ calc11_set_1583 = calc11_set_1585 := by decide +kernel

theorem calc11_set_1586_eq : calc11_card_1579.envelope ∩ calc11_card_1577.envelope = calc11_set_1586 := by decide +kernel

theorem calc11_set_1587_eq : calc11_card_1578.envelope ∩ calc11_set_1586 = calc11_set_1587 := by decide +kernel

theorem calc11_set_1588_eq : calc11_set_1584 ∪ calc11_set_1587 = calc11_set_1588 := by decide +kernel

theorem calc11_finishA_1589 : calc11_set_1588.erase (3, 4) = inline_863.required := by decide +kernel

theorem calc11_finishT_1589 : insert (3, 4) calc11_set_1585 = inline_863.envelope := by decide +kernel

theorem eq_inline_863 : inline_863 = combine (3, 4) [placed 4 (3, 2) card_15, placed 0 (2, 1) card_65, placed 1 (1, 3) card_72] := by
  rw [calc11_card_1577_eq, calc11_card_1578_eq, calc11_card_1579_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1580_eq, calc11_set_1582_eq, calc11_set_1584_eq, calc11_set_1586_eq, calc11_set_1587_eq, calc11_set_1588_eq, calc11_finishA_1589]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1581_eq, calc11_set_1583_eq, calc11_set_1585_eq, calc11_finishT_1589]
  · decide +kernel

theorem valid_inline_863 : Valid inline_863 := by
  rw [eq_inline_863]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 2) valid_15
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_65
  subst c
  exact placed_valid 1 (1, 3) valid_72

theorem calc11_card_1590_eq : placed 4 (3, 0) card_318 = calc11_card_1590 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1591_eq : placed 2 (2, 7) card_334 = calc11_card_1591 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1592_eq : inline_863.required ∪ ∅ = calc11_set_1592 := by decide +kernel

theorem calc11_set_1593_eq : inline_863.envelope ∪ ∅ = calc11_set_1593 := by decide +kernel

theorem calc11_set_1594_eq : inline_862.required ∪ calc11_set_1592 = calc11_set_1594 := by decide +kernel

theorem calc11_set_1595_eq : inline_862.envelope ∪ calc11_set_1593 = calc11_set_1595 := by decide +kernel

theorem calc11_set_1596_eq : inline_861.required ∪ calc11_set_1594 = calc11_set_1596 := by decide +kernel

theorem calc11_set_1597_eq : inline_861.envelope ∪ calc11_set_1595 = calc11_set_1597 := by decide +kernel

theorem calc11_set_1598_eq : calc11_card_1591.required ∪ calc11_set_1596 = calc11_set_1598 := by decide +kernel

theorem calc11_set_1599_eq : calc11_card_1591.envelope ∪ calc11_set_1597 = calc11_set_1599 := by decide +kernel

theorem calc11_set_1600_eq : calc11_card_1590.required ∪ calc11_set_1598 = calc11_set_1600 := by decide +kernel

theorem calc11_set_1601_eq : calc11_card_1590.envelope ∪ calc11_set_1599 = calc11_set_1601 := by decide +kernel

theorem calc11_set_1602_eq : inline_863.envelope ∩ calc11_card_1590.envelope = calc11_set_1602 := by decide +kernel

theorem calc11_set_1603_eq : inline_862.envelope ∩ calc11_set_1602 = calc11_set_1603 := by decide +kernel

theorem calc11_set_1604_eq : inline_861.envelope ∩ calc11_set_1603 = calc11_set_1604 := by decide +kernel

theorem calc11_set_1605_eq : calc11_card_1591.envelope ∩ calc11_set_1604 = calc11_set_1605 := by decide +kernel

theorem calc11_set_1606_eq : calc11_set_1600 ∪ calc11_set_1605 = calc11_set_1606 := by decide +kernel

theorem calc11_finishA_1607 : calc11_set_1606.erase (3, 3) = card_719.required := by decide +kernel

theorem calc11_finishT_1607 : insert (3, 3) calc11_set_1601 = card_719.envelope := by decide +kernel

theorem eq_card_719 : card_719 = combine (3, 3) [placed 4 (3, 0) card_318, placed 2 (2, 7) card_334, inline_861, inline_862, inline_863] := by
  rw [calc11_card_1590_eq, calc11_card_1591_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1592_eq, calc11_set_1594_eq, calc11_set_1596_eq, calc11_set_1598_eq, calc11_set_1600_eq, calc11_set_1602_eq, calc11_set_1603_eq, calc11_set_1604_eq, calc11_set_1605_eq, calc11_set_1606_eq, calc11_finishA_1607]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1593_eq, calc11_set_1595_eq, calc11_set_1597_eq, calc11_set_1599_eq, calc11_set_1601_eq, calc11_finishT_1607]
  · decide +kernel

theorem valid_719 : Valid card_719 := by
  rw [eq_card_719]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 0) valid_318
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_334
  rcases hc with rfl | hc
  · exact valid_inline_861
  rcases hc with rfl | hc
  · exact valid_inline_862
  subst c
  exact valid_inline_863


end OAI.Snaky21.Certificate

theorem solution : Valid card_719 ∧ True :=
  ⟨valid_719, True.intro⟩
