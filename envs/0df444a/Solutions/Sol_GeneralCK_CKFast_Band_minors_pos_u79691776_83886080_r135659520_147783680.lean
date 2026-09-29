-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u79691776_83886080_r135659520_147783680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:47:59.141007+00:00
-- url     : https://prove2.me/submissions/a73bf08d-3100-487b-b8e6-60e371386173

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/200, 1/10]`, `ρ ∈ [207/1280, 451/2560]` by 15 cells of the computing
correction-band checker; each cell is kernel-checked in its own declaration. -/

theorem leaf_ok {U0 U1 R0 R1 : ℤ} {h : Hint} (hc : cellOK U0 U1 R0 R1 h = true) :
    treeOK U0 U1 R0 R1 (.leaf h) = true := by
  simpa only [treeOK] using hc

theorem join_su {U0 U1 R0 R1 m : ℤ} {l r : Tree} (hm : (decide (U0 ≤ m) && decide (m ≤ U1)) = true)
    (hl : treeOK U0 m R0 R1 l = true) (hr : treeOK m U1 R0 R1 r = true) :
    treeOK U0 U1 R0 R1 (.su m l r) = true := by
  simp only [treeOK, Bool.and_eq_true] at hm ⊢
  exact ⟨⟨hm, hl⟩, hr⟩

theorem join_sr {U0 U1 R0 R1 m : ℤ} {l r : Tree} (hm : (decide (R0 ≤ m) && decide (m ≤ R1)) = true)
    (hl : treeOK U0 U1 R0 m l = true) (hr : treeOK U0 U1 m R1 r = true) :
    treeOK U0 U1 R0 R1 (.sr m l r) = true := by
  simp only [treeOK, Bool.and_eq_true] at hm ⊢
  exact ⟨⟨hm, hl⟩, hr⟩

set_option maxRecDepth 100000 in
theorem cell0 : cellOK 79691776 80740352 135659520 138690560 ⟨⟨131606309743, 131606309752⟩, ⟨126134271696, 137182750431⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 79691776 80740352 138690560 141721600 ⟨⟨134037915316, 134037915329⟩, ⟨128557751522, 139621783431⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 80740352 81788928 135659520 138690560 ⟨⟨130446439071, 130446439081⟩, ⟨125024766356, 135970897646⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 80740352 81788928 138690560 141721600 ⟨⟨132863103785, 132863103797⟩, ⟨127433169777, 138395149803⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 79691776 80740352 141721600 147783680 ⟨⟨137656555218, 137656555230⟩, ⟨130283890707, 145212991557⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 80740352 81788928 141721600 144752640 ⟨⟨135264674612, 135264674624⟩, ⟨129826693941, 140804097374⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 80740352 81788928 144752640 147783680 ⟨⟨137651388090, 137651388100⟩, ⟨132205569526, 143197982775⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 81788928 82837504 135659520 138690560 ⟨⟨129303879008, 129303879017⟩, ⟨123931594814, 134777372489⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 81788928 82837504 138690560 141721600 ⟨⟨131705692988, 131705693000⟩, ⟨126325020266, 137186924670⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 82837504 83886080 135659520 138690560 ⟨⟨128178194906, 128178194918⟩, ⟨122854350726, 133601710658⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 82837504 83886080 138690560 141721600 ⟨⟨130565248788, 130565248797⟩, ⟨125232896747, 135996644692⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 81788928 82837504 141721600 144752640 ⟨⟨134092697039, 134092697051⟩, ⟨128703846540, 139581459817⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 81788928 82837504 144752640 147783680 ⟨⟨136465120840, 136465120853⟩, ⟨131068297651, 141961213291⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 82837504 83886080 141721600 144752640 ⟨⟨132937770786, 132937770798⟩, ⟨127597117792, 138376843315⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 82837504 83886080 144752640 147783680 ⟨⟨135295983955, 135295983967⟩, ⟨129947231434, 140742535075⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 79691776 83886080 135659520 147783680 t = true :=
  ⟨_, (join_su (m := 81788928) (by decide) (join_sr (m := 141721600) (by decide) (join_su (m := 80740352) (by decide) (join_sr (m := 138690560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 138690560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 80740352) (by decide) (leaf_ok cell4) (join_sr (m := 144752640) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_sr (m := 141721600) (by decide) (join_su (m := 82837504) (by decide) (join_sr (m := 138690560) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 138690560) (by decide) (leaf_ok cell9) (leaf_ok cell10))) (join_su (m := 82837504) (by decide) (join_sr (m := 144752640) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_sr (m := 144752640) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/200 : ℝ) (1/10 : ℝ) →
    rho ∈ Set.Icc (207/1280 : ℝ) (451/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((79691776 : ℤ) : ℝ) / (D : ℝ)) = (19/200 : ℝ) := by norm_num [D]
  have e1 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e2 : (((135659520 : ℤ) : ℝ) / (D : ℝ)) = (207/1280 : ℝ) := by norm_num [D]
  have e3 : (((147783680 : ℤ) : ℝ) / (D : ℝ)) = (451/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
