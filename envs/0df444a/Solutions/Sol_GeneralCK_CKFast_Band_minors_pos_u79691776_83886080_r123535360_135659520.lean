-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u79691776_83886080_r123535360_135659520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:47:45.725897+00:00
-- url     : https://prove2.me/submissions/9d41e6c0-3a25-4a6a-9772-4c85fbaf6e97

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/200, 1/10]`, `ρ ∈ [377/2560, 207/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 79691776 80740352 123535360 126566400 ⟨⟨121720985138, 121720985148⟩, ⟨116283763840, 127265444426⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 79691776 80740352 126566400 129597440 ⟨⟨124216672091, 124216672103⟩, ⟨118770386188, 129769480881⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 80740352 81788928 123535360 126566400 ⟨⟨120623927383, 120623927395⟩, ⟨115237570114, 126115804876⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 80740352 81788928 126566400 129597440 ⟨⟨123103438167, 123103438177⟩, ⟨117707898604, 128603808565⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 79691776 80740352 129597440 132628480 ⟨⟨126695945469, 126695945479⟩, ⟨121240839797, 132256863085⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 79691776 80740352 132628480 135659520 ⟨⟨129159071293, 129159071303⟩, ⟨123695383798, 134727863976⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 80740352 81788928 129597440 132628480 ⟨⟨125566855958, 125566855971⟩, ⟨120162374124, 131075483091⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 80740352 81788928 132628480 135659520 ⟨⟨128014438786, 128014438798⟩, ⟨122601248050, 133531093153⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 81788928 82837504 123535360 126566400 ⟨⟨119543754305, 119543754316⟩, ⟨114207251463, 124984103790⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 81788928 82837504 126566400 129597440 ⟨⟨122007205737, 122007205747⟩, ⟨116661411024, 127456182397⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 82837504 83886080 123535360 126566400 ⟨⟨118480030825, 118480030837⟩, ⟨113192402783, 123869874581⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 82837504 83886080 126566400 129597440 ⟨⟨120927539571, 120927539583⟩, ⟨115630517775, 126326136100⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 81788928 82837504 129597440 132628480 ⟨⟨124454877693, 124454877704⟩, ⟨119100026380, 129912249812⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 81788928 82837504 132628480 135659520 ⟨⟨126887020476, 126887020486⟩, ⟨121523341408, 132352562787⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 82837504 83886080 129597440 132628480 ⟨⟨123359575471, 123359575480⟩, ⟨118053390497, 128766697473⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 82837504 83886080 132628480 135659520 ⟨⟨125776381356, 125776381366⟩, ⟨120461257590, 131191807755⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 79691776 83886080 123535360 135659520 t = true :=
  ⟨_, (join_su (m := 81788928) (by decide) (join_sr (m := 129597440) (by decide) (join_su (m := 80740352) (by decide) (join_sr (m := 126566400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 126566400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 80740352) (by decide) (join_sr (m := 132628480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 132628480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 129597440) (by decide) (join_su (m := 82837504) (by decide) (join_sr (m := 126566400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 126566400) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 82837504) (by decide) (join_sr (m := 132628480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 132628480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/200 : ℝ) (1/10 : ℝ) →
    rho ∈ Set.Icc (377/2560 : ℝ) (207/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((79691776 : ℤ) : ℝ) / (D : ℝ)) = (19/200 : ℝ) := by norm_num [D]
  have e1 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e2 : (((123535360 : ℤ) : ℝ) / (D : ℝ)) = (377/2560 : ℝ) := by norm_num [D]
  have e3 : (((135659520 : ℤ) : ℝ) / (D : ℝ)) = (207/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
