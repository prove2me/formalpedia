-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u86507520_89128960_r83886080_95682560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:29:10.344583+00:00
-- url     : https://prove2.me/submissions/650990bf-e212-41bf-a249-81baf8c7f058

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [33/320, 17/160]`, `ρ ∈ [1/10, 73/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 86507520 87162880 83886080 86835200 ⟨⟨82250459452, 82250459459⟩, ⟨78516821808, 86042409766⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 87162880 87818240 83886080 86835200 ⟨⟨81770209946, 81770209955⟩, ⟨78058707279, 85539397126⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 86507520 87162880 86835200 89784320 ⟨⟨84788291264, 84788291271⟩, ⟨81045958517, 88588581067⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 87162880 87818240 86835200 89784320 ⟨⟨84295980934, 84295980943⟩, ⟨80575780138, 88073518901⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 87818240 88473600 83886080 86835200 ⟨⟨81294776954, 81294776962⟩, ⟨77605133737, 85041487171⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 88473600 89128960 83886080 86835200 ⟨⟨80824079859, 80824079870⟩, ⟨77156025805, 84548593810⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 87818240 88473600 86835200 89784320 ⟨⟨83808570251, 83808570260⟩, ⟨80110227190, 87563641029⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 88473600 89128960 86835200 89784320 ⟨⟨83325977757, 83325977768⟩, ⟨79649223393, 87058860579⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 86507520 87162880 89784320 92733440 ⟨⟨87309205459, 87309205463⟩, ⟨83558397516, 91117616337⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 87162880 87818240 89784320 92733440 ⟨⟨86805062356, 86805062367⟩, ⟨83076379834, 90590736124⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 86507520 87162880 92733440 95682560 ⟨⟨89813471310, 89813471312⟩, ⟨86054402144, 93629790818⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 87162880 87818240 92733440 95682560 ⟨⟨89297717969, 89297717980⟩, ⟨85560764335, 93091318368⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 87818240 88473600 89784320 92733440 ⟨⟨86305898401, 86305898412⟩, ⟨82599068444, 90069118126⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 88473600 89128960 89784320 92733440 ⟨⟨85811631361, 85811631372⟩, ⟨82126386241, 89552674758⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 87818240 88473600 92733440 95682560 ⟨⟨88787019769, 88787019780⟩, ⟨85071910223, 92558182501⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 88473600 89128960 92733440 95682560 ⟨⟨88281293771, 88281293783⟩, ⟨84587761952, 92030294983⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 86507520 89128960 83886080 95682560 t = true :=
  ⟨_, (join_sr (m := 89784320) (by decide) (join_su (m := 87818240) (by decide) (join_sr (m := 86835200) (by decide) (join_su (m := 87162880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 87162880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 86835200) (by decide) (join_su (m := 88473600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 88473600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 87818240) (by decide) (join_sr (m := 92733440) (by decide) (join_su (m := 87162880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 87162880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 92733440) (by decide) (join_su (m := 88473600) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 88473600) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (33/320 : ℝ) (17/160 : ℝ) →
    rho ∈ Set.Icc (1/10 : ℝ) (73/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((86507520 : ℤ) : ℝ) / (D : ℝ)) = (33/320 : ℝ) := by norm_num [D]
  have e1 : (((89128960 : ℤ) : ℝ) / (D : ℝ)) = (17/160 : ℝ) := by norm_num [D]
  have e2 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e3 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
