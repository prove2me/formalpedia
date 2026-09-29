-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u99614720_104857600_r201850880_225443840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:50:00.464634+00:00
-- url     : https://prove2.me/submissions/13d7e285-7544-42a5-90b8-aa975bc4db3d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/160, 1/8]`, `ρ ∈ [77/320, 43/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 99614720 100925440 201850880 207749120 ⟨⟨157925862788, 157925862800⟩, ⟨150808688992, 165198123017⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 100925440 102236160 201850880 207749120 ⟨⟨156496056766, 156496056769⟩, ⟨149444743330, 163700235162⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 99614720 100925440 207749120 213647360 ⟨⟨161716028180, 161716028191⟩, ⟨154581655264, 169003926442⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 100925440 102236160 207749120 213647360 ⟨⟨160262961366, 160262961371⟩, ⟨153194151839, 167483130483⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 102236160 103546880 201850880 207749120 ⟨⟨155085284753, 155085284764⟩, ⟨148098654722, 162222607735⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 103546880 104857600 201850880 207749120 ⟨⟨153693096466, 153693096477⟩, ⟨146770004622, 160764757213⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 102236160 103546880 207749120 213647360 ⟨⟨158828999201, 158828999212⟩, ⟨151824593444, 165982646223⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 103546880 104857600 207749120 213647360 ⟨⟨157413693999, 157413694008⟩, ⟨150472563352, 164501993606⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 99614720 100925440 213647360 219545600 ⟨⟨165475800985, 165475800996⟩, ⟨158324758035, 172778820702⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 100925440 102236160 213647360 219545600 ⟨⟨164000067575, 164000067582⟩, ⟨156914282018, 171235718849⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 99614720 100925440 219545600 225443840 ⟨⟨169205883323, 169205883332⟩, ⟨162038678899, 176523528437⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 100925440 102236160 219545600 225443840 ⟨⟨167708056897, 167708056905⟩, ⟨160605795526, 174958701622⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 102236160 103546880 213647360 219545600 ⟨⟨162543498129, 162543498140⟩, ⟨155521827677, 169712968712⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 103546880 104857600 213647360 219545600 ⟨⟨161105647769, 161105647780⟩, ⟨154146980320, 168210093902⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 102236160 103546880 219545600 225443840 ⟨⟨166229443066, 166229443077⟩, ⟨159190999762, 173414255943⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 103546880 104857600 219545600 225443840 ⟨⟨164769599947, 164769599958⟩, ⟨157793879153, 171889718849⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 99614720 104857600 201850880 225443840 t = true :=
  ⟨_, (join_sr (m := 213647360) (by decide) (join_su (m := 102236160) (by decide) (join_sr (m := 207749120) (by decide) (join_su (m := 100925440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 100925440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 207749120) (by decide) (join_su (m := 103546880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 103546880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 102236160) (by decide) (join_sr (m := 219545600) (by decide) (join_su (m := 100925440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 100925440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 219545600) (by decide) (join_su (m := 103546880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 103546880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/160 : ℝ) (1/8 : ℝ) →
    rho ∈ Set.Icc (77/320 : ℝ) (43/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((99614720 : ℤ) : ℝ) / (D : ℝ)) = (19/160 : ℝ) := by norm_num [D]
  have e1 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e2 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  have e3 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
