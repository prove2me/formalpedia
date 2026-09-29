-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u83886080_89128960_r178257920_201850880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:47:29.461453+00:00
-- url     : https://prove2.me/submissions/83f07e48-20ab-4410-993e-42fcabd4603e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/10, 17/160]`, `ρ ∈ [17/80, 77/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 83886080 85196800 178257920 184156160 ⟨⟨160054471714, 160054471724⟩, ⟨152096504112, 168208684921⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 85196800 86507520 178257920 184156160 ⟨⟨158458284210, 158458284220⟩, ⟨150585513415, 166523970151⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 83886080 85196800 184156160 190054400 ⟨⟨164292731728, 164292731740⟩, ⟨156319973902, 172459181195⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 85196800 86507520 184156160 190054400 ⟨⟨162669416818, 162669416828⟩, ⟨154781311982, 170747980578⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 86507520 87818240 178257920 184156160 ⟨⟨156887694416, 156887694426⟩, ⟨149098325788, 164866735533⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 87818240 89128960 178257920 184156160 ⟨⟨155341996068, 155341996073⟩, ⟨147634291740, 163236214925⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 86507520 87818240 184156160 190054400 ⟨⟨161071783014, 161071783027⟩, ⟨153266568246, 169064307735⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 87818240 89128960 184156160 190054400 ⟨⟨159499129374, 159499129379⟩, ⟨151775096890, 167407403666⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 83886080 85196800 190054400 195952640 ⟨⟨168488100278, 168488100288⟩, ⟨160501321235, 176666049569⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 85196800 86507520 190054400 195952640 ⟨⟨166838541395, 166838541408⟩, ⟨158935859612, 174929256087⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 83886080 85196800 195952640 201850880 ⟨⟨172641739495, 172641739507⟩, ⟨164641670548, 180830489568⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 85196800 86507520 195952640 201850880 ⟨⟨170966783289, 170966783301⟩, ⟨163050245246, 179068958167⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 86507520 87818240 190054400 195952640 ⟨⟨165214728621, 165214728631⟩, ⟨157394412707, 173220019927⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 87818240 89128960 190054400 195952640 ⟨⟨163615966681, 163615966687⟩, ⟨155876338802, 171537589547⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 86507520 87818240 195952640 201850880 ⟨⟨169317621030, 169317621042⟩, ⟨161482913825, 177334996844⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 87818240 89128960 195952640 201850880 ⟨⟨167693563451, 167693563456⟩, ⟨159939039014, 175627861795⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 83886080 89128960 178257920 201850880 t = true :=
  ⟨_, (join_sr (m := 190054400) (by decide) (join_su (m := 86507520) (by decide) (join_sr (m := 184156160) (by decide) (join_su (m := 85196800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 85196800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 184156160) (by decide) (join_su (m := 87818240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 87818240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 86507520) (by decide) (join_sr (m := 195952640) (by decide) (join_su (m := 85196800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 85196800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 195952640) (by decide) (join_su (m := 87818240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 87818240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/10 : ℝ) (17/160 : ℝ) →
    rho ∈ Set.Icc (17/80 : ℝ) (77/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e1 : (((89128960 : ℤ) : ℝ) / (D : ℝ)) = (17/160 : ℝ) := by norm_num [D]
  have e2 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e3 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
