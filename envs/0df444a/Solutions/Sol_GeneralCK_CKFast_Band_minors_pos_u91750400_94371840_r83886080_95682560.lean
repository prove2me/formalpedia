-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u91750400_94371840_r83886080_95682560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:38:28.57672+00:00
-- url     : https://prove2.me/submissions/019c4592-3176-49c1-b66e-12c7ffc41678

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/64, 9/80]`, `ρ ∈ [1/10, 73/640]` by 18 cells of the computing
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
theorem cell0 : cellOK 91750400 92405760 83886080 86835200 ⟨⟨78538936265, 78538936275⟩, ⟨74974947871, 82156497004⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 92405760 93061120 83886080 86835200 ⟨⟨78095060296, 78095060306⟩, ⟨74551142145, 81692001352⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 91750400 92405760 86835200 89784320 ⟨⟨80982562489, 80982562499⟩, ⟨77409888562, 84608513634⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 92405760 93061120 86835200 89784320 ⟨⟨80527267547, 80527267558⟩, ⟨76974669924, 84132599665⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 93061120 93716480 83886080 85360640 ⟨⟨77047850507, 77047850511⟩, ⟨74319175288, 79808015618⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 93061120 93716480 85360640 86835200 ⟨⟨78262019398, 78262019405⟩, ⟨75529542627, 81025914396⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 93716480 94371840 83886080 85360640 ⟨⟨76615194500, 76615194511⟩, ⟨73900881979, 79360692365⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 93716480 94371840 85360640 86835200 ⟨⟨77823680659, 77823680668⟩, ⟨75105572018, 80572904701⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 93061120 93716480 86835200 89784320 ⟨⟨80076269077, 80076269081⟩, ⟨76543511576, 83661227054⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 93716480 94371840 86835200 89784320 ⟨⟨79629498898, 79629498909⟩, ⟨76116349594, 83194323191⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 91750400 92405760 89784320 92733440 ⟨⟨83410997586, 83410997595⟩, ⟨79829831540, 87045146655⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 92405760 93061120 89784320 92733440 ⟨⟨82944484540, 82944484548⟩, ⟨79383397790, 86558018251⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 91750400 92405760 92733440 95682560 ⟨⟨85824470116, 85824470127⟩, ⟨82235000520, 89466629511⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 92405760 93061120 92733440 95682560 ⟨⟨85346935259, 85346935270⟩, ⟨81777545002, 88968485859⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 93061120 93716480 89784320 92733440 ⟨⟨82482341440, 82482341446⟩, ⟨78941098795, 86075503529⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 93716480 94371840 89784320 92733440 ⟨⟨82024499388, 82024499399⟩, ⟨78502869872, 85597529193⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 93061120 93716480 92733440 95682560 ⟨⟨84873840824, 84873840826⟩, ⟨81324295748, 88475025158⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 93716480 94371840 92733440 95682560 ⟨⟨84405117234, 84405117245⟩, ⟨80875187366, 87986173492⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 91750400 94371840 83886080 95682560 t = true :=
  ⟨_, (join_sr (m := 89784320) (by decide) (join_su (m := 93061120) (by decide) (join_sr (m := 86835200) (by decide) (join_su (m := 92405760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 92405760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 86835200) (by decide) (join_su (m := 93716480) (by decide) (join_sr (m := 85360640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 85360640) (by decide) (leaf_ok cell6) (leaf_ok cell7))) (join_su (m := 93716480) (by decide) (leaf_ok cell8) (leaf_ok cell9)))) (join_su (m := 93061120) (by decide) (join_sr (m := 92733440) (by decide) (join_su (m := 92405760) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_su (m := 92405760) (by decide) (leaf_ok cell12) (leaf_ok cell13))) (join_sr (m := 92733440) (by decide) (join_su (m := 93716480) (by decide) (leaf_ok cell14) (leaf_ok cell15)) (join_su (m := 93716480) (by decide) (leaf_ok cell16) (leaf_ok cell17)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/64 : ℝ) (9/80 : ℝ) →
    rho ∈ Set.Icc (1/10 : ℝ) (73/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((91750400 : ℤ) : ℝ) / (D : ℝ)) = (7/64 : ℝ) := by norm_num [D]
  have e1 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e2 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e3 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
