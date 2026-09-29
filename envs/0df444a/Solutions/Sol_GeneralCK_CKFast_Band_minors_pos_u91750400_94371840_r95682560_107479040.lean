-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u91750400_94371840_r95682560_107479040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:30:33.256213+00:00
-- url     : https://prove2.me/submissions/80a1e2b0-6b52-4b55-9f9b-013327682d7b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/64, 9/80]`, `ρ ∈ [73/640, 41/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 91750400 92405760 95682560 98631680 ⟨⟨88223203952, 88223203961⟩, ⟨84625614663, 91873190808⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 92405760 93061120 95682560 98631680 ⟨⟨87734839133, 87734839144⟩, ⟨84157326392, 91364226532⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 91750400 92405760 98631680 101580800 ⟨⟨90607418392, 90607418403⟩, ⟨87001888699, 94265054444⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 92405760 93061120 98631680 101580800 ⟨⟨90108411139, 90108411147⟩, ⟨86522952479, 93745459738⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 93061120 93716480 95682560 98631680 ⟨⟨87250982300, 87250982306⟩, ⟨83693313034, 90860011530⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 93716480 94371840 95682560 98631680 ⟨⟨86771563266, 86771563276⟩, ⟨83233508538, 90360471316⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 93061120 93716480 98631680 101580800 ⟨⟨89613976627, 89613976631⟩, ⟨86048357050, 93230677779⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 93716480 94371840 98631680 101580800 ⟨⟨89124044108, 89124044116⟩, ⟨85578035760, 92720633565⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 91750400 92405760 101580800 104529920 ⟨⟨92977328300, 92977328311⟩, ⟨89364033047, 96642439751⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 92405760 93061120 101580800 104529920 ⟨⟨92467861931, 92467861942⟩, ⟨88874629581, 96112400494⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 91750400 92405760 104529920 107479040 ⟨⟨95333144207, 95333144217⟩, ⟨91712253929, 99005561594⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 92405760 93061120 104529920 107479040 ⟨⟨94813397960, 94813397968⟩, ⟨91212559938, 98465259476⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 93061120 93716480 101580800 104529920 ⟨⟨91963030350, 91963030354⟩, ⟨88389630114, 95587234707⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 93716480 94371840 101580800 104529920 ⟨⟨91462762286, 91462762296⟩, ⟨87908967432, 95066866919⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 93061120 93716480 104529920 107479040 ⟨⟨94298345913, 94298345920⟩, ⟨90717330561, 97929888893⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 93716480 94371840 104529920 107479040 ⟨⟨93787916338, 93787916346⟩, ⟨90226498076, 97399373950⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 91750400 94371840 95682560 107479040 t = true :=
  ⟨_, (join_sr (m := 101580800) (by decide) (join_su (m := 93061120) (by decide) (join_sr (m := 98631680) (by decide) (join_su (m := 92405760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 92405760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 98631680) (by decide) (join_su (m := 93716480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 93716480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 93061120) (by decide) (join_sr (m := 104529920) (by decide) (join_su (m := 92405760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 92405760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 104529920) (by decide) (join_su (m := 93716480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 93716480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/64 : ℝ) (9/80 : ℝ) →
    rho ∈ Set.Icc (73/640 : ℝ) (41/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((91750400 : ℤ) : ℝ) / (D : ℝ)) = (7/64 : ℝ) := by norm_num [D]
  have e1 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e2 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  have e3 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
