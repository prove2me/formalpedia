-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u79691776_81788928_r75038720_87162880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:40:13.833555+00:00
-- url     : https://prove2.me/submissions/f702a48a-f817-4bf0-97de-59d1d512a0b1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/200, 39/400]`, `ρ ∈ [229/2560, 133/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 79691776 80216064 75038720 78069760 ⟨⟨79513994468, 79513994477⟩, ⟨75927295427, 83155408444⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 80216064 80740352 75038720 78069760 ⟨⟨79116966912, 79116966923⟩, ⟨75549063708, 82739059301⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 79691776 80216064 78069760 81100800 ⟨⟨82319708912, 82319708923⟩, ⟨78724749756, 85968972558⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 80216064 80740352 78069760 81100800 ⟨⟨81911296034, 81911296043⟩, ⟨78335124715, 85541254060⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 80740352 81264640 75038720 78069760 ⟨⟨78723461674, 78723461683⟩, ⟨75174150359, 82326444263⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 81264640 81788928 75038720 78069760 ⟨⟨78333427108, 78333427117⟩, ⟨74802507120, 81917508135⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 80740352 81264640 78069760 81100800 ⟨⟨81506475919, 81506475930⟩, ⟨77948889608, 85117338817⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 81264640 81788928 78069760 81100800 ⟨⟨81105196287, 81105196299⟩, ⟨77565995503, 84697171041⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 79691776 80216064 81100800 84131840 ⟨⟨85103668877, 85103668886⟩, ⟨81500724827, 88760509539⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 80216064 80740352 81100800 84131840 ⟨⟨84684119150, 84684119162⟩, ⟨81099951214, 88321673792⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 79691776 80216064 84131840 87162880 ⟨⟨87866266269, 87866266278⟩, ⟨84255603882, 91530419998⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 80216064 80740352 84131840 87162880 ⟨⟨87435821330, 87435821339⟩, ⟨83843919789, 91080712073⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 80740352 81264640 81100800 84131840 ⟨⟨84268229203, 84268229212⟩, ⟨80702635721, 87886706964⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 81264640 81788928 81100800 84131840 ⟨⟨83855946167, 83855946178⟩, ⟨80308728791, 87455552726⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 80740352 81264640 84131840 87162880 ⟨⟨87009099880, 87009099891⟩, ⟨83435758750, 90634935390⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 81264640 81788928 84131840 87162880 ⟨⟨86586048535, 86586048544⟩, ⟨83031070645, 90193033140⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 79691776 81788928 75038720 87162880 t = true :=
  ⟨_, (join_sr (m := 81100800) (by decide) (join_su (m := 80740352) (by decide) (join_sr (m := 78069760) (by decide) (join_su (m := 80216064) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 80216064) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 78069760) (by decide) (join_su (m := 81264640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 81264640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 80740352) (by decide) (join_sr (m := 84131840) (by decide) (join_su (m := 80216064) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 80216064) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 84131840) (by decide) (join_su (m := 81264640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 81264640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/200 : ℝ) (39/400 : ℝ) →
    rho ∈ Set.Icc (229/2560 : ℝ) (133/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((79691776 : ℤ) : ℝ) / (D : ℝ)) = (19/200 : ℝ) := by norm_num [D]
  have e1 : (((81788928 : ℤ) : ℝ) / (D : ℝ)) = (39/400 : ℝ) := by norm_num [D]
  have e2 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  have e3 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
