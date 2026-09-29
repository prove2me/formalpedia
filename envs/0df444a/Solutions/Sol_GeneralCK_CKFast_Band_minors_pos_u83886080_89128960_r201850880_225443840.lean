-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u83886080_89128960_r201850880_225443840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:47:55.173747+00:00
-- url     : https://prove2.me/submissions/28167bd4-e44d-4f38-884e-9be0e7645ff2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/10, 17/160]`, `ρ ∈ [77/320, 43/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 83886080 85196800 201850880 207749120 ⟨⟨176754770133, 176754770145⟩, ⟨168742106903, 184953657312⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 85196800 86507520 201850880 207749120 ⟨⟨175055228265, 175055228277⟩, ⟨167125520158, 183168206812⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 83886080 85196800 207749120 213647360 ⟨⟨180828273481, 180828273493⟩, ⟨172803677772, 189036667559⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 85196800 86507520 207749120 213647360 ⟨⟨179104924337, 179104924347⟩, ⟨171162699651, 187228082446⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 86507520 87818240 201850880 207749120 ⟨⟨173381512198, 173381512210⟩, ⟨165533090224, 181410323551⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 87818240 89128960 201850880 207749120 ⟨⟨171732938949, 171732938951⟩, ⟨163964184592, 179679271694⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 86507520 87818240 207749120 213647360 ⟨⟨177407417949, 177407417961⟩, ⟨169545926092, 185447047258⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 87818240 89128960 207749120 213647360 ⟨⟨175735077857, 175735077863⟩, ⟨167952729631, 183692834320⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 83886080 85196800 213647360 219545600 ⟨⟨184863293179, 184863293192⟩, ⟨176827394744, 193080595627⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 85196800 86507520 213647360 219545600 ⟨⟨183116883474, 183116883484⟩, ⟨175162764664, 191249627755⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 83886080 85196800 219545600 225443840 ⟨⟨188860836923, 188860836935⟩, ⟨180814235120, 197086479231⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 85196800 86507520 219545600 225443840 ⟨⟨187092083216, 187092083226⟩, ⟨179126663295, 195233849398⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 86507520 87818240 213647360 219545600 ⟨⟨181396319600, 181396319610⟩, ⟨173522372714, 189446179047⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 87818240 89128960 213647360 219545600 ⟨⟨179700931826, 179700931831⟩, ⟨171905596718, 187669530149⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 86507520 87818240 219545600 225443840 ⟨⟨185349165482, 185349165494⟩, ⟨177463349904, 193408695493⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 87818240 89128960 219545600 225443840 ⟨⟨183631420901, 183631420906⟩, ⟨175823678277, 191610306618⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 83886080 89128960 201850880 225443840 t = true :=
  ⟨_, (join_sr (m := 213647360) (by decide) (join_su (m := 86507520) (by decide) (join_sr (m := 207749120) (by decide) (join_su (m := 85196800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 85196800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 207749120) (by decide) (join_su (m := 87818240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 87818240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 86507520) (by decide) (join_sr (m := 219545600) (by decide) (join_su (m := 85196800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 85196800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 219545600) (by decide) (join_su (m := 87818240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 87818240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/10 : ℝ) (17/160 : ℝ) →
    rho ∈ Set.Icc (77/320 : ℝ) (43/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e1 : (((89128960 : ℤ) : ℝ) / (D : ℝ)) = (17/160 : ℝ) := by norm_num [D]
  have e2 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  have e3 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
