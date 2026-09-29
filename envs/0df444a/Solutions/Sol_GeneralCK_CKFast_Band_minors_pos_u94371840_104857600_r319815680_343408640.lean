-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u94371840_104857600_r319815680_343408640
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:54:42.103176+00:00
-- url     : https://prove2.me/submissions/0457dccd-bc45-458d-a751-d9bcc9a8d0d7

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/80, 1/8]`, `ρ ∈ [61/160, 131/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 94371840 96993280 319815680 325713920 ⟨⟨235127415829, 235127415839⟩, ⟨223152632748, 247433869816⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 94371840 96993280 325713920 331612160 ⟨⟨238473048241, 238473048253⟩, ⟨226478410830, 250796018805⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 96993280 99614720 319815680 325713920 ⟨⟨231405124946, 231405124950⟩, ⟨219611284774, 243524362468⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 96993280 99614720 325713920 331612160 ⟨⟨234722213645, 234722213650⟩, ⟨222907297894, 246859386852⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 94371840 96993280 331612160 337510400 ⟨⟨241798061295, 241798061305⟩, ⟨229783982236, 254137160003⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 94371840 96993280 337510400 343408640 ⟨⟨245102895624, 245102895636⟩, ⟨233069772846, 257457748528⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 96993280 99614720 331612160 337510400 ⟨⟨238019312775, 238019312780⟩, ⟨226183730653, 250174033173⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 96993280 99614720 337510400 343408640 ⟨⟨241296842666, 241296842672⟩, ⟨229440989271, 253468735673⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 99614720 102236160 319815680 325713920 ⟨⟨227762305254, 227762305264⟩, ⟨216143981215, 239699938764⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 99614720 102236160 325713920 331612160 ⟨⟨231050536840, 231050536850⟩, ⟨219410009824, 243007420349⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 102236160 104857600 319815680 325713920 ⟨⟨224195769983, 224195769992⟩, ⟨212747780882, 235957159958⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 102236160 104857600 325713920 331612160 ⟨⟨227454867423, 227454867435⟩, ⟨215983635435, 239236723966⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 99614720 102236160 331612160 337510400 ⟨⟨234319394879, 234319394891⟩, ⟨222657069469, 246295141337⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 99614720 102236160 337510400 343408640 ⟨⟨237569280280, 237569280290⟩, ⟨225885547573, 249563515972⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 102236160 104857600 331612160 337510400 ⟨⟨230695193455, 230695193467⟩, ⟨219201117540, 242497132272⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 102236160 104857600 337510400 343408640 ⟨⟨233917130413, 233917130422⟩, ⟨222400596667, 245738779972⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 94371840 104857600 319815680 343408640 t = true :=
  ⟨_, (join_su (m := 99614720) (by decide) (join_sr (m := 331612160) (by decide) (join_su (m := 96993280) (by decide) (join_sr (m := 325713920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 325713920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 96993280) (by decide) (join_sr (m := 337510400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 337510400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 331612160) (by decide) (join_su (m := 102236160) (by decide) (join_sr (m := 325713920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 325713920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 102236160) (by decide) (join_sr (m := 337510400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 337510400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/80 : ℝ) (1/8 : ℝ) →
    rho ∈ Set.Icc (61/160 : ℝ) (131/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e1 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e2 : (((319815680 : ℤ) : ℝ) / (D : ℝ)) = (61/160 : ℝ) := by norm_num [D]
  have e3 : (((343408640 : ℤ) : ℝ) / (D : ℝ)) = (131/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
