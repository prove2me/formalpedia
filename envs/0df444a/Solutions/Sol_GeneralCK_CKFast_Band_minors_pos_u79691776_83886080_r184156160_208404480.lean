-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u79691776_83886080_r184156160_208404480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:51:31.730218+00:00
-- url     : https://prove2.me/submissions/b2e3110b-e4a4-475e-a09e-f93a9de4e57f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/200, 1/10]`, `ρ ∈ [281/1280, 159/640]` by 12 cells of the computing
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
theorem cell0 : cellOK 79691776 80740352 184156160 190218240 ⟨⟨169901005537, 169901005547⟩, ⟨162440668842, 177526652706⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 80740352 81788928 184156160 190218240 ⟨⟨168527714318, 168527714327⟩, ⟨161134443834, 176083967711⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 79691776 80740352 190218240 196280320 ⟨⟨174301024010, 174301024023⟩, ⟨166831604985, 181933277581⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 80740352 81788928 190218240 196280320 ⟨⟨172906034363, 172906034373⟩, ⟨165503156926, 180469494120⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 81788928 82837504 184156160 190218240 ⟨⟨167172572696, 167172572706⟩, ⟨159845212116, 174660638543⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 82837504 83886080 184156160 190218240 ⟨⟨165835168048, 165835168058⟩, ⟨158572591119, 173256221087⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 81788928 82837504 190218240 196280320 ⟨⟨171529220933, 171529220946⟩, ⟨164191751982, 179025067364⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 82837504 83886080 190218240 196280320 ⟨⟨170170175126, 170170175139⟩, ⟨162897010649, 177599558283⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 79691776 81788928 196280320 202342400 ⟨⟨177943673162, 177943673172⟩, ⟨166877557037, 189371132565⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 79691776 81788928 202342400 208404480 ⟨⟨182240722814, 182240722826⟩, ⟨171154701341, 193683283293⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 81788928 83886080 196280320 202342400 ⟨⟨175148107700, 175148107713⟩, ⟨164264549128, 186383822573⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 81788928 83886080 202342400 208404480 ⟨⟨179404760824, 179404760836⟩, ⟨168499952315, 190657210072⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 79691776 83886080 184156160 208404480 t = true :=
  ⟨_, (join_sr (m := 196280320) (by decide) (join_su (m := 81788928) (by decide) (join_sr (m := 190218240) (by decide) (join_su (m := 80740352) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 80740352) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 190218240) (by decide) (join_su (m := 82837504) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 82837504) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 81788928) (by decide) (join_sr (m := 202342400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 202342400) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/200 : ℝ) (1/10 : ℝ) →
    rho ∈ Set.Icc (281/1280 : ℝ) (159/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((79691776 : ℤ) : ℝ) / (D : ℝ)) = (19/200 : ℝ) := by norm_num [D]
  have e1 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e2 : (((184156160 : ℤ) : ℝ) / (D : ℝ)) = (281/1280 : ℝ) := by norm_num [D]
  have e3 : (((208404480 : ℤ) : ℝ) / (D : ℝ)) = (159/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
