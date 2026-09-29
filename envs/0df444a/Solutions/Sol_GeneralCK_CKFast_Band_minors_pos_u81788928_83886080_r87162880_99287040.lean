-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u81788928_83886080_r87162880_99287040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:40:53.685425+00:00
-- url     : https://prove2.me/submissions/375d14cd-ce15-4f72-93ed-0fd02296ab61

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [39/400, 1/10]`, `ρ ∈ [133/1280, 303/2560]` by 14 cells of the computing
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
theorem cell0 : cellOK 81788928 82313216 87162880 90193920 ⟨⟨88865952564, 88865952573⟩, ⟨85321616732, 92461441535⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 82313216 82837504 87162880 90193920 ⟨⟨88439664552, 88439664561⟩, ⟨84913293364, 92016722151⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 81788928 82313216 90193920 93224960 ⟨⟨91545579039, 91545579050⟩, ⟨87993953571, 95147986986⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 82313216 82837504 90193920 93224960 ⟨⟨91109086969, 91109086979⟩, ⟨87575409308, 94693087322⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 82837504 83361792 87162880 90193920 ⟨⟨88016951266, 88016951276⟩, ⟨84508358067, 91575770748⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 83361792 83886080 87162880 90193920 ⟨⟨87597762849, 87597762858⟩, ⟨84106763954, 91138534377⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 82837504 83361792 90193920 93224960 ⟨⟨90676225453, 90676225462⟩, ⟨87160310091, 94242010168⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 83361792 83886080 90193920 93224960 ⟨⟨90246944215, 90246944224⟩, ⟨86748608585, 93794702191⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 81788928 82313216 93224960 96256000 ⟨⟨94205834024, 94205834034⟩, ⟨90647149357, 97814932816⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 82313216 82837504 93224960 96256000 ⟨⟨93759348952, 93759348963⟩, ⟨90218592363, 97350066733⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 81788928 82837504 96256000 99287040 ⟨⟨96618442886, 96618442895⟩, ⟨91377321793, 101969546119⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 82837504 83361792 93224960 96256000 ⟨⟨93316547528, 93316547540⟩, ⟨89793534700, 96889074919⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 83361792 83886080 93224960 96256000 ⟨⟨92877379101, 92877379112⟩, ⟨89371928617, 96431903706⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 82837504 83886080 96256000 99287040 ⟨⟨95713353279, 95713353290⟩, ⟨90521770545, 101013061194⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 81788928 83886080 87162880 99287040 t = true :=
  ⟨_, (join_sr (m := 93224960) (by decide) (join_su (m := 82837504) (by decide) (join_sr (m := 90193920) (by decide) (join_su (m := 82313216) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 82313216) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 90193920) (by decide) (join_su (m := 83361792) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 83361792) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 82837504) (by decide) (join_sr (m := 96256000) (by decide) (join_su (m := 82313216) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 96256000) (by decide) (join_su (m := 83361792) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (leaf_ok cell13))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (39/400 : ℝ) (1/10 : ℝ) →
    rho ∈ Set.Icc (133/1280 : ℝ) (303/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((81788928 : ℤ) : ℝ) / (D : ℝ)) = (39/400 : ℝ) := by norm_num [D]
  have e1 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e2 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  have e3 : (((99287040 : ℤ) : ℝ) / (D : ℝ)) = (303/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
