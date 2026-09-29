-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u99614720_104857600_r166461440_178257920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:46:44.042443+00:00
-- url     : https://prove2.me/submissions/248ac208-e732-4a23-b789-64b7e1d69804

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/160, 1/8]`, `ρ ∈ [127/640, 17/80]` by 12 cells of the computing
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
theorem cell0 : cellOK 99614720 100925440 166461440 169410560 ⟨⟨133501753959, 133501753970⟩, ⟨128012262210, 139092811375⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 99614720 100925440 169410560 172359680 ⟨⟨135504944982, 135504944991⟩, ⟨130005625323, 141105395487⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 100925440 102236160 166461440 169410560 ⟨⟨132232209330, 132232209332⟩, ⟨126792469687, 137772010543⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 100925440 102236160 169410560 172359680 ⟨⟨134221555129, 134221555136⟩, ⟨128771914881, 139770839676⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 99614720 100925440 172359680 178257920 ⟨⟨138493011708, 138493011716⟩, ⟨131470556258, 145678545423⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 100925440 102236160 172359680 178257920 ⟨⟨137189208681, 137189208683⟩, ⟨130233936000, 144305043975⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 102236160 103546880 166461440 169410560 ⟨⟨130980955237, 130980955248⟩, ⟨125590001247, 136470503552⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 102236160 103546880 169410560 172359680 ⟨⟨132956537103, 132956537114⟩, ⟨127555615885, 138455652221⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 103546880 104857600 166461440 169410560 ⟨⟨129747531435, 129747531445⟩, ⟨124404424602, 135187800959⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 103546880 104857600 169410560 172359680 ⟨⟨131709430957, 131709430966⟩, ⟨126356296038, 137159344324⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 102236160 103546880 172359680 178257920 ⟨⟨135903891599, 135903891608⟩, ⟨129014538742, 142951351998⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 103546880 104857600 172359680 178257920 ⟨⟨134636601157, 134636601166⟩, ⟨127811941033, 141616972357⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 99614720 104857600 166461440 178257920 t = true :=
  ⟨_, (join_su (m := 102236160) (by decide) (join_sr (m := 172359680) (by decide) (join_su (m := 100925440) (by decide) (join_sr (m := 169410560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 169410560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 100925440) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 172359680) (by decide) (join_su (m := 103546880) (by decide) (join_sr (m := 169410560) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 169410560) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 103546880) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/160 : ℝ) (1/8 : ℝ) →
    rho ∈ Set.Icc (127/640 : ℝ) (17/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((99614720 : ℤ) : ℝ) / (D : ℝ)) = (19/160 : ℝ) := by norm_num [D]
  have e1 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e2 : (((166461440 : ℤ) : ℝ) / (D : ℝ)) = (127/640 : ℝ) := by norm_num [D]
  have e3 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
