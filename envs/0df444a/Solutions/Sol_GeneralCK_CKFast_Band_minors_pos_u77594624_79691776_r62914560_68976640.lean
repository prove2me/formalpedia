-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u77594624_79691776_r62914560_68976640
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:31:58.775106+00:00
-- url     : https://prove2.me/submissions/96442033-e718-4f51-b0d1-582e9715d706

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/400, 19/200]`, `ρ ∈ [3/40, 421/5120]` by 16 cells of the computing
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
theorem cell0 : cellOK 77594624 78118912 62914560 64430080 ⟨⟨68753070997, 68753071006⟩, ⟨66083124649, 71455015372⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 77594624 78118912 64430080 65945600 ⟨⟨70233070685, 70233070696⟩, ⟨67559131611, 72938899690⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 78118912 78643200 62914560 64430080 ⟨⟨68394145992, 68394146003⟩, ⟨65738034865, 71081943262⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 78118912 78643200 64430080 65945600 ⟨⟨69867667862, 69867667871⟩, ⟨67207568819, 72559347218⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 77594624 78118912 65945600 67461120 ⟨⟨71706835372, 71706835381⟩, ⟨69028964450, 74416488320⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 77594624 78118912 67461120 68976640 ⟨⟨73174425081, 73174425092⟩, ⟨70492682199, 75887842288⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 78118912 78643200 65945600 67461120 ⟨⟨71335030232, 71335030244⟩, ⟨68671003252, 74030531887⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 78118912 78643200 67461120 68976640 ⟨⟨72796292022, 72796292031⟩, ⟨70128396106, 75495557155⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 78643200 79167488 62914560 64430080 ⟨⟨68038605171, 68038605180⟩, ⟨65396170140, 70712419349⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 78643200 79167488 64430080 65945600 ⟨⟨69505695089, 69505695101⟩, ⟨66859277271, 72183388445⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 79167488 79691776 62914560 64430080 ⟨⟨67686396128, 67686396139⟩, ⟨65057480852, 70346388352⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 79167488 79691776 64430080 65945600 ⟨⟨69147099470, 69147099479⟩, ⟨66514206838, 71810967603⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 78643200 79167488 65945600 67461120 ⟨⟨70966699889, 70966699898⟩, ⟨68316358369, 73648213509⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 78643200 79167488 67461120 68976640 ⟨⟨72421677390, 72421677402⟩, ⟨69767470309, 75106953315⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 79167488 79691776 65945600 67461120 ⟨⟨70601790956, 70601790967⟩, ⟨67964979179, 73269476951⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 79167488 79691776 67461120 68976640 ⟨⟨72050527350, 72050527359⟩, ⟨69409853717, 74721974084⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 77594624 79691776 62914560 68976640 t = true :=
  ⟨_, (join_su (m := 78643200) (by decide) (join_sr (m := 65945600) (by decide) (join_su (m := 78118912) (by decide) (join_sr (m := 64430080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 64430080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 78118912) (by decide) (join_sr (m := 67461120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 67461120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 65945600) (by decide) (join_su (m := 79167488) (by decide) (join_sr (m := 64430080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 64430080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 79167488) (by decide) (join_sr (m := 67461120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 67461120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/400 : ℝ) (19/200 : ℝ) →
    rho ∈ Set.Icc (3/40 : ℝ) (421/5120 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((77594624 : ℤ) : ℝ) / (D : ℝ)) = (37/400 : ℝ) := by norm_num [D]
  have e1 : (((79691776 : ℤ) : ℝ) / (D : ℝ)) = (19/200 : ℝ) := by norm_num [D]
  have e2 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e3 : (((68976640 : ℤ) : ℝ) / (D : ℝ)) = (421/5120 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
