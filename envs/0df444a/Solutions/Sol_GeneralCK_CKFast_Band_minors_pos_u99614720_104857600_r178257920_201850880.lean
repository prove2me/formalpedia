-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u99614720_104857600_r178257920_201850880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:48:13.708899+00:00
-- url     : https://prove2.me/submissions/f20da6c1-137f-4e89-a02d-d28937582e21

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/160, 1/8]`, `ρ ∈ [17/80, 77/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 99614720 100925440 178257920 184156160 ⟨⟨142446458970, 142446458979⟩, ⟨135403816670, 149650556519⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 100925440 102236160 178257920 184156160 ⟨⟨141116082299, 141116082304⟩, ⟨134140382787, 148250782371⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 99614720 100925440 184156160 190054400 ⟨⟨146365660958, 146365660967⟩, ⟨139303478549, 153587687843⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 100925440 102236160 184156160 190054400 ⟨⟨145009422162, 145009422169⟩, ⟨138013929403, 152162364596⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 102236160 103546880 178257920 184156160 ⟨⟨139804329778, 139804329787⟩, ⟨132894327112, 146870936531⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 103546880 104857600 178257920 184156160 ⟨⟨138510743279, 138510743290⟩, ⟨131665226533, 145510523989⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 102236160 103546880 184156160 190054400 ⟨⟨143671930597, 143671930608⟩, ⟨136741898678, 150757073312⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 103546880 104857600 184156160 190054400 ⟨⟨142352729658, 142352729666⟩, ⟨135486963952, 149371321436⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 99614720 100925440 190054400 195952640 ⟨⟨150251437030, 150251437041⟩, ⟨143170335529, 157490784568⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 100925440 102236160 190054400 195952640 ⟨⟨148870022093, 148870022100⟩, ⟨141855344884, 156040609363⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 99614720 100925440 195952640 201850880 ⟨⟨154104581123, 154104581133⟩, ⟨147005156984, 161360665267⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 100925440 102236160 195952640 201850880 ⟨⟨152698651582, 152698651586⟩, ⟨145665375030, 159886309932⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 102236160 103546880 190054400 195952640 ⟨⟨147507463196, 147507463207⟩, ⟨140557998697, 154610555478⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 103546880 104857600 190054400 195952640 ⟨⟨146163305564, 146163305575⟩, ⟨139277875552, 153200133113⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 102236160 103546880 195952640 201850880 ⟨⟨151311673420, 151311673431⟩, ⟨144343350168, 158432151814⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 103546880 104857600 195952640 201850880 ⟨⟨149943193982, 149943193990⟩, ⟨143038662282, 156997704129⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 99614720 104857600 178257920 201850880 t = true :=
  ⟨_, (join_sr (m := 190054400) (by decide) (join_su (m := 102236160) (by decide) (join_sr (m := 184156160) (by decide) (join_su (m := 100925440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 100925440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 184156160) (by decide) (join_su (m := 103546880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 103546880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 102236160) (by decide) (join_sr (m := 195952640) (by decide) (join_su (m := 100925440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 100925440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 195952640) (by decide) (join_su (m := 103546880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 103546880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/160 : ℝ) (1/8 : ℝ) →
    rho ∈ Set.Icc (17/80 : ℝ) (77/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((99614720 : ℤ) : ℝ) / (D : ℝ)) = (19/160 : ℝ) := by norm_num [D]
  have e1 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e2 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e3 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
