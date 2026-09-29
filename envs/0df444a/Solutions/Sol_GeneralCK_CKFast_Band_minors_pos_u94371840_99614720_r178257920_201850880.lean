-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u94371840_99614720_r178257920_201850880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:48:00.027507+00:00
-- url     : https://prove2.me/submissions/90a61fde-77bd-420a-a252-196f4d3dac34

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/80, 19/160]`, `ρ ∈ [17/80, 77/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 94371840 95682560 178257920 184156160 ⟨⟨147963941108, 147963941114⟩, ⟨140640318583, 155459459606⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 95682560 96993280 178257920 184156160 ⟨⟨146554157836, 146554157847⟩, ⟨139302840394, 153974663576⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 94371840 95682560 184156160 190054400 ⟨⟨151987784411, 151987784416⟩, ⟨144645823989, 159499765326⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 95682560 96993280 184156160 190054400 ⟨⟨150551666272, 150551666284⟩, ⟨143281679969, 157989035584⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 96993280 98304000 178257920 184156160 ⟨⟨145164997448, 145164997457⟩, ⟨137984584742, 152511957211⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 98304000 99614720 178257920 184156160 ⟨⟨143795933813, 143795933824⟩, ⟨136685066386, 151070771318⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 96993280 98304000 184156160 190054400 ⟨⟨149136285790, 149136285799⟩, ⟨141936894212, 156500486567⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 98304000 99614720 184156160 190054400 ⟨⟨147741119278, 147741119289⟩, ⟨140610982889, 155033552683⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 94371840 95682560 190054400 195952640 ⟨⟨155975308744, 155975308749⟩, ⟨148615681012, 163503098866⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 95682560 96993280 190054400 195952640 ⟨⟨154513602027, 154513602036⟩, ⟨147225604983, 161967192774⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 94371840 95682560 195952640 201850880 ⟨⟨159927414482, 159927414489⟩, ⟨152550761640, 167470388987⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 95682560 96993280 195952640 201850880 ⟨⟨158440837503, 158440837513⟩, ⟨151135460455, 165910034956⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 96993280 98304000 190054400 195952640 ⟨⟨153072732166, 153072732177⟩, ⟨145855007414, 160453542949⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 98304000 99614720 190054400 195952640 ⟨⟨151652178257, 151652178266⟩, ⟨144503406229, 158961587712⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 96993280 98304000 195952640 201850880 ⟨⟨156975181940, 156975181951⟩, ⟨149739743293, 164371998171⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 98304000 99614720 195952640 201850880 ⟨⟨155529929966, 155529929976⟩, ⟨148363130150, 162855721150⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 94371840 99614720 178257920 201850880 t = true :=
  ⟨_, (join_sr (m := 190054400) (by decide) (join_su (m := 96993280) (by decide) (join_sr (m := 184156160) (by decide) (join_su (m := 95682560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 95682560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 184156160) (by decide) (join_su (m := 98304000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 98304000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 96993280) (by decide) (join_sr (m := 195952640) (by decide) (join_su (m := 95682560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 95682560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 195952640) (by decide) (join_su (m := 98304000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 98304000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/80 : ℝ) (19/160 : ℝ) →
    rho ∈ Set.Icc (17/80 : ℝ) (77/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e1 : (((99614720 : ℤ) : ℝ) / (D : ℝ)) = (19/160 : ℝ) := by norm_num [D]
  have e2 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e3 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
