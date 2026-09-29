-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u94371840_104857600_r461373440_508559360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:58:11.865266+00:00
-- url     : https://prove2.me/submissions/34ea2e43-99da-4721-ae17-667c1df4f3d3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/80, 1/8]`, `ρ ∈ [11/20, 97/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 94371840 96993280 461373440 473169920 ⟨⟨311996697064, 311996697076⟩, ⟨296616016959, 327770783388⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 96993280 99614720 461373440 473169920 ⟨⟨307719807035, 307719807041⟩, ⟨292542392068, 323286531584⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 94371840 96993280 473169920 484966400 ⟨⟨317878024348, 317878024360⟩, ⟨302478191206, 333661788915⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 96993280 99614720 473169920 484966400 ⟨⟨313566081164, 313566081171⟩, ⟨298366389177, 329146026496⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 99614720 102236160 461373440 473169920 ⟨⟨303512203050, 303512203062⟩, ⟨288533578046, 318876044154⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 102236160 104857600 461373440 473169920 ⟨⟨299371512165, 299371512177⟩, ⟨284587362178, 314536793019⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 99614720 102236160 473169920 484966400 ⟨⟨309322472410, 309322472423⟩, ⟨294318620954, 324702886606⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 102236160 104857600 473169920 484966400 ⟨⟨305144882100, 305144882113⟩, ⟨290332722091, 320329907390⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 94371840 96993280 484966400 496762880 ⟨⟨323710813131, 323710813144⟩, ⟨308292567465, 339503656448⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 96993280 99614720 484966400 496762880 ⟨⟨319364945344, 319364945350⟩, ⟨304143746550, 334957467648⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 94371840 96993280 496762880 508559360 ⟨⟨329496993941, 329496993953⟩, ⟨314061017109, 345298370307⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 96993280 99614720 496762880 508559360 ⟨⟨325118262977, 325118262983⟩, ⟨309876269344, 340722771979⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 99614720 102236160 484966400 496762880 ⟨⟨315086454992, 315086455004⟩, ⟨300058171682, 330482760531⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 102236160 104857600 484966400 496762880 ⟨⟨310873081490, 310873081502⟩, ⟨296033725596, 326077137384⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 99614720 102236160 496762880 508559360 ⟨⟨320805948761, 320805948774⟩, ⟨305753971021, 336217516957⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 102236160 104857600 496762880 508559360 ⟨⟨316557844568, 316557844580⟩, ⟨301692050939, 331780269621⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 94371840 104857600 461373440 508559360 t = true :=
  ⟨_, (join_sr (m := 484966400) (by decide) (join_su (m := 99614720) (by decide) (join_sr (m := 473169920) (by decide) (join_su (m := 96993280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 96993280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 473169920) (by decide) (join_su (m := 102236160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 102236160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 99614720) (by decide) (join_sr (m := 496762880) (by decide) (join_su (m := 96993280) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 96993280) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 496762880) (by decide) (join_su (m := 102236160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 102236160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/80 : ℝ) (1/8 : ℝ) →
    rho ∈ Set.Icc (11/20 : ℝ) (97/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e1 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e2 : (((461373440 : ℤ) : ℝ) / (D : ℝ)) = (11/20 : ℝ) := by norm_num [D]
  have e3 : (((508559360 : ℤ) : ℝ) / (D : ℝ)) = (97/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
