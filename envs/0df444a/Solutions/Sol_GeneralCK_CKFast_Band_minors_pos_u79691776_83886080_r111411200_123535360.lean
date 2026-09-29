-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u79691776_83886080_r111411200_123535360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:47:17.981609+00:00
-- url     : https://prove2.me/submissions/b7184673-3108-445a-a313-a645ff546e15

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/200, 1/10]`, `ρ ∈ [17/128, 377/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 79691776 80740352 111411200 114442240 ⟨⟨111568566545, 111568566554⟩, ⟨106170198111, 117077074371⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 79691776 80740352 114442240 117473280 ⟨⟨114132691191, 114132691203⟩, ⟨108724205161, 119650585190⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 80740352 81788928 111411200 114442240 ⟨⟨110539588206, 110539588216⟩, ⟨105192501144, 115994990841⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 80740352 81788928 114442240 117473280 ⟨⟨113086169232, 113086169244⟩, ⟨107728868801, 118551080806⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 79691776 80740352 117473280 120504320 ⟨⟨116679276126, 116679276138⟩, ⟨111260947285, 122206285537⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 79691776 80740352 120504320 123535360 ⟨⟨119208612563, 119208612576⟩, ⟨113780707835, 124744474523⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 80740352 81788928 117473280 120504320 ⟨⟨115615565715, 115615565725⟩, ⟨110248320800, 121089721043⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 80740352 81788928 120504320 123535360 ⟨⟨118128059813, 118128059822⟩, ⟨112751131727, 123611201325⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 81788928 82837504 111411200 114442240 ⟨⟨109526950757, 109526950766⟩, ⟨104230103844, 114930337913⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 81788928 82837504 114442240 117473280 ⟨⟨112056136201, 112056136212⟩, ⟨106748987907, 117469146193⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 82837504 83886080 111411200 114442240 ⟨⟨108530221753, 108530221762⟩, ⟨103282605433, 113882649733⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 82837504 83886080 114442240 117473280 ⟨⟨111042158665, 111042158676⟩, ⟨105784160291, 116404314989⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 81788928 82837504 117473280 120504320 ⟨⟨114568483997, 114568484006⟩, ⟨109251297411, 119990857137⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 81788928 82837504 120504320 123535360 ⟨⟨117064267568, 117064267577⟩, ⟨111737298486, 122495751505⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 82837504 83886080 117473280 120504320 ⟨⟨113537596781, 113537596790⟩, ⟨108269473748, 118909227171⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 82837504 83886080 120504320 123535360 ⟨⟨116016801095, 116016801104⟩, ⟨110738803774, 121397658346⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 79691776 83886080 111411200 123535360 t = true :=
  ⟨_, (join_su (m := 81788928) (by decide) (join_sr (m := 117473280) (by decide) (join_su (m := 80740352) (by decide) (join_sr (m := 114442240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 114442240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 80740352) (by decide) (join_sr (m := 120504320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 120504320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 117473280) (by decide) (join_su (m := 82837504) (by decide) (join_sr (m := 114442240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 114442240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 82837504) (by decide) (join_sr (m := 120504320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 120504320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/200 : ℝ) (1/10 : ℝ) →
    rho ∈ Set.Icc (17/128 : ℝ) (377/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((79691776 : ℤ) : ℝ) / (D : ℝ)) = (19/200 : ℝ) := by norm_num [D]
  have e1 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e2 : (((111411200 : ℤ) : ℝ) / (D : ℝ)) = (17/128 : ℝ) := by norm_num [D]
  have e3 : (((123535360 : ℤ) : ℝ) / (D : ℝ)) = (377/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
