-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u83886080_94371840_r461373440_508559360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:56:55.584919+00:00
-- url     : https://prove2.me/submissions/fa7c3199-9191-4d81-82ed-480a97520d69

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/10, 9/80]`, `ρ ∈ [11/20, 97/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 83886080 86507520 461373440 473169920 ⟨⟨329849168787, 329849168796⟩, ⟨313607133487, 346500900891⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 86507520 89128960 461373440 473169920 ⟨⟨325268749721, 325268749735⟩, ⟨309249678453, 341693474369⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 83886080 86507520 473169920 484966400 ⟨⟨335859915672, 335859915679⟩, ⟨319613162040, 352505047975⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 86507520 89128960 473169920 484966400 ⟨⟨331248899125, 331248899138⟩, ⟨315221189177, 347671431801⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 89128960 91750400 461373440 473169920 ⟨⟨320768462606, 320768462619⟩, ⟨304967139140, 336971371139⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 91750400 94371840 461373440 473169920 ⟨⟨316345371258, 316345371271⟩, ⟨300756781442, 332331461297⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 89128960 91750400 473169920 484966400 ⟨⟨326716794469, 326716794482⟩, ⟨310903127032, 342921685603⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 91750400 94371840 473169920 484966400 ⟨⟨322260739372, 322260739385⟩, ⟨306656304271, 338252765064⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 83886080 86507520 484966400 496762880 ⟨⟨341817593851, 341817593858⟩, ⟨325566679768, 358455780177⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 86507520 89128960 484966400 496762880 ⟨⟨337177110459, 337177110472⟩, ⟨321141376135, 353597028896⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 83886080 86507520 496762880 508559360 ⟨⟨347724418664, 347724418673⟩, ⟨331469841328, 364355364735⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 86507520 89128960 496762880 508559360 ⟨⟨343055525499, 343055525510⟩, ⟨327012320410, 359472460324⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 89128960 91750400 484966400 496762880 ⟨⟨332614321730, 332614321742⟩, ⟨316788973450, 348820706089⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 91750400 94371840 484966400 496762880 ⟨⟨328126436791, 328126436804⟩, ⟨312506861402, 344123849914⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 89128960 91750400 496762880 508559360 ⟨⟨338463114136, 338463114149⟩, ⟨322626687728, 354670555867⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 91750400 94371840 496762880 508559360 ⟨⟨333944462832, 333944462845⟩, ⟨318310392270, 349946768965⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 83886080 94371840 461373440 508559360 t = true :=
  ⟨_, (join_sr (m := 484966400) (by decide) (join_su (m := 89128960) (by decide) (join_sr (m := 473169920) (by decide) (join_su (m := 86507520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 86507520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 473169920) (by decide) (join_su (m := 91750400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 91750400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 89128960) (by decide) (join_sr (m := 496762880) (by decide) (join_su (m := 86507520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 86507520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 496762880) (by decide) (join_su (m := 91750400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 91750400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/10 : ℝ) (9/80 : ℝ) →
    rho ∈ Set.Icc (11/20 : ℝ) (97/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e1 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e2 : (((461373440 : ℤ) : ℝ) / (D : ℝ)) = (11/20 : ℝ) := by norm_num [D]
  have e3 : (((508559360 : ℤ) : ℝ) / (D : ℝ)) = (97/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
