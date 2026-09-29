-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u83886080_104857600_r697303040_744488960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:01:48.969451+00:00
-- url     : https://prove2.me/submissions/e2d877fb-35d9-4d87-acee-9eb2e485d288

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/10, 1/8]`, `ρ ∈ [133/160, 71/80]` by 16 cells of the computing
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
theorem cell0 : cellOK 83886080 89128960 697303040 709099520 ⟨⟨439591195498, 439591195511⟩, ⟨413368543360, 466398573857⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 83886080 89128960 709099520 720896000 ⟨⟨444866543169, 444866543183⟩, ⟨418615895523, 471680682207⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 89128960 94371840 697303040 709099520 ⟨⟨429619696717, 429619696725⟩, ⟨403849438080, 455990258375⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 89128960 94371840 709099520 720896000 ⟨⟨434857249589, 434857249599⟩, ⟨409050584572, 461244170630⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 83886080 89128960 720896000 732692480 ⟨⟨450120136797, 450120136810⟩, ⟨423841581670, 476941081282⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 83886080 89128960 732692480 744488960 ⟨⟨455353025896, 455353025910⟩, ⟨429046624100, 482180837056⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 89128960 94371840 720896000 732692480 ⟨⟨440073607981, 440073607990⟩, ⟨414230724319, 466476800961⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 89128960 94371840 732692480 744488960 ⟨⟨445269776521, 445269776530⟩, ⟨419390832827, 471689173884⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 94371840 99614720 697303040 709099520 ⟨⟨419866668215, 419866668228⟩, ⟨394535718242, 445811507029⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 94371840 99614720 709099520 720896000 ⟨⟨425062564132, 425062564145⟩, ⟨399687418691, 451032706989⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 99614720 104857600 697303040 709099520 ⟨⟨410318831642, 410318831656⟩, ⟨385415023034, 435848350571⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 99614720 104857600 709099520 720896000 ⟨⟨415469483962, 415469483975⟩, ⟨390514273561, 441032635647⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 94371840 99614720 720896000 732692480 ⟨⟨430237866911, 430237866924⟩, ⟨404818795697, 456233115076⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 94371840 99614720 732692480 744488960 ⟨⟨435393536154, 435393536166⟩, ⟨409930778516, 461413713335⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 99614720 104857600 720896000 732692480 ⟨⟨420600177973, 420600177987⟩, ⟨395593901654, 446196671159⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 99614720 104857600 732692480 744488960 ⟨⟨425711828429, 425711828442⟩, ⟨400654791061, 451341396117⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 83886080 104857600 697303040 744488960 t = true :=
  ⟨_, (join_su (m := 94371840) (by decide) (join_sr (m := 720896000) (by decide) (join_su (m := 89128960) (by decide) (join_sr (m := 709099520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 709099520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 89128960) (by decide) (join_sr (m := 732692480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 732692480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 720896000) (by decide) (join_su (m := 99614720) (by decide) (join_sr (m := 709099520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 709099520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 99614720) (by decide) (join_sr (m := 732692480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 732692480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/10 : ℝ) (1/8 : ℝ) →
    rho ∈ Set.Icc (133/160 : ℝ) (71/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e1 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e2 : (((697303040 : ℤ) : ℝ) / (D : ℝ)) = (133/160 : ℝ) := by norm_num [D]
  have e3 : (((744488960 : ℤ) : ℝ) / (D : ℝ)) = (71/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
