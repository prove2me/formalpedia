-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u83886080_104857600_r744488960_791674880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:01:40.383485+00:00
-- url     : https://prove2.me/submissions/1e93c969-15f1-41a7-8a00-5c6fab32adea

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/10, 1/8]`, `ρ ∈ [71/80, 151/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 83886080 89128960 744488960 756285440 ⟨⟨460566230058, 460566230071⟩, ⟨434232016611, 487400984278⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 83886080 89128960 756285440 768081920 ⟨⟨465760740510, 465760740525⟩, ⟨439398725961, 492602528147⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 89128960 94371840 744488960 756285440 ⟨⟨450446732086, 450446732091⟩, ⟨424531859264, 476882284826⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 89128960 94371840 756285440 768081920 ⟨⟨455605425218, 455605425228⟩, ⟨429654727778, 482057101643⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 83886080 89128960 768081920 779878400 ⟨⟨470937521616, 470937521629⟩, ⟨444547693254, 497786445872⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 83886080 89128960 779878400 791674880 ⟨⟨476097512275, 476097512289⟩, ⟨449679835254, 502953688176⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 89128960 94371840 768081920 779878400 ⟨⟨460746781498, 460746781506⟩, ⟨434760338749, 487214566055⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 89128960 94371840 779878400 791674880 ⟨⟨465871702814, 465871702823⟩, ⟨439849570001, 492355595020⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 94371840 99614720 744488960 756285440 ⟨⟨440530505791, 440530505804⟩, ⟨415024272102, 466575456798⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 94371840 99614720 756285440 768081920 ⟨⟨445649685382, 445649685396⟩, ⟨420100158321, 471719274867⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 99614720 104857600 744488960 756285440 ⟨⟨430805326410, 430805326423⟩, ⟨405697803176, 456467724529⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 99614720 104857600 756285440 768081920 ⟨⟨435881540496, 435881540510⟩, ⟨410723778105, 461576546666⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 94371840 99614720 768081920 779878400 ⟨⟨450751961346, 450751961361⟩, ⟨425159297071, 476846072627⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 94371840 99614720 779878400 791674880 ⟨⟨455838198133, 455838198145⟩, ⟨430202527381, 481956732094⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 99614720 104857600 768081920 779878400 ⟨⟨440941317877, 440941317892⟩, ⟨415733535716, 466668730245⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 99614720 104857600 779878400 791674880 ⟨⟨445985485422, 445985485435⟩, ⟨420727876607, 471745121563⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 83886080 104857600 744488960 791674880 t = true :=
  ⟨_, (join_su (m := 94371840) (by decide) (join_sr (m := 768081920) (by decide) (join_su (m := 89128960) (by decide) (join_sr (m := 756285440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 756285440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 89128960) (by decide) (join_sr (m := 779878400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 779878400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 768081920) (by decide) (join_su (m := 99614720) (by decide) (join_sr (m := 756285440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 756285440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 99614720) (by decide) (join_sr (m := 779878400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 779878400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/10 : ℝ) (1/8 : ℝ) →
    rho ∈ Set.Icc (71/80 : ℝ) (151/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e1 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e2 : (((744488960 : ℤ) : ℝ) / (D : ℝ)) = (71/80 : ℝ) := by norm_num [D]
  have e3 : (((791674880 : ℤ) : ℝ) / (D : ℝ)) = (151/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
