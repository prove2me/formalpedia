-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u89128960_94371840_r131072000_142868480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:38:54.565887+00:00
-- url     : https://prove2.me/submissions/1268a2e5-60ad-4517-9634-b83b5c21e9b0

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/160, 9/80]`, `ρ ∈ [5/32, 109/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 89128960 90439680 131072000 134021120 ⟨⟨118092332476, 118092332486⟩, ⟨112287807874, 124019382557⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 89128960 90439680 134021120 136970240 ⟨⟨120348623886, 120348623897⟩, ⟨114532910055, 126286231571⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 90439680 91750400 131072000 134021120 ⟨⟨116851002758, 116851002767⟩, ⟨111106436656, 122715931375⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 90439680 91750400 134021120 136970240 ⟨⟨119089688843, 119089688852⟩, ⟨113333848446, 124965287612⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 89128960 90439680 136970240 139919360 ⟨⟨122592374219, 122592374229⟩, ⟨116765679387, 128540333324⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 89128960 90439680 139919360 142868480 ⟨⟨124823760930, 124823760942⟩, ⟨118986288482, 130781870163⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 90439680 91750400 136970240 139919360 ⟨⟨121316126845, 121316126855⟩, ⟨115549215217, 127202194505⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 90439680 91750400 139919360 142868480 ⟨⟨123530487919, 123530487930⟩, ⟨117752703484, 129426827886⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 91750400 93061120 131072000 134021120 ⟨⟨115630939797, 115630939806⟩, ⟨109944987726, 121435153932⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 91750400 93061120 134021120 136970240 ⟨⟨117852171431, 117852171440⟩, ⟨112154868647, 123667158371⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 93061120 94371840 131072000 134021120 ⟨⟨114431525791, 114431525802⟩, ⟨108802888222, 120176385050⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 93061120 94371840 134021120 136970240 ⟨⟨116635453078, 116635453089⟩, ⟨110995396498, 122391178488⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 91750400 93061120 136970240 139919360 ⟨⟨120061440414, 120061440423⟩, ⟨114352984915, 125887003733⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 91750400 93061120 139919360 142868480 ⟨⟨122258911848, 122258911859⟩, ⟨116539497185, 128094859603⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 93061120 94371840 136970240 139919360 ⟨⟨118827695810, 118827695819⟩, ⟨113176413245, 124594095699⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 93061120 94371840 139919360 142868480 ⟨⟨121008413269, 121008413280⟩, ⟨115346093497, 126785300260⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 89128960 94371840 131072000 142868480 t = true :=
  ⟨_, (join_su (m := 91750400) (by decide) (join_sr (m := 136970240) (by decide) (join_su (m := 90439680) (by decide) (join_sr (m := 134021120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 134021120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 90439680) (by decide) (join_sr (m := 139919360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 139919360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 136970240) (by decide) (join_su (m := 93061120) (by decide) (join_sr (m := 134021120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 134021120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 93061120) (by decide) (join_sr (m := 139919360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 139919360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/160 : ℝ) (9/80 : ℝ) →
    rho ∈ Set.Icc (5/32 : ℝ) (109/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((89128960 : ℤ) : ℝ) / (D : ℝ)) = (17/160 : ℝ) := by norm_num [D]
  have e1 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e2 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e3 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
