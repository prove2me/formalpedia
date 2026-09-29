-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u96993280_99614720_r95682560_107479040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:36:19.177512+00:00
-- url     : https://prove2.me/submissions/da2489f8-cdf8-4e0c-aee4-0ee1920000bf

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/320, 19/160]`, `ρ ∈ [73/640, 41/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 96993280 97648640 95682560 98631680 ⟨⟨84438680039, 84438680047⟩, ⟨80995401744, 87930393230⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 97648640 98304000 95682560 98631680 ⟨⟨83984494041, 83984494049⟩, ⟨80559538110, 87457423048⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 96993280 97648640 98631680 101580800 ⟨⟨86739536815, 86739536825⟩, ⟨83288303254, 90238961783⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 97648640 98304000 98631680 101580800 ⟨⟨86275210814, 86275210825⟩, ⟨82842302017, 89755854539⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 98304000 98959360 95682560 98631680 ⟨⟨83534293810, 83534293820⟩, ⟨80127457643, 86988648169⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 98959360 99614720 95682560 98631680 ⟨⟨83088019944, 83088019955⟩, ⟨79699104373, 86524005626⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 98304000 98959360 98631680 101580800 ⟨⟨85814930914, 85814930922⟩, ⟨82400145113, 89277001970⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 98959360 99614720 98631680 101580800 ⟨⟨85358637171, 85358637180⟩, ⟨81961775998, 88802340607⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 96993280 97648640 101580800 104529920 ⟨⟨89027482276, 89027482284⟩, ⟨85568448426, 92534464686⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 97648640 98304000 101580800 104529920 ⟨⟨88553179183, 88553179193⟩, ⟨85112470178, 92041385567⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 96993280 97648640 104529920 107479040 ⟨⟨91302696645, 91302696655⟩, ⟨87836013920, 94817085752⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 97648640 98304000 104529920 107479040 ⟨⟨90818575945, 90818575953⟩, ⟨87370215910, 94314196434⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 98304000 98959360 101580800 104529920 ⟨⟨88082980170, 88082980178⟩, ⟨84660395108, 91552618113⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 98959360 99614720 101580800 104529920 ⟨⟨87616824796, 87616824807⟩, ⟨84212166149, 91068098387⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 98304000 98959360 104529920 107479040 ⟨⟨90338615020, 90338615031⟩, ⟨86908377676, 93815673458⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 98959360 99614720 104529920 107479040 ⟨⟨89862752982, 89862752991⟩, ⟨86450441666, 93321452467⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 96993280 99614720 95682560 107479040 t = true :=
  ⟨_, (join_sr (m := 101580800) (by decide) (join_su (m := 98304000) (by decide) (join_sr (m := 98631680) (by decide) (join_su (m := 97648640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 97648640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 98631680) (by decide) (join_su (m := 98959360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 98959360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 98304000) (by decide) (join_sr (m := 104529920) (by decide) (join_su (m := 97648640) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 97648640) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 104529920) (by decide) (join_su (m := 98959360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 98959360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/320 : ℝ) (19/160 : ℝ) →
    rho ∈ Set.Icc (73/640 : ℝ) (41/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((96993280 : ℤ) : ℝ) / (D : ℝ)) = (37/320 : ℝ) := by norm_num [D]
  have e1 : (((99614720 : ℤ) : ℝ) / (D : ℝ)) = (19/160 : ℝ) := by norm_num [D]
  have e2 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  have e3 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
