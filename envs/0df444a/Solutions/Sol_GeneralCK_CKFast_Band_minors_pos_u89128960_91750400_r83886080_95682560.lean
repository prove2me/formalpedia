-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u89128960_91750400_r83886080_95682560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:30:08.799077+00:00
-- url     : https://prove2.me/submissions/00ec320c-43a7-4d96-b2cb-bf2577b9191a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/160, 7/64]`, `ρ ∈ [1/10, 73/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 89128960 89784320 83886080 86835200 ⟨⟨80358039879, 80358039888⟩, ⟨76711309797, 84060632916⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 89784320 90439680 83886080 86835200 ⟨⟨79896579996, 79896580000⟩, ⟨76270913672, 83577522265⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 89128960 89784320 86835200 89784320 ⟨⟨82848123830, 82848123841⟩, ⟨79192694177, 86559092643⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 89784320 90439680 86835200 89784320 ⟨⟨82374930625, 82374930629⟩, ⟨78740566622, 86064254225⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 90439680 91095040 83886080 86835200 ⟨⟨79439624906, 79439624917⟩, ⟨75834766986, 83099181486⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 91095040 91750400 83886080 86835200 ⟨⟨78987100997, 78987101005⟩, ⟨75402800847, 82625532008⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 90439680 91095040 86835200 89784320 ⟨⟨81906322017, 81906322025⟩, ⟨78292769416, 85574264182⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 91095040 91750400 86835200 89784320 ⟨⟨81442223572, 81442223583⟩, ⟨77849232807, 85089043181⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 89128960 89784320 89784320 92733440 ⟨⟨85322180845, 85322180856⟩, ⟨81658257837, 89041320406⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 89784320 90439680 89784320 92733440 ⟨⟨84837468248, 84837468252⟩, ⟨81194609503, 88534971362⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 89128960 89784320 92733440 95682560 ⟨⟨87780458883, 87780458894⟩, ⟨84108243379, 91507569558⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 89784320 90439680 92733440 95682560 ⟨⟨87284435804, 87284435806⟩, ⟨83633280023, 90989921879⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 90439680 91095040 89784320 92733440 ⟨⟨84357416687, 84357416696⟩, ⟨80735369118, 88033545788⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 91095040 91750400 89784320 92733440 ⟨⟨83881950984, 83881950992⟩, ⟨80280466136, 87536963644⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 90439680 91095040 92733440 95682560 ⟨⟨86793146953, 86793146964⟩, ⟨83162799027, 90477269466⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 91095040 91750400 92733440 95682560 ⟨⟨86306516470, 86306516481⟩, ⟨82696729108, 89969531646⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 89128960 91750400 83886080 95682560 t = true :=
  ⟨_, (join_sr (m := 89784320) (by decide) (join_su (m := 90439680) (by decide) (join_sr (m := 86835200) (by decide) (join_su (m := 89784320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 89784320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 86835200) (by decide) (join_su (m := 91095040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 91095040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 90439680) (by decide) (join_sr (m := 92733440) (by decide) (join_su (m := 89784320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 89784320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 92733440) (by decide) (join_su (m := 91095040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 91095040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/160 : ℝ) (7/64 : ℝ) →
    rho ∈ Set.Icc (1/10 : ℝ) (73/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((89128960 : ℤ) : ℝ) / (D : ℝ)) = (17/160 : ℝ) := by norm_num [D]
  have e1 : (((91750400 : ℤ) : ℝ) / (D : ℝ)) = (7/64 : ℝ) := by norm_num [D]
  have e2 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e3 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
