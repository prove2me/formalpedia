-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u83886080_89128960_r131072000_142868480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:40:25.307489+00:00
-- url     : https://prove2.me/submissions/3928b254-72c9-4ab7-abfa-881d9638ef0a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/10, 17/160]`, `ρ ∈ [5/32, 109/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 83886080 85196800 131072000 134021120 ⟨⟨123283595481, 123283595493⟩, ⟨117224817620, 129474229166⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 83886080 85196800 134021120 136970240 ⟨⟨125611828003, 125611828013⟩, ⟨119542299430, 131812456764⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 85196800 86507520 131072000 134021120 ⟨⟨121950490456, 121950490467⟩, ⟨115957542061, 128072854629⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 85196800 86507520 134021120 136970240 ⟨⟨124260508976, 124260508988⟩, ⟨118256684216, 130393027153⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 83886080 85196800 136970240 139919360 ⟨⟨127926267065, 127926267075⟩, ⟨121846217651, 134136664311⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 83886080 85196800 139919360 142868480 ⟨⟨130227118065, 130227118077⟩, ⟨124136771922, 136447063005⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 85196800 86507520 136970240 139919360 ⟨⟨126557059689, 126557059698⟩, ⟨120542582880, 132699510486⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 85196800 86507520 139919360 142868480 ⟨⟨128840340572, 128840340581⟩, ⟨122815430516, 134992508161⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 86507520 87818240 131072000 134021120 ⟨⟨120641392095, 120641392107⟩, ⟨114712726764, 126697106769⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 86507520 87818240 134021120 136970240 ⟨⟨122933349270, 122933349282⟩, ⟨116993693054, 128999364173⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 87818240 89128960 131072000 134021120 ⟨⟨119355572227, 119355572232⟩, ⟨113489697624, 125346200346⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 87818240 89128960 134021120 136970240 ⟨⟨121629620492, 121629620497⟩, ⟨115752650930, 127630683131⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 86507520 87818240 136970240 139919360 ⟨⟨125212155750, 125212155760⟩, ⟨119261727502, 131288254635⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 86507520 87818240 139919360 142868480 ⟨⟨127478002389, 127478002398⟩, ⟨121517015688, 133563974336⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 87818240 89128960 136970240 139919360 ⟨⟨123890826890, 123890826892⟩, ⟨118002975858, 129902112873⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 87818240 89128960 139919360 142868480 ⟨⟨126139375437, 126139375441⟩, ⟨120240851377, 132160678688⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 83886080 89128960 131072000 142868480 t = true :=
  ⟨_, (join_su (m := 86507520) (by decide) (join_sr (m := 136970240) (by decide) (join_su (m := 85196800) (by decide) (join_sr (m := 134021120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 134021120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 85196800) (by decide) (join_sr (m := 139919360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 139919360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 136970240) (by decide) (join_su (m := 87818240) (by decide) (join_sr (m := 134021120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 134021120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 87818240) (by decide) (join_sr (m := 139919360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 139919360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/10 : ℝ) (17/160 : ℝ) →
    rho ∈ Set.Icc (5/32 : ℝ) (109/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e1 : (((89128960 : ℤ) : ℝ) / (D : ℝ)) = (17/160 : ℝ) := by norm_num [D]
  have e2 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e3 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
