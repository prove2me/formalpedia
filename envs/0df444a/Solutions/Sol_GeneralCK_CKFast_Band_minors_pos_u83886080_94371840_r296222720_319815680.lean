-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u83886080_94371840_r296222720_319815680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:53:37.645186+00:00
-- url     : https://prove2.me/submissions/33c88a4f-7166-4069-9a02-f7d6f0519c74

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/10, 9/80]`, `ρ ∈ [113/320, 61/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 83886080 86507520 296222720 302120960 ⟨⟨236814811703, 236814811709⟩, ⟨224116494099, 249889340822⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 83886080 86507520 302120960 308019200 ⟨⟨240369345393, 240369345401⟩, ⟨227655310187, 253455160227⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 86507520 89128960 296222720 302120960 ⟨⟨232853501205, 232853501218⟩, ⟨220367343605, 245707733329⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 86507520 89128960 302120960 308019200 ⟨⟨236378189936, 236378189947⟩, ⟨223874637711, 249245657096⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 83886080 86507520 308019200 313917440 ⟨⟨243898323764, 243898323772⟩, ⟨231169059503, 256994981227⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 83886080 86507520 313917440 319815680 ⟨⟨247402342928, 247402342934⟩, ⟨234658317476, 260509419920⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 86507520 89128960 308019200 313917440 ⟨⟨239878112641, 239878112654⟩, ⟨227357654457, 252758365744⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 86507520 89128960 313917440 319815680 ⟨⟨243353836957, 243353836970⟩, ⟨230816941647, 256246446186⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 89128960 91750400 296222720 302120960 ⟨⟨228988299326, 228988299338⟩, ⟨216707192663, 241629618510⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 89128960 91750400 302120960 308019200 ⟨⟨232482708528, 232482708541⟩, ⟨220182663492, 245139062269⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 91750400 94371840 296222720 302120960 ⟨⟨225214951802, 225214951812⟩, ⟨213132145454, 237650372608⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 91750400 94371840 302120960 308019200 ⟨⟨228678700326, 228678700338⟩, ⟨216575535233, 241130816455⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 89128960 91750400 308019200 313917440 ⟨⟨235953123793, 235953123803⟩, ⟨223634627127, 248624059627⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 89128960 91750400 313917440 319815680 ⟨⟨239400085560, 239400085572⟩, ⟨227063605032, 252085169573⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 91750400 94371840 308019200 313917440 ⟨⟨232119209489, 232119209501⟩, ⟨219996168713, 244587567410⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 91750400 94371840 313917440 319815680 ⟨⟨235536993785, 235536993797⟩, ⟨223394542268, 248021157760⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 83886080 94371840 296222720 319815680 t = true :=
  ⟨_, (join_su (m := 89128960) (by decide) (join_sr (m := 308019200) (by decide) (join_su (m := 86507520) (by decide) (join_sr (m := 302120960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 302120960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 86507520) (by decide) (join_sr (m := 313917440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 313917440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 308019200) (by decide) (join_su (m := 91750400) (by decide) (join_sr (m := 302120960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 302120960) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 91750400) (by decide) (join_sr (m := 313917440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 313917440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/10 : ℝ) (9/80 : ℝ) →
    rho ∈ Set.Icc (113/320 : ℝ) (61/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e1 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e2 : (((296222720 : ℤ) : ℝ) / (D : ℝ)) = (113/320 : ℝ) := by norm_num [D]
  have e3 : (((319815680 : ℤ) : ℝ) / (D : ℝ)) = (61/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
