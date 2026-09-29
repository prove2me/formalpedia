-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u83886080_94371840_r225443840_249036800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:50:44.42818+00:00
-- url     : https://prove2.me/submissions/1543fa31-62b0-404f-aaf0-ca373a3982b5

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/10, 9/80]`, `ρ ∈ [43/160, 19/64]` by 20 cells of the computing
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
theorem cell0 : cellOK 83886080 86507520 225443840 231342080 ⟨⟨191923404484, 191923404489⟩, ⟨179460814949, 204819174253⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 83886080 86507520 231342080 237240320 ⟨⟨195838390385, 195838390388⟩, ⟨183352199605, 208752733595⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 86507520 87818240 225443840 231342080 ⟨⟨189266872406, 189266872416⟩, ⟨181369747364, 197335540207⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 87818240 89128960 225443840 231342080 ⟨⟨187527434907, 187527434912⟩, ⟨179707837869, 195516079559⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 86507520 89128960 231342080 237240320 ⟨⟨192266978984, 192266978996⟩, ⟨180011079145, 204939466272⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 83886080 86507520 237240320 243138560 ⟨⟨199719041973, 199719041979⟩, ⟨187210078833, 212651182569⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 83886080 86507520 243138560 249036800 ⟨⟨203566225933, 203566225941⟩, ⟨191035282891, 216515423788⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 86507520 89128960 237240320 243138560 ⟨⟨196106822559, 196106822572⟩, ⟨183826552049, 208799052917⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 86507520 89128960 243138560 249036800 ⟨⟨199914398005, 199914398018⟩, ⟨187610534204, 212625638734⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 89128960 90439680 225443840 231342080 ⟨⟨185812522765, 185812522777⟩, ⟨178068993879, 193722659956⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 90439680 91750400 225443840 231342080 ⟨⟨184121524856, 184121524867⟩, ⟨176452645688, 191954627190⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 89128960 91750400 231342080 237240320 ⟨⟨188794855577, 188794855587⟩, ⟨176760541931, 201234695050⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 91750400 93061120 225443840 231342080 ⟨⟨182453850874, 182453850886⟩, ⟨174858242864, 190211349492⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 93061120 94371840 225443840 231342080 ⟨⟨180808930437, 180808930449⟩, ⟨173285253406, 188492216558⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 91750400 93061120 231342080 237240320 ⟨⟨186252996105, 186252996117⟩, ⟨178644567310, 194021451780⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 93061120 94371840 231342080 237240320 ⟨⟨184586980509, 184586980519⟩, ⟨177050032879, 192281737699⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 89128960 91750400 237240320 243138560 ⟨⟨192593759488, 192593759500⟩, ⟨180533631096, 205055108695⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 89128960 91750400 243138560 249036800 ⟨⟨196361556390, 196361556400⟩, ⟨184276373885, 208843692621⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 91750400 94371840 237240320 243138560 ⟨⟨189175063005, 189175063016⟩, ⟨177327000433, 201414059386⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell19 : cellOK 91750400 94371840 243138560 249036800 ⟨⟨192902963619, 192902963631⟩, ⟨181028525644, 205164362194⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 83886080 94371840 225443840 249036800 t = true :=
  ⟨_, (join_su (m := 89128960) (by decide) (join_sr (m := 237240320) (by decide) (join_su (m := 86507520) (by decide) (join_sr (m := 231342080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 231342080) (by decide) (join_su (m := 87818240) (by decide) (leaf_ok cell2) (leaf_ok cell3)) (leaf_ok cell4))) (join_su (m := 86507520) (by decide) (join_sr (m := 243138560) (by decide) (leaf_ok cell5) (leaf_ok cell6)) (join_sr (m := 243138560) (by decide) (leaf_ok cell7) (leaf_ok cell8)))) (join_sr (m := 237240320) (by decide) (join_su (m := 91750400) (by decide) (join_sr (m := 231342080) (by decide) (join_su (m := 90439680) (by decide) (leaf_ok cell9) (leaf_ok cell10)) (leaf_ok cell11)) (join_sr (m := 231342080) (by decide) (join_su (m := 93061120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 93061120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))) (join_su (m := 91750400) (by decide) (join_sr (m := 243138560) (by decide) (leaf_ok cell16) (leaf_ok cell17)) (join_sr (m := 243138560) (by decide) (leaf_ok cell18) (leaf_ok cell19)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/10 : ℝ) (9/80 : ℝ) →
    rho ∈ Set.Icc (43/160 : ℝ) (19/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e1 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e2 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e3 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
