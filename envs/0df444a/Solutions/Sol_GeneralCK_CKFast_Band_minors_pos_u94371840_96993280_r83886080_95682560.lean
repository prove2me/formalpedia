-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u94371840_96993280_r83886080_95682560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:28:53.358774+00:00
-- url     : https://prove2.me/submissions/4ecd453e-dcb0-4968-a075-3b183f6cffd1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/80, 37/320]`, `ρ ∈ [1/10, 73/640]` by 20 cells of the computing
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
theorem cell0 : cellOK 94371840 95027200 83886080 85360640 ⟨⟨76186605819, 76186605829⟩, ⟨73486485478, 78917611797⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 94371840 95027200 85360640 86835200 ⟨⟨77389447526, 77389447534⟩, ⟨74685536783, 80124175644⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 95027200 95682560 83886080 85360640 ⟨⟨75762020144, 75762020153⟩, ⟨73075924528, 78478706434⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 95027200 95682560 85360640 86835200 ⟨⟨76959255278, 76959255286⟩, ⟨74269375256, 79679659355⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 94371840 95027200 86835200 89784320 ⟨⟨79186890312, 79186890322⟩, ⟨75693121419, 82731817032⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 95027200 95682560 86835200 89784320 ⟨⟨78748378024, 78748378035⟩, ⟨75273765807, 82273639060⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 95682560 96337920 83886080 85360640 ⟨⟨75341374527, 75341374537⟩, ⟨72669139171, 78043910239⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 95682560 96337920 85360640 86835200 ⟨⟨76533040576, 76533040584⟩, ⟨73857027070, 79239289421⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 96337920 96993280 83886080 85360640 ⟨⟨74924607364, 74924607368⟩, ⟨72266070713, 77613158588⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 96337920 96993280 85360640 86835200 ⟨⟨76110741421, 76110741425⟩, ⟨73448433127, 78803000834⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 95682560 96337920 86835200 89784320 ⟨⟨78313898131, 78313898139⟩, ⟨74858222809, 81819721244⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 96337920 96993280 86835200 89784320 ⟨⟨77883388073, 77883388077⟩, ⟨74446433728, 81369996988⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 94371840 95027200 89784320 92733440 ⟨⟨81570890961, 81570890971⟩, ⟨78068647698, 85124023527⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 95027200 95682560 89784320 92733440 ⟨⟨81121450154, 81121450164⟩, ⟨77638370287, 84654916343⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 94371840 95027200 92733440 95682560 ⟨⟨83940696408, 83940696419⟩, ⟨80430155830, 87501858521⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 95027200 95682560 92733440 95682560 ⟨⟨83480511684, 83480511695⟩, ⟨79989138461, 87022009441⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 95682560 96337920 89784320 92733440 ⟨⟨80676112357, 80676112365⟩, ⟨77211976949, 84190138939⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 96337920 96993280 89784320 92733440 ⟨⟨80234814311, 80234814315⟩, ⟨76789408249, 83729624065⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 95682560 96337920 92733440 95682560 ⟨⟨83024497796, 83024497806⟩, ⟨79552073874, 86546556936⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell19 : cellOK 96337920 96993280 92733440 95682560 ⟨⟨82572590841, 82572590843⟩, ⟨79118901959, 86075433147⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 94371840 96993280 83886080 95682560 t = true :=
  ⟨_, (join_sr (m := 89784320) (by decide) (join_su (m := 95682560) (by decide) (join_sr (m := 86835200) (by decide) (join_su (m := 95027200) (by decide) (join_sr (m := 85360640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 85360640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 95027200) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 86835200) (by decide) (join_su (m := 96337920) (by decide) (join_sr (m := 85360640) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 85360640) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 96337920) (by decide) (leaf_ok cell10) (leaf_ok cell11)))) (join_su (m := 95682560) (by decide) (join_sr (m := 92733440) (by decide) (join_su (m := 95027200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 95027200) (by decide) (leaf_ok cell14) (leaf_ok cell15))) (join_sr (m := 92733440) (by decide) (join_su (m := 96337920) (by decide) (leaf_ok cell16) (leaf_ok cell17)) (join_su (m := 96337920) (by decide) (leaf_ok cell18) (leaf_ok cell19)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/80 : ℝ) (37/320 : ℝ) →
    rho ∈ Set.Icc (1/10 : ℝ) (73/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e1 : (((96993280 : ℤ) : ℝ) / (D : ℝ)) = (37/320 : ℝ) := by norm_num [D]
  have e2 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e3 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
