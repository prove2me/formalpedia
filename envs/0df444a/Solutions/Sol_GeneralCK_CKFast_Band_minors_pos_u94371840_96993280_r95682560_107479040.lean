-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u94371840_96993280_r95682560_107479040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:35:35.971006+00:00
-- url     : https://prove2.me/submissions/2e6857f0-43cc-45bd-8588-055f8e22a0cc

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/80, 37/320]`, `ρ ∈ [73/640, 41/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 94371840 95027200 95682560 98631680 ⟨⟨86296513334, 86296513345⟩, ⟨82777848230, 89865532983⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 95027200 95682560 95682560 98631680 ⟨⟨85825765236, 85825765246⟩, ⟨82326268785, 89375125160⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 94371840 95027200 98631680 101580800 ⟨⟨88638544322, 88638544333⟩, ⟨85111923334, 92215253672⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 95027200 95682560 98631680 101580800 ⟨⟨88157409444, 88157409455⟩, ⟨84649955846, 91714466211⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 95682560 96337920 95682560 98631680 ⟨⟨85359253104, 85359253113⟩, ⟨81878708179, 88889177973⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 96337920 96993280 95682560 98631680 ⟨⟨84896912433, 84896912437⟩, ⟨81435105669, 88407622996⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 95682560 96337920 98631680 101580800 ⟨⟨87680573052, 87680573060⟩, ⟨84192070687, 91218200796⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 96337920 96993280 98631680 101580800 ⟨⟨87207970086, 87207970090⟩, ⟨83738206520, 90726388491⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 94371840 95027200 101580800 104529920 ⟨⟨90966987970, 90966987980⟩, ⟨87432575708, 94551223238⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 95027200 95682560 101580800 104529920 ⟨⟨90475639064, 90475639072⟩, ⟨86960390466, 94040231305⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 94371840 95027200 104529920 107479040 ⟨⟨93282038988, 93282038999⟩, ⟨89739996145, 96873640332⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 95027200 95682560 104529920 107479040 ⟨⟨92780645062, 92780645071⟩, ⟨89257759789, 96352615260⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 95682560 96337920 101580800 104529920 ⟨⟨89988648633, 89988648643⟩, ⟨86492348549, 93533820267⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 96337920 96993280 101580800 104529920 ⟨⟨89505951117, 89505951121⟩, ⟨86028388079, 93031920721⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 95682560 96337920 104529920 107479040 ⟨⟨92283667159, 92283667169⟩, ⟨88779725343, 95836227453⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 96337920 96993280 104529920 107479040 ⟨⟨91791039255, 91791039259⟩, ⟨88305830429, 95324407085⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 94371840 96993280 95682560 107479040 t = true :=
  ⟨_, (join_sr (m := 101580800) (by decide) (join_su (m := 95682560) (by decide) (join_sr (m := 98631680) (by decide) (join_su (m := 95027200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 95027200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 98631680) (by decide) (join_su (m := 96337920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 96337920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 95682560) (by decide) (join_sr (m := 104529920) (by decide) (join_su (m := 95027200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 95027200) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 104529920) (by decide) (join_su (m := 96337920) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 96337920) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/80 : ℝ) (37/320 : ℝ) →
    rho ∈ Set.Icc (73/640 : ℝ) (41/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e1 : (((96993280 : ℤ) : ℝ) / (D : ℝ)) = (37/320 : ℝ) := by norm_num [D]
  have e2 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  have e3 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
