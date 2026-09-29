-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u94371840_99614720_r119275520_131072000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:40:32.789845+00:00
-- url     : https://prove2.me/submissions/dd63d45d-b312-4a3c-ad0f-fe658f17ee35

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/80, 19/160]`, `ρ ∈ [91/640, 5/32]` by 16 cells of the computing
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
theorem cell0 : cellOK 94371840 95682560 119275520 122224640 ⟨⟨104387767980, 104387767985⟩, ⟨98863073995, 110028827456⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 94371840 95682560 122224640 125173760 ⟨⟨106621789210, 106621789212⟩, ⟨101084819963, 112274590838⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 95682560 96993280 119275520 122224640 ⟨⟨103298674364, 103298674373⟩, ⟨97828985573, 108882708375⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 95682560 96993280 122224640 125173760 ⟨⟨105514575991, 105514575999⟩, ⟨100032579329, 111110408331⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 94371840 95682560 125173760 128122880 ⟨⟨108843753010, 108843753014⟩, ⟨103294714062, 114508092200⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 94371840 95682560 128122880 131072000 ⟨⟨111053824846, 111053824852⟩, ⟨105492917233, 116729501581⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 95682560 96993280 125173760 128122880 ⟨⟨107718707140, 107718707151⟩, ⟨102224602653, 113326138559⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 95682560 96993280 128122880 131072000 ⟨⟨109911227337, 109911227348⟩, ⟨104405210744, 115530062953⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 96993280 98304000 119275520 122224640 ⟨⟨102227856406, 102227856415⟩, ⟨96811970882, 107756124508⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 96993280 98304000 122224640 125173760 ⟨⟨104425814694, 104425814702⟩, ⟨98997594938, 109965929987⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 98304000 99614720 119275520 122224640 ⟨⟨101174792824, 101174792835⟩, ⟨95811547896, 106648513097⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 98304000 99614720 122224640 125173760 ⟨⟨103354982030, 103354982039⟩, ⟨97979382358, 108840591493⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 96993280 98304000 125173760 128122880 ⟨⟨106612281846, 106612281857⟩, ⟨101171922523, 112164050295⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 96993280 98304000 128122880 131072000 ⟨⟨108787411683, 108787411693⟩, ⟨103335103323, 114350643435⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 98304000 99614720 125173760 128122880 ⟨⟨105523952067, 105523952076⟩, ⟨100136187068, 111021261784⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 98304000 99614720 128122880 131072000 ⟨⟨107681851277, 107681851286⟩, ⟨102282106417, 113190676315⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 94371840 99614720 119275520 131072000 t = true :=
  ⟨_, (join_su (m := 96993280) (by decide) (join_sr (m := 125173760) (by decide) (join_su (m := 95682560) (by decide) (join_sr (m := 122224640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 122224640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 95682560) (by decide) (join_sr (m := 128122880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 128122880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 125173760) (by decide) (join_su (m := 98304000) (by decide) (join_sr (m := 122224640) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 122224640) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 98304000) (by decide) (join_sr (m := 128122880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 128122880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/80 : ℝ) (19/160 : ℝ) →
    rho ∈ Set.Icc (91/640 : ℝ) (5/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e1 : (((99614720 : ℤ) : ℝ) / (D : ℝ)) = (19/160 : ℝ) := by norm_num [D]
  have e2 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  have e3 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
