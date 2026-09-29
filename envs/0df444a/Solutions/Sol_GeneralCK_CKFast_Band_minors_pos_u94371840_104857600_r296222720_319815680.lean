-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u94371840_104857600_r296222720_319815680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:54:03.293175+00:00
-- url     : https://prove2.me/submissions/250cca88-f7e5-48f3-aaa8-d95259f7012e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/80, 1/8]`, `ρ ∈ [113/320, 61/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 94371840 96993280 296222720 302120960 ⟨⟨221529463871, 221529463883⟩, ⟨209638541245, 233765656177⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 94371840 96993280 302120960 308019200 ⟨⟨224962219082, 224962219094⟩, ⟨213049631641, 237216638851⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 96993280 99614720 296222720 302120960 ⟨⟨217928079549, 217928079554⟩, ⟨206222935789, 229971391214⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 96993280 99614720 302120960 308019200 ⟨⟨221329552890, 221329552896⟩, ⟨209601544231, 233392504822⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 94371840 96993280 308019200 313917440 ⟨⟨228372471808, 228372471820⟩, ⟨216438697429, 240644666428⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 94371840 96993280 313917440 319815680 ⟨⟨231760711789, 231760711801⟩, ⟨219806211067, 244050245696⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 96993280 99614720 308019200 313917440 ⟨⟨224709242824, 224709242830⟩, ⟨212958840665, 236791385062⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 96993280 99614720 313917440 319815680 ⟨⟨228067615483, 228067615489⟩, ⟨216295274764, 240168514367⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 99614720 102236160 296222720 302120960 ⟨⟨214407262927, 214407262938⟩, ⟨202882084553, 226263740596⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 99614720 102236160 302120960 308019200 ⟨⟨217777205917, 217777205929⟩, ⟨206228060894, 229654625865⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 102236160 104857600 296222720 302120960 ⟨⟨210963681360, 210963681372⟩, ⟨199612927575, 222639089511⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 102236160 104857600 302120960 308019200 ⟨⟨214301881964, 214301881973⟩, ⟨202926151094, 225999431467⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 99614720 102236160 308019200 313917440 ⟨⟨221126066757, 221126066768⟩, ⟨209553418915, 233023983166⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 99614720 102236160 313917440 319815680 ⟨⟨224454289071, 224454289083⟩, ⟨212858586584, 236372271681⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 102236160 104857600 308019200 313917440 ⟨⟨217619683897, 217619683908⟩, ⟨206219431275, 229338934365⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 102236160 104857600 313917440 319815680 ⟨⟨220917509334, 220917509346⟩, ⟨209493175415, 232658035203⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 94371840 104857600 296222720 319815680 t = true :=
  ⟨_, (join_su (m := 99614720) (by decide) (join_sr (m := 308019200) (by decide) (join_su (m := 96993280) (by decide) (join_sr (m := 302120960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 302120960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 96993280) (by decide) (join_sr (m := 313917440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 313917440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 308019200) (by decide) (join_su (m := 102236160) (by decide) (join_sr (m := 302120960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 302120960) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 102236160) (by decide) (join_sr (m := 313917440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 313917440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/80 : ℝ) (1/8 : ℝ) →
    rho ∈ Set.Icc (113/320 : ℝ) (61/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e1 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e2 : (((296222720 : ℤ) : ℝ) / (D : ℝ)) = (113/320 : ℝ) := by norm_num [D]
  have e3 : (((319815680 : ℤ) : ℝ) / (D : ℝ)) = (61/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
