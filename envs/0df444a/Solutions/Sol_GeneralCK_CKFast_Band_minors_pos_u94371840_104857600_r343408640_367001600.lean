-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u94371840_104857600_r343408640_367001600
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:54:50.978725+00:00
-- url     : https://prove2.me/submissions/a0ec5331-5c84-47a2-9f40-591dd765511e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/80, 1/8]`, `ρ ∈ [131/320, 7/16]` by 9 cells of the computing
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
theorem cell0 : cellOK 94371840 96993280 343408640 355205120 ⟨⟨250023248355, 250023248367⟩, ⟨234891439900, 265652221318⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 96993280 99614720 343408640 355205120 ⟨⟨246177338916, 246177338921⟩, ⟨231281289342, 261561299501⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 94371840 96993280 355205120 367001600 ⟨⟨256517010944, 256517010956⟩, ⟨241354236896, 272165747020⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 96993280 99614720 355205120 367001600 ⟨⟨252619915942, 252619915948⟩, ⟨237689588421, 268027560065⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 99614720 102236160 343408640 355205120 ⟨⟨242409387618, 242409387628⟩, ⟨227742553952, 257555116185⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 102236160 104857600 343408640 349306880 ⟨⟨237121051467, 237121051478⟩, ⟨225582433580, 248962052544⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 102236160 104857600 349306880 355205120 ⟨⟨240307320931, 240307320942⟩, ⟨228746980619, 252167326159⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 99614720 102236160 355205120 367001600 ⟨⟨248800031476, 248800031488⟩, ⟨234095842334, 263973097890⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 102236160 104857600 355205120 367001600 ⟨⟨245054404282, 245054404295⟩, ⟨230570309245, 259999138767⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 94371840 104857600 343408640 367001600 t = true :=
  ⟨_, (join_su (m := 99614720) (by decide) (join_sr (m := 355205120) (by decide) (join_su (m := 96993280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 96993280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 355205120) (by decide) (join_su (m := 102236160) (by decide) (leaf_ok cell4) (join_sr (m := 349306880) (by decide) (leaf_ok cell5) (leaf_ok cell6))) (join_su (m := 102236160) (by decide) (leaf_ok cell7) (leaf_ok cell8))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/80 : ℝ) (1/8 : ℝ) →
    rho ∈ Set.Icc (131/320 : ℝ) (7/16 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e1 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e2 : (((343408640 : ℤ) : ℝ) / (D : ℝ)) = (131/320 : ℝ) := by norm_num [D]
  have e3 : (((367001600 : ℤ) : ℝ) / (D : ℝ)) = (7/16 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
