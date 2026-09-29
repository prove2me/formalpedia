-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u75497472_83886080_r281149440_305397760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:55:29.516869+00:00
-- url     : https://prove2.me/submissions/75b3681e-7983-4549-a35e-40916cff4fb8

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/100, 1/10]`, `ρ ∈ [429/1280, 233/640]` by 10 cells of the computing
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
theorem cell0 : cellOK 75497472 77594624 281149440 293273600 ⟨⟨243138690044, 243138690055⟩, ⟨227776515546, 259035849102⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 77594624 79691776 281149440 293273600 ⟨⟨239727053915, 239727053920⟩, ⟨224604376132, 255373687845⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 75497472 77594624 293273600 305397760 ⟨⟨250729925054, 250729925065⟩, ⟨235368198844, 266610011083⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 77594624 79691776 293273600 305397760 ⟨⟨247270226733, 247270226739⟩, ⟨232143374947, 262905220880⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 79691776 81788928 281149440 287211520 ⟨⟨234496335668, 234496335679⟩, ⟨223225332946, 246066851406⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 79691776 81788928 287211520 293273600 ⟨⟨238273641674, 238273641687⟩, ⟨226992815547, 249849981502⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 81788928 83886080 281149440 287211520 ⟨⟨231241555962, 231241555975⟩, ⟨220133315593, 242643561911⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 81788928 83886080 287211520 293273600 ⟨⟨234993266650, 234993266664⟩, ⟨223873763686, 246402737790⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 79691776 81788928 293273600 305397760 ⟨⟨243883085893, 243883085906⟩, ⟨228984610542, 259279769088⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 81788928 83886080 293273600 305397760 ⟨⟨240565739500, 240565739513⟩, ⟨225889417614, 255730608478⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 75497472 83886080 281149440 305397760 t = true :=
  ⟨_, (join_su (m := 79691776) (by decide) (join_sr (m := 293273600) (by decide) (join_su (m := 77594624) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 77594624) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 293273600) (by decide) (join_su (m := 81788928) (by decide) (join_sr (m := 287211520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 287211520) (by decide) (leaf_ok cell6) (leaf_ok cell7))) (join_su (m := 81788928) (by decide) (leaf_ok cell8) (leaf_ok cell9))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/100 : ℝ) (1/10 : ℝ) →
    rho ∈ Set.Icc (429/1280 : ℝ) (233/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e1 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e2 : (((281149440 : ℤ) : ℝ) / (D : ℝ)) = (429/1280 : ℝ) := by norm_num [D]
  have e3 : (((305397760 : ℤ) : ℝ) / (D : ℝ)) = (233/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
