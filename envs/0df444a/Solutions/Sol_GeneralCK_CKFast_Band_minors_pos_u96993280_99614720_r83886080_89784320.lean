-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u96993280_99614720_r83886080_89784320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:28:56.377786+00:00
-- url     : https://prove2.me/submissions/a254ca44-22cb-4b2e-8e2d-6d641d19c7d1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/320, 19/160]`, `ρ ∈ [1/10, 137/1280]` by 14 cells of the computing
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
theorem cell0 : cellOK 96993280 97648640 83886080 85360640 ⟨⟨74511658335, 74511658343⟩, ⟨71866661694, 77186388227⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 96993280 97648640 85360640 86835200 ⟨⟨75692297112, 75692297120⟩, ⟨73043535573, 78370729969⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 97648640 98304000 83886080 85360640 ⟨⟨74102468406, 74102468416⟩, ⟨71470855851, 76763537236⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 97648640 98304000 85360640 86835200 ⟨⟨75277648231, 75277648239⟩, ⟨72642277750, 77942414537⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 96993280 97648640 86835200 89784320 ⟨⟨77456786594, 77456786605⟩, ⟨74038341084, 80924401110⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 97648640 98304000 86835200 89784320 ⟨⟨77034033731, 77034033741⟩, ⟨73633888591, 80482869791⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 98304000 98959360 83886080 85360640 ⟨⟨73696979765, 73696979773⟩, ⟨71078598089, 76344544998⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 98304000 98959360 85360640 86835200 ⟨⟨74866736584, 74866736594⟩, ⟨72244604175, 77517993551⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 98959360 99614720 83886080 85360640 ⟨⟨73295135797, 73295135807⟩, ⟨70689834450, 75929352159⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 98959360 99614720 85360640 86835200 ⟨⟨74459505189, 74459505199⟩, ⟨71850460508, 77097407298⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 98304000 98959360 86835200 88309760 ⟨⟨76033128853, 76033128863⟩, ⟨73407277199, 78688046045⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 98304000 98959360 88309760 89784320 ⟨⟨77196180430, 77196180440⟩, ⟨74566640667, 79854726690⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 98959360 99614720 86835200 88309760 ⟨⟨75620553794, 75620553802⟩, ⟨73007796764, 78262110637⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 98959360 99614720 88309760 89784320 ⟨⟨76778305001, 76778305011⟩, ⟨74161866268, 79423485913⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 96993280 99614720 83886080 89784320 t = true :=
  ⟨_, (join_su (m := 98304000) (by decide) (join_sr (m := 86835200) (by decide) (join_su (m := 97648640) (by decide) (join_sr (m := 85360640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 85360640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 97648640) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 86835200) (by decide) (join_su (m := 98959360) (by decide) (join_sr (m := 85360640) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 85360640) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 98959360) (by decide) (join_sr (m := 88309760) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_sr (m := 88309760) (by decide) (leaf_ok cell12) (leaf_ok cell13)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/320 : ℝ) (19/160 : ℝ) →
    rho ∈ Set.Icc (1/10 : ℝ) (137/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((96993280 : ℤ) : ℝ) / (D : ℝ)) = (37/320 : ℝ) := by norm_num [D]
  have e1 : (((99614720 : ℤ) : ℝ) / (D : ℝ)) = (19/160 : ℝ) := by norm_num [D]
  have e2 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e3 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
