-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u83886080_104857600_r791674880_838860800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:03:09.053832+00:00
-- url     : https://prove2.me/submissions/8ca8fd34-d952-42ab-ada2-8f2516292675

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/10, 1/8]`, `ρ ∈ [151/160, 1]` by 13 cells of the computing
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
theorem cell0 : cellOK 83886080 89128960 791674880 815267840 ⟨⟨483808010989, 483808011002⟩, ⟨451518831480, 516684872558⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 89128960 94371840 791674880 803471360 ⟨⟨470981068598, 470981068607⟩, ⟨444923277930, 497481082028⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 89128960 94371840 803471360 815267840 ⟨⟨476075736998, 476075737003⟩, ⟨449982298600, 502591898336⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 83886080 89128960 815267840 838860800 ⟨⟨494038259223, 494038259239⟩, ⟨461718748663, 526882775016⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 89128960 94371840 815267840 838860800 ⟨⟨483692009799, 483692009808⟩, ⟨451881475865, 516066092671⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 94371840 99614720 791674880 803471360 ⟨⟨460909239333, 460909239346⟩, ⟨435230668450, 487052113406⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 94371840 99614720 803471360 815267840 ⟨⟨465965908761, 465965908773⟩, ⟨440244520633, 492133055953⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 99614720 104857600 791674880 803471360 ⟨⟨451014850689, 451014850702⟩, ⟨425707583056, 476806546589⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 99614720 104857600 803471360 815267840 ⟨⟨456030202901, 456030202915⟩, ⟨430673419927, 481853811989⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 94371840 99614720 815267840 827064320 ⟨⟨471009011459, 471009011472⟩, ⟨445244866388, 497200379455⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 94371840 99614720 827064320 838860800 ⟨⟨476039334684, 476039334697⟩, ⟨450232471189, 502254885004⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 99614720 104857600 815267840 827064320 ⟨⟨461032313875, 461032313889⟩, ⟨435626135518, 486887706126⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 99614720 104857600 827064320 838860800 ⟨⟨466021938910, 466021938923⟩, ⟨440566462399, 491908999988⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 83886080 104857600 791674880 838860800 t = true :=
  ⟨_, (join_su (m := 94371840) (by decide) (join_sr (m := 815267840) (by decide) (join_su (m := 89128960) (by decide) (leaf_ok cell0) (join_sr (m := 803471360) (by decide) (leaf_ok cell1) (leaf_ok cell2))) (join_su (m := 89128960) (by decide) (leaf_ok cell3) (leaf_ok cell4))) (join_sr (m := 815267840) (by decide) (join_su (m := 99614720) (by decide) (join_sr (m := 803471360) (by decide) (leaf_ok cell5) (leaf_ok cell6)) (join_sr (m := 803471360) (by decide) (leaf_ok cell7) (leaf_ok cell8))) (join_su (m := 99614720) (by decide) (join_sr (m := 827064320) (by decide) (leaf_ok cell9) (leaf_ok cell10)) (join_sr (m := 827064320) (by decide) (leaf_ok cell11) (leaf_ok cell12)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/10 : ℝ) (1/8 : ℝ) →
    rho ∈ Set.Icc (151/160 : ℝ) (1 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e1 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e2 : (((791674880 : ℤ) : ℝ) / (D : ℝ)) = (151/160 : ℝ) := by norm_num [D]
  have e3 : (((838860800 : ℤ) : ℝ) / (D : ℝ)) = (1 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
