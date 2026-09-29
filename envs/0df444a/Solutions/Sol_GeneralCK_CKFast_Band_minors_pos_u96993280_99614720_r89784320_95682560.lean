-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u96993280_99614720_r89784320_95682560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:30:45.129337+00:00
-- url     : https://prove2.me/submissions/96cc952e-2c67-4ee7-ae51-d561c8066718

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/320, 19/160]`, `ρ ∈ [137/1280, 73/640]` by 8 cells of the computing
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
theorem cell0 : cellOK 96993280 97648640 89784320 92733440 ⟨⟨79797494070, 79797494078⟩, ⟨76370605985, 83273305875⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 97648640 98304000 89784320 92733440 ⟨⟨79364090979, 79364090987⟩, ⟨75955513153, 82821119903⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 96993280 97648640 92733440 95682560 ⟨⟨82124728223, 82124728233⟩, ⟨78689563835, 85608571624⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 97648640 98304000 92733440 95682560 ⟨⟨81680848658, 81680848668⟩, ⟨78264001828, 85145907299⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 98304000 98959360 89784320 92733440 ⟨⟨78934545625, 78934545635⟩, ⟨75544073908, 82373003013⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 98959360 99614720 89784320 92733440 ⟨⟨78508799814, 78508799824⟩, ⟨75136233544, 81928893376⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 98304000 98959360 92733440 95682560 ⟨⟨81240892099, 81240892109⟩, ⟨77842159432, 84687376439⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 98959360 99614720 92733440 95682560 ⟨⟨80804799725, 80804799735⟩, ⟨77423981287, 84232916624⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 96993280 99614720 89784320 95682560 t = true :=
  ⟨_, (join_su (m := 98304000) (by decide) (join_sr (m := 92733440) (by decide) (join_su (m := 97648640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 97648640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 92733440) (by decide) (join_su (m := 98959360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 98959360) (by decide) (leaf_ok cell6) (leaf_ok cell7))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/320 : ℝ) (19/160 : ℝ) →
    rho ∈ Set.Icc (137/1280 : ℝ) (73/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((96993280 : ℤ) : ℝ) / (D : ℝ)) = (37/320 : ℝ) := by norm_num [D]
  have e1 : (((99614720 : ℤ) : ℝ) / (D : ℝ)) = (19/160 : ℝ) := by norm_num [D]
  have e2 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  have e3 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
