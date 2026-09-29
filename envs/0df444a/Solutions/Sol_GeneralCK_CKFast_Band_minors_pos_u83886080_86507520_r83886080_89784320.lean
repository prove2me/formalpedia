-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u83886080_86507520_r83886080_89784320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:08:20.75428+00:00
-- url     : https://prove2.me/submissions/efab23af-32e7-4565-bdfe-d2cbcd030940

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/10, 33/320]`, `ρ ∈ [1/10, 137/1280]` by 8 cells of the computing
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
theorem cell0 : cellOK 83886080 84541440 83886080 86835200 ⟨⟨84221301706, 84221301715⟩, ⟨80396259381, 88107280985⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 84541440 85196800 83886080 86835200 ⟨⟨83720941644, 83720941655⟩, ⟨79919191521, 87582955369⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 83886080 84541440 86835200 89784320 ⟨⟨86808225274, 86808225286⟩, ⟨82974514138, 90702482370⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 84541440 85196800 86835200 89784320 ⟨⟨86295463277, 86295463285⟩, ⟨82485035523, 90165772843⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 85196800 85852160 83886080 86835200 ⟨⟨83225739882, 83225739893⟩, ⟨79446984094, 87064097622⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 85852160 86507520 83886080 86835200 ⟨⟨82735607956, 82735607965⟩, ⟨78979554443, 86550613201⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 85196800 85852160 86835200 89784320 ⟨⟨85787946156, 85787946165⟩, ⟨82000505455, 89634615980⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 85852160 86507520 86835200 89784320 ⟨⟨85285584575, 85285584587⟩, ⟨81520840347, 89108916433⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 83886080 86507520 83886080 89784320 t = true :=
  ⟨_, (join_su (m := 85196800) (by decide) (join_sr (m := 86835200) (by decide) (join_su (m := 84541440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 84541440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 86835200) (by decide) (join_su (m := 85852160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 85852160) (by decide) (leaf_ok cell6) (leaf_ok cell7))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/10 : ℝ) (33/320 : ℝ) →
    rho ∈ Set.Icc (1/10 : ℝ) (137/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e1 : (((86507520 : ℤ) : ℝ) / (D : ℝ)) = (33/320 : ℝ) := by norm_num [D]
  have e2 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e3 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
