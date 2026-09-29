-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u79691776_83886080_r159907840_184156160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:49:28.722175+00:00
-- url     : https://prove2.me/submissions/4aec106f-c94c-478b-a007-98ca0af2cb35

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/200, 1/10]`, `ρ ∈ [61/320, 281/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 79691776 80740352 159907840 165969920 ⟨⟨151800938260, 151800938271⟩, ⟨144385030389, 159392458663⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 80740352 81788928 159907840 165969920 ⟨⟨150522843977, 150522843989⟩, ⟨143176007920, 158042641371⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 79691776 80740352 165969920 172032000 ⟨⟨156403991882, 156403991892⟩, ⟨148975666917, 164005293016⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 80740352 81788928 165969920 172032000 ⟨⟨155100757577, 155100757590⟩, ⟨147741019660, 162630904843⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 81788928 82837504 159907840 165969920 ⟨⟨149262648669, 149262648681⟩, ⟨141983633349, 156712035393⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 82837504 83886080 159907840 165969920 ⟨⟨148019925957, 148019925969⟩, ⟨140807514452, 155400178297⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 81788928 82837504 165969920 172032000 ⟨⟨153815508829, 153815508842⟩, ⟨146523130799, 161275787625⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 82837504 83886080 165969920 172032000 ⟨⟨152547822276, 152547822288⟩, ⟨145321610065, 159939483135⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 79691776 80740352 172032000 178094080 ⟨⟨160953977757, 160953977769⟩, ⟨153514142070, 168564194172⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 80740352 81788928 172032000 178094080 ⟨⟨159626525185, 159626525197⟩, ⟨152254779728, 167166166569⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 79691776 80740352 178094080 184156160 ⟨⟨165452476332, 165452476342⟩, ⟨158001985873, 173070792466⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 80740352 81788928 178094080 184156160 ⟨⟨164101684823, 164101684835⟩, ⟨156718777201, 171650013054⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 81788928 82837504 172032000 178094080 ⟨⟨158317127988, 158317127998⟩, ⟨151012269394, 165787453051⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 82837504 83886080 172032000 178094080 ⟨⟨157025366125, 157025366137⟩, ⟨149786223081, 164427599876⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 81788928 82837504 178094080 184156160 ⟨⟨162769002986, 162769002996⟩, ⟨155452498463, 170248575623⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 82837504 83886080 178094080 184156160 ⟨⟨161454014372, 161454014384⟩, ⟨154202764249, 168866031149⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 79691776 83886080 159907840 184156160 t = true :=
  ⟨_, (join_sr (m := 172032000) (by decide) (join_su (m := 81788928) (by decide) (join_sr (m := 165969920) (by decide) (join_su (m := 80740352) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 80740352) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 165969920) (by decide) (join_su (m := 82837504) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 82837504) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 81788928) (by decide) (join_sr (m := 178094080) (by decide) (join_su (m := 80740352) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 80740352) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 178094080) (by decide) (join_su (m := 82837504) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 82837504) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/200 : ℝ) (1/10 : ℝ) →
    rho ∈ Set.Icc (61/320 : ℝ) (281/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((79691776 : ℤ) : ℝ) / (D : ℝ)) = (19/200 : ℝ) := by norm_num [D]
  have e1 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e2 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  have e3 : (((184156160 : ℤ) : ℝ) / (D : ℝ)) = (281/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
