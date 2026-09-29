-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u79691776_83886080_r99287040_111411200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:42:21.805287+00:00
-- url     : https://prove2.me/submissions/3412c6cf-ca58-4284-a54a-4ccdad834697

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/200, 1/10]`, `ρ ∈ [303/2560, 17/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 79691776 80740352 99287040 102318080 ⟨⟨101130604615, 101130604624⟩, ⟨95775621153, 106598692406⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 79691776 80740352 102318080 105349120 ⟨⟨103767939145, 103767939154⟩, ⟨98401654865, 109246580747⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 80740352 81788928 99287040 102318080 ⟨⟨100175543904, 100175543916⟩, ⟨94872159643, 105590097465⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 80740352 81788928 102318080 105349120 ⟨⟨102793817631, 102793817641⟩, ⟨97479063547, 108219022295⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 79691776 80740352 105349120 108380160 ⟨⟨106386499119, 106386499131⟩, ⟨101009223015, 111875389350⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 79691776 80740352 108380160 111411200 ⟨⟨108986604184, 108986604196⟩, ⟨103598636260, 114485446907⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 80740352 81788928 105349120 108380160 ⟨⟨105393711202, 105393711211⟩, ⟨100067889091, 110829268659⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 80740352 81788928 108380160 111411200 ⟨⟨107975533977, 107975533989⟩, ⟨102638936996, 113421154619⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 81788928 82837504 99287040 102318080 ⟨⟨99236142327, 99236142339⟩, ⟨93983286283, 104598285777⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 81788928 82837504 102318080 105349120 ⟨⟨101835539856, 101835539865⟩, ⟨96571252204, 107208423290⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 82837504 83886080 99287040 102318080 ⟨⟨98311973943, 98311973952⟩, ⟨93108608492, 103622796076⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 82837504 83886080 102318080 105349120 ⟨⟨100892677837, 100892677847⟩, ⟨95677825795, 106214320899⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 81788928 82837504 105349120 108380160 ⟨⟨104416941934, 104416941943⟩, ⟨99141517431, 109800273778⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 81788928 82837504 108380160 111411200 ⟨⟨106980648016, 106980648028⟩, ⟨101694373109, 112374145068⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 82837504 83886080 105349120 108380160 ⟨⟨103455761581, 103455761592⟩, ⟨98229710817, 108787940600⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 82837504 83886080 108380160 111411200 ⟨⟨106001515086, 106001515097⟩, ⟨100764545473, 111343953146⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 79691776 83886080 99287040 111411200 t = true :=
  ⟨_, (join_su (m := 81788928) (by decide) (join_sr (m := 105349120) (by decide) (join_su (m := 80740352) (by decide) (join_sr (m := 102318080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 102318080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 80740352) (by decide) (join_sr (m := 108380160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 108380160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 105349120) (by decide) (join_su (m := 82837504) (by decide) (join_sr (m := 102318080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 102318080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 82837504) (by decide) (join_sr (m := 108380160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 108380160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/200 : ℝ) (1/10 : ℝ) →
    rho ∈ Set.Icc (303/2560 : ℝ) (17/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((79691776 : ℤ) : ℝ) / (D : ℝ)) = (19/200 : ℝ) := by norm_num [D]
  have e1 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e2 : (((99287040 : ℤ) : ℝ) / (D : ℝ)) = (303/2560 : ℝ) := by norm_num [D]
  have e3 : (((111411200 : ℤ) : ℝ) / (D : ℝ)) = (17/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
