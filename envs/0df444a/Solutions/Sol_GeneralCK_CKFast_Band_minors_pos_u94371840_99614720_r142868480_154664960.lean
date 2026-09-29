-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u94371840_99614720_r142868480_154664960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:45:14.172144+00:00
-- url     : https://prove2.me/submissions/f5287573-f6ec-4676-8055-a75a4ad8e1fc

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/80, 19/160]`, `ρ ∈ [109/640, 59/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 94371840 95682560 142868480 145817600 ⟨⟨121931386335, 121931386342⟩, ⟨116314000741, 127660902372⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 94371840 95682560 145817600 148766720 ⟨⟨124073415349, 124073415356⟩, ⟨118445278686, 129813158400⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 95682560 96993280 142868480 145817600 ⟨⟨120705048018, 120705048030⟩, ⟨115142262949, 126378126814⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 95682560 96993280 145817600 148766720 ⟨⟨122831094728, 122831094740⟩, ⟨117257487036, 128514494229⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 94371840 95682560 148766720 151715840 ⟨⟨126204629222, 126204629227⟩, ⟨120565913962, 131954428130⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 94371840 95682560 151715840 154664960 ⟨⟨128325170967, 128325170970⟩, ⟨122676045898, 134084858293⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 95682560 96993280 148766720 151715840 ⟨⟨124946569653, 124946569664⟩, ⟨119362307698, 130640122631⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 95682560 96993280 151715840 154664960 ⟨⟨127051610938, 127051610947⟩, ⟨121456859550, 132755153734⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 96993280 98304000 142868480 145817600 ⟨⟨119498195140, 119498195148⟩, ⟨113988861942, 125116034835⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 96993280 98304000 145817600 148766720 ⟨⟨121608381154, 121608381163⟩, ⟨116088160875, 127236627199⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 98304000 99614720 142868480 145817600 ⟨⟨118310296417, 118310296428⟩, ⟨112853302472, 123874057334⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 98304000 99614720 145817600 148766720 ⟨⟨120404742961, 120404742972⟩, ⟨114936804162, 125978988274⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 96993280 98304000 148766720 151715840 ⟨⟨123708232824, 123708232832⟩, ⟨118177289785, 129346721858⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 96993280 98304000 151715840 154664960 ⟨⟨125797883610, 125797883619⟩, ⟨120256378747, 131446455705⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 98304000 99614720 148766720 151715840 ⟨⟨122489086845, 122489086856⟩, ⟨117010363552, 128073657009⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 98304000 99614720 151715840 154664960 ⟨⟨124563457027, 124563457036⟩, ⟨119074106348, 130158195778⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 94371840 99614720 142868480 154664960 t = true :=
  ⟨_, (join_su (m := 96993280) (by decide) (join_sr (m := 148766720) (by decide) (join_su (m := 95682560) (by decide) (join_sr (m := 145817600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 145817600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 95682560) (by decide) (join_sr (m := 151715840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 151715840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 148766720) (by decide) (join_su (m := 98304000) (by decide) (join_sr (m := 145817600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 145817600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 98304000) (by decide) (join_sr (m := 151715840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 151715840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/80 : ℝ) (19/160 : ℝ) →
    rho ∈ Set.Icc (109/640 : ℝ) (59/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e1 : (((99614720 : ℤ) : ℝ) / (D : ℝ)) = (19/160 : ℝ) := by norm_num [D]
  have e2 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  have e3 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
