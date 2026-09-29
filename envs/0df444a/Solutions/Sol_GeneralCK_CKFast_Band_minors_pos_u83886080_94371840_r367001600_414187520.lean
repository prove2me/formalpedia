-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u83886080_94371840_r367001600_414187520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:54:58.556407+00:00
-- url     : https://prove2.me/submissions/10ed6acc-547f-449f-aa59-15139f687c0f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/10, 9/80]`, `ρ ∈ [7/16, 79/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 83886080 86507520 367001600 378798080 ⟨⟨279550030363, 279550030369⟩, ⟨263375021167, 296234059010⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 86507520 89128960 367001600 378798080 ⟨⟨275265867584, 275265867597⟩, ⟨259347139770, 291684823141⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 83886080 86507520 378798080 390594560 ⟨⟨286078807929, 286078807938⟩, ⟨269891712399, 302761557484⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 86507520 89128960 378798080 390594560 ⟨⟨281751623798, 281751623811⟩, ⟨265816467429, 298174330889⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 89128960 91750400 367001600 378798080 ⟨⟨271071426538, 271071426551⟩, ⟨255401734647, 287232740084⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 91750400 94371840 367001600 378798080 ⟨⟨266963089897, 266963089908⟩, ⟨251535507828, 282873871593⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 89128960 91750400 378798080 390594560 ⟨⟨277513007568, 277513007578⟩, ⟨261822831340, 293682782834⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 91750400 94371840 378798080 390594560 ⟨⟨273359435925, 273359435938⟩, ⟨257907582257, 289283088846⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 83886080 86507520 390594560 402391040 ⟨⟨292532505397, 292532505401⟩, ⟨276334595745, 309212996982⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 86507520 89128960 390594560 402391040 ⟨⟨288164250123, 288164250134⟩, ⟨272213984119, 304589653139⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 83886080 86507520 402391040 414187520 ⟨⟨298914370494, 298914370502⟩, ⟨282706801355, 315591731468⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 86507520 89128960 402391040 414187520 ⟨⟨294506863753, 294506863766⟩, ⟨278542692027, 310934012304⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 89128960 91750400 390594560 402391040 ⟨⟨283883388609, 283883388619⟩, ⟨268174083724, 300060505740⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 91750400 94371840 390594560 402391040 ⟨⟨279686489059, 279686489070⟩, ⟨264211747319, 295621840332⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 89128960 91750400 402391040 414187520 ⟨⟨290185560645, 290185560655⟩, ⟨274458370625, 306369003514⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 91750400 94371840 402391040 414187520 ⟨⟨285947118345, 285947118355⟩, ⟨270450762987, 301893096957⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 83886080 94371840 367001600 414187520 t = true :=
  ⟨_, (join_sr (m := 390594560) (by decide) (join_su (m := 89128960) (by decide) (join_sr (m := 378798080) (by decide) (join_su (m := 86507520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 86507520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 378798080) (by decide) (join_su (m := 91750400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 91750400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 89128960) (by decide) (join_sr (m := 402391040) (by decide) (join_su (m := 86507520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 86507520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 402391040) (by decide) (join_su (m := 91750400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 91750400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/10 : ℝ) (9/80 : ℝ) →
    rho ∈ Set.Icc (7/16 : ℝ) (79/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e1 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e2 : (((367001600 : ℤ) : ℝ) / (D : ℝ)) = (7/16 : ℝ) := by norm_num [D]
  have e3 : (((414187520 : ℤ) : ℝ) / (D : ℝ)) = (79/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
