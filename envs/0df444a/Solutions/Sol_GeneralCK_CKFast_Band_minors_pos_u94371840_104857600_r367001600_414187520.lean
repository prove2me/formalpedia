-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u94371840_104857600_r367001600_414187520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:55:07.808136+00:00
-- url     : https://prove2.me/submissions/2b5b10a6-d120-4801-b148-ae8a556e1d05

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/80, 1/8]`, `ρ ∈ [7/16, 79/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 94371840 96993280 367001600 378798080 ⟨⟨262937446048, 262937446060⟩, ⟨247745347385, 278604504333⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 96993280 99614720 367001600 378798080 ⟨⟨258991273284, 258991273290⟩, ⟨244028313232, 274421132542⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 94371840 96993280 378798080 390594560 ⟨⟨269287584111, 269287584123⟩, ⟨254067678449, 284971640817⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 96993280 99614720 378798080 390594560 ⟨⟨265294310709, 265294310715⟩, ⟨250300244641, 280745030375⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 99614720 102236160 367001600 378798080 ⟨⟨255121525522, 255121525534⟩, ⟨240381624319, 270320442385⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 102236160 104857600 367001600 378798080 ⟨⟨251325319439, 251325319451⟩, ⟨236802647047, 266299297821⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 99614720 102236160 378798080 390594560 ⟨⟨261376643914, 261376643926⟩, ⟨246602559663, 276600033892⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 102236160 104857600 378798080 390594560 ⟨⟨257531769166, 257531769178⟩, ⟨242972045270, 272533598940⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 94371840 96993280 390594560 402391040 ⟨⟨275570311422, 275570311432⟩, ⟨260324002175, 291270150756⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 96993280 99614720 390594560 402391040 ⟨⟨271531792747, 271531792750⟩, ⟨256508036866, 287002123177⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 94371840 96993280 402391040 414187520 ⟨⟨281788379313, 281788379324⟩, ⟨266516964085, 297502885156⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 96993280 99614720 402391040 414187520 ⟨⟨277706357174, 277706357179⟩, ⟨262654225257, 293195145956⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 99614720 102236160 390594560 402391040 ⟨⟨267568033969, 267568033979⟩, ⟨252761189333, 282814621707⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 102236160 104857600 390594560 402391040 ⟨⟨263676288003, 263676288014⟩, ⟨249080936091, 278704675397⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 99614720 102236160 402391040 414187520 ⟨⟨273698223983, 273698223995⟩, ⟨258859942665, 288966828707⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 102236160 104857600 402391040 414187520 ⟨⟨269761298753, 269761298765⟩, ⟨255131646882, 284815041765⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 94371840 104857600 367001600 414187520 t = true :=
  ⟨_, (join_sr (m := 390594560) (by decide) (join_su (m := 99614720) (by decide) (join_sr (m := 378798080) (by decide) (join_su (m := 96993280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 96993280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 378798080) (by decide) (join_su (m := 102236160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 102236160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 99614720) (by decide) (join_sr (m := 402391040) (by decide) (join_su (m := 96993280) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 96993280) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 402391040) (by decide) (join_su (m := 102236160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 102236160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/80 : ℝ) (1/8 : ℝ) →
    rho ∈ Set.Icc (7/16 : ℝ) (79/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e1 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e2 : (((367001600 : ℤ) : ℝ) / (D : ℝ)) = (7/16 : ℝ) := by norm_num [D]
  have e3 : (((414187520 : ℤ) : ℝ) / (D : ℝ)) = (79/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
