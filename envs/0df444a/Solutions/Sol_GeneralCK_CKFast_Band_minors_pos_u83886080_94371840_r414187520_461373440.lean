-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u83886080_94371840_r414187520_461373440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T11:08:05.623386+00:00
-- url     : https://prove2.me/submissions/41d3efe6-69ab-41a7-8376-537a07d32078

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/10, 9/80]`, `ρ ∈ [79/160, 11/20]` by 16 cells of the computing
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
theorem cell0 : cellOK 83886080 86507520 414187520 425984000 ⟨⟨305227489674, 305227489681⟩, ⟨289011307712, 321900944316⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 86507520 89128960 414187520 425984000 ⟨⟨300782430050, 300782430063⟩, ⟨284805450625, 317210470074⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 83886080 86507520 425984000 437780480 ⟨⟨311474798823, 311474798829⟩, ⟨295250951500, 328143659939⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 86507520 89128960 425984000 437780480 ⟨⟨306993772461, 306993772474⟩, ⟨291004985797, 323421938173⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 89128960 91750400 414187520 425984000 ⟨⟨296422371756, 296422371769⟩, ⟨280678436612, 312611219514⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 91750400 94371840 414187520 425984000 ⟨⟨292144058386, 292144058398⟩, ⟨276627262958, 308099687147⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 89128960 91750400 425984000 437780480 ⟨⟨302596536321, 302596536331⟩, ⟨286836900433, 318789955687⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 91750400 94371840 425984000 437780480 ⟨⟨298279917844, 298279917857⟩, ⟨282743762448, 314244306059⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 83886080 86507520 437780480 449576960 ⟨⟨317659093153, 317659093161⟩, ⟨301428436695, 334322754428⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 86507520 89128960 437780480 449576960 ⟨⟨313143581686, 313143581699⟩, ⟨297143898270, 329571188241⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 83886080 86507520 449576960 461373440 ⟨⟨323783036315, 323783036319⟩, ⟨307546342975, 340440965372⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 86507520 89128960 449576960 461373440 ⟨⟨319234424132, 319234424145⟩, ⟨303224671412, 335660860942⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 89128960 91750400 437780480 449576960 ⟨⟨308710643488, 308710643501⟩, ⟨292936262824, 324907881739⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 91750400 94371840 437780480 449576960 ⟨⟨304357187303, 304357187316⟩, ⟨288802665437, 320329524053⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 89128960 91750400 449576960 461373440 ⟨⟨314767165033, 314767165043⟩, ⟨298978913758, 330967543578⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 91750400 94371840 449576960 461373440 ⟨⟨310378246539, 310378246549⟩, ⟨294806271383, 326357794552⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 83886080 94371840 414187520 461373440 t = true :=
  ⟨_, (join_sr (m := 437780480) (by decide) (join_su (m := 89128960) (by decide) (join_sr (m := 425984000) (by decide) (join_su (m := 86507520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 86507520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 425984000) (by decide) (join_su (m := 91750400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 91750400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 89128960) (by decide) (join_sr (m := 449576960) (by decide) (join_su (m := 86507520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 86507520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 449576960) (by decide) (join_su (m := 91750400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 91750400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/10 : ℝ) (9/80 : ℝ) →
    rho ∈ Set.Icc (79/160 : ℝ) (11/20 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e1 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e2 : (((414187520 : ℤ) : ℝ) / (D : ℝ)) = (79/160 : ℝ) := by norm_num [D]
  have e3 : (((461373440 : ℤ) : ℝ) / (D : ℝ)) = (11/20 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
