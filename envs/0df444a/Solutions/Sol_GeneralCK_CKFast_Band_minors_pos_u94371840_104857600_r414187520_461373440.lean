-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u94371840_104857600_r414187520_461373440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:57:33.880561+00:00
-- url     : https://prove2.me/submissions/bf8bddde-6b3c-404d-b0e0-569b2c4fb0ea

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/80, 1/8]`, `ρ ∈ [79/160, 11/20]` by 16 cells of the computing
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
theorem cell0 : cellOK 94371840 96993280 414187520 425984000 ⟨⟨287944412672, 287944412683⟩, ⟨272649090946, 303672560955⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 96993280 99614720 414187520 425984000 ⟨⟨283820522873, 283820522880⟩, ⟨268741233504, 299326707607⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 94371840 96993280 425984000 437780480 ⟨⟨294040917794, 294040917806⟩, ⟨278722797987, 309781769530⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 96993280 99614720 425984000 437780480 ⟨⟨289876697092, 289876697098⟩, ⟨274771380323, 305399298783⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 99614720 102236160 414187520 425984000 ⟨⟨279769630488, 279769630500⟩, ⟨264901144041, 295059159186⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 102236160 104857600 414187520 425984000 ⟨⟨275789119179, 275789119191⟩, ⟨261126406367, 290867101153⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 99614720 102236160 425984000 437780480 ⟨⟨285784564954, 285784564966⟩, ⟨270887019050, 301094006130⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 102236160 104857600 425984000 437780480 ⟨⟨281761968207, 281761968220⟩, ⟨267067350330, 296863151928⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 94371840 96993280 437780480 449576960 ⟨⟨300080289668, 300080289680⟩, ⟨284740395610, 315832984566⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 96993280 99614720 437780480 449576960 ⟨⟨295877182184, 295877182190⟩, ⟨280746885660, 311415299179⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 94371840 96993280 449576960 461373440 ⟨⟨306064818717, 306064818729⟩, ⟨290704095609, 321828569324⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 96993280 99614720 449576960 461373440 ⟨⟨301824181868, 301824181872⟩, ⟨286669876466, 317376984271⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 99614720 102236160 437780480 449576960 ⟨⟨291745240045, 291745240057⟩, ⟨276819700252, 307073657957⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 102236160 104857600 437780480 449576960 ⟨⟨287681971709, 287681971721⟩, ⟨272956526942, 302805393956⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 99614720 102236160 449576960 461373440 ⟨⟨297653775403, 297653775415⟩, ⟨282701232523, 313000304767⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 102236160 104857600 449576960 461373440 ⟨⟨293551167863, 293551167873⟩, ⟨278795901727, 308695934378⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 94371840 104857600 414187520 461373440 t = true :=
  ⟨_, (join_sr (m := 437780480) (by decide) (join_su (m := 99614720) (by decide) (join_sr (m := 425984000) (by decide) (join_su (m := 96993280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 96993280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 425984000) (by decide) (join_su (m := 102236160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 102236160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 99614720) (by decide) (join_sr (m := 449576960) (by decide) (join_su (m := 96993280) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 96993280) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 449576960) (by decide) (join_su (m := 102236160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 102236160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/80 : ℝ) (1/8 : ℝ) →
    rho ∈ Set.Icc (79/160 : ℝ) (11/20 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e1 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e2 : (((414187520 : ℤ) : ℝ) / (D : ℝ)) = (79/160 : ℝ) := by norm_num [D]
  have e3 : (((461373440 : ℤ) : ℝ) / (D : ℝ)) = (11/20 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
