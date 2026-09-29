-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u83886080_94371840_r319815680_367001600
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:54:42.310808+00:00
-- url     : https://prove2.me/submissions/37d736d1-9870-4788-8762-882377d7fc94

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/10, 9/80]`, `ρ ∈ [61/160, 7/16]` by 19 cells of the computing
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
theorem cell0 : cellOK 83886080 86507520 319815680 331612160 ⟨⟨252612835091, 252612835100⟩, ⟨236501639507, 269289684104⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 86507520 89128960 319815680 325713920 ⟨⟨246805914525, 246805914536⟩, ⟨234253031943, 259710468490⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 86507520 89128960 325713920 331612160 ⟨⟨250234881593, 250234881605⟩, ⟨237666443420, 263150986517⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 83886080 86507520 331612160 343408640 ⟨⟨259478067675, 259478067679⟩, ⟨243348292166, 276158837594⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 86507520 89128960 331612160 343408640 ⟨⟨255336136713, 255336136724⟩, ⟨239475914572, 271736299173⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 89128960 91750400 319815680 325713920 ⟨⟨242824119375, 242824119385⟩, ⟨230470104569, 255522935395⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 89128960 91750400 325713920 331612160 ⟨⟨246225736420, 246225736432⟩, ⟨233854619485, 258937885272⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 91750400 94371840 319815680 325713920 ⟨⟨238932553824, 238932553834⟩, ⟨226771139114, 251432105172⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 91750400 94371840 325713920 331612160 ⟨⟨242306376823, 242306376835⟩, ⟨230126429776, 254820913220⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 89128960 91750400 331612160 343408640 ⟨⟨251287214839, 251287214849⟩, ⟨235688378978, 267415241824⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 91750400 94371840 331612160 343408640 ⟨⟨247327388508, 247327388518⟩, ⟨231982151909, 263191363418⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 83886080 86507520 343408640 355205120 ⟨⟨266253366410, 266253366418⟩, ⟨250106870932, 282936539350⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 86507520 89128960 343408640 355205120 ⟨⟨262061671808, 262061671821⟩, ⟨246180269000, 278469486766⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 83886080 86507520 355205120 367001600 ⟨⟨272942751988, 272942751994⟩, ⟨256781229525, 289626964373⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 86507520 89128960 355205120 367001600 ⟨⟨268703701652, 268703701665⟩, ⟨252802846344, 285117735086⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 89128960 91750400 343408640 355205120 ⟨⟨257961925441, 257961925454⟩, ⟨242337766050, 274102493707⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 91750400 94371840 343408640 355205120 ⟨⟨253950314748, 253950314760⟩, ⟨238575908130, 269831383071⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 89128960 91750400 355205120 367001600 ⟨⟨264555501677, 264555501687⟩, ⟨248907771399, 280707120633⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 91750400 94371840 355205120 367001600 ⟨⟨260494438280, 260494438293⟩, ⟨245092629315, 276391065217⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 83886080 94371840 319815680 367001600 t = true :=
  ⟨_, (join_sr (m := 343408640) (by decide) (join_su (m := 89128960) (by decide) (join_sr (m := 331612160) (by decide) (join_su (m := 86507520) (by decide) (leaf_ok cell0) (join_sr (m := 325713920) (by decide) (leaf_ok cell1) (leaf_ok cell2))) (join_su (m := 86507520) (by decide) (leaf_ok cell3) (leaf_ok cell4))) (join_sr (m := 331612160) (by decide) (join_su (m := 91750400) (by decide) (join_sr (m := 325713920) (by decide) (leaf_ok cell5) (leaf_ok cell6)) (join_sr (m := 325713920) (by decide) (leaf_ok cell7) (leaf_ok cell8))) (join_su (m := 91750400) (by decide) (leaf_ok cell9) (leaf_ok cell10)))) (join_su (m := 89128960) (by decide) (join_sr (m := 355205120) (by decide) (join_su (m := 86507520) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 86507520) (by decide) (leaf_ok cell13) (leaf_ok cell14))) (join_sr (m := 355205120) (by decide) (join_su (m := 91750400) (by decide) (leaf_ok cell15) (leaf_ok cell16)) (join_su (m := 91750400) (by decide) (leaf_ok cell17) (leaf_ok cell18)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/10 : ℝ) (9/80 : ℝ) →
    rho ∈ Set.Icc (61/160 : ℝ) (7/16 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e1 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e2 : (((319815680 : ℤ) : ℝ) / (D : ℝ)) = (61/160 : ℝ) := by norm_num [D]
  have e3 : (((367001600 : ℤ) : ℝ) / (D : ℝ)) = (7/16 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
