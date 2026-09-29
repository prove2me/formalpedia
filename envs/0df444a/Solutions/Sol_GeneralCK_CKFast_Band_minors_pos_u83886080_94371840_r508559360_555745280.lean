-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u83886080_94371840_r508559360_555745280
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:59:56.003216+00:00
-- url     : https://prove2.me/submissions/dbf95fa6-afea-4689-ba6d-8a5c4c301f33

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/10, 9/80]`, `ρ ∈ [97/160, 53/80]` by 15 cells of the computing
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
theorem cell0 : cellOK 83886080 86507520 508559360 520355840 ⟨⟨353582510078, 353582510082⟩, ⟨337324710636, 370205969154⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 86507520 89128960 508559360 520355840 ⟨⟨348886195443, 348886195454⟩, ⟨332836016990, 365299825941⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 83886080 86507520 520355840 532152320 ⟨⟨359393898406, 359393898414⟩, ⟨343133266215, 376009667331⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 86507520 89128960 520355840 532152320 ⟨⟨354671086279, 354671086292⟩, ⟨338614379766, 371081136506⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 89128960 91750400 508559360 520355840 ⟨⟨344265155465, 344265155478⟩, ⟨328418197548, 360473268106⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 91750400 94371840 508559360 520355840 ⟨⟨339716735250, 339716735263⟩, ⟨324068758880, 355723489784⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 89128960 91750400 520355840 532152320 ⟨⟨350022348539, 350022348552⟩, ⟨334165353594, 366230791243⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 91750400 94371840 520355840 532152320 ⟨⟨345445094926, 345445094939⟩, ⟨329783750176, 361455899392⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 83886080 86507520 532152320 543948800 ⟨⟨365160529657, 365160529664⟩, ⟨348897406168, 381768445210⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 86507520 89128960 532152320 543948800 ⟨⟨360412083776, 360412083789⟩, ⟨344349246180, 376818318992⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 83886080 89128960 543948800 555745280 ⟨⟨368488512454, 368488512470⟩, ⟨342653645728, 395201475728⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 89128960 91750400 532152320 543948800 ⟨⟨355736519893, 355736519906⟩, ⟨339869933918, 371944993943⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 91750400 94371840 532152320 543948800 ⟨⟨351131310234, 351131310246⟩, ⟨335457086121, 367145808924⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 89128960 91750400 543948800 555745280 ⟨⟨361409424132, 361409424145⟩, ⟨345533648011, 377617669757⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 91750400 94371840 543948800 555745280 ⟨⟨356777081124, 356777081137⟩, ⟨341090421502, 372794957983⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 83886080 94371840 508559360 555745280 t = true :=
  ⟨_, (join_sr (m := 532152320) (by decide) (join_su (m := 89128960) (by decide) (join_sr (m := 520355840) (by decide) (join_su (m := 86507520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 86507520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 520355840) (by decide) (join_su (m := 91750400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 91750400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 89128960) (by decide) (join_sr (m := 543948800) (by decide) (join_su (m := 86507520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 543948800) (by decide) (join_su (m := 91750400) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 91750400) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/10 : ℝ) (9/80 : ℝ) →
    rho ∈ Set.Icc (97/160 : ℝ) (53/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e1 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e2 : (((508559360 : ℤ) : ℝ) / (D : ℝ)) = (97/160 : ℝ) := by norm_num [D]
  have e3 : (((555745280 : ℤ) : ℝ) / (D : ℝ)) = (53/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
