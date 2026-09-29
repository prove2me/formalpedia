-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u75497472_83886080_r256901120_281149440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:55:22.726419+00:00
-- url     : https://prove2.me/submissions/89e7b383-7e5d-47cf-b766-cc32cfae19ae

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/100, 1/10]`, `ρ ∈ [49/160, 429/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 75497472 77594624 256901120 262963200 ⟨⟨225575776753, 225575776766⟩, ⟨213996329420, 237485162909⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 75497472 77594624 262963200 269025280 ⟨⟨229539272843, 229539272856⟩, ⟨217951023589, 241452762127⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 77594624 79691776 256901120 262963200 ⟨⟨222284515695, 222284515703⟩, ⟨210884367037, 234007534312⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 77594624 79691776 262963200 269025280 ⟨⟨226219680394, 226219680402⟩, ⟨214809064045, 237948718523⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 75497472 77594624 269025280 275087360 ⟨⟨233467349393, 233467349406⟩, ⟨221870884879, 245384422499⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 75497472 77594624 275087360 281149440 ⟨⟨237360949383, 237360949396⟩, ⟨225756825184, 249281116786⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 77594624 79691776 269025280 275087360 ⟨⟨230120361372, 230120361378⟩, ⟨218699866912, 241854890036⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 77594624 79691776 275087360 281149440 ⟨⟨233987462292, 233987462296⟩, ⟨222557649297, 245726981423⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 79691776 81788928 256901120 262963200 ⟨⟨219068343665, 219068343678⟩, ⟨207841981187, 230610742584⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 79691776 81788928 262963200 269025280 ⟨⟨222974832724, 222974832734⟩, ⟨211736453208, 234525037054⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 81788928 83886080 256901120 262963200 ⟨⟨215924228683, 215924228696⟩, ⟨204866394439, 227291491279⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 81788928 83886080 262963200 269025280 ⟨⟨219801740002, 219801740015⟩, ⟨208730447866, 231178472280⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 79691776 81788928 269025280 275087360 ⟨⟨226847755172, 226847755186⟩, ⟨215597948978, 238405229018⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 79691776 81788928 275087360 281149440 ⟨⟨230687976966, 230687976979⟩, ⟨219427305525, 242252212434⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 81788928 83886080 269025280 275087360 ⟨⟨223646582918, 223646582931⟩, ⟨212562422133, 235032244492⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 81788928 83886080 275087360 281149440 ⟨⟨227459587215, 227459587228⟩, ⟨216363119177, 238853664776⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 75497472 83886080 256901120 281149440 t = true :=
  ⟨_, (join_su (m := 79691776) (by decide) (join_sr (m := 269025280) (by decide) (join_su (m := 77594624) (by decide) (join_sr (m := 262963200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 262963200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 77594624) (by decide) (join_sr (m := 275087360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 275087360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 269025280) (by decide) (join_su (m := 81788928) (by decide) (join_sr (m := 262963200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 262963200) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 81788928) (by decide) (join_sr (m := 275087360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 275087360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/100 : ℝ) (1/10 : ℝ) →
    rho ∈ Set.Icc (49/160 : ℝ) (429/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e1 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e2 : (((256901120 : ℤ) : ℝ) / (D : ℝ)) = (49/160 : ℝ) := by norm_num [D]
  have e3 : (((281149440 : ℤ) : ℝ) / (D : ℝ)) = (429/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
