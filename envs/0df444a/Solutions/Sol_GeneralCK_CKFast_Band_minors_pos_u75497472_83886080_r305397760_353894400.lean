-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u75497472_83886080_r305397760_353894400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:56:37.246134+00:00
-- url     : https://prove2.me/submissions/011d8054-791c-41c0-9065-041f09e71c07

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/100, 1/10]`, `ρ ∈ [233/640, 27/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 75497472 77594624 305397760 317521920 ⟨⟨258198693856, 258198693869⟩, ⟨242839605782, 274060037314⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 77594624 79691776 305397760 317521920 ⟨⟨254693900928, 254693900936⟩, ⟨239565115799, 270315490024⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 75497472 77594624 317521920 329646080 ⟨⟨265551163942, 265551163952⟩, ⟨250196654984, 281392320873⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 77594624 79691776 317521920 329646080 ⟨⟨262004008338, 262004008341⟩, ⟨246875288032, 277610649185⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 79691776 81788928 305397760 317521920 ⟨⟨251260775323, 251260775336⟩, ⟨236356078283, 266649069820⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 81788928 83886080 305397760 317521920 ⟨⟨247896633481, 247896633495⟩, ⟨233210067321, 263057828454⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 79691776 81788928 317521920 329646080 ⟨⟨258527593406, 258527593417⟩, ⟨243618718554, 273905871517⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 81788928 83886080 317521920 329646080 ⟨⟨255119313114, 255119313125⟩, ⟨240424581949, 270275135237⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 75497472 77594624 329646080 341770240 ⟨⟨272793117569, 272793117582⟩, ⟨257444905248, 288612845123⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 77594624 79691776 329646080 341770240 ⟨⟨269206116551, 269206116559⟩, ⟨254079240853, 284796464639⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 75497472 77594624 341770240 353894400 ⟨⟨279929983125, 279929983138⟩, ⟨264589584053, 295727217879⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 77594624 79691776 341770240 353894400 ⟨⟨276305458112, 276305458118⟩, ⟨261182009884, 291878346859⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 79691776 81788928 329646080 341770240 ⟨⟨265688900256, 265688900269⟩, ⟨250777678491, 281055729944⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 81788928 83886080 329646080 341770240 ⟨⟨262238938073, 262238938087⟩, ⟨247537913856, 277387880609⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 79691776 81788928 341770240 353894400 ⟨⟨272749738783, 272749738794⟩, ⟨257837808427, 288103863826⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 81788928 83886080 341770240 353894400 ⟨⟨269260367760, 269260367771⟩, ⟨254554734494, 284401097151⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 75497472 83886080 305397760 353894400 t = true :=
  ⟨_, (join_sr (m := 329646080) (by decide) (join_su (m := 79691776) (by decide) (join_sr (m := 317521920) (by decide) (join_su (m := 77594624) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 77594624) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 317521920) (by decide) (join_su (m := 81788928) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 81788928) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 79691776) (by decide) (join_sr (m := 341770240) (by decide) (join_su (m := 77594624) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 77594624) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 341770240) (by decide) (join_su (m := 81788928) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 81788928) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/100 : ℝ) (1/10 : ℝ) →
    rho ∈ Set.Icc (233/640 : ℝ) (27/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e1 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e2 : (((305397760 : ℤ) : ℝ) / (D : ℝ)) = (233/640 : ℝ) := by norm_num [D]
  have e3 : (((353894400 : ℤ) : ℝ) / (D : ℝ)) = (27/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
