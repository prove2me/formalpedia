-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u75497472_83886080_r402391040_450887680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:57:28.998103+00:00
-- url     : https://prove2.me/submissions/ea90a4e7-92ec-4a78-ba5d-0071e0fd6e41

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/100, 1/10]`, `ρ ∈ [307/640, 43/80]` by 13 cells of the computing
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
theorem cell0 : cellOK 75497472 77594624 402391040 414515200 ⟨⟨314206558349, 314206558362⟩, ⟨298922234990, 329880427415⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 77594624 79691776 402391040 414515200 ⟨⟨310423473551, 310423473557⟩, ⟨295335248053, 325896610242⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 75497472 77594624 414515200 426639360 ⟨⟨320810320553, 320810320564⟩, ⟨305539677879, 336458146169⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 77594624 79691776 414515200 426639360 ⟨⟨317000365639, 317000365646⟩, ⟨301921873325, 332451876193⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 79691776 81788928 402391040 414515200 ⟨⟨306704117712, 306704117725⟩, ⟨291807657198, 321980892427⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 81788928 83886080 402391040 414515200 ⟨⟨303046365533, 303046365546⟩, ⟨288337491668, 318130996973⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 79691776 81788928 414515200 426639360 ⟨⟨313253112745, 313253112759⟩, ⟨298362630927, 328512468678⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 81788928 83886080 414515200 426639360 ⟨⟨309566496220, 309566496233⟩, ⟨294860030251, 324637716240⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 75497472 79691776 426639360 438763520 ⟨⟨325413572993, 325413573006⟩, ⟨302410945285, 349284304747⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 75497472 79691776 438763520 450887680 ⟨⟨331858887277, 331858887290⟩, ⟨308846993150, 355713607703⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 79691776 81788928 426639360 438763520 ⟨⟨319729863647, 319729863661⟩, ⟨304846069806, 334971372400⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 81788928 83886080 426639360 438763520 ⟨⟨316015726220, 316015726233⟩, ⟨301312436710, 331073026369⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 79691776 83886080 438763520 450887680 ⟨⟨324260171752, 324260171763⟩, ⟨301762686734, 347586526281⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 75497472 83886080 402391040 450887680 t = true :=
  ⟨_, (join_sr (m := 426639360) (by decide) (join_su (m := 79691776) (by decide) (join_sr (m := 414515200) (by decide) (join_su (m := 77594624) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 77594624) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 414515200) (by decide) (join_su (m := 81788928) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 81788928) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 79691776) (by decide) (join_sr (m := 438763520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 438763520) (by decide) (join_su (m := 81788928) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (leaf_ok cell12))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/100 : ℝ) (1/10 : ℝ) →
    rho ∈ Set.Icc (307/640 : ℝ) (43/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e1 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e2 : (((402391040 : ℤ) : ℝ) / (D : ℝ)) = (307/640 : ℝ) := by norm_num [D]
  have e3 : (((450887680 : ℤ) : ℝ) / (D : ℝ)) = (43/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
