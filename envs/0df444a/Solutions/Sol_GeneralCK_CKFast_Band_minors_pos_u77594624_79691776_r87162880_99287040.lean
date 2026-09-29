-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u77594624_79691776_r87162880_99287040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:40:37.049117+00:00
-- url     : https://prove2.me/submissions/406cf753-a7e1-4166-9f7a-7b79143b7261

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/400, 19/200]`, `ρ ∈ [133/1280, 303/2560]` by 12 cells of the computing
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
theorem cell0 : cellOK 77594624 78118912 87162880 90193920 ⟨⟨92411259328, 92411259340⟩, ⟨88716109097, 96161550415⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 78118912 78643200 87162880 90193920 ⟨⟨91954457697, 91954457706⟩, ⟨88278880124, 95684651639⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 77594624 78118912 90193920 93224960 ⟨⟨95174578623, 95174578635⟩, ⟨91472319638, 98931546412⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 78118912 78643200 90193920 93224960 ⟨⟨94707111126, 94707111136⟩, ⟨91024397306, 98444017551⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 78643200 79167488 87162880 90193920 ⟨⟨91501666477, 91501666486⟩, ⟨87845448734, 95211983833⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 79167488 79691776 87162880 90193920 ⟨⟨91052827380, 91052827392⟩, ⟨87415760172, 94743485033⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 78643200 79167488 90193920 93224960 ⟨⟨94243713249, 94243713259⟩, ⟨90580333252, 97960777203⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 79167488 79691776 90193920 93224960 ⟨⟨93784326281, 93784326293⟩, ⟨90140072246, 97481763023⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 77594624 78643200 93224960 96256000 ⟨⟨97677265240, 97677265249⟩, ⟨92239020515, 103234280339⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 77594624 78643200 96256000 99287040 ⟨⟨100393528597, 100393528609⟩, ⟨94943466255, 105961545027⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 78643200 79691776 93224960 96256000 ⟨⟨96729704357, 96729704369⟩, ⟨91345452279, 102230616311⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 78643200 79691776 96256000 99287040 ⟨⟨99425667548, 99425667557⟩, ⟨94029529254, 104937681055⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 77594624 79691776 87162880 99287040 t = true :=
  ⟨_, (join_sr (m := 93224960) (by decide) (join_su (m := 78643200) (by decide) (join_sr (m := 90193920) (by decide) (join_su (m := 78118912) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 78118912) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 90193920) (by decide) (join_su (m := 79167488) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 79167488) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 78643200) (by decide) (join_sr (m := 96256000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 96256000) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/400 : ℝ) (19/200 : ℝ) →
    rho ∈ Set.Icc (133/1280 : ℝ) (303/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((77594624 : ℤ) : ℝ) / (D : ℝ)) = (37/400 : ℝ) := by norm_num [D]
  have e1 : (((79691776 : ℤ) : ℝ) / (D : ℝ)) = (19/200 : ℝ) := by norm_num [D]
  have e2 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  have e3 : (((99287040 : ℤ) : ℝ) / (D : ℝ)) = (303/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
