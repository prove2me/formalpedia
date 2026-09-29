-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u94371840_96993280_r107479040_119275520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:39:52.458975+00:00
-- url     : https://prove2.me/submissions/d5749f42-bd8e-4190-849c-35742dbb9dd4

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/80, 37/320]`, `ρ ∈ [41/320, 91/640]` by 14 cells of the computing
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
theorem cell0 : cellOK 94371840 95027200 107479040 110428160 ⟨⟨95583888307, 95583888316⟩, ⟨92034371764, 99182699719⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 95027200 95682560 107479040 110428160 ⟨⟨95072614727, 95072614735⟩, ⟨91542247376, 98651809106⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 94371840 95027200 110428160 113377280 ⟨⟨97872723165, 97872723174⟩, ⟨94315886102, 101478592360⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 95027200 95682560 110428160 113377280 ⟨⟨97351731752, 97351731762⟩, ⟨93814033307, 100938000173⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 95682560 96337920 107479040 110428160 ⟨⟨94565812354, 94565812362⟩, ⟨91054381152, 98125609732⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 96337920 96993280 107479040 110428160 ⟨⟨94063414736, 94063414738⟩, ⟨90570710253, 97604031389⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 95682560 96337920 110428160 113377280 ⟨⟨96835264437, 96835264447⟩, ⟨93316492669, 100402150880⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 96337920 96993280 110428160 113377280 ⟨⟨96323254383, 96323254388⟩, ⟨92823200928, 99870973932⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 94371840 95027200 113377280 116326400 ⟨⟨100148727208, 100148727219⟩, ⟨96584719201, 103761505529⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 95027200 95682560 113377280 116326400 ⟨⟨99618176330, 99618176341⟩, ⟨96073294251, 103211372197⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 94371840 95682560 116326400 119275520 ⟨⟨102141520733, 102141520740⟩, ⟨96629312208, 107770628773⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 95682560 96337920 113377280 116326400 ⟨⟨99092200222, 99092200233⟩, ⟨95566233262, 102666031174⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 96337920 96993280 113377280 116326400 ⟨⟨98570731703, 98570731707⟩, ⟨95063472588, 102125411599⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 95682560 96993280 116326400 119275520 ⟨⟨101070839767, 101070839778⟩, ⟨95613663329, 106642871707⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 94371840 96993280 107479040 119275520 t = true :=
  ⟨_, (join_sr (m := 113377280) (by decide) (join_su (m := 95682560) (by decide) (join_sr (m := 110428160) (by decide) (join_su (m := 95027200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 95027200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 110428160) (by decide) (join_su (m := 96337920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 96337920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 95682560) (by decide) (join_sr (m := 116326400) (by decide) (join_su (m := 95027200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 116326400) (by decide) (join_su (m := 96337920) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (leaf_ok cell13))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/80 : ℝ) (37/320 : ℝ) →
    rho ∈ Set.Icc (41/320 : ℝ) (91/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e1 : (((96993280 : ℤ) : ℝ) / (D : ℝ)) = (37/320 : ℝ) := by norm_num [D]
  have e2 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  have e3 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
