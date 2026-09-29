-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u79691776_81788928_r87162880_99287040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:40:57.486552+00:00
-- url     : https://prove2.me/submissions/fa6fcc14-3982-433a-952a-99714100dedd

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/200, 39/400]`, `ρ ∈ [133/1280, 303/2560]` by 14 cells of the computing
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
theorem cell0 : cellOK 79691776 80216064 87162880 90193920 ⟨⟨90607883273, 90607883283⟩, ⟨86989760748, 94279094500⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 80216064 80740352 87162880 90193920 ⟨⟨90166778136, 90166778145⟩, ⟨86567397824, 93818752685⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 79691776 80216064 90193920 93224960 ⟨⟨93328892662, 93328892674⟩, ⟨89703560133, 97006913904⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 80216064 80740352 90193920 93224960 ⟨⟨92877355950, 92877355959⟩, ⟨89270743808, 96536169920⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 80740352 81264640 87162880 90193920 ⟨⟨89729457040, 89729457049⟩, ⟨86148619772, 93362401223⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 81264640 81788928 87162880 90193920 ⟨⟨89295866122, 89295866134⟩, ⟨85733375960, 92909982882⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 80740352 81264640 90193920 93224960 ⟨⟨92429660791, 92429660801⟩, ⟨88841571173, 96069472329⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 81264640 81788928 90193920 93224960 ⟨⟨91985752902, 91985752913⟩, ⟨88415991131, 95606763520⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 79691776 80216064 93224960 96256000 ⟨⟨96029658104, 96029658113⟩, ⟨92397357930, 99714249671⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 80216064 80740352 93224960 96256000 ⟨⟨95567912255, 95567912267⟩, ⟨91954307605, 99233328899⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 79691776 80740352 96256000 99287040 ⟨⟨98474168212, 98474168223⟩, ⟨93130803861, 103931387641⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 80740352 81264640 93224960 96256000 ⟨⟨95110062560, 95110062572⟩, ⟨91514956912, 98756507610⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 81264640 81788928 93224960 96256000 ⟨⟨94656054358, 94656054367⟩, ⟨91079254340, 98283727862⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 80740352 81788928 96256000 99287040 ⟨⟨97538573331, 97538573343⟩, ⟨92246869626, 102942168465⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 79691776 81788928 87162880 99287040 t = true :=
  ⟨_, (join_sr (m := 93224960) (by decide) (join_su (m := 80740352) (by decide) (join_sr (m := 90193920) (by decide) (join_su (m := 80216064) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 80216064) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 90193920) (by decide) (join_su (m := 81264640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 81264640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 80740352) (by decide) (join_sr (m := 96256000) (by decide) (join_su (m := 80216064) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 96256000) (by decide) (join_su (m := 81264640) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (leaf_ok cell13))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/200 : ℝ) (39/400 : ℝ) →
    rho ∈ Set.Icc (133/1280 : ℝ) (303/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((79691776 : ℤ) : ℝ) / (D : ℝ)) = (19/200 : ℝ) := by norm_num [D]
  have e1 : (((81788928 : ℤ) : ℝ) / (D : ℝ)) = (39/400 : ℝ) := by norm_num [D]
  have e2 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  have e3 : (((99287040 : ℤ) : ℝ) / (D : ℝ)) = (303/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
