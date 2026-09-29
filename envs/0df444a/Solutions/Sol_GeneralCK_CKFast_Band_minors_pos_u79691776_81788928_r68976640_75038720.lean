-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u79691776_81788928_r68976640_75038720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:38:27.490556+00:00
-- url     : https://prove2.me/submissions/1a583f08-ebca-4c83-b2d4-e15d68ec3cf3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/200, 39/400]`, `ρ ∈ [421/5120, 229/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 79691776 80216064 68976640 70492160 ⟨⟨73119498216, 73119498226⟩, ⟨70488403046, 75780976422⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 79691776 80216064 70492160 72007680 ⟨⟨74550432572, 74550432581⟩, ⟨71915589822, 77215559662⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 80216064 80740352 68976640 70492160 ⟨⟨72749033248, 72749033257⟩, ⟨70131172247, 75396992549⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 80216064 80740352 70492160 72007680 ⟨⟨74173948687, 74173948698⟩, ⟨71552342847, 76825556161⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 79691776 80216064 72007680 73523200 ⟨⟨75975645814, 75975645826⟩, ⟨73337109323, 78644368129⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 79691776 80216064 73523200 75038720 ⟨⟨77395190835, 77395190846⟩, ⟨74753013600, 80067455550⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 80216064 80740352 72007680 73523200 ⟨⟨75593210156, 75593210166⟩, ⟨72967912547, 78248412892⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 80216064 80740352 73523200 75038720 ⟨⟨77006869591, 77006869600⟩, ⟨74377932463, 79665615506⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 80740352 81264640 68976640 70492160 ⟨⟨72381918752, 72381918760⟩, ⟨69777144693, 75016510685⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 80740352 81264640 70492160 72007680 ⟨⟨73800855122, 73800855131⟩, ⟨71192339280, 76439094143⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 81264640 81788928 68976640 70492160 ⟨⟨72018104760, 72018104769⟩, ⟨69426272897, 74639478278⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 81264640 81788928 70492160 72007680 ⟨⟨73431101500, 73431101512⟩, ⟨70835531221, 76056120678⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 80740352 81264640 72007680 73523200 ⟨⟨75214203694, 75214203706⟩, ⟨72601998387, 77856037645⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 80740352 81264640 73523200 75038720 ⟨⟨76622015481, 76622015492⟩, ⟨74006172222, 79267393002⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 81264640 81788928 72007680 73523200 ⟨⟨74838575678, 74838575687⟩, ⟨72239318553, 77467189080⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 81264640 81788928 73523200 75038720 ⟨⟨76240577386, 76240577395⟩, ⟨73637684206, 78872734375⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 79691776 81788928 68976640 75038720 t = true :=
  ⟨_, (join_su (m := 80740352) (by decide) (join_sr (m := 72007680) (by decide) (join_su (m := 80216064) (by decide) (join_sr (m := 70492160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 70492160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 80216064) (by decide) (join_sr (m := 73523200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 73523200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 72007680) (by decide) (join_su (m := 81264640) (by decide) (join_sr (m := 70492160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 70492160) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 81264640) (by decide) (join_sr (m := 73523200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 73523200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/200 : ℝ) (39/400 : ℝ) →
    rho ∈ Set.Icc (421/5120 : ℝ) (229/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((79691776 : ℤ) : ℝ) / (D : ℝ)) = (19/200 : ℝ) := by norm_num [D]
  have e1 : (((81788928 : ℤ) : ℝ) / (D : ℝ)) = (39/400 : ℝ) := by norm_num [D]
  have e2 : (((68976640 : ℤ) : ℝ) / (D : ℝ)) = (421/5120 : ℝ) := by norm_num [D]
  have e3 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
