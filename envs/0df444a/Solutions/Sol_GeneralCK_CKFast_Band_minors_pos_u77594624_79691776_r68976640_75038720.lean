-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u77594624_79691776_r68976640_75038720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:37:16.244622+00:00
-- url     : https://prove2.me/submissions/3722a663-4207-4c77-84f9-1b087ca9aeb4

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/400, 19/200]`, `ρ ∈ [421/5120, 229/2560]` by 15 cells of the computing
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
theorem cell0 : cellOK 77594624 78118912 68976640 70492160 ⟨⟨74635899039, 74635899048⟩, ⟨71950343113, 77353021793⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 77594624 78118912 70492160 72007680 ⟨⟨76091315677, 76091315686⟩, ⟨73402004671, 78812086227⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 78118912 78643200 68976640 70492160 ⟨⟨74251511359, 74251511368⟩, ⟨71579804565, 76954482109⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 78118912 78643200 70492160 72007680 ⟨⟨75700745602, 75700745614⟩, ⟨73025285058, 78407365047⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 77594624 78118912 72007680 75038720 ⟨⟨78263209078, 78263209087⟩, ⟨74607733329, 81976031640⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 78118912 78643200 72007680 73523200 ⟨⟨77144051360, 77144051369⟩, ⟨74464893275, 79854263489⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 78118912 78643200 73523200 75038720 ⟨⟨78581484487, 78581484499⟩, ⟨75898684176, 81295234204⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 78643200 79167488 68976640 70492160 ⟨⟨73870684659, 73870684669⟩, ⟨71212669229, 76559665858⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 78643200 79167488 70492160 72007680 ⟨⟨75313778005, 75313778014⟩, ⟨72652010526, 78006408363⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 79167488 79691776 68976640 70492160 ⟨⟨73493364666, 73493364674⟩, ⟨70848885553, 76168515933⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 79167488 79691776 70492160 72007680 ⟨⟨74930358184, 74930358195⟩, ⟨72282129087, 77609158675⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 78643200 79167488 72007680 73523200 ⟨⟨76751012997, 76751013009⟩, ⟨74085548878, 79447237305⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 78643200 79167488 73523200 75038720 ⟨⟨78182444489, 78182444498⟩, ⟨75513338257, 80882208416⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 79167488 79691776 72007680 73523200 ⟨⟨76361562473, 76361562482⟩, ⟨73709638006, 79043957751⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 79167488 79691776 73523200 75038720 ⟨⟨77787031386, 77787031397⟩, ⟨75131465309, 80472967884⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 77594624 79691776 68976640 75038720 t = true :=
  ⟨_, (join_su (m := 78643200) (by decide) (join_sr (m := 72007680) (by decide) (join_su (m := 78118912) (by decide) (join_sr (m := 70492160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 70492160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 78118912) (by decide) (leaf_ok cell4) (join_sr (m := 73523200) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_sr (m := 72007680) (by decide) (join_su (m := 79167488) (by decide) (join_sr (m := 70492160) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 70492160) (by decide) (leaf_ok cell9) (leaf_ok cell10))) (join_su (m := 79167488) (by decide) (join_sr (m := 73523200) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_sr (m := 73523200) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/400 : ℝ) (19/200 : ℝ) →
    rho ∈ Set.Icc (421/5120 : ℝ) (229/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((77594624 : ℤ) : ℝ) / (D : ℝ)) = (37/400 : ℝ) := by norm_num [D]
  have e1 : (((79691776 : ℤ) : ℝ) / (D : ℝ)) = (19/200 : ℝ) := by norm_num [D]
  have e2 : (((68976640 : ℤ) : ℝ) / (D : ℝ)) = (421/5120 : ℝ) := by norm_num [D]
  have e3 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
