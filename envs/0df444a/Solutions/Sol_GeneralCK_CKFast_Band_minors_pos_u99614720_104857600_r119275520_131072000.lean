-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u99614720_104857600_r119275520_131072000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:39:26.893761+00:00
-- url     : https://prove2.me/submissions/1499d020-a0c9-4304-8b70-a1f20c34a81d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/160, 1/8]`, `ρ ∈ [91/640, 5/32]` by 17 cells of the computing
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
theorem cell0 : cellOK 99614720 100925440 119275520 122224640 ⟨⟨100138982342, 100138982352⟩, ⟨94827252906, 105559333186⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 99614720 100925440 122224640 125173760 ⟨⟨102301574677, 102301574686⟩, ⟨96977475461, 107733850278⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 100925440 102236160 119275520 122224640 ⟨⟨99119942712, 99119942718⟩, ⟨93858639626, 104488064548⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 100925440 102236160 122224640 125173760 ⟨⟨101265108321, 101265108323⟩, ⟨95991425543, 106645184443⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 99614720 100925440 125173760 128122880 ⟨⟨104453212665, 104453212676⟩, ⟨99116927972, 109897229069⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 99614720 100925440 128122880 131072000 ⟨⟨106594039391, 106594039399⟩, ⟨101245749736, 112049616472⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 100925440 102236160 125173760 128122880 ⟨⟨103399577479, 103399577485⟩, ⟨98113694325, 108791428802⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 100925440 102236160 128122880 131072000 ⟨⟨105523488220, 105523488224⟩, ⟨100225580379, 110926939317⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 102236160 103546880 119275520 122224640 ⟨⟨98117209801, 98117209809⟩, ⟨92905278386, 103434206676⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 102236160 103546880 122224640 125173760 ⟨⟨100245116730, 100245116739⟩, ⟨95020800516, 105574091765⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 103546880 104202240 119275520 122224640 ⟨⟨97375591959, 97375591967⟩, ⟨94047217559, 100746525579⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 104202240 104857600 119275520 122224640 ⟨⟨96886045791, 96886045799⟩, ⟨93574136680, 100240148772⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 103546880 104857600 122224640 125173760 ⟨⟨99241150938, 99241150946⟩, ⟨94065184101, 104520088785⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 102236160 103546880 125173760 128122880 ⟨⟨102362578400, 102362578408⟩, ⟨97126051832, 107703357258⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 102236160 103546880 128122880 131072000 ⟨⟨104469727983, 104469727991⟩, ⟨99221162045, 109822139831⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 103546880 104857600 125173760 128122880 ⟨⟨101341764555, 101341764565⟩, ⟨96153582005, 106632529425⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 103546880 104857600 128122880 131072000 ⟨⟨103432306103, 103432306111⟩, ⟨98232074230, 108734731649⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 99614720 104857600 119275520 131072000 t = true :=
  ⟨_, (join_su (m := 102236160) (by decide) (join_sr (m := 125173760) (by decide) (join_su (m := 100925440) (by decide) (join_sr (m := 122224640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 122224640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 100925440) (by decide) (join_sr (m := 128122880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 128122880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 125173760) (by decide) (join_su (m := 103546880) (by decide) (join_sr (m := 122224640) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 122224640) (by decide) (join_su (m := 104202240) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (leaf_ok cell12))) (join_su (m := 103546880) (by decide) (join_sr (m := 128122880) (by decide) (leaf_ok cell13) (leaf_ok cell14)) (join_sr (m := 128122880) (by decide) (leaf_ok cell15) (leaf_ok cell16)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/160 : ℝ) (1/8 : ℝ) →
    rho ∈ Set.Icc (91/640 : ℝ) (5/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((99614720 : ℤ) : ℝ) / (D : ℝ)) = (19/160 : ℝ) := by norm_num [D]
  have e1 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e2 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  have e3 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
