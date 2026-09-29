-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u99614720_104857600_r142868480_154664960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:45:44.256798+00:00
-- url     : https://prove2.me/submissions/8cde33eb-d282-48fb-839e-f86adc55706b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/160, 1/8]`, `ρ ∈ [109/640, 59/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 99614720 100925440 142868480 145817600 ⟨⟨117140840106, 117140840115⟩, ⟨111735107323, 122651646307⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 99614720 100925440 145817600 148766720 ⟨⟨119219667923, 119219667933⟩, ⟨113802938825, 124741029402⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 100925440 102236160 142868480 145817600 ⟨⟨115989333058, 115989333063⟩, ⟨110633816474, 121448273843⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 100925440 102236160 145817600 148766720 ⟨⟨118052662345, 118052662349⟩, ⟨112686103930, 123522222522⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 99614720 100925440 148766720 151715840 ⟨⟨121288619177, 121288619186⟩, ⟨115861050232, 126820380135⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 99614720 100925440 151715840 154664960 ⟨⟨123347818480, 123347818489⟩, ⟨117909563041, 128889826267⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 100925440 102236160 148766720 151715840 ⟨⟨120106335721, 120106335727⟩, ⟨114728888134, 125586363174⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 100925440 102236160 151715840 154664960 ⟨⟨122150473619, 122150473622⟩, ⟨116762286520, 127640819257⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 102236160 103546880 142868480 145817600 ⟨⟨114855299881, 114855299890⟩, ⟨109548986325, 120263431198⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 102236160 103546880 145817600 148766720 ⟨⟨116903250204, 116903250215⟩, ⟨111585854918, 122322058638⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 103546880 104857600 142868480 145817600 ⟨⟨113738282138, 113738282146⟩, ⟨108480188937, 119096627925⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 103546880 104857600 145817600 148766720 ⟨⟨115770972374, 115770972385⟩, ⟨110501762839, 121140046971⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 102236160 103546880 148766720 151715840 ⟨⟨118941759980, 118941759989⟩, ⟨113613431879, 124371097034⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 102236160 103546880 151715840 154664960 ⟨⟨120970945611, 120970945620⟩, ⟨115631830741, 126410665691⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 103546880 104857600 148766720 151715840 ⟨⟨117794432281, 117794432290⟩, ⟨112514251658, 123174090742⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 103546880 104857600 151715840 154664960 ⟨⟨119808774376, 119808774385⟩, ⟨114517765164, 125198874546⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 99614720 104857600 142868480 154664960 t = true :=
  ⟨_, (join_su (m := 102236160) (by decide) (join_sr (m := 148766720) (by decide) (join_su (m := 100925440) (by decide) (join_sr (m := 145817600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 145817600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 100925440) (by decide) (join_sr (m := 151715840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 151715840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 148766720) (by decide) (join_su (m := 103546880) (by decide) (join_sr (m := 145817600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 145817600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 103546880) (by decide) (join_sr (m := 151715840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 151715840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/160 : ℝ) (1/8 : ℝ) →
    rho ∈ Set.Icc (109/640 : ℝ) (59/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((99614720 : ℤ) : ℝ) / (D : ℝ)) = (19/160 : ℝ) := by norm_num [D]
  have e1 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e2 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  have e3 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
