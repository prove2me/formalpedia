-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u83886080_89128960_r142868480_154664960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:39:51.879155+00:00
-- url     : https://prove2.me/submissions/51fc8332-aee4-494f-8f49-31416e081f53

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/10, 17/160]`, `ρ ∈ [109/640, 59/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 83886080 85196800 142868480 145817600 ⟨⟨132514582283, 132514582293⟩, ⟨126414157922, 138743859754⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 83886080 85196800 145817600 148766720 ⟨⟨134788856974, 134788856984⟩, ⟨128678567481, 141027257285⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 85196800 86507520 142868480 145817600 ⟨⟨131110545683, 131110545692⟩, ⟨125075415823, 137272219630⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 85196800 86507520 145817600 148766720 ⟨⟨133367865261, 133367865271⟩, ⟨127322723832, 139538840379⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 83886080 85196800 148766720 151715840 ⟨⟨137050135486, 137050135498⟩, ⟨130930188658, 143297454255⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 83886080 85196800 151715840 154664960 ⟨⟨139298607361, 139298607370⟩, ⟨133169205867, 145554645356⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 85196800 86507520 148766720 151715840 ⟨⟨135612485824, 135612485834⟩, ⟨129557535995, 141792562016⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 85196800 86507520 151715840 154664960 ⟨⟨137844590265, 137844590275⟩, ⟨131780030284, 144033572388⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 86507520 87818240 142868480 145817600 ⟨⟨129731076316, 129731076326⟩, ⟨123759739605, 135826715575⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 86507520 87818240 145817600 148766720 ⟨⟨131971561028, 131971561040⟩, ⟨125990077759, 138076666876⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 87818240 89128960 142868480 145817600 ⟨⟨128375446610, 128375446615⟩, ⟨122466453038, 134406566011⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 87818240 89128960 145817600 148766720 ⟨⟨130599217431, 130599217436⟩, ⟨124679953080, 136639956685⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 86507520 87818240 148766720 151715840 ⟨⟨134199636482, 134199636494⟩, ⟨128208205248, 140314013086⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 86507520 87818240 151715840 154664960 ⟨⟨136415479185, 136415479194⟩, ⟨130414293855, 142538935461⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 87818240 89128960 148766720 151715840 ⟨⟨132810861547, 132810861552⟩, ⟨126881520495, 138861029046⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 87818240 89128960 151715840 154664960 ⟨⟨135010549327, 135010549330⟩, ⟨129071321121, 141069958022⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 83886080 89128960 142868480 154664960 t = true :=
  ⟨_, (join_su (m := 86507520) (by decide) (join_sr (m := 148766720) (by decide) (join_su (m := 85196800) (by decide) (join_sr (m := 145817600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 145817600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 85196800) (by decide) (join_sr (m := 151715840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 151715840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 148766720) (by decide) (join_su (m := 87818240) (by decide) (join_sr (m := 145817600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 145817600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 87818240) (by decide) (join_sr (m := 151715840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 151715840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/10 : ℝ) (17/160 : ℝ) →
    rho ∈ Set.Icc (109/640 : ℝ) (59/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e1 : (((89128960 : ℤ) : ℝ) / (D : ℝ)) = (17/160 : ℝ) := by norm_num [D]
  have e2 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  have e3 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
