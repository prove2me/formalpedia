-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u83886080_104857600_r555745280_602931200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:01:14.644496+00:00
-- url     : https://prove2.me/submissions/44d8bb49-1b45-4491-917f-2f9b777dcbb2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/10, 1/8]`, `ρ ∈ [53/80, 23/32]` by 20 cells of the computing
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
theorem cell0 : cellOK 83886080 89128960 555745280 567541760 ⟨⟨374159269223, 374159269236⟩, ⟨348291877567, 400880728715⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 83886080 89128960 567541760 579338240 ⟨⟨379790999837, 379790999850⟩, ⟨353891723040, 406520607464⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 89128960 94371840 555745280 567541760 ⟨⟨364705026602, 364705026611⟩, ⟨339399363902, 390862885896⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 89128960 94371840 567541760 579338240 ⟨⟨370287708266, 370287708271⟩, ⟨344940424305, 396465177119⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 83886080 89128960 579338240 591134720 ⟨⟨385385335925, 385385335938⟩, ⟨359454753190, 412122790325⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 83886080 89128960 591134720 602931200 ⟨⟨390943847851, 390943847865⟩, ⟨364982481721, 417688890780⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 89128960 94371840 579338240 591134720 ⟨⟨375834332103, 375834332111⟩, ⟨350446123474, 402030934528⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 89128960 94371840 591134720 602931200 ⟨⟨381346381567, 381346381575⟩, ⟨355917887421, 407561688101⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 94371840 96993280 555745280 567541760 ⟨⟨357791169888, 357791169901⟩, ⟨342274948442, 373628655486⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 96993280 99614720 555745280 567541760 ⟨⟨353261961796, 353261961802⟩, ⟨337924885053, 368919179787⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 94371840 99614720 567541760 579338240 ⟨⟨361048046207, 361048046220⟩, ⟨336231440915, 386693336853⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 99614720 102236160 555745280 567541760 ⟨⟨348794359107, 348794359122⟩, ⟨333633208039, 364274432650⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 102236160 104857600 555745280 567541760 ⟨⟨344386401991, 344386402004⟩, ⟨329398059973, 359692359956⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 99614720 102236160 567541760 579338240 ⟨⟨354281041575, 354281041588⟩, ⟨339099604873, 369773538145⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 102236160 104857600 567541760 579338240 ⟨⟨349843519534, 349843519547⟩, ⟨334832289416, 365164803902⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 94371840 99614720 579338240 591134720 ⟨⟨366542664058, 366542664070⟩, ⟨341676384243, 392217421147⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 94371840 99614720 591134720 602931200 ⟨⟨372003991080, 372003991093⟩, ⟨347088765616, 397707647342⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 99614720 102236160 579338240 591134720 ⟨⟨359734073786, 359734073799⟩, ⟨344532776399, 375238649977⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 102236160 104857600 579338240 591134720 ⟨⟨355267683184, 355267683197⟩, ⟨340234015015, 370603916539⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell19 : cellOK 99614720 104857600 591134720 602931200 ⟨⟨362900486627, 362900486640⟩, ⟨338480305642, 388109421666⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 83886080 104857600 555745280 602931200 t = true :=
  ⟨_, (join_su (m := 94371840) (by decide) (join_sr (m := 579338240) (by decide) (join_su (m := 89128960) (by decide) (join_sr (m := 567541760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 567541760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 89128960) (by decide) (join_sr (m := 591134720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 591134720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 579338240) (by decide) (join_su (m := 99614720) (by decide) (join_sr (m := 567541760) (by decide) (join_su (m := 96993280) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 567541760) (by decide) (join_su (m := 102236160) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 102236160) (by decide) (leaf_ok cell13) (leaf_ok cell14)))) (join_su (m := 99614720) (by decide) (join_sr (m := 591134720) (by decide) (leaf_ok cell15) (leaf_ok cell16)) (join_sr (m := 591134720) (by decide) (join_su (m := 102236160) (by decide) (leaf_ok cell17) (leaf_ok cell18)) (leaf_ok cell19)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/10 : ℝ) (1/8 : ℝ) →
    rho ∈ Set.Icc (53/80 : ℝ) (23/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e1 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e2 : (((555745280 : ℤ) : ℝ) / (D : ℝ)) = (53/80 : ℝ) := by norm_num [D]
  have e3 : (((602931200 : ℤ) : ℝ) / (D : ℝ)) = (23/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
