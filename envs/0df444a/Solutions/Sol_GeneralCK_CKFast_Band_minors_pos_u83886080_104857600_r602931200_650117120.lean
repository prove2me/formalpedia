-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u83886080_104857600_r602931200_650117120
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:01:18.817721+00:00
-- url     : https://prove2.me/submissions/d70e8399-0251-42bc-8597-244c062f2afb

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/10, 1/8]`, `ρ ∈ [23/32, 31/40]` by 16 cells of the computing
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
theorem cell0 : cellOK 83886080 89128960 602931200 614727680 ⟨⟨396468048125, 396468048138⟩, ⟨370476368116, 423220461144⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 83886080 89128960 614727680 626524160 ⟨⟨401959394595, 401959394608⟩, ⟨375937820550, 428718996010⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 89128960 94371840 602931200 614727680 ⟨⟨386825287270, 386825287279⟩, ⟨361357092758, 413058911735⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 89128960 94371840 614727680 626524160 ⟨⟨392272429835, 392272429845⟩, ⟨366765069295, 418524026327⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 83886080 89128960 626524160 638320640 ⟨⟨407419293437, 407419293450⟩, ⟨381368198634, 434185935482⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 83886080 89128960 638320640 650117120 ⟨⟨412849101970, 412849101984⟩, ⟨386768815989, 439622668202⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 89128960 94371840 626524160 638320640 ⟨⟨397689142562, 397689142567⟩, ⟨372143102470, 423958402666⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 89128960 94371840 638320640 650117120 ⟨⟨403076713928, 403076713937⟩, ⟨377492435660, 429363364145⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 94371840 99614720 602931200 614727680 ⟨⟨377433377800, 377433377814⟩, ⟨352469881550, 403165411339⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 94371840 99614720 614727680 626524160 ⟨⟨382832129130, 382832129145⟩, ⟨357820985943, 408592060528⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 99614720 104857600 602931200 614727680 ⟨⟨368276496282, 368276496294⟩, ⟨343800227237, 393523044473⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 99614720 104857600 614727680 626524160 ⟨⟨373623023770, 373623023785⟩, ⟨349091358352, 398906599073⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 94371840 99614720 626524160 638320640 ⟨⟨388201506748, 388201506760⟩, ⟨363143292239, 413988896365⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 94371840 99614720 638320640 650117120 ⟨⟨393542731325, 393542731338⟩, ⟨368437975473, 419357176798⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 99614720 104857600 626524160 638320640 ⟨⟨378941260798, 378941260811⟩, ⟨354354842811, 404261318196⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 99614720 104857600 638320640 650117120 ⟨⟨384232361642, 384232361655⟩, ⟨359591789435, 409588394751⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 83886080 104857600 602931200 650117120 t = true :=
  ⟨_, (join_su (m := 94371840) (by decide) (join_sr (m := 626524160) (by decide) (join_su (m := 89128960) (by decide) (join_sr (m := 614727680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 614727680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 89128960) (by decide) (join_sr (m := 638320640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 638320640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 626524160) (by decide) (join_su (m := 99614720) (by decide) (join_sr (m := 614727680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 614727680) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 99614720) (by decide) (join_sr (m := 638320640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 638320640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/10 : ℝ) (1/8 : ℝ) →
    rho ∈ Set.Icc (23/32 : ℝ) (31/40 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e1 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e2 : (((602931200 : ℤ) : ℝ) / (D : ℝ)) = (23/32 : ℝ) := by norm_num [D]
  have e3 : (((650117120 : ℤ) : ℝ) / (D : ℝ)) = (31/40 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
