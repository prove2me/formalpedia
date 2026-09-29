-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u83886080_89128960_r119275520_131072000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:41:19.472711+00:00
-- url     : https://prove2.me/submissions/0f2fddd5-58f0-4dfb-9d04-c04ab2498d70

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/10, 17/160]`, `ρ ∈ [91/640, 5/32]` by 16 cells of the computing
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
theorem cell0 : cellOK 83886080 85196800 119275520 122224640 ⟨⟨113828472043, 113828472055⟩, ⟨107815117021, 119976737313⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 83886080 85196800 122224640 125173760 ⟨⟨116214018905, 116214018914⟩, ⟨110188932586, 122373247183⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 85196800 86507520 119275520 122224640 ⟨⟨112571635505, 112571635516⟩, ⟨106624551800, 118651052824⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 85196800 86507520 122224640 125173760 ⟨⟨114937587216, 114937587225⟩, ⟨108978671420, 121028103008⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 83886080 85196800 125173760 128122880 ⟨⟨118584907159, 118584907168⟩, ⟨112548344224, 124754846850⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 83886080 85196800 128122880 131072000 ⟨⟨120941359862, 120941359874⟩, ⟨114893568509, 127121765911⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 85196800 86507520 125173760 128122880 ⟨⟨117289237837, 117289237849⟩, ⟨111318737997, 123390606796⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 85196800 86507520 128122880 131072000 ⟨⟨119626802122, 119626802134⟩, ⟨113644960087, 125738785184⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 86507520 87818240 119275520 122224640 ⟨⟨111338103205, 111338103214⟩, ⟨105455701038, 117350342531⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 86507520 87818240 122224640 125173760 ⟨⟨113684649811, 113684649821⟩, ⟨107790325404, 119708110749⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 87818240 89128960 119275520 122224640 ⟨⟨110127150708, 110127150712⟩, ⟨104307897137, 116073821793⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 87818240 89128960 122224640 125173760 ⟨⟨112454480866, 112454480868⟩, ⟨106623224855, 118412485158⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 86507520 87818240 125173760 128122880 ⟨⟨116017242994, 116017243006⟩, ⟨110111237899, 122051686406⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 86507520 87818240 128122880 131072000 ⟨⟨118336089540, 118336089552⟩, ⟨112418639387, 124381282263⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 87818240 89128960 125173760 128122880 ⟨⟨114768195721, 114768195725⟩, ⟨108925172471, 120737300142⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 87818240 89128960 128122880 131072000 ⟨⟨117068494433, 117068494437⟩, ⟨111213933487, 123048471612⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 83886080 89128960 119275520 131072000 t = true :=
  ⟨_, (join_su (m := 86507520) (by decide) (join_sr (m := 125173760) (by decide) (join_su (m := 85196800) (by decide) (join_sr (m := 122224640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 122224640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 85196800) (by decide) (join_sr (m := 128122880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 128122880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 125173760) (by decide) (join_su (m := 87818240) (by decide) (join_sr (m := 122224640) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 122224640) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 87818240) (by decide) (join_sr (m := 128122880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 128122880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/10 : ℝ) (17/160 : ℝ) →
    rho ∈ Set.Icc (91/640 : ℝ) (5/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e1 : (((89128960 : ℤ) : ℝ) / (D : ℝ)) = (17/160 : ℝ) := by norm_num [D]
  have e2 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  have e3 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
