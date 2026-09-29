-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u83886080_89128960_r107479040_119275520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:30:25.56809+00:00
-- url     : https://prove2.me/submissions/a63e1ee3-fd4e-4541-b6d4-9f09065749dd

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/10, 17/160]`, `ρ ∈ [41/320, 91/640]` by 18 cells of the computing
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
theorem cell0 : cellOK 83886080 85196800 107479040 110428160 ⟨⟨104135069147, 104135069157⟩, ⟨98171322750, 110236828545⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 83886080 85196800 110428160 113377280 ⟨⟨106581577549, 106581577560⟩, ⟨100605012291, 112695375815⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 85196800 86507520 107479040 110428160 ⟨⟨102960363259, 102960363268⟩, ⟨97063218838, 108992801860⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 85196800 86507520 110428160 113377280 ⟨⟨105385758364, 105385758373⟩, ⟨99475723943, 111430343043⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 83886080 85196800 113377280 116326400 ⟨⟨109012486506, 109012486515⟩, ⟨103023385025, 115138043822⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 83886080 85196800 116326400 119275520 ⟨⟨111428038792, 111428038802⟩, ⟨105426676422, 117565082722⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 85196800 86507520 113377280 116326400 ⟨⟨107795947288, 107795947298⟩, ⟨101873297601, 113852405783⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 85196800 86507520 116326400 119275520 ⟨⟨110191163477, 110191163486⟩, ⟨104256166284, 116259230575⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 86507520 87162880 107479040 110428160 ⟨⟨102094098449, 102094098451⟩, ⟨98296737620, 105946970567⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 87162880 87818240 107479040 110428160 ⟨⟨101523449842, 101523449851⟩, ⟨97748109490, 105353737224⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 86507520 87818240 110428160 113377280 ⟨⟨104212610433, 104212610444⟩, ⟨98367486136, 110189687648⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 87818240 88473600 107479040 110428160 ⟨⟨100958187952, 100958187961⟩, ⟨97204604412, 104766163272⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 88473600 89128960 107479040 110428160 ⟨⟨100398227217, 100398227226⟩, ⟨96666141623, 104184158166⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 87818240 89128960 110428160 113377280 ⟨⟨103061415602, 103061415607⟩, ⟨97279639617, 108972628898⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 86507520 87818240 113377280 116326400 ⟨⟨106602301174, 106602301186⟩, ⟨100744492699, 112591355070⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 86507520 87818240 116326400 119275520 ⟨⟨108977392131, 108977392140⟩, ⟨103107159850, 114978164555⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 87818240 89128960 113377280 116326400 ⟨⟨105430827552, 105430827557⟩, ⟨99636307916, 111354109281⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 87818240 89128960 116326400 119275520 ⟨⟨107786002053, 107786002057⟩, ⟨101978991944, 113721100967⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 83886080 89128960 107479040 119275520 t = true :=
  ⟨_, (join_su (m := 86507520) (by decide) (join_sr (m := 113377280) (by decide) (join_su (m := 85196800) (by decide) (join_sr (m := 110428160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 110428160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 85196800) (by decide) (join_sr (m := 116326400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 116326400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 113377280) (by decide) (join_su (m := 87818240) (by decide) (join_sr (m := 110428160) (by decide) (join_su (m := 87162880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 110428160) (by decide) (join_su (m := 88473600) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (leaf_ok cell13))) (join_su (m := 87818240) (by decide) (join_sr (m := 116326400) (by decide) (leaf_ok cell14) (leaf_ok cell15)) (join_sr (m := 116326400) (by decide) (leaf_ok cell16) (leaf_ok cell17)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/10 : ℝ) (17/160 : ℝ) →
    rho ∈ Set.Icc (41/320 : ℝ) (91/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e1 : (((89128960 : ℤ) : ℝ) / (D : ℝ)) = (17/160 : ℝ) := by norm_num [D]
  have e2 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  have e3 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
