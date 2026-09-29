-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u99614720_104857600_r225443840_249036800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:53:21.139925+00:00
-- url     : https://prove2.me/submissions/0f539ea0-08d1-4272-85d4-b914c74b03d3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/160, 1/8]`, `ρ ∈ [43/160, 19/64]` by 15 cells of the computing
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
theorem cell0 : cellOK 99614720 100925440 225443840 231342080 ⟨⟨172906956580, 172906956589⟩, ⟨165724079605, 180238750661⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 100925440 102236160 225443840 231342080 ⟨⟨171387590954, 171387590959⟩, ⟨164269334987, 178652759420⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 99614720 100925440 231342080 237240320 ⟨⟨176579682227, 176579682236⟩, ⟨169381602825, 183925167616⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 100925440 102236160 231342080 237240320 ⟨⟨175039312246, 175039312249⟩, ⟨167905524709, 182318552931⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 102236160 103546880 225443840 231342080 ⟨⟨169887476464, 169887476474⟩, ⟨162832733778, 177087168758⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 103546880 104857600 225443840 231342080 ⟨⟨168406174395, 168406174404⟩, ⟨161413865939, 175541510106⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 102236160 103546880 231342080 237240320 ⟨⟨173518222423, 173518222433⟩, ⟨166447636215, 180732348870⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 103546880 104857600 231342080 237240320 ⟨⟨172015977358, 172015977369⟩, ⟨165007529888, 179166090980⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 99614720 100925440 237240320 243138560 ⟨⟨180224702582, 180224702591⟩, ⟨173011872882, 187583439578⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 100925440 102236160 237240320 243138560 ⟨⟨178663844885, 178663844890⟩, ⟨171514971371, 185956723679⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 99614720 102236160 243138560 249036800 ⟨⟨183049777153, 183049777163⟩, ⟨171764078307, 194694814317⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 102236160 103546880 237240320 243138560 ⟨⟨177122287387, 177122287396⟩, ⟨170036296632, 184350419596⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 103546880 104857600 237240320 243138560 ⟨⟨175599598134, 175599598143⟩, ⟨168575443943, 182764067113⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 102236160 103546880 243138560 249036800 ⟨⟨180700260801, 180700260811⟩, ⟨173599288286, 187941986551⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 103546880 104857600 243138560 249036800 ⟨⟨179157609682, 179157609693⟩, ⟨172118165383, 186336027147⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 99614720 104857600 225443840 249036800 t = true :=
  ⟨_, (join_sr (m := 237240320) (by decide) (join_su (m := 102236160) (by decide) (join_sr (m := 231342080) (by decide) (join_su (m := 100925440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 100925440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 231342080) (by decide) (join_su (m := 103546880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 103546880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 102236160) (by decide) (join_sr (m := 243138560) (by decide) (join_su (m := 100925440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 243138560) (by decide) (join_su (m := 103546880) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 103546880) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/160 : ℝ) (1/8 : ℝ) →
    rho ∈ Set.Icc (43/160 : ℝ) (19/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((99614720 : ℤ) : ℝ) / (D : ℝ)) = (19/160 : ℝ) := by norm_num [D]
  have e1 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e2 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e3 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
