-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u94371840_99614720_r201850880_225443840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:48:45.616631+00:00
-- url     : https://prove2.me/submissions/4dc72679-6484-45c9-8eb4-6f77802bf3a7

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/80, 19/160]`, `ρ ∈ [77/320, 43/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 94371840 95682560 201850880 207749120 ⟨⟨163844972975, 163844972977⟩, ⟨156451910170, 171402534057⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 95682560 96993280 201850880 207749120 ⟨⟨162334217315, 162334217327⟩, ⟨155012064896, 169818432852⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 94371840 95682560 207749120 213647360 ⟨⟨167728827754, 167728827761⟩, ⟨160319944362, 175300403358⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 95682560 96993280 207749120 213647360 ⟨⟨166194559457, 166194559466⟩, ⟨158856211383, 173693229336⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 96993280 98304000 201850880 207749120 ⟨⟨160844453871, 160844453883⟩, ⟨153591895411, 168256696217⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 98304000 99614720 201850880 207749120 ⟨⟨159375168156, 159375168167⟩, ⟨152190924076, 166716771110⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 96993280 98304000 207749120 213647360 ⟨⟨164681341221, 164681341232⟩, ⟨157412232969, 172108454402⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 98304000 99614720 207749120 213647360 ⟨⟨163188662151, 163188662160⟩, ⟨155987534095, 170545530163⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 94371840 95682560 213647360 219545600 ⟨⟨171579795728, 171579795733⟩, ⟨164155656520, 179164838317⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 95682560 96993280 213647360 219545600 ⟨⟨170022656386, 170022656398⟩, ⟨162668668612, 177535240607⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 94371840 95682560 219545600 225443840 ⟨⟨175398668255, 175398668260⟩, ⟨167959814554, 182996653676⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 95682560 96993280 219545600 225443840 ⟨⟨173819276094, 173819276106⟩, ⟨166450181872, 181345257289⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 96993280 98304000 213647360 219545600 ⟨⟨168486612790, 168486612800⟩, ⟨161201501789, 175928064483⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 98304000 99614720 213647360 219545600 ⟨⟨166971157833, 166971157845⟩, ⟨159753683888, 174342766401⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 96993280 98304000 219545600 225443840 ⟨⟨172261013910, 172261013920⟩, ⟨164960425260, 179716293712⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 98304000 99614720 219545600 225443840 ⟨⟨170723378590, 170723378602⟩, ⟨163490075613, 178109224418⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 94371840 99614720 201850880 225443840 t = true :=
  ⟨_, (join_sr (m := 213647360) (by decide) (join_su (m := 96993280) (by decide) (join_sr (m := 207749120) (by decide) (join_su (m := 95682560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 95682560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 207749120) (by decide) (join_su (m := 98304000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 98304000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 96993280) (by decide) (join_sr (m := 219545600) (by decide) (join_su (m := 95682560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 95682560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 219545600) (by decide) (join_su (m := 98304000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 98304000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/80 : ℝ) (19/160 : ℝ) →
    rho ∈ Set.Icc (77/320 : ℝ) (43/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e1 : (((99614720 : ℤ) : ℝ) / (D : ℝ)) = (19/160 : ℝ) := by norm_num [D]
  have e2 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  have e3 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
