-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u86507520_89128960_r95682560_107479040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:29:43.888079+00:00
-- url     : https://prove2.me/submissions/d34d89c5-0dbc-4e33-bd1d-0920f22283ab

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [33/320, 17/160]`, `ρ ∈ [73/640, 41/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 86507520 87162880 95682560 98631680 ⟨⟨92301352219, 92301352224⟩, ⟨88534230056, 96125373693⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 87162880 87818240 95682560 98631680 ⟨⟨91774205821, 91774205830⟩, ⟨88029186078, 95575529320⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 86507520 87162880 98631680 101580800 ⟨⟨94773105895, 94773105902⟩, ⟨90998133387, 98604628270⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 87162880 87818240 98631680 101580800 ⟨⟨94234778417, 94234778426⟩, ⟨90481892138, 98043626949⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 87818240 88473600 95682560 98631680 ⟨⟨91252187171, 91252187183⟩, ⟨87528999879, 95031092466⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 88473600 89128960 95682560 98631680 ⟨⟨90735212695, 90735212706⟩, ⟨87033592902, 94491974319⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 87818240 88473600 98631680 101580800 ⟨⟨93701648035, 93701648044⟩, ⟨89970579533, 97488100781⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 88473600 89128960 98631680 101580800 ⟨⟨93173630595, 93173630606⟩, ⟨89464116379, 96937960432⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 86507520 87162880 101580800 104529920 ⟨⟨97228984508, 97228984515⟩, ⟨93446358904, 101067812142⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 87162880 87818240 101580800 104529920 ⟨⟨96679682876, 96679682887⟩, ⟨92919124367, 100495863671⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 86507520 87162880 104529920 107479040 ⟨⟨99669234841, 99669234846⟩, ⟨95879148155, 103515177356⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 87162880 87818240 104529920 107479040 ⟨⟨99109161086, 99109161097⟩, ⟨95341119536, 102932486504⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 87818240 88473600 101580800 104529920 ⟨⟨96135644548, 96135644557⟩, ⟨92396886236, 99929454799⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 88473600 89128960 101580800 104529920 ⟨⟨95596784843, 95596784854⟩, ⟨91879564741, 99368495737⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 87818240 88473600 104529920 107479040 ⟨⟨98554413806, 98554413815⟩, ⟨94808152093, 102355396628⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 88473600 89128960 104529920 107479040 ⟨⟨98004907852, 98004907863⟩, ⟨94280165532, 101783817533⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 86507520 89128960 95682560 107479040 t = true :=
  ⟨_, (join_sr (m := 101580800) (by decide) (join_su (m := 87818240) (by decide) (join_sr (m := 98631680) (by decide) (join_su (m := 87162880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 87162880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 98631680) (by decide) (join_su (m := 88473600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 88473600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 87818240) (by decide) (join_sr (m := 104529920) (by decide) (join_su (m := 87162880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 87162880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 104529920) (by decide) (join_su (m := 88473600) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 88473600) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (33/320 : ℝ) (17/160 : ℝ) →
    rho ∈ Set.Icc (73/640 : ℝ) (41/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((86507520 : ℤ) : ℝ) / (D : ℝ)) = (33/320 : ℝ) := by norm_num [D]
  have e1 : (((89128960 : ℤ) : ℝ) / (D : ℝ)) = (17/160 : ℝ) := by norm_num [D]
  have e2 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  have e3 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
