-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u89128960_94371840_r178257920_201850880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:47:34.73946+00:00
-- url     : https://prove2.me/submissions/aae3deb3-ff9f-4db2-a983-1104d7056035

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/160, 9/80]`, `ρ ∈ [17/80, 77/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 89128960 90439680 178257920 184156160 ⟨⟨153820509370, 153820509382⟩, ⟨146192785905, 161631671156⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 90439680 91750400 178257920 184156160 ⟨⟨152322579750, 152322579761⟩, ⟨144773205858, 160052394655⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 89128960 90439680 184156160 190054400 ⟨⟨157950780953, 157950780965⟩, ⟨150306275859, 165776537781⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 90439680 91750400 184156160 190054400 ⟨⟨156426087615, 156426087626⟩, ⟨148859505717, 164171006567⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 91750400 93061120 178257920 184156160 ⟨⟨150847576640, 150847576652⟩, ⟨143374971076, 158497702106⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 93061120 94371840 178257920 184156160 ⟨⟨149394892372, 149394892383⟩, ⟨141997521900, 156966935228⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 91750400 93061120 184156160 190054400 ⟨⟨154924422828, 154924422839⟩, ⟨147434208606, 162590132283⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 93061120 94371840 184156160 190054400 ⟨⟨153445182596, 153445182607⟩, ⟨146029827243, 161033261775⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 89128960 90439680 190054400 195952640 ⟨⟨162041585860, 162041585870⟩, ⟨154381019562, 169881241261⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 90439680 91750400 190054400 195952640 ⟨⟨160490940811, 160490940820⟩, ⟨152907858921, 168250277940⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 89128960 90439680 195952640 201850880 ⟨⟨166093946374, 166093946385⟩, ⟨158418006553, 173946836510⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 90439680 91750400 195952640 201850880 ⟨⟨164518129567, 164518129576⟩, ⟨156919224093, 172291230524⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 91750400 93061120 190054400 195952640 ⟨⟨158963409400, 158963409410⟩, ⟨151456282070, 166644027741⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 93061120 94371840 190054400 195952640 ⟨⟨157458391654, 157458391663⟩, ⟨150025734489, 165061842947⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 91750400 93061120 195952640 201850880 ⟨⟨162965495606, 162965495617⟩, ⟨155442120228, 170660378168⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 93061120 94371840 195952640 201850880 ⟨⟨161435448858, 161435448868⟩, ⟨153986143529, 169053637453⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 89128960 94371840 178257920 201850880 t = true :=
  ⟨_, (join_sr (m := 190054400) (by decide) (join_su (m := 91750400) (by decide) (join_sr (m := 184156160) (by decide) (join_su (m := 90439680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 90439680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 184156160) (by decide) (join_su (m := 93061120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 93061120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 91750400) (by decide) (join_sr (m := 195952640) (by decide) (join_su (m := 90439680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 90439680) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 195952640) (by decide) (join_su (m := 93061120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 93061120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/160 : ℝ) (9/80 : ℝ) →
    rho ∈ Set.Icc (17/80 : ℝ) (77/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((89128960 : ℤ) : ℝ) / (D : ℝ)) = (17/160 : ℝ) := by norm_num [D]
  have e1 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e2 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e3 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
