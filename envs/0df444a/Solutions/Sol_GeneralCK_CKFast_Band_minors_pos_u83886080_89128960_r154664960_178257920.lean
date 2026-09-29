-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u83886080_89128960_r154664960_178257920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:40:09.531454+00:00
-- url     : https://prove2.me/submissions/76d9b915-2b59-451e-a52b-33bd87074932

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/10, 17/160]`, `ρ ∈ [59/320, 17/80]` by 19 cells of the computing
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
theorem cell0 : cellOK 83886080 85196800 154664960 160563200 ⟨⟨142647708223, 142647708235⟩, ⟨134757423054, 150744785564⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 85196800 86507520 154664960 157614080 ⟨⟨140064357944, 140064357954⟩, ⟨133990381274, 146262055666⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 85196800 86507520 157614080 160563200 ⟨⟨142271964775, 142271964787⟩, ⟨136188760225, 148478192442⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 83886080 85196800 160563200 166461440 ⟨⟨147070057113, 147070057123⟩, ⟨139161483975, 155182735765⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 85196800 86507520 160563200 166461440 ⟨⟨145560950012, 145560950025⟩, ⟨137739119013, 153583248034⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 86507520 87818240 154664960 157614080 ⟨⟨138619262275, 138619262284⟩, ⟨132608512133, 144751611764⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 86507520 87818240 157614080 160563200 ⟨⟨140811155616, 140811155625⟩, ⟨134791025470, 146952216352⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 87818240 89128960 154664960 157614080 ⟨⟨137198447929, 137198447934⟩, ⟨131249517708, 143266915214⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 87818240 89128960 157614080 160563200 ⟨⟨139374721394, 139374721399⟩, ⟨133416270007, 145452068978⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 86507520 87818240 160563200 166461440 ⟨⟨144077066070, 144077066082⟩, ⟨136340086848, 152010974806⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 87818240 89128960 160563200 166461440 ⟨⟨142617685811, 142617685816⟩, ⟨134963729882, 150465130969⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 83886080 85196800 166461440 172359680 ⟨⟨151444409483, 151444409495⟩, ⟨143518490920, 159571780365⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 85196800 86507520 166461440 172359680 ⟨⟨149905284032, 149905284044⟩, ⟨142065608428, 157942878658⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 83886080 85196800 172359680 178257920 ⟨⟨155772114678, 155772114688⟩, ⟨147829746131, 163913315641⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 85196800 86507520 172359680 178257920 ⟨⟨154203976739, 154203976749⟩, ⟨146347335495, 162256019765⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 86507520 87818240 166461440 172359680 ⟨⟨148391528806, 148391528818⟩, ⟨140636237752, 156341302007⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 87818240 89128960 166461440 172359680 ⟨⟨146902428225, 146902428230⟩, ⟨139229723448, 154766271159⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 86507520 87818240 172359680 178257920 ⟨⟨152661333363, 152661333373⟩, ⟨144888592935, 160626136962⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 87818240 89128960 172359680 178257920 ⟨⟨151143473389, 151143473392⟩, ⟨143452865732, 159022894322⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 83886080 89128960 154664960 178257920 t = true :=
  ⟨_, (join_sr (m := 166461440) (by decide) (join_su (m := 86507520) (by decide) (join_sr (m := 160563200) (by decide) (join_su (m := 85196800) (by decide) (leaf_ok cell0) (join_sr (m := 157614080) (by decide) (leaf_ok cell1) (leaf_ok cell2))) (join_su (m := 85196800) (by decide) (leaf_ok cell3) (leaf_ok cell4))) (join_sr (m := 160563200) (by decide) (join_su (m := 87818240) (by decide) (join_sr (m := 157614080) (by decide) (leaf_ok cell5) (leaf_ok cell6)) (join_sr (m := 157614080) (by decide) (leaf_ok cell7) (leaf_ok cell8))) (join_su (m := 87818240) (by decide) (leaf_ok cell9) (leaf_ok cell10)))) (join_su (m := 86507520) (by decide) (join_sr (m := 172359680) (by decide) (join_su (m := 85196800) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 85196800) (by decide) (leaf_ok cell13) (leaf_ok cell14))) (join_sr (m := 172359680) (by decide) (join_su (m := 87818240) (by decide) (leaf_ok cell15) (leaf_ok cell16)) (join_su (m := 87818240) (by decide) (leaf_ok cell17) (leaf_ok cell18)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/10 : ℝ) (17/160 : ℝ) →
    rho ∈ Set.Icc (59/320 : ℝ) (17/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e1 : (((89128960 : ℤ) : ℝ) / (D : ℝ)) = (17/160 : ℝ) := by norm_num [D]
  have e2 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  have e3 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
