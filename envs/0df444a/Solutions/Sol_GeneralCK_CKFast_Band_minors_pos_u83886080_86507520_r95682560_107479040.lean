-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u83886080_86507520_r95682560_107479040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:29:27.085852+00:00
-- url     : https://prove2.me/submissions/c2f0d816-37bd-4cd8-8035-9bd2f459bcd5

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/10, 33/320]`, `ρ ∈ [73/640, 41/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 83886080 84541440 95682560 98631680 ⟨⟨94462954249, 94462954260⟩, ⟨90604617839, 98380674895⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 84541440 85196800 95682560 98631680 ⟨⟨93914422385, 93914422393⟩, ⟨90079321053, 97808270841⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 83886080 84541440 98631680 101580800 ⟨⟨96980137369, 96980137380⟩, ⟨93114031707, 100905243883⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 84541440 85196800 98631680 101580800 ⟨⟨96420141214, 96420141223⟩, ⟨92577247780, 100321407211⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 85196800 85852160 95682560 98631680 ⟨⟨93371372075, 93371372084⟩, ⟨89559214465, 97241650450⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 85852160 86507520 95682560 98631680 ⟨⟨92833711828, 92833711837⟩, ⟨89044212139, 96680716428⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 85196800 85852160 98631680 101580800 ⟨⟨95865698288, 95865698297⟩, ⟨92045727488, 99743423882⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 85852160 86507520 98631680 101580800 ⟨⟨95316716517, 95316716529⟩, ⟨91519384244, 99171196100⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 83886080 84541440 101580800 104529920 ⟨⟨99480585043, 99480585052⟩, ⟨95606919612, 103412869916⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 84541440 85196800 101580800 104529920 ⟨⟨98909344715, 98909344726⟩, ⟨95058865540, 102817823771⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 83886080 84541440 104529920 107479040 ⟨⟨101964564830, 101964564839⟩, ⟨98083543340, 105903826351⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 84541440 85196800 104529920 107479040 ⟨⟨101382295072, 101382295083⟩, ⟨97524430877, 105297788364⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 85196800 85852160 101580800 104529920 ⟨⟨98343725900, 98343725911⟩, ⟨94516145187, 102228697224⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 85852160 86507520 101580800 104529920 ⟨⟨97783636007, 97783636017⟩, ⟨93978671390, 101645392027⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 85196800 85852160 104529920 107479040 ⟨⟨100805711845, 100805711854⟩, ⟨96970718999, 104697732924⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 85852160 86507520 104529920 107479040 ⟨⟨100234722095, 100234722107⟩, ⟨96422320013, 104103561398⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 83886080 86507520 95682560 107479040 t = true :=
  ⟨_, (join_sr (m := 101580800) (by decide) (join_su (m := 85196800) (by decide) (join_sr (m := 98631680) (by decide) (join_su (m := 84541440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 84541440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 98631680) (by decide) (join_su (m := 85852160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 85852160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 85196800) (by decide) (join_sr (m := 104529920) (by decide) (join_su (m := 84541440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 84541440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 104529920) (by decide) (join_su (m := 85852160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 85852160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/10 : ℝ) (33/320 : ℝ) →
    rho ∈ Set.Icc (73/640 : ℝ) (41/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e1 : (((86507520 : ℤ) : ℝ) / (D : ℝ)) = (33/320 : ℝ) := by norm_num [D]
  have e2 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  have e3 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
