-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u89128960_91750400_r95682560_107479040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:29:54.548644+00:00
-- url     : https://prove2.me/submissions/14fc9146-e57f-40aa-a967-13076e018ff1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/160, 7/64]`, `ρ ∈ [73/640, 41/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 89128960 89784320 95682560 98631680 ⟨⟨90223200659, 90223200670⟩, ⟨86542888315, 93958088043⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 89784320 90439680 95682560 98631680 ⟨⟨89716071127, 89716071132⟩, ⟨86056810949, 93429348713⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 89128960 89784320 98631680 101580800 ⟨⟨92650643788, 92650643799⟩, ⟨88962425213, 96393118551⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 89784320 90439680 98631680 101580800 ⟨⟨92132607100, 92132607104⟩, ⟨88465430239, 95853489691⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 90439680 91095040 95682560 98631680 ⟨⟨89213745891, 89213745899⟩, ⟨85575287270, 92905673267⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 91095040 91750400 95682560 98631680 ⟨⟨88716148453, 88716148461⟩, ⟨85098245313, 92386980461⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 90439680 91095040 98631680 101580800 ⟨⟨91619441745, 91619441754⟩, ⟨87973057292, 95318990272⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 91095040 91750400 98631680 101580800 ⟨⟨91111070653, 91111070664⟩, ⟨87485233790, 94789538526⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 89128960 89784320 101580800 104529920 ⟨⟨95063020933, 95063020942⟩, ⟨91367081842, 98812898665⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 89784320 90439680 101580800 104529920 ⟨⟨94534271777, 94534271782⟩, ⟨90859361170, 98262577676⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 89128960 89784320 104529920 107479040 ⟨⟨97460559928, 97460559937⟩, ⟨93757081288, 101217660994⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 89784320 90439680 104529920 107479040 ⟨⟨96921288525, 96921288529⟩, ⟨93238822470, 100656840693⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 90439680 91095040 101580800 104529920 ⟨⟨94010458074, 94010458085⟩, ⟨90356327990, 97717448724⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 91095040 91750400 101580800 104529920 ⟨⟨93491502234, 93491502243⟩, ⟨89857909151, 97177429575⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 90439680 91095040 104529920 107479040 ⟨⟨96387013871, 96387013882⟩, ⟨92725313827, 100101272166⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 91095040 91750400 104529920 107479040 ⟨⟨95857657908, 95857657916⟩, ⟨92216481687, 99550872764⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 89128960 91750400 95682560 107479040 t = true :=
  ⟨_, (join_sr (m := 101580800) (by decide) (join_su (m := 90439680) (by decide) (join_sr (m := 98631680) (by decide) (join_su (m := 89784320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 89784320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 98631680) (by decide) (join_su (m := 91095040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 91095040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 90439680) (by decide) (join_sr (m := 104529920) (by decide) (join_su (m := 89784320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 89784320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 104529920) (by decide) (join_su (m := 91095040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 91095040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/160 : ℝ) (7/64 : ℝ) →
    rho ∈ Set.Icc (73/640 : ℝ) (41/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((89128960 : ℤ) : ℝ) / (D : ℝ)) = (17/160 : ℝ) := by norm_num [D]
  have e1 : (((91750400 : ℤ) : ℝ) / (D : ℝ)) = (7/64 : ℝ) := by norm_num [D]
  have e2 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  have e3 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
