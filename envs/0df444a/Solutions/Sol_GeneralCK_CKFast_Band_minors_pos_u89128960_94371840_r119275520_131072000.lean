-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u89128960_94371840_r119275520_131072000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:30:08.272443+00:00
-- url     : https://prove2.me/submissions/704d199c-7407-4fae-89b7-e51230238f1e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/160, 9/80]`, `ρ ∈ [91/640, 5/32]` by 16 cells of the computing
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
theorem cell0 : cellOK 89128960 90439680 119275520 122224640 ⟨⟨108938083931, 108938083940⟩, ⟨103180500193, 114820739173⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 89128960 90439680 122224640 125173760 ⟨⟨111246384774, 111246384784⟩, ⟨105476727705, 117140474017⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 90439680 91750400 119275520 122224640 ⟨⟨107770237556, 107770237567⟩, ⟨102072896523, 113590374680⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 90439680 91750400 122224640 125173760 ⟨⟨110059694601, 110059694610⟩, ⟨104350218051, 115891356397⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 89128960 90439680 125173760 128122880 ⟨⟨113541399205, 113541399217⟩, ⟨107759897798, 119446695304⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 89128960 90439680 128122880 131072000 ⟨⟨115823319071, 115823319080⟩, ⟨110030196903, 121739600346⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 90439680 91750400 125173760 128122880 ⟨⟨112336185187, 112336185198⟩, ⟨106614796043, 118179150330⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 90439680 91750400 128122880 131072000 ⟨⟨114599894146, 114599894155⟩, ⟨108866810161, 120453946535⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 91750400 93061120 119275520 122224640 ⟨⟨106622973506, 106622973517⟩, ⟨100984497329, 112382038096⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 91750400 93061120 122224640 125173760 ⟨⟨108893770556, 108893770565⟩, ⟨103243104820, 114664441007⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 93061120 94371840 119275520 122224640 ⟨⟨105495679549, 105495679560⟩, ⟨99914737416, 111195067425⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 93061120 94371840 122224640 125173760 ⟨⟨107747998614, 107747998623⟩, ⟨102154820505, 113459064659⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 91750400 93061120 125173760 128122880 ⟨⟨111151912446, 111151912455⟩, ⟨105489274150, 116933973133⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 91750400 93061120 128122880 131072000 ⟨⟨113397577282, 113397577291⟩, ⟨107723178479, 119190817574⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 93061120 94371840 125173760 128122880 ⟨⟨109987965440, 109987965450⟩, ⟨104382762564, 115710499607⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 93061120 94371840 128122880 131072000 ⟨⟨112215751683, 112215751694⟩, ⟨106598730523, 117949548705⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 89128960 94371840 119275520 131072000 t = true :=
  ⟨_, (join_su (m := 91750400) (by decide) (join_sr (m := 125173760) (by decide) (join_su (m := 90439680) (by decide) (join_sr (m := 122224640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 122224640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 90439680) (by decide) (join_sr (m := 128122880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 128122880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 125173760) (by decide) (join_su (m := 93061120) (by decide) (join_sr (m := 122224640) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 122224640) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 93061120) (by decide) (join_sr (m := 128122880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 128122880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/160 : ℝ) (9/80 : ℝ) →
    rho ∈ Set.Icc (91/640 : ℝ) (5/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((89128960 : ℤ) : ℝ) / (D : ℝ)) = (17/160 : ℝ) := by norm_num [D]
  have e1 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e2 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  have e3 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
