-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u94371840_99614720_r154664960_166461440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:46:14.229197+00:00
-- url     : https://prove2.me/submissions/e61161f6-4438-4ada-8775-ee4c086ec4d7

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/80, 19/160]`, `ρ ∈ [59/320, 127/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 94371840 95682560 154664960 157614080 ⟨⟨130435181079, 130435181083⟩, ⟨124775811405, 136204593001⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 94371840 95682560 157614080 160563200 ⟨⟨132534797596, 132534797603⟩, ⟨126865345020, 138313773827⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 95682560 96993280 154664960 157614080 ⟨⟨129146354333, 129146354342⟩, ⟨123541274897, 134859726761⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 95682560 96993280 157614080 160563200 ⟨⟨131230933240, 131230933249⟩, ⟨125615683780, 136953978508⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 94371840 95682560 160563200 163512320 ⟨⟨134624156159, 134624156166⟩, ⟨128944778963, 140412539853⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 94371840 95682560 163512320 166461440 ⟨⟨136703390056, 136703390061⟩, ⟨131014243193, 142501027723⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 95682560 96993280 160563200 163512320 ⟨⟨133305478773, 133305478781⟩, ⟨127680214032, 139038043397⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 95682560 96993280 163512320 166461440 ⟨⟨135370119802, 135370119814⟩, ⟨129734991327, 141112053526⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 96993280 98304000 154664960 157614080 ⟨⟨127877464689, 127877464700⟩, ⟨122325555632, 133535963244⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 96993280 98304000 157614080 160563200 ⟨⟨129947105002, 129947105011⟩, ⟨124384946153, 135615376679⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 98304000 99614720 154664960 157614080 ⟨⟨126627980276, 126627980284⟩, ⟨121128156150, 132232734556⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 98304000 99614720 157614080 160563200 ⟨⟨128682781230, 128682781241⟩, ⟨123172634497, 134297401112⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 96993280 98304000 160563200 163512320 ⟨⟨132006931299, 132006931310⟩, ⟨126434673914, 137684825939⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 96993280 98304000 163512320 166461440 ⟨⟨134057068200, 134057068211⟩, ⟨128474860454, 139744438744⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 98304000 99614720 160563200 163512320 ⟨⟨130727982447, 130727982456⟩, ⟨125207660919, 136352321053⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 98304000 99614720 163512320 166461440 ⟨⟨132763704434, 132763704443⟩, ⟨127233352972, 138397617870⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 94371840 99614720 154664960 166461440 t = true :=
  ⟨_, (join_su (m := 96993280) (by decide) (join_sr (m := 160563200) (by decide) (join_su (m := 95682560) (by decide) (join_sr (m := 157614080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 157614080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 95682560) (by decide) (join_sr (m := 163512320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 163512320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 160563200) (by decide) (join_su (m := 98304000) (by decide) (join_sr (m := 157614080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 157614080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 98304000) (by decide) (join_sr (m := 163512320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 163512320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/80 : ℝ) (19/160 : ℝ) →
    rho ∈ Set.Icc (59/320 : ℝ) (127/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e1 : (((99614720 : ℤ) : ℝ) / (D : ℝ)) = (19/160 : ℝ) := by norm_num [D]
  have e2 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  have e3 : (((166461440 : ℤ) : ℝ) / (D : ℝ)) = (127/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
