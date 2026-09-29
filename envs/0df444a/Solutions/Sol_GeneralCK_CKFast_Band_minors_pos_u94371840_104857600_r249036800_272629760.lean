-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u94371840_104857600_r249036800_272629760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:53:26.67603+00:00
-- url     : https://prove2.me/submissions/78496bd2-d9a2-4418-b818-6dc9238c80c0

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/80, 1/8]`, `ρ ∈ [19/64, 13/40]` by 16 cells of the computing
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
theorem cell0 : cellOK 94371840 96993280 249036800 254935040 ⟨⟨193193895548, 193193895558⟩, ⟨181495820076, 205265672678⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 94371840 96993280 254935040 260833280 ⟨⟨196826021781, 196826021793⟩, ⟨185101743375, 208920355658⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 96993280 99614720 249036800 254935040 ⟨⟨189871811909, 189871811914⟩, ⟨178368764926, 201739610376⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 96993280 99614720 254935040 260833280 ⟨⟨193465933170, 193465933175⟩, ⟨181935571738, 205357645910⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 94371840 96993280 260833280 266731520 ⟨⟨200431199786, 200431199796⟩, ⟨188681363284, 212547472153⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 94371840 96993280 266731520 272629760 ⟨⟨204010041930, 204010041940⟩, ⟨192235268132, 216147658479⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 96993280 99614720 260833280 266731520 ⟨⟨197034051372, 197034051375⟩, ⟨185477005045, 208949070989⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 96993280 99614720 266731520 272629760 ⟨⟨200576746521, 200576746526⟩, ⟨188993622170, 212514488284⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 99614720 102236160 249036800 254935040 ⟨⟨186631487598, 186631487609⟩, ⟨175316832998, 198302292100⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 99614720 102236160 254935040 260833280 ⟨⟨190187546015, 190187546024⟩, ⟨178844571395, 201883500280⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 102236160 104857600 249036800 254935040 ⟨⟨183469307209, 183469307218⟩, ⟨172336744185, 194949749419⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 102236160 104857600 254935040 260833280 ⟨⟨186987278720, 186987278732⟩, ⟨175825487590, 198493993820⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 99614720 102236160 260833280 266731520 ⟨⟨193718517289, 193718517298⟩, ⟨182347836129, 205439026076⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 99614720 102236160 266731520 272629760 ⟨⟨197224950795, 197224950807⟩, ⟨185827155187, 208969440289⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 102236160 104857600 260833280 266731520 ⟨⟨190481050363, 190481050372⟩, ⟨179290627919, 202013456316⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 102236160 104857600 266731520 272629760 ⟨⟨193951142511, 193951142521⟩, ⟨182732665406, 205508677521⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 94371840 104857600 249036800 272629760 t = true :=
  ⟨_, (join_su (m := 99614720) (by decide) (join_sr (m := 260833280) (by decide) (join_su (m := 96993280) (by decide) (join_sr (m := 254935040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 254935040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 96993280) (by decide) (join_sr (m := 266731520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 266731520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 260833280) (by decide) (join_su (m := 102236160) (by decide) (join_sr (m := 254935040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 254935040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 102236160) (by decide) (join_sr (m := 266731520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 266731520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/80 : ℝ) (1/8 : ℝ) →
    rho ∈ Set.Icc (19/64 : ℝ) (13/40 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e1 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e2 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e3 : (((272629760 : ℤ) : ℝ) / (D : ℝ)) = (13/40 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
