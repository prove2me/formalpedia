-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u89128960_94371840_r201850880_225443840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:48:24.112214+00:00
-- url     : https://prove2.me/submissions/6108661e-ae19-4bba-bcfc-faf55304cef7

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/160, 9/80]`, `ρ ∈ [77/320, 43/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 89128960 90439680 201850880 207749120 ⟨⟨170108850155, 170108850167⟩, ⟨162418193385, 177974342151⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 90439680 91750400 201850880 207749120 ⟨⟨168508610983, 168508610995⟩, ⟨160894528296, 176294851355⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 89128960 90439680 207749120 213647360 ⟨⟨174087251769, 174087251782⟩, ⟨166382505057, 181964742155⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 90439680 91750400 207749120 213647360 ⟨⟨172463310485, 172463310497⟩, ⟨164834668371, 180262094307⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 91750400 93061120 201850880 207749120 ⟨⟨166931609000, 166931609011⟩, ⟨159392621620, 174640140057⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 93061120 94371840 201850880 207749120 ⟨⟨165377253187, 165377253199⟩, ⟨157911925325, 173009572238⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 91750400 93061120 207749120 213647360 ⟨⟨170862646809, 170862646821⟩, ⟨163308655850, 178584238157⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 93061120 94371840 207749120 213647360 ⟨⟨169284674587, 169284674596⟩, ⟨161803923134, 176930543868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 89128960 90439680 213647360 219545600 ⟨⟨178030074140, 178030074150⟩, ⟨170311836374, 185918987375⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 90439680 91750400 213647360 219545600 ⟨⟨176383123189, 176383123199⟩, ⟨168740512239, 184193881545⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 89128960 90439680 219545600 225443840 ⟨⟨181938209912, 181938209924⟩, ⟨174207053239, 189837997005⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 90439680 91750400 219545600 225443840 ⟨⟨180268915202, 180268915212⟩, ⟨172612900120, 188091104904⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 91750400 93061120 213647360 219545600 ⟨⟨174759477232, 174759477241⟩, ⟨167191064816, 182493566850⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 93061120 94371840 213647360 219545600 ⟨⟨173158555189, 173158555199⟩, ⟨165662953655, 180817419819⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 91750400 93061120 219545600 225443840 ⟨⟨178622940664, 178622940675⟩, ⟨171040663859, 186368991464⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 93061120 94371840 219545600 225443840 ⟨⟨176999710487, 176999710498⟩, ⟨169489808137, 184671039728⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 89128960 94371840 201850880 225443840 t = true :=
  ⟨_, (join_sr (m := 213647360) (by decide) (join_su (m := 91750400) (by decide) (join_sr (m := 207749120) (by decide) (join_su (m := 90439680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 90439680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 207749120) (by decide) (join_su (m := 93061120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 93061120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 91750400) (by decide) (join_sr (m := 219545600) (by decide) (join_su (m := 90439680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 90439680) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 219545600) (by decide) (join_su (m := 93061120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 93061120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/160 : ℝ) (9/80 : ℝ) →
    rho ∈ Set.Icc (77/320 : ℝ) (43/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((89128960 : ℤ) : ℝ) / (D : ℝ)) = (17/160 : ℝ) := by norm_num [D]
  have e1 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e2 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  have e3 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
