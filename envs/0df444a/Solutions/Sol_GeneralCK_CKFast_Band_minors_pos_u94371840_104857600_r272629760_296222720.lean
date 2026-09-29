-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u94371840_104857600_r272629760_296222720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T11:08:30.918573+00:00
-- url     : https://prove2.me/submissions/35d96a09-8628-4b58-9cb5-e3d4a8191d5d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/80, 1/8]`, `ρ ∈ [13/40, 113/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 94371840 96993280 272629760 278528000 ⟨⟨207563143161, 207563143173⟩, ⟨195764029822, 219721532510⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 94371840 96993280 278528000 284426240 ⟨⟨211091081657, 211091081669⟩, ⟨199268204433, 223269694380⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 96993280 99614720 272629760 278528000 ⟨⟨204094582487, 204094582492⟩, ⟨192485965212, 216054483393⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 96993280 99614720 278528000 284426240 ⟨⟨207588107593, 207588107599⟩, ⟨195954561593, 219569625474⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 94371840 96993280 284426240 290324480 ⟨⟨214594419447, 214594419459⟩, ⟨202748332802, 226792727154⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 94371840 96993280 290324480 296222720 ⟨⟨218073703018, 218073703028⟩, ⟨206204941077, 230291197478⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 96993280 99614720 284426240 290324480 ⟨⟨211057855184, 211057855189⟩, ⟨199399924589, 223060467861⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 96993280 99614720 290324480 296222720 ⟨⟨214504344172, 214504344175⟩, ⟨202822553832, 226527548642⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 99614720 102236160 272629760 278528000 ⟨⟨200707380960, 200707380969⟩, ⟨189283042449, 212475297908⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 99614720 102236160 278528000 284426240 ⟨⟨204166327791, 204166327803⟩, ⟨192715998179, 215957138691⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 102236160 104857600 272629760 278528000 ⟨⟨197398061693, 197398061704⟩, ⟨186152087203, 208980183403⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 102236160 104857600 278528000 284426240 ⟨⟨200822301074, 200822301086⟩, ⟨189549367835, 212428485818⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 99614720 102236160 284426240 290324480 ⟨⟨207602297408, 207602297420⟩, ⟨196126509508, 219415487720⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 99614720 102236160 290324480 296222720 ⟨⟨211015782527, 211015782536⟩, ⟨199515050892, 222850855925⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 102236160 104857600 284426240 290324480 ⟨⟨204224340930, 204224340940⟩, ⟨192924969631, 215854083013⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 102236160 104857600 290324480 296222720 ⟨⟨207604649087, 207604649098⟩, ⟨196279343152, 219257460097⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 94371840 104857600 272629760 296222720 t = true :=
  ⟨_, (join_su (m := 99614720) (by decide) (join_sr (m := 284426240) (by decide) (join_su (m := 96993280) (by decide) (join_sr (m := 278528000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 278528000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 96993280) (by decide) (join_sr (m := 290324480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 290324480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 284426240) (by decide) (join_su (m := 102236160) (by decide) (join_sr (m := 278528000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 278528000) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 102236160) (by decide) (join_sr (m := 290324480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 290324480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/80 : ℝ) (1/8 : ℝ) →
    rho ∈ Set.Icc (13/40 : ℝ) (113/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e1 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e2 : (((272629760 : ℤ) : ℝ) / (D : ℝ)) = (13/40 : ℝ) := by norm_num [D]
  have e3 : (((296222720 : ℤ) : ℝ) / (D : ℝ)) = (113/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
