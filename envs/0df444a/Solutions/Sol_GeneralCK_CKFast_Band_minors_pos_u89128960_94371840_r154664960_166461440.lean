-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u89128960_94371840_r154664960_166461440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:42:38.648931+00:00
-- url     : https://prove2.me/submissions/aadce38a-8251-400f-b365-d86ada856c10

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/160, 9/80]`, `ρ ∈ [59/320, 127/640]` by 14 cells of the computing
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
theorem cell0 : cellOK 89128960 90439680 154664960 157614080 ⟨⟨135801219753, 135801219762⟩, ⟨129912749394, 141807222088⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 89128960 90439680 157614080 160563200 ⟨⟨137961968231, 137961968242⟩, ⟨132063845884, 143977008351⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 90439680 91750400 154664960 157614080 ⟨⟨134426909534, 134426909543⟩, ⟨128597583468, 140371817537⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 90439680 91750400 157614080 160563200 ⟨⟨136572228997, 136572229006⟩, ⟨130733129885, 142526321340⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 89128960 90439680 160563200 166461440 ⟨⟨141182117559, 141182117571⟩, ⟨133609415666, 148944962048⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 90439680 91750400 160563200 166461440 ⟨⟨139769696104, 139769696115⟩, ⟨132276535663, 147449742718⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 91750400 93061120 154664960 157614080 ⟨⟨133074874653, 133074874662⟩, ⟨127303419906, 138960014316⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 91750400 93061120 157614080 160563200 ⟨⟨135204861978, 135204861988⟩, ⟨129423522349, 141099322216⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 93061120 94371840 154664960 157614080 ⟨⟨131744496856, 131744496865⟩, ⟨126029681224, 137571151461⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 93061120 94371840 157614080 160563200 ⟨⟨133859249667, 133859249679⟩, ⟨128134446029, 139695351326⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 91750400 93061120 160563200 163512320 ⟨⟨137324125963, 137324125975⟩, ⟨131533066965, 143227743112⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 91750400 93061120 163512320 166461440 ⟨⟨139432809238, 139432809250⟩, ⟨133632192772, 145345423262⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 93061120 94371840 160563200 163512320 ⟨⟨135963514583, 135963514592⟩, ⟨130228884809, 141808903053⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 93061120 94371840 163512320 166461440 ⟨⟨138057429472, 138057429481⟩, ⟨132313131975, 143911948009⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 89128960 94371840 154664960 166461440 t = true :=
  ⟨_, (join_su (m := 91750400) (by decide) (join_sr (m := 160563200) (by decide) (join_su (m := 90439680) (by decide) (join_sr (m := 157614080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 157614080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 90439680) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 160563200) (by decide) (join_su (m := 93061120) (by decide) (join_sr (m := 157614080) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 157614080) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 93061120) (by decide) (join_sr (m := 163512320) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_sr (m := 163512320) (by decide) (leaf_ok cell12) (leaf_ok cell13)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/160 : ℝ) (9/80 : ℝ) →
    rho ∈ Set.Icc (59/320 : ℝ) (127/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((89128960 : ℤ) : ℝ) / (D : ℝ)) = (17/160 : ℝ) := by norm_num [D]
  have e1 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e2 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  have e3 : (((166461440 : ℤ) : ℝ) / (D : ℝ)) = (127/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
