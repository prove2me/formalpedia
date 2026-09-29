-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u83886080_94371840_r249036800_272629760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:53:15.239771+00:00
-- url     : https://prove2.me/submissions/1f900eb6-01c9-4fb9-a782-f96d5bcec3a2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/10, 9/80]`, `ρ ∈ [19/64, 13/40]` by 16 cells of the computing
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
theorem cell0 : cellOK 83886080 86507520 249036800 254935040 ⟨⟨207380780825, 207380780833⟩, ⟨194828615668, 220346329959⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 83886080 86507520 254935040 260833280 ⟨⟨211163518279, 211163518285⟩, ⟨198590855770, 224144745187⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 86507520 89128960 249036800 254935040 ⟨⟨203690497711, 203690497721⟩, ⟨191363785275, 216420048486⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 86507520 89128960 254935040 260833280 ⟨⟨207435889203, 207435889215⟩, ⟨195087041574, 220183080536⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 83886080 86507520 260833280 266731520 ⟨⟨214915224129, 214915224133⟩, ⟨202322757566, 227911486195⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 83886080 86507520 266731520 272629760 ⟨⟨218636659488, 218636659493⟩, ⟨206025052176, 231647343485⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 86507520 89128960 260833280 266731520 ⟨⟨211151316175, 211151316185⟩, ⟨198781017007, 223915507947⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 86507520 89128960 266731520 272629760 ⟨⟨214837499449, 214837499461⟩, ⟨202446403968, 227618079540⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 89128960 91750400 249036800 254935040 ⟨⟨200098995098, 200098995110⟩, ⟨187989488265, 212601226288⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 89128960 91750400 254935040 260833280 ⟨⟨203806801478, 203806801490⟩, ⟨191673670624, 216328464789⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 91750400 94371840 249036800 254935040 ⟨⟨196601588392, 196601588404⟩, ⟨184701488516, 208884707525⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 91750400 94371840 254935040 260833280 ⟨⟨200271623824, 200271623834⟩, ⟨188346547755, 212575809534⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 89128960 91750400 260833280 266731520 ⟨⟨207485679358, 207485679368⟩, ⟨195329596639, 220026139835⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 89128960 91750400 266731520 272629760 ⟨⟨211136311414, 211136311424⟩, ⟨198957922066, 223694960720⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 91750400 94371840 260833280 266731520 ⟨⟨203913736044, 203913736054⟩, ⟨191964342904, 216238360787⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 91750400 94371840 266731520 272629760 ⟨⟨207528571613, 207528571624⟩, ⟨195555495072, 219873033108⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 83886080 94371840 249036800 272629760 t = true :=
  ⟨_, (join_su (m := 89128960) (by decide) (join_sr (m := 260833280) (by decide) (join_su (m := 86507520) (by decide) (join_sr (m := 254935040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 254935040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 86507520) (by decide) (join_sr (m := 266731520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 266731520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 260833280) (by decide) (join_su (m := 91750400) (by decide) (join_sr (m := 254935040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 254935040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 91750400) (by decide) (join_sr (m := 266731520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 266731520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/10 : ℝ) (9/80 : ℝ) →
    rho ∈ Set.Icc (19/64 : ℝ) (13/40 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e1 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e2 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e3 : (((272629760 : ℤ) : ℝ) / (D : ℝ)) = (13/40 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
