-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u94371840_99614720_r131072000_142868480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:44:11.105608+00:00
-- url     : https://prove2.me/submissions/6871fce0-fcad-4a99-9408-e12189a08539

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/80, 19/160]`, `ρ ∈ [5/32, 109/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 94371840 95682560 131072000 134021120 ⟨⟨113252167133, 113252167139⟩, ⟨107679587490, 118938985843⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 94371840 95682560 134021120 136970240 ⟨⟨115438939304, 115438939309⟩, ⟨109854879976, 121136708762⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 95682560 96993280 131072000 134021120 ⟨⟨112092293201, 112092293211⟩, ⟨106574556013, 117722342393⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 95682560 96993280 134021120 136970240 ⟨⟨114262058520, 114262058529⟩, ⟨108732788139, 119903134823⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 94371840 95682560 136970240 139919360 ⟨⟨117614297893, 117614297895⟩, ⟨112018947043, 123322831091⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 94371840 95682560 139919360 142868480 ⟨⟨119778396593, 119778396598⟩, ⟨114171938311, 125497510649⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 95682560 96993280 136970240 139919360 ⟨⟨116420674318, 116420674327⟩, ⟨110880054145, 122072595312⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 95682560 96993280 139919360 142868480 ⟨⟨118568288922, 118568288931⟩, ⟨113016498453, 124230876132⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 96993280 98304000 131072000 134021120 ⟨⟨110951355260, 110951355270⟩, ⟨105487284365, 116525864542⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 96993280 98304000 134021120 136970240 ⟨⟨113104260941, 113104260951⟩, ⟨107628610080, 118689865955⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 98304000 99614720 131072000 134021120 ⟨⟨109828825375, 109828825386⟩, ⟨104417282259, 115348984706⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 98304000 99614720 134021120 136970240 ⟨⟨111965017513, 111965017522⟩, ⟨106541853986, 117496333907⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 96993280 98304000 136970240 139919360 ⟨⟨115246274460, 115246274468⟩, ⟨109759222369, 120842797281⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 96993280 98304000 139919360 142868480 ⟨⟨117377538974, 117377538983⟩, ⟨111879260654, 122984805462⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 98304000 99614720 136970240 139919360 ⟨⟨114090568332, 114090568341⟩, ⟨108655958569, 119632868280⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 98304000 99614720 139919360 142868480 ⟨⟨116205616032, 116205616042⟩, ⟨110759730629, 121758729642⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 94371840 99614720 131072000 142868480 t = true :=
  ⟨_, (join_su (m := 96993280) (by decide) (join_sr (m := 136970240) (by decide) (join_su (m := 95682560) (by decide) (join_sr (m := 134021120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 134021120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 95682560) (by decide) (join_sr (m := 139919360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 139919360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 136970240) (by decide) (join_su (m := 98304000) (by decide) (join_sr (m := 134021120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 134021120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 98304000) (by decide) (join_sr (m := 139919360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 139919360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/80 : ℝ) (19/160 : ℝ) →
    rho ∈ Set.Icc (5/32 : ℝ) (109/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e1 : (((99614720 : ℤ) : ℝ) / (D : ℝ)) = (19/160 : ℝ) := by norm_num [D]
  have e2 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e3 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
