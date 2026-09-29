-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u94371840_99614720_r225443840_249036800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:53:07.559526+00:00
-- url     : https://prove2.me/submissions/f5184b19-36e2-4e55-a5af-0033b4c34895

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/80, 19/160]`, `ρ ∈ [43/160, 19/64]` by 13 cells of the computing
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
theorem cell0 : cellOK 94371840 95682560 225443840 231342080 ⟨⟨179186212210, 179186212217⟩, ⟨171733162946, 186796638606⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 95682560 96993280 225443840 231342080 ⟨⟨177585163078, 177585163090⟩, ⟨170201473994, 185124045479⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 94371840 95682560 231342080 237240320 ⟨⟨182943170978, 182943170981⟩, ⟨175476423707, 190565557753⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 95682560 96993280 231342080 237240320 ⟨⟨181321039296, 181321039306⟩, ⟨173923246231, 188872347757⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 96993280 98304000 225443840 231342080 ⟨⟨176005267391, 176005267403⟩, ⟨168689705212, 183473885819⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 98304000 99614720 225443840 231342080 ⟨⟨174446026201, 174446026210⟩, ⟨167197390751, 181845626257⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 96993280 98304000 231342080 237240320 ⟨⟨179720074411, 179720074422⟩, ⟨172390022775, 187201561973⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 98304000 99614720 231342080 237240320 ⟨⟨178139781684, 178139781695⟩, ⟨170876290912, 185552672315⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 94371840 96993280 237240320 243138560 ⟨⟨185846257633, 185846257643⟩, ⟨174202623976, 197870965306⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 94371840 96993280 243138560 249036800 ⟨⟨189534190602, 189534190614⟩, ⟨177862987986, 201582767714⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 96993280 98304000 237240320 243138560 ⟨⟨183406115371, 183406115382⟩, ⟨176062039176, 190900021672⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 98304000 99614720 237240320 243138560 ⟨⟨181805306119, 181805306128⟩, ⟨174527418590, 189231042187⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 96993280 99614720 243138560 249036800 ⟨⟨186251090819, 186251090824⟩, ⟨174776011477, 198094343968⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 94371840 99614720 225443840 249036800 t = true :=
  ⟨_, (join_sr (m := 237240320) (by decide) (join_su (m := 96993280) (by decide) (join_sr (m := 231342080) (by decide) (join_su (m := 95682560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 95682560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 231342080) (by decide) (join_su (m := 98304000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 98304000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 96993280) (by decide) (join_sr (m := 243138560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 243138560) (by decide) (join_su (m := 98304000) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (leaf_ok cell12))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/80 : ℝ) (19/160 : ℝ) →
    rho ∈ Set.Icc (43/160 : ℝ) (19/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e1 : (((99614720 : ℤ) : ℝ) / (D : ℝ)) = (19/160 : ℝ) := by norm_num [D]
  have e2 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e3 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
