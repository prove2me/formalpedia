-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u96993280_99614720_r107479040_119275520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:39:26.891513+00:00
-- url     : https://prove2.me/submissions/e0e267bb-a774-4f1a-8cfa-34ba1c52af94

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/320, 19/160]`, `ρ ∈ [41/320, 91/640]` by 14 cells of the computing
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
theorem cell0 : cellOK 96993280 97648640 107479040 110428160 ⟨⟨93565356747, 93565356756⟩, ⟨90091173094, 97087005289⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 97648640 98304000 107479040 110428160 ⟨⟨93071574581, 93071574589⟩, ⟨89615709309, 96574464029⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 96993280 97648640 110428160 113377280 ⟨⟨95815636081, 95815636091⟩, ⟨92334096075, 99344400193⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 97648640 98304000 110428160 113377280 ⟨⟨95312345338, 95312345348⟩, ⟨91849117328, 98822361914⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 98304000 98959360 107479040 110428160 ⟨⟨92582005683, 92582005691⟩, ⟨89144259727, 96066341550⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 98959360 99614720 107479040 110428160 ⟨⟨92096588743, 92096588752⟩, ⟨88676766336, 95562573113⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 98304000 98959360 110428160 113377280 ⟨⟨94813319218, 94813319226⟩, ⟨91368205096, 98304792690⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 98959360 99614720 110428160 113377280 ⟨⟨94318496022, 94318496031⟩, ⟨90891300953, 97791627432⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 96993280 97648640 113377280 116326400 ⟨⟨98053704914, 98053704922⟩, ⟨94564949840, 101589444032⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 97648640 98304000 113377280 116326400 ⟨⟨97541055312, 97541055320⟩, ⟨94070603846, 101058060411⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 96993280 98304000 116326400 119275520 ⟨⟨100018250338, 100018250349⟩, ⟨94614897951, 105534472922⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 98304000 98959360 113377280 116326400 ⟨⟨97032719609, 97032719620⟩, ⟨93580374636, 100531194020⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 98959360 99614720 113377280 116326400 ⟨⟨96528635765, 96528635775⟩, ⟨93094203400, 100008779455⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 98304000 99614720 116326400 119275520 ⟨⟨98983233422, 98983233430⟩, ⟨93632536706, 104444871464⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 96993280 99614720 107479040 119275520 t = true :=
  ⟨_, (join_sr (m := 113377280) (by decide) (join_su (m := 98304000) (by decide) (join_sr (m := 110428160) (by decide) (join_su (m := 97648640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 97648640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 110428160) (by decide) (join_su (m := 98959360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 98959360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 98304000) (by decide) (join_sr (m := 116326400) (by decide) (join_su (m := 97648640) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 116326400) (by decide) (join_su (m := 98959360) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (leaf_ok cell13))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/320 : ℝ) (19/160 : ℝ) →
    rho ∈ Set.Icc (41/320 : ℝ) (91/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((96993280 : ℤ) : ℝ) / (D : ℝ)) = (37/320 : ℝ) := by norm_num [D]
  have e1 : (((99614720 : ℤ) : ℝ) / (D : ℝ)) = (19/160 : ℝ) := by norm_num [D]
  have e2 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  have e3 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
