-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u75497472_83886080_r353894400_402391040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:57:05.284768+00:00
-- url     : https://prove2.me/submissions/a8fb188c-e8d2-4903-aa41-c83b88dbc04c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/100, 1/10]`, `ρ ∈ [27/64, 307/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 75497472 77594624 353894400 366018560 ⟨⟨286966863399, 286966863413⟩, ⟨271635613384, 302740702161⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 77594624 79691776 353894400 366018560 ⟨⟨283306956864, 283306956871⟩, ⟨268188341224, 298861379174⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 75497472 77594624 366018560 378142720 ⟨⟨293908561161, 293908561174⟩, ⟨278587633120, 309658243922⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 77594624 79691776 366018560 378142720 ⟨⟨290215251841, 290215251850⟩, ⟨275102713295, 305750343690⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 79691776 81788928 353894400 366018560 ⟨⟨279714859266, 279714859279⟩, ⟨264803684333, 295055181577⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 81788928 83886080 353894400 366018560 ⟨⟨276188184209, 276188184222⟩, ⟨261479455333, 291319523163⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 79691776 81788928 366018560 378142720 ⟨⟨286588741660, 286588741673⟩, ⟨271679628215, 301914305506⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 81788928 83886080 366018560 378142720 ⟨⟨283026712916, 283026712929⟩, ⟨268316246899, 298147625260⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 75497472 77594624 378142720 390266880 ⟨⟨300759602319, 300759602330⟩, ⟨285450022283, 316484497106⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 77594624 79691776 378142720 390266880 ⟨⟨297034718929, 297034718933⟩, ⟨281929356716, 312549744722⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 75497472 77594624 390266880 402391040 ⟨⟨307524256937, 307524256950⟩, ⟨292226918378, 323223846320⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 77594624 79691776 390266880 402391040 ⟨⟨303769490538, 303769490547⟩, ⟨288672272394, 319263830053⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 79691776 81788928 378142720 390266880 ⟨⟨293375615844, 293375615855⟩, ⟨278469726688, 308685593740⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 81788928 83886080 378142720 390266880 ⟨⟨289780041769, 289780041782⟩, ⟨275069056159, 304889618893⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 79691776 81788928 390266880 402391040 ⟨⟨300079480056, 300079480069⟩, ⟨285177847939, 315373160141⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 81788928 83886080 390266880 402391040 ⟨⟨296452038317, 296452038331⟩, ⟨281741622383, 311549486992⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 75497472 83886080 353894400 402391040 t = true :=
  ⟨_, (join_sr (m := 378142720) (by decide) (join_su (m := 79691776) (by decide) (join_sr (m := 366018560) (by decide) (join_su (m := 77594624) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 77594624) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 366018560) (by decide) (join_su (m := 81788928) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 81788928) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 79691776) (by decide) (join_sr (m := 390266880) (by decide) (join_su (m := 77594624) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 77594624) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 390266880) (by decide) (join_su (m := 81788928) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 81788928) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/100 : ℝ) (1/10 : ℝ) →
    rho ∈ Set.Icc (27/64 : ℝ) (307/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e1 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e2 : (((353894400 : ℤ) : ℝ) / (D : ℝ)) = (27/64 : ℝ) := by norm_num [D]
  have e3 : (((402391040 : ℤ) : ℝ) / (D : ℝ)) = (307/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
