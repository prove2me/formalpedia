-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u77594624_79691776_r75038720_87162880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:36:56.884001+00:00
-- url     : https://prove2.me/submissions/48c298ce-384f-4c61-b169-414558dbd0bb

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/400, 19/200]`, `ρ ∈ [229/2560, 133/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 77594624 78118912 75038720 78069760 ⟨⟨81138398107, 81138398119⟩, ⟨77474405751, 84859290087⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 78118912 78643200 75038720 78069760 ⟨⟨80726743404, 80726743416⟩, ⟨77082398128, 84427429538⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 77594624 78118912 78069760 81100800 ⟨⟨83990371314, 83990371323⟩, ⟨80318162843, 87719035184⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 78118912 78643200 78069760 81100800 ⟨⟨83567042990, 83567043002⟩, ⟨79914468713, 87275522641⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 78643200 79167488 75038720 78069760 ⟨⟨80318828387, 80318828396⟩, ⟨76693911895, 83999535479⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 79167488 79691776 75038720 78069760 ⟨⟨79914597033, 79914597045⟩, ⟨76308894748, 83575548004⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 78643200 79167488 78069760 81100800 ⟨⟨83147527411, 83147527420⟩, ⟨79514370321, 86836048157⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 79167488 79691776 78069760 81100800 ⟨⟨82731767898, 82731767907⟩, ⟨79117814652, 86400551225⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 77594624 78118912 81100800 84131840 ⟨⟨86819560535, 86819560544⟩, ⟨83139426623, 90555708623⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 78118912 78643200 81100800 84131840 ⟨⟨86384821434, 86384821443⟩, ⟨82724304883, 90100810761⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 77594624 78118912 84131840 87162880 ⟨⟨89626386526, 89626386538⟩, ⟨85938608396, 93369740645⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 78118912 78643200 84131840 87162880 ⟨⟨89180492049, 89180492058⟩, ⟨85512310702, 92903716494⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 78643200 79167488 81100800 84131840 ⟨⟨85953964446, 85953964458⟩, ⟨82312849594, 89650018792⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 79167488 79691776 81100800 84131840 ⟨⟨85526932304, 85526932313⟩, ⟨81905007107, 89203271659⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 78643200 79167488 84131840 87162880 ⟨⟨88738545528, 88738545537⟩, ⟨85089746697, 92441862492⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 79167488 79691776 84131840 87162880 ⟨⟨88300489153, 88300489165⟩, ⟨84670862147, 91984117097⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 77594624 79691776 75038720 87162880 t = true :=
  ⟨_, (join_sr (m := 81100800) (by decide) (join_su (m := 78643200) (by decide) (join_sr (m := 78069760) (by decide) (join_su (m := 78118912) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 78118912) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 78069760) (by decide) (join_su (m := 79167488) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 79167488) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 78643200) (by decide) (join_sr (m := 84131840) (by decide) (join_su (m := 78118912) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 78118912) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 84131840) (by decide) (join_su (m := 79167488) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 79167488) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/400 : ℝ) (19/200 : ℝ) →
    rho ∈ Set.Icc (229/2560 : ℝ) (133/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((77594624 : ℤ) : ℝ) / (D : ℝ)) = (37/400 : ℝ) := by norm_num [D]
  have e1 : (((79691776 : ℤ) : ℝ) / (D : ℝ)) = (19/200 : ℝ) := by norm_num [D]
  have e2 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  have e3 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
