-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u81788928_83886080_r75038720_87162880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:40:31.432496+00:00
-- url     : https://prove2.me/submissions/c5e9ae76-a202-41d7-a649-0785417ec24b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [39/400, 1/10]`, `ρ ∈ [229/2560, 133/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 81788928 82313216 75038720 78069760 ⟨⟨77946812592, 77946812604⟩, ⟨74434086697, 81512196822⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 82313216 82837504 75038720 78069760 ⟨⟨77563568511, 77563568520⟩, ⟨74068842703, 81110457322⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 81788928 82313216 78069760 81100800 ⟨⟨80707405884, 80707405893⟩, ⟨77186394429, 84280696041⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 82313216 82837504 78069760 81100800 ⟨⟨80313054455, 80313054467⟩, ⟨76810039338, 83867860227⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 82837504 83361792 75038720 78069760 ⟨⟨77183646215, 77183646227⟩, ⟨73706729661, 80712237670⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 83361792 83886080 75038720 78069760 ⟨⟨76806998013, 76806998022⟩, ⟨73347702989, 80317486917⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 82837504 83361792 78069760 81100800 ⟨⟨79922092739, 79922092747⟩, ⟨76436884095, 83458611049⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 83361792 83886080 78069760 81100800 ⟨⟨79534472416, 79534472425⟩, ⟨76066883459, 83052896978⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 81788928 82313216 81100800 84131840 ⟨⟨83447218215, 83447218226⟩, ⟨79918181844, 87028155863⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 82313216 82837504 81100800 84131840 ⟨⟨83041994523, 83041994532⟩, ⟨79530947219, 86604462245⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 81788928 82313216 84131840 87162880 ⟨⟨86166614940, 86166614949⟩, ⟨82629806334, 89754949621⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 82313216 82837504 84131840 87162880 ⟨⟨85750747751, 85750747762⟩, ⟨82231917597, 89320630234⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 82837504 83361792 81100800 84131840 ⟨⟨82640225252, 82640225263⟩, ⟨79146978176, 86184418795⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 83361792 83886080 81100800 84131840 ⟨⟨82241861526, 82241861537⟩, ⟨78766228882, 85767973461⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 82837504 83361792 84131840 87162880 ⟨⟨85338396619, 85338396630⟩, ⟨81837357144, 88890021424⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 83361792 83886080 84131840 87162880 ⟨⟨84929512149, 84929512158⟩, ⟨81446078593, 88463070659⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 81788928 83886080 75038720 87162880 t = true :=
  ⟨_, (join_sr (m := 81100800) (by decide) (join_su (m := 82837504) (by decide) (join_sr (m := 78069760) (by decide) (join_su (m := 82313216) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 82313216) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 78069760) (by decide) (join_su (m := 83361792) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 83361792) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 82837504) (by decide) (join_sr (m := 84131840) (by decide) (join_su (m := 82313216) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 82313216) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 84131840) (by decide) (join_su (m := 83361792) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 83361792) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (39/400 : ℝ) (1/10 : ℝ) →
    rho ∈ Set.Icc (229/2560 : ℝ) (133/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((81788928 : ℤ) : ℝ) / (D : ℝ)) = (39/400 : ℝ) := by norm_num [D]
  have e1 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e2 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  have e3 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
