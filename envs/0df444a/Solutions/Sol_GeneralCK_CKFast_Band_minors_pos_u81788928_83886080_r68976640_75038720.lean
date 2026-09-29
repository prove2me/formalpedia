-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u81788928_83886080_r68976640_75038720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:39:19.985008+00:00
-- url     : https://prove2.me/submissions/e36d4407-ad56-4cbb-9681-ecafd6f6efd0

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [39/400, 1/10]`, `ρ ∈ [421/5120, 229/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 81788928 82313216 68976640 70492160 ⟨⟨71657542308, 71657542317⟩, ⟨69078510340, 74265843845⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 81788928 82313216 70492160 72007680 ⟨⟨73064638468, 73064638477⟩, ⟨70481871740, 75676583889⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 82313216 82837504 68976640 70492160 ⟨⟨71300183418, 71300183427⟩, ⟨68733811408, 73895556949⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 82313216 82837504 70492160 72007680 ⟨⟨72701417647, 72701417659⟩, ⟨70131314821, 75300432968⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 81788928 82313216 72007680 73523200 ⟨⟨74466276362, 74466276373⟩, ⟨71879825716, 77081814963⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 81788928 82313216 73523200 75038720 ⟨⟨75862505198, 75862505210⟩, ⟨73272420712, 78481587040⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 82313216 82837504 72007680 73523200 ⟨⟨74097257002, 74097257011⟩, ⟨71523473480, 76699864111⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 82313216 82837504 73523200 75038720 ⟨⟨75487749813, 75487749822⟩, ⟨72910334969, 78093899470⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 82837504 83361792 68976640 70492160 ⟨⟨70945981066, 70945981074⟩, ⟨68392131408, 73528568164⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 82837504 83361792 70492160 72007680 ⟨⟨72341391633, 72341391642⟩, ⟨69783815370, 74927618104⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 83361792 83886080 68976640 70492160 ⟨⟨70594889166, 70594889175⟩, ⟨68053426530, 73164829038⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 83361792 83886080 70492160 72007680 ⟨⟨71984513949, 71984513958⟩, ⟨69439329182, 74558090482⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 82837504 83361792 72007680 73523200 ⟨⟨73731469815, 73731469823⟩, ⟨71170216360, 76321286365⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 82837504 83361792 73523200 75038720 ⟨⟨75116263089, 75116263098⟩, ⟨72551381126, 77709621159⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 83361792 83886080 72007680 73523200 ⟨⟨73368867955, 73368867966⟩, ⟨70820009777, 75946032545⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 83361792 83886080 73523200 75038720 ⟨⟨74747997830, 74747997841⟩, ⟨72195514240, 77328702588⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 81788928 83886080 68976640 75038720 t = true :=
  ⟨_, (join_su (m := 82837504) (by decide) (join_sr (m := 72007680) (by decide) (join_su (m := 82313216) (by decide) (join_sr (m := 70492160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 70492160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 82313216) (by decide) (join_sr (m := 73523200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 73523200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 72007680) (by decide) (join_su (m := 83361792) (by decide) (join_sr (m := 70492160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 70492160) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 83361792) (by decide) (join_sr (m := 73523200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 73523200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (39/400 : ℝ) (1/10 : ℝ) →
    rho ∈ Set.Icc (421/5120 : ℝ) (229/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((81788928 : ℤ) : ℝ) / (D : ℝ)) = (39/400 : ℝ) := by norm_num [D]
  have e1 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e2 : (((68976640 : ℤ) : ℝ) / (D : ℝ)) = (421/5120 : ℝ) := by norm_num [D]
  have e3 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
