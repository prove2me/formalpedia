-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u99614720_102236160_r95682560_107479040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:37:50.249423+00:00
-- url     : https://prove2.me/submissions/5c898cd9-9444-4637-94b2-b432a810d4d4

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/160, 39/320]`, `ρ ∈ [73/640, 41/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 99614720 100270080 95682560 98631680 ⟨⟨82645614239, 82645614245⟩, ⟨79274423443, 86063433720⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 100270080 100925440 95682560 98631680 ⟨⟨82207019647, 82207019657⟩, ⟨78853361086, 85606872000⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 99614720 100270080 98631680 101580800 ⟨⟨84906270849, 84906270856⟩, ⟨81527139257, 88331808250⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 100270080 100925440 98631680 101580800 ⟨⟨84457774370, 84457774380⟩, ⟨81096180564, 87865343950⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 100925440 101580800 95682560 98631680 ⟨⟨81772180269, 81772180277⟩, ⟨78435864602, 85154261221⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 101580800 102236160 95682560 98631680 ⟨⟨81341041298, 81341041307⟩, ⟨78021882321, 84705543326⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 100925440 101580800 98631680 101580800 ⟨⟨84013091308, 84013091316⟩, ⟨80668846660, 87402887968⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 101580800 102236160 98631680 101580800 ⟨⟨83572166336, 83572166344⟩, ⟨80245085332, 86944381749⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 99614720 100270080 101580800 104529920 ⟨⟨87154653833, 87154653839⟩, ⟨83767727357, 90587763734⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 100270080 100925440 101580800 104529920 ⟨⟨86696409211, 86696409219⟩, ⟨83327023887, 90111552744⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 99614720 100270080 104529920 107479040 ⟨⟨89390930139, 89390930146⟩, ⟨85996351448, 92831470380⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 100270080 100925440 104529920 107479040 ⟨⟨88923087973, 88923087981⟩, ⟨85546051694, 92345665370⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 100925440 101580800 101580800 104529920 ⟨⟨86242034014, 86242034024⟩, ⟨82890001967, 89639405222⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 101580800 102236160 101580800 104529920 ⟨⟨85791472433, 85791472443⟩, ⟨82456608867, 89171262162⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 100925440 101580800 104529920 107479040 ⟨⟨88459169114, 88459169125⟩, ⟨85099488154, 91863976823⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 101580800 102236160 104529920 107479040 ⟨⟨87999117310, 87999117318⟩, ⟨84656607624, 91386345313⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 99614720 102236160 95682560 107479040 t = true :=
  ⟨_, (join_sr (m := 101580800) (by decide) (join_su (m := 100925440) (by decide) (join_sr (m := 98631680) (by decide) (join_su (m := 100270080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 100270080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 98631680) (by decide) (join_su (m := 101580800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 101580800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 100925440) (by decide) (join_sr (m := 104529920) (by decide) (join_su (m := 100270080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 100270080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 104529920) (by decide) (join_su (m := 101580800) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 101580800) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/160 : ℝ) (39/320 : ℝ) →
    rho ∈ Set.Icc (73/640 : ℝ) (41/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((99614720 : ℤ) : ℝ) / (D : ℝ)) = (19/160 : ℝ) := by norm_num [D]
  have e1 : (((102236160 : ℤ) : ℝ) / (D : ℝ)) = (39/320 : ℝ) := by norm_num [D]
  have e2 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  have e3 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
