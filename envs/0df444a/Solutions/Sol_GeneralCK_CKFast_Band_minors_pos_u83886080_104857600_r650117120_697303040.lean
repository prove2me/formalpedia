-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u83886080_104857600_r650117120_697303040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:01:16.582469+00:00
-- url     : https://prove2.me/submissions/265358c8-f0dc-4d63-82d9-957686c8d31c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/10, 1/8]`, `ρ ∈ [31/40, 133/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 83886080 89128960 650117120 661913600 ⟨⟨418250131291, 418250131304⟩, ⟨392140942674, 445030534183⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 83886080 89128960 661913600 673710080 ⟨⟨423623648753, 423623648767⟩, ⟨397485807465, 450410827479⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 89128960 94371840 650117120 661913600 ⟨⟨408436389968, 408436389977⟩, ⟨382814272336, 434740189307⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 89128960 94371840 661913600 673710080 ⟨⟨413769376484, 413769376492⟩, ⟨388109778112, 440090114245⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 83886080 89128960 673710080 685506560 ⟨⟨428970880304, 428970880320⟩, ⟨402804600009, 455764798684⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 83886080 89128960 685506560 697303040 ⟨⟨434293012686, 434293012698⟩, ⟨408098472855, 461093657278⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 89128960 94371840 673710080 685506560 ⟨⟨419076841147, 419076841155⟩, ⟨393380082671, 445414334863⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 89128960 94371840 685506560 697303040 ⟨⟨424359915480, 424359915485⟩, ⟨398626281596, 450714008984⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 94371840 99614720 650117120 661913600 ⟨⟨398856984645, 398856984657⟩, ⟨373706174206, 424698118541⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 94371840 99614720 661913600 673710080 ⟨⟨404145411588, 404145411600⟩, ⟨378948992352, 430012899235⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 99614720 104857600 650117120 661913600 ⟨⟨389497445038, 389497445050⟩, ⟨364803273768, 414888983864⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 99614720 104857600 661913600 673710080 ⟨⟨394737595950, 394737595963⟩, ⟨369990339700, 420164204791⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 94371840 99614720 673710080 685506560 ⟨⟨409409122013, 409409122026⟩, ⟨384167500896, 435302659468⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 94371840 99614720 685506560 697303040 ⟨⟨414649192539, 414649192550⟩, ⟨389362739540, 440568504690⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 99614720 104857600 673710080 685506560 ⟨⟨399953867262, 399953867275⟩, ⟨375154001007, 425415142746⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 99614720 104857600 685506560 697303040 ⟨⟨405147281360, 405147281370⟩, ⟨380295242829, 430642850611⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 83886080 104857600 650117120 697303040 t = true :=
  ⟨_, (join_su (m := 94371840) (by decide) (join_sr (m := 673710080) (by decide) (join_su (m := 89128960) (by decide) (join_sr (m := 661913600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 661913600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 89128960) (by decide) (join_sr (m := 685506560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 685506560) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 673710080) (by decide) (join_su (m := 99614720) (by decide) (join_sr (m := 661913600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 661913600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 99614720) (by decide) (join_sr (m := 685506560) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 685506560) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/10 : ℝ) (1/8 : ℝ) →
    rho ∈ Set.Icc (31/40 : ℝ) (133/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e1 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e2 : (((650117120 : ℤ) : ℝ) / (D : ℝ)) = (31/40 : ℝ) := by norm_num [D]
  have e3 : (((697303040 : ℤ) : ℝ) / (D : ℝ)) = (133/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
