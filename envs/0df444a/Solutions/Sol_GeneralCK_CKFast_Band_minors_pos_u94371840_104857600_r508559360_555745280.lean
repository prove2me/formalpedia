-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u94371840_104857600_r508559360_555745280
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:00:42.809496+00:00
-- url     : https://prove2.me/submissions/b7e2b539-8308-46a2-a758-a4742ef5d20c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/80, 1/8]`, `ρ ∈ [97/160, 53/80]` by 16 cells of the computing
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
theorem cell0 : cellOK 94371840 96993280 508559360 520355840 ⟨⟨335238419957, 335238419967⟩, ⟨319785338128, 351047833618⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 96993280 99614720 508559360 520355840 ⟨⟨330827824150, 330827824154⟩, ⟨315565693197, 346443779407⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 94371840 96993280 520355840 532152320 ⟨⟨340936871390, 340936871402⟩, ⟨325467259207, 356753872994⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 96993280 99614720 520355840 532152320 ⟨⟨336495349727, 336495349734⟩, ⟨321213688026, 352122257207⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 99614720 102236160 508559360 520355840 ⟨⟨326482682225, 326482682235⟩, ⟨311407693910, 341908933890⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 102236160 104857600 508559360 520355840 ⟨⟨322200839784, 322200839797⟩, ⟨307309314027, 337441021538⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 99614720 102236160 520355840 532152320 ⟨⟨332118318242, 332118318255⟩, ⟨317020952997, 347558720404⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 102236160 104857600 520355840 532152320 ⟨⟨327803673367, 327803673379⟩, ⟨312887071733, 343061045198⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 94371840 96993280 532152320 543948800 ⟨⟨346594059582, 346594059594⟩, ⟨331108443539, 362418242886⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 96993280 99614720 532152320 543948800 ⟨⟨342122495178, 342122495184⟩, ⟨326821861593, 357759904090⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 94371840 96993280 543948800 555745280 ⟨⟨352211630814, 352211630826⟩, ⟨336710492389, 368042629681⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 96993280 99614720 543948800 555745280 ⟨⟨347710854143, 347710854150⟩, ⟨332391762847, 363358354022⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 99614720 102236160 532152320 543948800 ⟨⟨337714457612, 337714457625⟩, ⟨322595301969, 353168520458⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 102236160 104857600 532152320 543948800 ⟨⟨333367892667, 333367892680⟩, ⟨318426825022, 348641930853⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 99614720 102236160 543948800 555745280 ⟨⟨343272642404, 343272642417⟩, ⟨328132238670, 358739916470⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 102236160 104857600 543948800 555745280 ⟨⟨338894989281, 338894989293⟩, ⟨323930021862, 354185210290⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 94371840 104857600 508559360 555745280 t = true :=
  ⟨_, (join_sr (m := 532152320) (by decide) (join_su (m := 99614720) (by decide) (join_sr (m := 520355840) (by decide) (join_su (m := 96993280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 96993280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 520355840) (by decide) (join_su (m := 102236160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 102236160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 99614720) (by decide) (join_sr (m := 543948800) (by decide) (join_su (m := 96993280) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 96993280) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 543948800) (by decide) (join_su (m := 102236160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 102236160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/80 : ℝ) (1/8 : ℝ) →
    rho ∈ Set.Icc (97/160 : ℝ) (53/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e1 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e2 : (((508559360 : ℤ) : ℝ) / (D : ℝ)) = (97/160 : ℝ) := by norm_num [D]
  have e3 : (((555745280 : ℤ) : ℝ) / (D : ℝ)) = (53/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
