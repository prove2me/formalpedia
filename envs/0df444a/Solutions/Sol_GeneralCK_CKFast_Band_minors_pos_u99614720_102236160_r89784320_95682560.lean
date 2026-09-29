-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u99614720_102236160_r89784320_95682560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:36:51.605023+00:00
-- url     : https://prove2.me/submissions/e2cd6a43-890d-4563-93f9-269b8d775cac

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/160, 39/320]`, `ρ ∈ [137/1280, 73/640]` by 8 cells of the computing
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
theorem cell0 : cellOK 99614720 100270080 89784320 92733440 ⟨⟨78086796538, 78086796544⟩, ⟨74731938459, 81488730428⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 100270080 100925440 89784320 92733440 ⟨⟨77668479934, 77668479944⟩, ⟨74331136133, 81052454836⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 99614720 100270080 92733440 95682560 ⟨⟨80372513910, 80372513912⟩, ⟨77009413143, 83782466699⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 100270080 100925440 92733440 95682560 ⟨⟨79943978171, 79943978181⟩, ⟨76598401833, 83335966751⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 100925440 101580800 89784320 92733440 ⟨⟨77253795278, 77253795286⟩, ⟨73933775087, 80620008480⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 101580800 102236160 89784320 92733440 ⟨⟨76842688930, 76842688938⟩, ⟨73539804873, 80191334399⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 100925440 101580800 92733440 95682560 ⟨⟨79519137181, 79519137191⟩, ⟨76190895249, 82893358076⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 101580800 102236160 92733440 95682560 ⟨⟨79097936697, 79097936707⟩, ⟨75786842309, 82454583143⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 99614720 102236160 89784320 95682560 t = true :=
  ⟨_, (join_su (m := 100925440) (by decide) (join_sr (m := 92733440) (by decide) (join_su (m := 100270080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 100270080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 92733440) (by decide) (join_su (m := 101580800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 101580800) (by decide) (leaf_ok cell6) (leaf_ok cell7))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/160 : ℝ) (39/320 : ℝ) →
    rho ∈ Set.Icc (137/1280 : ℝ) (73/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((99614720 : ℤ) : ℝ) / (D : ℝ)) = (19/160 : ℝ) := by norm_num [D]
  have e1 : (((102236160 : ℤ) : ℝ) / (D : ℝ)) = (39/320 : ℝ) := by norm_num [D]
  have e2 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  have e3 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
