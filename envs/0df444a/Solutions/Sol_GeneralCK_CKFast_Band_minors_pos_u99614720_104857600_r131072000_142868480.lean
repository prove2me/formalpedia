-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u99614720_104857600_r131072000_142868480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:45:48.268212+00:00
-- url     : https://prove2.me/submissions/39103a87-9780-47f8-9614-e5ad280f934c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/160, 1/8]`, `ρ ∈ [5/32, 109/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 99614720 100925440 131072000 134021120 ⟨⟨108724195434, 108724195442⟩, ⟨103364077643, 114191156800⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 99614720 100925440 134021120 136970240 ⟨⟨110843818931, 110843818941⟩, ⟨105472046235, 116321991842⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 100925440 102236160 131072000 134021120 ⟨⟨107636976190, 107636976194⟩, ⟨102327215824, 113051855212⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 100925440 102236160 134021120 136970240 ⟨⟨109740174711, 109740174717⟩, ⟨104418730537, 115166313299⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 99614720 100925440 136970240 139919360 ⟨⟨112953045641, 112953045650⟩, ⟨107569787751, 118442260904⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 99614720 100925440 139919360 142868480 ⟨⟨115052008984, 115052008994⟩, ⟨109657432180, 120552100881⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 100925440 102236160 136970240 139919360 ⟨⟨111833214841, 111833214843⟩, ⟨106500252202, 117270448039⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 100925440 102236160 139919360 142868480 ⟨⟨113916225401, 113916225408⟩, ⟨108571906365, 119364391585⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 102236160 103546880 131072000 134021120 ⟨⟨106566696386, 106566696394⟩, ⟨101306258685, 111930573814⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 102236160 103546880 134021120 136970240 ⟨⟨108653612302, 108653612310⟩, ⟨103381467144, 114028791241⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 103546880 104857600 131072000 134021120 ⟨⟨105512901926, 105512901936⟩, ⟨100300783894, 110826825081⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 103546880 104857600 134021120 136970240 ⟨⟨107583676268, 107583676278⟩, ⟨102359832074, 112908937161⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 102236160 103546880 136970240 139919360 ⟨⟨110730602260, 110730602269⟩, ⟨105446910727, 116116921908⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 102236160 103546880 139919360 142868480 ⟨⟨112797790673, 112797790681⟩, ⟨107502710700, 118195093407⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 103546880 104857600 136970240 139919360 ⟨⟨109644751307, 109644751316⟩, ⟨104409337862, 114981193193⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 103546880 104857600 139919360 142868480 ⟨⟨111696247201, 111696247209⟩, ⟨106449418405, 117043716390⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 99614720 104857600 131072000 142868480 t = true :=
  ⟨_, (join_su (m := 102236160) (by decide) (join_sr (m := 136970240) (by decide) (join_su (m := 100925440) (by decide) (join_sr (m := 134021120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 134021120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 100925440) (by decide) (join_sr (m := 139919360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 139919360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 136970240) (by decide) (join_su (m := 103546880) (by decide) (join_sr (m := 134021120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 134021120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 103546880) (by decide) (join_sr (m := 139919360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 139919360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/160 : ℝ) (1/8 : ℝ) →
    rho ∈ Set.Icc (5/32 : ℝ) (109/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((99614720 : ℤ) : ℝ) / (D : ℝ)) = (19/160 : ℝ) := by norm_num [D]
  have e1 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e2 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e3 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
