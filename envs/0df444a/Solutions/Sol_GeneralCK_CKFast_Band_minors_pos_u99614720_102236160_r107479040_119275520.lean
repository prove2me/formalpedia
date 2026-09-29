-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u99614720_102236160_r107479040_119275520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:40:16.055647+00:00
-- url     : https://prove2.me/submissions/e4fea079-66aa-4f55-b38a-ca851502f1d7

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/160, 39/320]`, `ρ ∈ [41/320, 91/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 99614720 100270080 107479040 110428160 ⟨⟨91615263654, 91615263656⟩, ⟨88213172260, 95063095250⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 100270080 100925440 107479040 110428160 ⟨⟨91137971475, 91137971483⟩, ⟨87753421724, 94567845751⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 99614720 100270080 110428160 113377280 ⟨⟨93827815261, 93827815268⟩, ⟨90418347606, 97282802325⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 100270080 100925440 110428160 113377280 ⟨⟨93341217617, 93341217626⟩, ⟨89949288870, 96778254809⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 100925440 101580800 107479040 110428160 ⟨⟨90664654428, 90664654437⟩, ⟨87297460031, 94076763620⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 101580800 102236160 107479040 110428160 ⟨⟨90195255840, 90195255849⟩, ⟨86845233537, 93589789048⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 100925440 101580800 110428160 113377280 ⟨⟨92858644926, 92858644934⟩, ⟨89484069634, 96277923541⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 101580800 102236160 110428160 113377280 ⟨⟨92380040133, 92380040143⟩, ⟨89022635845, 95781748358⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 99614720 100270080 113377280 116326400 ⟨⟨96028742936, 96028742943⟩, ⟨92612032462, 99490752589⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 100270080 100925440 113377280 116326400 ⟨⟨95532981454, 95532981463⟩, ⟨92133805257, 98977050546⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 99614720 100270080 116326400 119275520 ⟨⟨98218201796, 98218201802⟩, ⟨94794379026, 101687104099⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 100270080 100925440 116326400 119275520 ⟨⟨97713415261, 97713415271⟩, ⟨94307120309, 101164388105⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 100925440 101580800 113377280 116326400 ⟨⟨95041292807, 95041292815⟩, ⟨91659466298, 98467611661⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 101580800 102236160 113377280 116326400 ⟨⟨94553619593, 94553619601⟩, ⟨91188961155, 97962375459⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 100925440 101580800 116326400 119275520 ⟨⟨97212747561, 97212747572⟩, ⟨93823796729, 100645980279⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 101580800 102236160 116326400 119275520 ⟨⟨96716140978, 96716140988⟩, ⟨93344353501, 100131819861⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 99614720 102236160 107479040 119275520 t = true :=
  ⟨_, (join_sr (m := 113377280) (by decide) (join_su (m := 100925440) (by decide) (join_sr (m := 110428160) (by decide) (join_su (m := 100270080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 100270080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 110428160) (by decide) (join_su (m := 101580800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 101580800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 100925440) (by decide) (join_sr (m := 116326400) (by decide) (join_su (m := 100270080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 100270080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 116326400) (by decide) (join_su (m := 101580800) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 101580800) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/160 : ℝ) (39/320 : ℝ) →
    rho ∈ Set.Icc (41/320 : ℝ) (91/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((99614720 : ℤ) : ℝ) / (D : ℝ)) = (19/160 : ℝ) := by norm_num [D]
  have e1 : (((102236160 : ℤ) : ℝ) / (D : ℝ)) = (39/320 : ℝ) := by norm_num [D]
  have e2 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  have e3 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
