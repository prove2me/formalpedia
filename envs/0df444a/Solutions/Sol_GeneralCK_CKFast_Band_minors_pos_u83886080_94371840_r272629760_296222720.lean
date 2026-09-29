-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u83886080_94371840_r272629760_296222720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:53:26.270594+00:00
-- url     : https://prove2.me/submissions/98b0fd6d-c708-46ac-b278-5dbf51135b7a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/10, 9/80]`, `ρ ∈ [13/40, 113/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 83886080 86507520 272629760 278528000 ⟨⟨222328561768, 222328561775⟩, ⟨209698448417, 235353082446⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 83886080 86507520 278528000 284426240 ⟨⟨225991645649, 225991645657⟩, ⟨213343633689, 239029444398⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 86507520 89128960 272629760 278528000 ⟨⟨218495137909, 218495137921⟩, ⟨206083874188, 231291520888⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 86507520 89128960 278528000 284426240 ⟨⟨222124909370, 222124909380⟩, ⟨209694079552, 234936535261⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 83886080 86507520 284426240 290324480 ⟨⟨229626603999, 229626604004⟩, ⟨216961274833, 242677147580⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 83886080 86507520 290324480 296222720 ⟨⟨233234108743, 233234108746⟩, ⟨220552018934, 246296888098⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 86507520 89128960 284426240 290324480 ⟨⟨225727471417, 225727471430⟩, ⟨213277652871, 238553804530⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 86507520 89128960 290324480 296222720 ⟨⟨229303462206, 229303462216⟩, ⟨216835208611, 242143990021⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 89128960 91750400 272629760 278528000 ⟨⟨214759360003, 214759360016⟩, ⟨202559283530, 227335615218⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 89128960 91750400 278528000 284426240 ⟨⟨218355467968, 218355467980⟩, ⟨206134299252, 230948770441⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 91750400 94371840 272629760 278528000 ⟨⟨211116758278, 211116758290⟩, ⟨199120607637, 223480478399⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 91750400 94371840 278528000 284426240 ⟨⟨214678905691, 214678905703⟩, ⟨202660266914, 227061329424⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 89128960 91750400 284426240 290324480 ⟨⟨221925259381, 221925259391⟩, ⟨209683569751, 234535073654⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 89128960 91750400 290324480 296222720 ⟨⟨225469340272, 225469340284⟩, ⟨213207678522, 238095153054⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 91750400 94371840 284426240 290324480 ⟨⟨218215606102, 218215606114⟩, ⟨206175042797, 230616200533⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 91750400 94371840 290324480 296222720 ⟨⟨221727435012, 221727435024⟩, ⟨209665489363, 234145688383⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 83886080 94371840 272629760 296222720 t = true :=
  ⟨_, (join_su (m := 89128960) (by decide) (join_sr (m := 284426240) (by decide) (join_su (m := 86507520) (by decide) (join_sr (m := 278528000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 278528000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 86507520) (by decide) (join_sr (m := 290324480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 290324480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 284426240) (by decide) (join_su (m := 91750400) (by decide) (join_sr (m := 278528000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 278528000) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 91750400) (by decide) (join_sr (m := 290324480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 290324480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/10 : ℝ) (9/80 : ℝ) →
    rho ∈ Set.Icc (13/40 : ℝ) (113/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e1 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e2 : (((272629760 : ℤ) : ℝ) / (D : ℝ)) = (13/40 : ℝ) := by norm_num [D]
  have e3 : (((296222720 : ℤ) : ℝ) / (D : ℝ)) = (113/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
