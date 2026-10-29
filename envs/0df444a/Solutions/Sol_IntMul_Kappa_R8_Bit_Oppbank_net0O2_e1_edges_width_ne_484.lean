-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_e1_edges_width_ne_484
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:50:03.560008+00:00
-- url     : https://prove2.me/submissions/805a1a7e-7516-478b-a5a3-2a5b0804fbeb

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_pickE_oneRun_headW

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd

private lemma pickE_headW_ne {q : Matrix (Fin 529) (Fin 529) ℚ} {r : ℕ} (hr : r ≠ 484) :
    (Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2)
      (OneRunNet2.pickE (OneRunNet2.PE q (OneRunNet2.oneRun r))).runs.head?).getD 0 ≠ 484 := by
  by_cases h : ∃ e, OneRunNet2.PE q (OneRunNet2.oneRun r) e
  · rw [IntMul.Kappa.R8.Bit.Oppbank.pickE_oneRun_headW q r h]
    exact hr
  · have hp : OneRunNet2.pickE (OneRunNet2.PE q (OneRunNet2.oneRun r)) = OneRunNet2.dfltE := by
      unfold OneRunNet2.pickE
      exact dif_neg h
    rw [hp]
    simp [OneRunNet2.dfltE]

private lemma rkC_le_23 {o c : ℕ} (ho : o < codeBound) (hc : c < codeBound) : rkC o c ≤ 23 := by
  have ho' : dimCF o ≤ 23 := IntMul.Kappa.R8.Bit.Oppbank.DimBound.dimCF_le_23 ho
  have hc' : dimCF c ≤ 23 := IntMul.Kappa.R8.Bit.Oppbank.DimBound.dimCF_le_23 hc
  unfold rkC
  dsimp only
  split_ifs with h <;> omega

private lemma rkC_ne {o c : ℕ} (ho : o < codeBound) (hc : c < codeBound) : rkC o c ≠ 484 := by
  have hle := rkC_le_23 ho hc
  intro h
  rw [h] at hle
  omega

private lemma e1_headW_ne (b o c : ℕ) :
    (Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2)
      (((toNB ch0O).e1 b o c).runs.head?)).getD 0 ≠ 484 := by
  show (Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) ((ch0O.e1 b o c).runs.head?)).getD 0 ≠ 484
  simp only [OneRunNet2.ch0O]
  split_ifs with h
  · exact pickE_headW_ne (q := K S0 Si0 (Dm o c) (Pl b)) (r := rkC o c) (rkC_ne h.2.1 h.2.2)
  · simp [OneRunNet2.dfltE]

theorem solution :
    (List.filter
      (fun e : Edge 529 =>
        decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = 484))
      (((List.range v).flatMap fun b =>
          NB.chunkProg (NB.ι1 b) ((toNB ch0O).e1 b) NB.cs1).filterMap Instr.edgeOf)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro e he
  rw [List.mem_filterMap] at he
  obtain ⟨x, hx, hxe⟩ := he
  simp only [List.mem_flatMap, List.mem_range] at hx
  obtain ⟨b, _hb, hxb⟩ := hx
  simp only [NB.chunkProg, List.mem_flatMap] at hxb
  obtain ⟨ch, _hch, hxch⟩ := hxb
  simp only [NB.chunkInstrs, List.mem_append, List.mem_map] at hxch
  rcases hxch with ⟨mv, _hmv, rfl⟩ | ⟨p, _hp, rfl⟩
  · simp only [Instr.edgeOf, Option.some.injEq] at hxe
    subst hxe
    simp only [decide_eq_true_eq]
    exact e1_headW_ne b mv.2 ch.1
  · simp [NB.xorG, Instr.edgeOf] at hxe
