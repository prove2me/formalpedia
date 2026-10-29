-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_ex_edges_width_ne_484
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:42:47.728981+00:00
-- url     : https://prove2.me/submissions/0f0d72e4-03d8-4cb1-b206-f735043945a8

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_pickE_oneRun_headW

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd

private lemma headW_pickE_ne {q : Matrix (Fin 529) (Fin 529) ℚ} {r : ℕ} (hr : r ≠ 484) :
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

theorem solution :
    (List.filter
      (fun e : Edge 529 =>
        decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = 484))
      ((List.range v).flatMap fun b =>
        (List.range' wEnt NR).map fun _ => (toNB ch0O).ex b)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro e he
  simp only [List.mem_flatMap, List.mem_map, List.mem_range, List.mem_range'] at he
  obtain ⟨b, hb, x, hx, rfl⟩ := he
  have hex : (toNB ch0O).ex b =
      OneRunNet2.pickE (OneRunNet2.PE (K S0 Si0 1 (1 - Pl b)) (OneRunNet2.oneRun 22)) := by
    show ch0O.ex b = _
    simp only [OneRunNet2.ch0O]
    exact if_pos hb
  rw [hex]
  simp only [decide_eq_true_eq]
  exact headW_pickE_ne (q := K S0 Si0 1 (1 - Pl b)) (by decide)
