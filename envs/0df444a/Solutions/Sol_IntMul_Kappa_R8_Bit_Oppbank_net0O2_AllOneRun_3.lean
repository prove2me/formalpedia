-- Prove2me | solution 3 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_AllOneRun
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:11:36.684452+00:00
-- url     : https://prove2.me/submissions/201f5691-f9f2-4470-a6a2-8fc333dfdf4b

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunMomExpand
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_edges_channel_pickE
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunMomExpand
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

private theorem pickE_oneRun_or_dflt
    (q : Matrix (Fin 529) (Fin 529) ℚ) (r : ℕ) :
    let P := OneRunNet2.PE q (oneRun r)
    OneRunNet2.pickE P = OneRunNet2.dfltE ∨ oneRun r (OneRunNet2.pickE P).runs := by
  classical
  by_cases h : ∃ e, OneRunNet2.PE q (oneRun r) e
  · right
    exact (pickE_of_exists h).2
  · left
    exact pickE_eq_dflt_of_empty h

theorem solution : AllOneRun := by
  intro e he
  rcases net0O2_edges_channel_pickE e he with
    h | ⟨b, o, c, hb, ho, hc, rfl⟩ | ⟨a, o, c, ha, ho, hc, rfl⟩ |
    ⟨b, hb, rfl⟩ | ⟨a, ha, rfl⟩ | ⟨a, t, ha, ht, rfl⟩ | ⟨a, s, ha, hs, rfl⟩
  · exact Or.inl h
  · rcases pickE_oneRun_or_dflt (K S0 Si0 (Dm o c) (Pl b)) (rkC o c) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨rkC o c, h⟩
  · rcases pickE_oneRun_or_dflt (K S0 Si0 (Pl a) (Dm o c)) (rkC o c) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨rkC o c, h⟩
  · rcases pickE_oneRun_or_dflt (K S0 Si0 1 (1 - Pl b)) 22 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨22, h⟩
  · rcases pickE_oneRun_or_dflt (K S0 Si0 (1 - Pl a) 1) 22 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨22, h⟩
  · rcases pickE_oneRun_or_dflt (K S0 Si0 (1 - Pl a) (1 - Pl t)) 484 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨484, h⟩
  · rcases pickE_oneRun_or_dflt (K S0 Si0 (Pl a) (Pl s)) 1 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨1, h⟩
