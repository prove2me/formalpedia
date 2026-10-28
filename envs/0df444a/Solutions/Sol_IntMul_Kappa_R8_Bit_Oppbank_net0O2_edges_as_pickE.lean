-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_edges_as_pickE
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:07:40.208365+00:00
-- url     : https://prove2.me/submissions/02c1de2f-535b-48a0-9514-951aaff7b5ae
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_edges_channel_pickE
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_pickE_PE_of_channel
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O_edges_ne_dfltE
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd hiding PE dfltE pickE
open Matrix

theorem solution :
    ∀ e ∈ net0O.edges,
      ∃ (r : ℕ) (q : Matrix (Fin 529) (Fin 529) ℚ),
        (∃ e', OneRunNet2.PE q (oneRun r) e') ∧ e = OneRunNet2.pickE (OneRunNet2.PE q (oneRun r)) := by
  intro e he
  have hne := net0O_edges_ne_dfltE e he
  rcases net0O2_edges_channel_pickE e he with
    h | ⟨b, o, c, hb, ho, hc, rfl⟩ | ⟨a, o, c, ha, ho, hc, rfl⟩ |
    ⟨b, hb, rfl⟩ | ⟨a, ha, rfl⟩ | ⟨a, t, ha, ht, rfl⟩ | ⟨a, s, ha, hs, rfl⟩
  · exact (hne h).elim
  · exact ⟨rkC o c, K S0 Si0 (Dm o c) (Pl b), pickE_PE_of_channel _ _ _ rfl hne⟩
  · exact ⟨rkC o c, K S0 Si0 (Pl a) (Dm o c), pickE_PE_of_channel _ _ _ rfl hne⟩
  · exact ⟨22, K S0 Si0 1 (1 - Pl b), pickE_PE_of_channel _ _ _ rfl hne⟩
  · exact ⟨22, K S0 Si0 (1 - Pl a) 1, pickE_PE_of_channel _ _ _ rfl hne⟩
  · exact ⟨484, K S0 Si0 (1 - Pl a) (1 - Pl t), pickE_PE_of_channel _ _ _ rfl hne⟩
  · exact ⟨1, K S0 Si0 (Pl a) (Pl s), pickE_PE_of_channel _ _ _ rfl hne⟩
