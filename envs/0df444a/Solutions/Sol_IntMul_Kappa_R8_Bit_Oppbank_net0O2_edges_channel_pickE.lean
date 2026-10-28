-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_edges_channel_pickE
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:46:26.275986+00:00
-- url     : https://prove2.me/submissions/5bdaa371-8a75-40c5-aa89-3331b1b5171b

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunFormalOK2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunFormalOK2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

private theorem e1_form (b o c : ℕ) :
    ch0O.e1 b o c = OneRunNet2.dfltE ∨
      (b < v ∧ o < codeBound ∧ c < codeBound ∧
        ch0O.e1 b o c =
          OneRunNet2.pickE (OneRunNet2.PE (K S0 Si0 (Dm o c) (Pl b)) (oneRun (rkC o c)))) := by
  simp only [ch0O]
  split_ifs with h
  · exact Or.inr ⟨h.1, h.2.1, h.2.2, rfl⟩
  · exact Or.inl rfl

private theorem e2_form (a o c : ℕ) :
    ch0O.e2 a o c = OneRunNet2.dfltE ∨
      (a < v ∧ o < codeBound ∧ c < codeBound ∧
        ch0O.e2 a o c =
          OneRunNet2.pickE (OneRunNet2.PE (K S0 Si0 (Pl a) (Dm o c)) (oneRun (rkC o c)))) := by
  simp only [ch0O]
  split_ifs with h
  · exact Or.inr ⟨h.1, h.2.1, h.2.2, rfl⟩
  · exact Or.inl rfl

private theorem ex_form (b : ℕ) :
    ch0O.ex b = OneRunNet2.dfltE ∨
      (b < v ∧ ch0O.ex b =
          OneRunNet2.pickE (OneRunNet2.PE (K S0 Si0 1 (1 - Pl b)) (oneRun 22))) := by
  simp only [ch0O]
  split_ifs with h
  · exact Or.inr ⟨h, rfl⟩
  · exact Or.inl rfl

private theorem ei_form (a : ℕ) :
    ch0O.ei a = OneRunNet2.dfltE ∨
      (a < v ∧ ch0O.ei a =
          OneRunNet2.pickE (OneRunNet2.PE (K S0 Si0 (1 - Pl a) 1) (oneRun 22))) := by
  simp only [ch0O]
  split_ifs with h
  · exact Or.inr ⟨h, rfl⟩
  · exact Or.inl rfl

private theorem en_form (a t : ℕ) :
    ch0O.en a t = OneRunNet2.dfltE ∨
      (a < v ∧ t < v ∧
        ch0O.en a t =
          OneRunNet2.pickE (OneRunNet2.PE (K S0 Si0 (1 - Pl a) (1 - Pl t)) (oneRun 484))) := by
  simp only [ch0O]
  split_ifs with h
  · exact Or.inr ⟨h.1, h.2, rfl⟩
  · exact Or.inl rfl

private theorem ec_form (a s : ℕ) :
    ch0O.ec a s = OneRunNet2.dfltE ∨
      (a < v ∧ s < v ∧
        ch0O.ec a s =
          OneRunNet2.pickE (OneRunNet2.PE (K S0 Si0 (Pl a) (Pl s)) (oneRun 1))) := by
  simp only [ch0O]
  split_ifs with h
  · exact Or.inr ⟨h.1, h.2, rfl⟩
  · exact Or.inl rfl

theorem solution :
    ∀ e ∈ net0O.edges,
      e = OneRunNet2.dfltE ∨
        (∃ b o c, b < v ∧ o < codeBound ∧ c < codeBound ∧
          e = OneRunNet2.pickE (OneRunNet2.PE (K S0 Si0 (Dm o c) (Pl b)) (oneRun (rkC o c)))) ∨
        (∃ a o c, a < v ∧ o < codeBound ∧ c < codeBound ∧
          e = OneRunNet2.pickE (OneRunNet2.PE (K S0 Si0 (Pl a) (Dm o c)) (oneRun (rkC o c)))) ∨
        (∃ b, b < v ∧ e = OneRunNet2.pickE (OneRunNet2.PE (K S0 Si0 1 (1 - Pl b)) (oneRun 22))) ∨
        (∃ a, a < v ∧ e = OneRunNet2.pickE (OneRunNet2.PE (K S0 Si0 (1 - Pl a) 1) (oneRun 22))) ∨
        (∃ a t, a < v ∧ t < v ∧
          e = OneRunNet2.pickE (OneRunNet2.PE (K S0 Si0 (1 - Pl a) (1 - Pl t)) (oneRun 484))) ∨
        (∃ a s, a < v ∧ s < v ∧
          e = OneRunNet2.pickE (OneRunNet2.PE (K S0 Si0 (Pl a) (Pl s)) (oneRun 1))) := by
  intro e he
  change e ∈ (NB.net (toNB ch0O)).edges at he
  rcases prog_fam (toNB ch0O) e he with
    ⟨b, o, c, rfl⟩ | ⟨a, o, c, rfl⟩ | ⟨b, rfl⟩ | ⟨a, t, rfl⟩ | ⟨a, rfl⟩ | ⟨a, s, rfl⟩
  · rcases e1_form b o c with h | ⟨hb, ho, hc, heq⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨b, o, c, hb, ho, hc, heq⟩)
  · rcases e2_form a o c with h | ⟨ha, ho, hc, heq⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl ⟨a, o, c, ha, ho, hc, heq⟩))
  · rcases ex_form b with h | ⟨hb, heq⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨b, hb, heq⟩)))
  · rcases en_form a t with h | ⟨ha, ht, heq⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, t, ha, ht, heq⟩)))))
  · rcases ei_form a with h | ⟨ha, heq⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, ha, heq⟩))))
  · rcases ec_form a s with h | ⟨ha, hs, heq⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, s, ha, hs, heq⟩)))))

