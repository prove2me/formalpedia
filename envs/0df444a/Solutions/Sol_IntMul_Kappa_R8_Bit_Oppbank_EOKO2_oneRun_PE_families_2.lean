-- Prove2me | solution 2 for IntMul.Kappa.R8.Bit.Oppbank.EOKO2_oneRun_PE_families
-- status  : ACCEPTED   (disprove)
-- author  : @scuba8684
-- created : 2026-11-26T06:44:03.2256+00:00
-- url     : https://prove2.me/submissions/f0a91ebe-a847-4aea-b280-1b6e2a762705

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank.EOKO2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd (Dm Pl nestOK K rkC)
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2 (PE oneRun)
open IntMul.Kappa.R8.Bit.Oppbank.SupG (codeBound)

private theorem oneRun_positive {r : ℕ} {rs : List (ℕ × ℕ × ℕ)}
    (h : oneRun r rs) : 0 < r := h.1

theorem solution : ¬ (
    (∀ b < 1771, ∀ o < codeBound, ∀ c < codeBound, nestOK o c = true →
      ∃ e, PE (K ch0NB.S ch0NB.Si (Dm o c) (Pl b)) (oneRun (rkC o c)) e) ∧
    (∀ a < 1771, ∀ o < codeBound, ∀ c < codeBound, nestOK o c = true →
      ∃ e, PE (K ch0NB.S ch0NB.Si (Pl a) (Dm o c)) (oneRun (rkC o c)) e) ∧
    (∀ b < 1771, ∃ e, PE (K ch0NB.S ch0NB.Si 1 (1 - Pl b)) (oneRun 22) e) ∧
    (∀ a < 1771, ∀ t < 1771, ∃ e, PE (K ch0NB.S ch0NB.Si (1 - Pl a) (1 - Pl t)) (oneRun 484) e) ∧
    (∀ a < 1771, ∃ e, PE (K ch0NB.S ch0NB.Si (1 - Pl a) 1) (oneRun 22) e) ∧
    (∀ a < 1771, ∀ s < 1771, ∃ e, PE (K ch0NB.S ch0NB.Si (Pl a) (Pl s)) (oneRun 1) e)) := by
  intro families
  have hbound : 0 < codeBound := by decide
  have hn : nestOK 0 0 = true := by rfl
  have hr : rkC 0 0 = 0 := by rfl
  obtain ⟨edge, hedge⟩ := families.1 0 (by decide) 0 hbound 0 hbound hn
  have hpos := oneRun_positive hedge.2
  rw [hr] at hpos
  exact (Nat.lt_irrefl 0) hpos
