-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_e2_PE
-- status  : ACCEPTED   (disprove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:01:17.851317+00:00
-- url     : https://prove2.me/submissions/bfd86238-309c-48dd-9ebb-63e9a3d073f9

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd

private theorem rkC_zero_zero : rkC 0 0 = 0 := by
  simp [rkC, dimCF]

private theorem oneRun_pos {r : ℕ} {rs : List (ℕ × ℕ × ℕ)} (h : oneRun r rs) : 0 < r :=
  h.1

theorem solution :
    ¬ (∀ (a o c : ℕ) (ha : a < v) (ho : o < codeBound) (hc : c < codeBound),
        ∃ e, OneRunNet2.PE (K S0 Si0 (Pl a) (Dm o c)) (oneRun (rkC o c)) e) := by
  intro h
  have hv : (0 : ℕ) < v := by decide
  have hcb : (0 : ℕ) < codeBound := by decide
  obtain ⟨e, hPE⟩ := h 0 0 0 hv hcb hcb
  have hRun : oneRun (rkC 0 0) e.runs := hPE.2
  have hpos : 0 < rkC 0 0 := oneRun_pos hRun
  have hz : rkC 0 0 = 0 := rkC_zero_zero
  omega
