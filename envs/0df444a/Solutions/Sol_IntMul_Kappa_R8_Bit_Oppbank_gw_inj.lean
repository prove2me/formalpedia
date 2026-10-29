-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.gw_inj
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T22:01:32.942985+00:00
-- url     : https://prove2.me/submissions/71a5fc55-6794-4ff8-9423-994dd6f25119

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankWireLayout
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.NB

private theorem gw_lt {g : ℕ} (hg : g < W) : gw g = .inl ⟨g, hg⟩ := by
  simp only [gw, dif_pos hg]

private theorem gw_ge {g : ℕ} (hg : ¬ g < W) (hbound : g < W + Tmp) :
    gw g = .inr ⟨(g - W) % Tmp, Nat.mod_lt _ (by decide : 0 < Tmp)⟩ := by
  simp only [gw, dif_neg hg]

theorem solution {g g' : ℕ} (hg : g < W + Tmp) (hg' : g' < W + Tmp)
    (h : gw g = gw g') : g = g' := by
  by_cases h1 : g < W <;> by_cases h2 : g' < W
  · rw [gw_lt h1, gw_lt h2] at h; simpa using h
  · rw [gw_lt h1, gw_ge (by omega) hg'] at h; simp at h
  · rw [gw_ge (by omega) hg, gw_lt h2] at h; simp at h
  · rw [gw_ge (by omega) hg, gw_ge (by omega) hg'] at h
    -- both inr: (g-W)%Tmp = (g'-W)%Tmp and both < Tmp so g-W = g'-W
    simp only [Sum.inr.injEq, Fin.mk.injEq] at h
    have hgW : g - W < Tmp := by omega
    have hgW' : g' - W < Tmp := by omega
    have : g - W = g' - W := by
      rw [← Nat.mod_eq_of_lt hgW, ← Nat.mod_eq_of_lt hgW', h]
    omega
