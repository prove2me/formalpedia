-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_layout_wires_lt_NL
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T06:22:05.055778+00:00
-- url     : https://prove2.me/submissions/206f2c89-4a63-47d6-8b6b-48973df4a025

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankWireLayout
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
open IntMul.Kappa.R8.Bit.Oppbank

/-- Domain of `wX` lands in the local address space. -/
private theorem wX_lt_NL {t : ℕ} (ht : t < v) : wX t < NL := by
  change t < NL; simp only [v, NL] at *; omega

/-- Domain of `wY` lands in the local address space. -/
private theorem wY_lt_NL {T : ℕ} (hT : T < v) : wY T < NL := by
  change v + T < NL; simp only [v, NL] at *; omega

/-- Domain of `wS` lands in the local address space. -/
private theorem wS_lt_NL {q : ℕ} (hq : q < NR) : wS q < NL := by
  change wEnt + q < NL
  have h1 : wEnt + NR = wAuxEnd := by simp only [wEnt, NR, wAuxEnd]
  have h2 : wAuxEnd < NL := by simp only [wAuxEnd, NL]; omega
  omega

/-- Domain of `wT` lands in the local address space. -/
private theorem wT_lt_NL {c : ℕ} (hc : c < h) : wT c < NL := by
  change wAuxEnd + c < NL
  have : NL = wAuxEnd + h := by simp only [NL, wAuxEnd, h]
  omega

theorem solution :
    (∀ t : ℕ, t < v → wX t < NL) ∧
    (∀ T : ℕ, T < v → wY T < NL) ∧
    (∀ q : ℕ, q < NR → wS q < NL) ∧
    (∀ c : ℕ, c < h → wT c < NL) :=
  ⟨fun _ ht => wX_lt_NL ht, fun _ hT => wY_lt_NL hT,
   fun _ hq => wS_lt_NL hq, fun _ hc => wT_lt_NL hc⟩

