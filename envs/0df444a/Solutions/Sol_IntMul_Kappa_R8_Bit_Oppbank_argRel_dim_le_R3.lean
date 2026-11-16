-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.argRel_dim_le_R3
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T09:36:56.570247+00:00
-- url     : https://prove2.me/submissions/d2212991-5ab3-48ea-8f66-3c2259c0124d

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG

private theorem a0_g0_w0 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 37500)) 65535) ≤ dimF (n.val + 37500) := by decide
private theorem a1_g0_w0 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 37500)) 16) ≤ dimF (n.val + 37500) := by decide
private theorem a0_g0_w1 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 37550)) 65535) ≤ dimF (n.val + 37550) := by decide
private theorem a1_g0_w1 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 37550)) 16) ≤ dimF (n.val + 37550) := by decide
private theorem a0_g0_w2 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 37600)) 65535) ≤ dimF (n.val + 37600) := by decide
private theorem a1_g0_w2 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 37600)) 16) ≤ dimF (n.val + 37600) := by decide
private theorem a0_g0_w3 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 37650)) 65535) ≤ dimF (n.val + 37650) := by decide
private theorem a1_g0_w3 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 37650)) 16) ≤ dimF (n.val + 37650) := by decide
private theorem a0_g0_w4 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 37700)) 65535) ≤ dimF (n.val + 37700) := by decide
private theorem a1_g0_w4 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 37700)) 16) ≤ dimF (n.val + 37700) := by decide
private theorem a0_g0_w5 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 37750)) 65535) ≤ dimF (n.val + 37750) := by decide
private theorem a1_g0_w5 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 37750)) 16) ≤ dimF (n.val + 37750) := by decide
private theorem a0_g0_w6 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 37800)) 65535) ≤ dimF (n.val + 37800) := by decide
private theorem a1_g0_w6 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 37800)) 16) ≤ dimF (n.val + 37800) := by decide
private theorem a0_g0_w7 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 37850)) 65535) ≤ dimF (n.val + 37850) := by decide
private theorem a1_g0_w7 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 37850)) 16) ≤ dimF (n.val + 37850) := by decide
private theorem a0_g0_w8 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 37900)) 65535) ≤ dimF (n.val + 37900) := by decide
private theorem a1_g0_w8 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 37900)) 16) ≤ dimF (n.val + 37900) := by decide
private theorem a0_g0_w9 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 37950)) 65535) ≤ dimF (n.val + 37950) := by decide
private theorem a1_g0_w9 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 37950)) 16) ≤ dimF (n.val + 37950) := by decide
private theorem a0_g0_w10 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 38000)) 65535) ≤ dimF (n.val + 38000) := by decide
private theorem a1_g0_w10 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 38000)) 16) ≤ dimF (n.val + 38000) := by decide
private theorem a0_g0_w11 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 38050)) 65535) ≤ dimF (n.val + 38050) := by decide
private theorem a1_g0_w11 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 38050)) 16) ≤ dimF (n.val + 38050) := by decide
private theorem a0_g0_w12 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 38100)) 65535) ≤ dimF (n.val + 38100) := by decide
private theorem a1_g0_w12 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 38100)) 16) ≤ dimF (n.val + 38100) := by decide
private theorem a0_g0_w13 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 38150)) 65535) ≤ dimF (n.val + 38150) := by decide
private theorem a1_g0_w13 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 38150)) 16) ≤ dimF (n.val + 38150) := by decide
private theorem a0_g0_w14 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 38200)) 65535) ≤ dimF (n.val + 38200) := by decide
private theorem a1_g0_w14 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 38200)) 16) ≤ dimF (n.val + 38200) := by decide
private theorem a0_g0_w15 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 38250)) 65535) ≤ dimF (n.val + 38250) := by decide
private theorem a1_g0_w15 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 38250)) 16) ≤ dimF (n.val + 38250) := by decide
private theorem a0_g0_w16 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 38300)) 65535) ≤ dimF (n.val + 38300) := by decide
private theorem a1_g0_w16 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 38300)) 16) ≤ dimF (n.val + 38300) := by decide
private theorem a0_g0_w17 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 38350)) 65535) ≤ dimF (n.val + 38350) := by decide
private theorem a1_g0_w17 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 38350)) 16) ≤ dimF (n.val + 38350) := by decide
private theorem a0_g0_w18 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 38400)) 65535) ≤ dimF (n.val + 38400) := by decide
private theorem a1_g0_w18 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 38400)) 16) ≤ dimF (n.val + 38400) := by decide
private theorem a0_g0_w19 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 38450)) 65535) ≤ dimF (n.val + 38450) := by decide
private theorem a1_g0_w19 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 38450)) 16) ≤ dimF (n.val + 38450) := by decide
private theorem a0_g0_w20 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 38500)) 65535) ≤ dimF (n.val + 38500) := by decide
private theorem a1_g0_w20 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 38500)) 16) ≤ dimF (n.val + 38500) := by decide
private theorem a0_g0_w21 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 38550)) 65535) ≤ dimF (n.val + 38550) := by decide
private theorem a1_g0_w21 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 38550)) 16) ≤ dimF (n.val + 38550) := by decide
private theorem a0_g0_w22 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 38600)) 65535) ≤ dimF (n.val + 38600) := by decide
private theorem a1_g0_w22 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 38600)) 16) ≤ dimF (n.val + 38600) := by decide
private theorem a0_g0_w23 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 38650)) 65535) ≤ dimF (n.val + 38650) := by decide
private theorem a1_g0_w23 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 38650)) 16) ≤ dimF (n.val + 38650) := by decide
private theorem a0_g0_w24 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 38700)) 65535) ≤ dimF (n.val + 38700) := by decide
private theorem a1_g0_w24 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 38700)) 16) ≤ dimF (n.val + 38700) := by decide
private theorem a0_g0_w25 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 38750)) 65535) ≤ dimF (n.val + 38750) := by decide
private theorem a1_g0_w25 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 38750)) 16) ≤ dimF (n.val + 38750) := by decide
private theorem a0_g0_w26 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 38800)) 65535) ≤ dimF (n.val + 38800) := by decide
private theorem a1_g0_w26 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 38800)) 16) ≤ dimF (n.val + 38800) := by decide
private theorem a0_g0_w27 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 38850)) 65535) ≤ dimF (n.val + 38850) := by decide
private theorem a1_g0_w27 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 38850)) 16) ≤ dimF (n.val + 38850) := by decide
private theorem a0_g0_w28 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 38900)) 65535) ≤ dimF (n.val + 38900) := by decide
private theorem a1_g0_w28 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 38900)) 16) ≤ dimF (n.val + 38900) := by decide
private theorem a0_g0_w29 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 38950)) 65535) ≤ dimF (n.val + 38950) := by decide
private theorem a1_g0_w29 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 38950)) 16) ≤ dimF (n.val + 38950) := by decide
private theorem a0_g0_w30 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 39000)) 65535) ≤ dimF (n.val + 39000) := by decide
private theorem a1_g0_w30 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 39000)) 16) ≤ dimF (n.val + 39000) := by decide
private theorem a0_g0_w31 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 39050)) 65535) ≤ dimF (n.val + 39050) := by decide
private theorem a1_g0_w31 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 39050)) 16) ≤ dimF (n.val + 39050) := by decide
private theorem a0_g0_w32 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 39100)) 65535) ≤ dimF (n.val + 39100) := by decide
private theorem a1_g0_w32 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 39100)) 16) ≤ dimF (n.val + 39100) := by decide
private theorem a0_g0_w33 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 39150)) 65535) ≤ dimF (n.val + 39150) := by decide
private theorem a1_g0_w33 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 39150)) 16) ≤ dimF (n.val + 39150) := by decide
private theorem a0_g0_w34 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 39200)) 65535) ≤ dimF (n.val + 39200) := by decide
private theorem a1_g0_w34 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 39200)) 16) ≤ dimF (n.val + 39200) := by decide
private theorem a0_g0_w35 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 39250)) 65535) ≤ dimF (n.val + 39250) := by decide
private theorem a1_g0_w35 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 39250)) 16) ≤ dimF (n.val + 39250) := by decide
private theorem a0_g0_w36 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 39300)) 65535) ≤ dimF (n.val + 39300) := by decide
private theorem a1_g0_w36 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 39300)) 16) ≤ dimF (n.val + 39300) := by decide
private theorem a0_g0_w37 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 39350)) 65535) ≤ dimF (n.val + 39350) := by decide
private theorem a1_g0_w37 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 39350)) 16) ≤ dimF (n.val + 39350) := by decide
private theorem a0_g0_w38 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 39400)) 65535) ≤ dimF (n.val + 39400) := by decide
private theorem a1_g0_w38 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 39400)) 16) ≤ dimF (n.val + 39400) := by decide
private theorem a0_g0_w39 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 39450)) 65535) ≤ dimF (n.val + 39450) := by decide
private theorem a1_g0_w39 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 39450)) 16) ≤ dimF (n.val + 39450) := by decide
private theorem a0_g0_w40 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 39500)) 65535) ≤ dimF (n.val + 39500) := by decide
private theorem a1_g0_w40 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 39500)) 16) ≤ dimF (n.val + 39500) := by decide
private theorem a0_g0_w41 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 39550)) 65535) ≤ dimF (n.val + 39550) := by decide
private theorem a1_g0_w41 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 39550)) 16) ≤ dimF (n.val + 39550) := by decide
private theorem a0_g0_w42 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 39600)) 65535) ≤ dimF (n.val + 39600) := by decide
private theorem a1_g0_w42 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 39600)) 16) ≤ dimF (n.val + 39600) := by decide
private theorem a0_g0_w43 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 39650)) 65535) ≤ dimF (n.val + 39650) := by decide
private theorem a1_g0_w43 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 39650)) 16) ≤ dimF (n.val + 39650) := by decide
private theorem a0_g0_w44 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 39700)) 65535) ≤ dimF (n.val + 39700) := by decide
private theorem a1_g0_w44 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 39700)) 16) ≤ dimF (n.val + 39700) := by decide
private theorem a0_g0_w45 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 39750)) 65535) ≤ dimF (n.val + 39750) := by decide
private theorem a1_g0_w45 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 39750)) 16) ≤ dimF (n.val + 39750) := by decide
private theorem a0_g0_w46 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 39800)) 65535) ≤ dimF (n.val + 39800) := by decide
private theorem a1_g0_w46 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 39800)) 16) ≤ dimF (n.val + 39800) := by decide
private theorem a0_g0_w47 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 39850)) 65535) ≤ dimF (n.val + 39850) := by decide
private theorem a1_g0_w47 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 39850)) 16) ≤ dimF (n.val + 39850) := by decide
private theorem a0_g0_w48 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 39900)) 65535) ≤ dimF (n.val + 39900) := by decide
private theorem a1_g0_w48 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 39900)) 16) ≤ dimF (n.val + 39900) := by decide
private theorem a0_g0_w49 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 39950)) 65535) ≤ dimF (n.val + 39950) := by decide
private theorem a1_g0_w49 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 39950)) 16) ≤ dimF (n.val + 39950) := by decide

private theorem pair_g0 (n : ℕ) (hlo : 37500 ≤ n) (hhi : n < 40000) :
    dimF (Nat.land (argF n) 65535) ≤ dimF n ∧
    dimF (Nat.shiftRight (argF n) 16) ≤ dimF n := by
  by_cases h0 : n < 37550
  · have hr : n - 37500 < 50 := by omega
    have heq : n = (n - 37500) + 37500 := by omega
    rw [heq]
    exact ⟨a0_g0_w0 ⟨n - 37500, hr⟩, a1_g0_w0 ⟨n - 37500, hr⟩⟩
  · by_cases h1 : n < 37600
    · have hr : n - 37550 < 50 := by omega
      have heq : n = (n - 37550) + 37550 := by omega
      rw [heq]
      exact ⟨a0_g0_w1 ⟨n - 37550, hr⟩, a1_g0_w1 ⟨n - 37550, hr⟩⟩
    · by_cases h2 : n < 37650
      · have hr : n - 37600 < 50 := by omega
        have heq : n = (n - 37600) + 37600 := by omega
        rw [heq]
        exact ⟨a0_g0_w2 ⟨n - 37600, hr⟩, a1_g0_w2 ⟨n - 37600, hr⟩⟩
      · by_cases h3 : n < 37700
        · have hr : n - 37650 < 50 := by omega
          have heq : n = (n - 37650) + 37650 := by omega
          rw [heq]
          exact ⟨a0_g0_w3 ⟨n - 37650, hr⟩, a1_g0_w3 ⟨n - 37650, hr⟩⟩
        · by_cases h4 : n < 37750
          · have hr : n - 37700 < 50 := by omega
            have heq : n = (n - 37700) + 37700 := by omega
            rw [heq]
            exact ⟨a0_g0_w4 ⟨n - 37700, hr⟩, a1_g0_w4 ⟨n - 37700, hr⟩⟩
          · by_cases h5 : n < 37800
            · have hr : n - 37750 < 50 := by omega
              have heq : n = (n - 37750) + 37750 := by omega
              rw [heq]
              exact ⟨a0_g0_w5 ⟨n - 37750, hr⟩, a1_g0_w5 ⟨n - 37750, hr⟩⟩
            · by_cases h6 : n < 37850
              · have hr : n - 37800 < 50 := by omega
                have heq : n = (n - 37800) + 37800 := by omega
                rw [heq]
                exact ⟨a0_g0_w6 ⟨n - 37800, hr⟩, a1_g0_w6 ⟨n - 37800, hr⟩⟩
              · by_cases h7 : n < 37900
                · have hr : n - 37850 < 50 := by omega
                  have heq : n = (n - 37850) + 37850 := by omega
                  rw [heq]
                  exact ⟨a0_g0_w7 ⟨n - 37850, hr⟩, a1_g0_w7 ⟨n - 37850, hr⟩⟩
                · by_cases h8 : n < 37950
                  · have hr : n - 37900 < 50 := by omega
                    have heq : n = (n - 37900) + 37900 := by omega
                    rw [heq]
                    exact ⟨a0_g0_w8 ⟨n - 37900, hr⟩, a1_g0_w8 ⟨n - 37900, hr⟩⟩
                  · by_cases h9 : n < 38000
                    · have hr : n - 37950 < 50 := by omega
                      have heq : n = (n - 37950) + 37950 := by omega
                      rw [heq]
                      exact ⟨a0_g0_w9 ⟨n - 37950, hr⟩, a1_g0_w9 ⟨n - 37950, hr⟩⟩
                    · by_cases h10 : n < 38050
                      · have hr : n - 38000 < 50 := by omega
                        have heq : n = (n - 38000) + 38000 := by omega
                        rw [heq]
                        exact ⟨a0_g0_w10 ⟨n - 38000, hr⟩, a1_g0_w10 ⟨n - 38000, hr⟩⟩
                      · by_cases h11 : n < 38100
                        · have hr : n - 38050 < 50 := by omega
                          have heq : n = (n - 38050) + 38050 := by omega
                          rw [heq]
                          exact ⟨a0_g0_w11 ⟨n - 38050, hr⟩, a1_g0_w11 ⟨n - 38050, hr⟩⟩
                        · by_cases h12 : n < 38150
                          · have hr : n - 38100 < 50 := by omega
                            have heq : n = (n - 38100) + 38100 := by omega
                            rw [heq]
                            exact ⟨a0_g0_w12 ⟨n - 38100, hr⟩, a1_g0_w12 ⟨n - 38100, hr⟩⟩
                          · by_cases h13 : n < 38200
                            · have hr : n - 38150 < 50 := by omega
                              have heq : n = (n - 38150) + 38150 := by omega
                              rw [heq]
                              exact ⟨a0_g0_w13 ⟨n - 38150, hr⟩, a1_g0_w13 ⟨n - 38150, hr⟩⟩
                            · by_cases h14 : n < 38250
                              · have hr : n - 38200 < 50 := by omega
                                have heq : n = (n - 38200) + 38200 := by omega
                                rw [heq]
                                exact ⟨a0_g0_w14 ⟨n - 38200, hr⟩, a1_g0_w14 ⟨n - 38200, hr⟩⟩
                              · by_cases h15 : n < 38300
                                · have hr : n - 38250 < 50 := by omega
                                  have heq : n = (n - 38250) + 38250 := by omega
                                  rw [heq]
                                  exact ⟨a0_g0_w15 ⟨n - 38250, hr⟩, a1_g0_w15 ⟨n - 38250, hr⟩⟩
                                · by_cases h16 : n < 38350
                                  · have hr : n - 38300 < 50 := by omega
                                    have heq : n = (n - 38300) + 38300 := by omega
                                    rw [heq]
                                    exact ⟨a0_g0_w16 ⟨n - 38300, hr⟩, a1_g0_w16 ⟨n - 38300, hr⟩⟩
                                  · by_cases h17 : n < 38400
                                    · have hr : n - 38350 < 50 := by omega
                                      have heq : n = (n - 38350) + 38350 := by omega
                                      rw [heq]
                                      exact ⟨a0_g0_w17 ⟨n - 38350, hr⟩, a1_g0_w17 ⟨n - 38350, hr⟩⟩
                                    · by_cases h18 : n < 38450
                                      · have hr : n - 38400 < 50 := by omega
                                        have heq : n = (n - 38400) + 38400 := by omega
                                        rw [heq]
                                        exact ⟨a0_g0_w18 ⟨n - 38400, hr⟩, a1_g0_w18 ⟨n - 38400, hr⟩⟩
                                      · by_cases h19 : n < 38500
                                        · have hr : n - 38450 < 50 := by omega
                                          have heq : n = (n - 38450) + 38450 := by omega
                                          rw [heq]
                                          exact ⟨a0_g0_w19 ⟨n - 38450, hr⟩, a1_g0_w19 ⟨n - 38450, hr⟩⟩
                                        · by_cases h20 : n < 38550
                                          · have hr : n - 38500 < 50 := by omega
                                            have heq : n = (n - 38500) + 38500 := by omega
                                            rw [heq]
                                            exact ⟨a0_g0_w20 ⟨n - 38500, hr⟩, a1_g0_w20 ⟨n - 38500, hr⟩⟩
                                          · by_cases h21 : n < 38600
                                            · have hr : n - 38550 < 50 := by omega
                                              have heq : n = (n - 38550) + 38550 := by omega
                                              rw [heq]
                                              exact ⟨a0_g0_w21 ⟨n - 38550, hr⟩, a1_g0_w21 ⟨n - 38550, hr⟩⟩
                                            · by_cases h22 : n < 38650
                                              · have hr : n - 38600 < 50 := by omega
                                                have heq : n = (n - 38600) + 38600 := by omega
                                                rw [heq]
                                                exact ⟨a0_g0_w22 ⟨n - 38600, hr⟩, a1_g0_w22 ⟨n - 38600, hr⟩⟩
                                              · by_cases h23 : n < 38700
                                                · have hr : n - 38650 < 50 := by omega
                                                  have heq : n = (n - 38650) + 38650 := by omega
                                                  rw [heq]
                                                  exact ⟨a0_g0_w23 ⟨n - 38650, hr⟩, a1_g0_w23 ⟨n - 38650, hr⟩⟩
                                                · by_cases h24 : n < 38750
                                                  · have hr : n - 38700 < 50 := by omega
                                                    have heq : n = (n - 38700) + 38700 := by omega
                                                    rw [heq]
                                                    exact ⟨a0_g0_w24 ⟨n - 38700, hr⟩, a1_g0_w24 ⟨n - 38700, hr⟩⟩
                                                  · by_cases h25 : n < 38800
                                                    · have hr : n - 38750 < 50 := by omega
                                                      have heq : n = (n - 38750) + 38750 := by omega
                                                      rw [heq]
                                                      exact ⟨a0_g0_w25 ⟨n - 38750, hr⟩, a1_g0_w25 ⟨n - 38750, hr⟩⟩
                                                    · by_cases h26 : n < 38850
                                                      · have hr : n - 38800 < 50 := by omega
                                                        have heq : n = (n - 38800) + 38800 := by omega
                                                        rw [heq]
                                                        exact ⟨a0_g0_w26 ⟨n - 38800, hr⟩, a1_g0_w26 ⟨n - 38800, hr⟩⟩
                                                      · by_cases h27 : n < 38900
                                                        · have hr : n - 38850 < 50 := by omega
                                                          have heq : n = (n - 38850) + 38850 := by omega
                                                          rw [heq]
                                                          exact ⟨a0_g0_w27 ⟨n - 38850, hr⟩, a1_g0_w27 ⟨n - 38850, hr⟩⟩
                                                        · by_cases h28 : n < 38950
                                                          · have hr : n - 38900 < 50 := by omega
                                                            have heq : n = (n - 38900) + 38900 := by omega
                                                            rw [heq]
                                                            exact ⟨a0_g0_w28 ⟨n - 38900, hr⟩, a1_g0_w28 ⟨n - 38900, hr⟩⟩
                                                          · by_cases h29 : n < 39000
                                                            · have hr : n - 38950 < 50 := by omega
                                                              have heq : n = (n - 38950) + 38950 := by omega
                                                              rw [heq]
                                                              exact ⟨a0_g0_w29 ⟨n - 38950, hr⟩, a1_g0_w29 ⟨n - 38950, hr⟩⟩
                                                            · by_cases h30 : n < 39050
                                                              · have hr : n - 39000 < 50 := by omega
                                                                have heq : n = (n - 39000) + 39000 := by omega
                                                                rw [heq]
                                                                exact ⟨a0_g0_w30 ⟨n - 39000, hr⟩, a1_g0_w30 ⟨n - 39000, hr⟩⟩
                                                              · by_cases h31 : n < 39100
                                                                · have hr : n - 39050 < 50 := by omega
                                                                  have heq : n = (n - 39050) + 39050 := by omega
                                                                  rw [heq]
                                                                  exact ⟨a0_g0_w31 ⟨n - 39050, hr⟩, a1_g0_w31 ⟨n - 39050, hr⟩⟩
                                                                · by_cases h32 : n < 39150
                                                                  · have hr : n - 39100 < 50 := by omega
                                                                    have heq : n = (n - 39100) + 39100 := by omega
                                                                    rw [heq]
                                                                    exact ⟨a0_g0_w32 ⟨n - 39100, hr⟩, a1_g0_w32 ⟨n - 39100, hr⟩⟩
                                                                  · by_cases h33 : n < 39200
                                                                    · have hr : n - 39150 < 50 := by omega
                                                                      have heq : n = (n - 39150) + 39150 := by omega
                                                                      rw [heq]
                                                                      exact ⟨a0_g0_w33 ⟨n - 39150, hr⟩, a1_g0_w33 ⟨n - 39150, hr⟩⟩
                                                                    · by_cases h34 : n < 39250
                                                                      · have hr : n - 39200 < 50 := by omega
                                                                        have heq : n = (n - 39200) + 39200 := by omega
                                                                        rw [heq]
                                                                        exact ⟨a0_g0_w34 ⟨n - 39200, hr⟩, a1_g0_w34 ⟨n - 39200, hr⟩⟩
                                                                      · by_cases h35 : n < 39300
                                                                        · have hr : n - 39250 < 50 := by omega
                                                                          have heq : n = (n - 39250) + 39250 := by omega
                                                                          rw [heq]
                                                                          exact ⟨a0_g0_w35 ⟨n - 39250, hr⟩, a1_g0_w35 ⟨n - 39250, hr⟩⟩
                                                                        · by_cases h36 : n < 39350
                                                                          · have hr : n - 39300 < 50 := by omega
                                                                            have heq : n = (n - 39300) + 39300 := by omega
                                                                            rw [heq]
                                                                            exact ⟨a0_g0_w36 ⟨n - 39300, hr⟩, a1_g0_w36 ⟨n - 39300, hr⟩⟩
                                                                          · by_cases h37 : n < 39400
                                                                            · have hr : n - 39350 < 50 := by omega
                                                                              have heq : n = (n - 39350) + 39350 := by omega
                                                                              rw [heq]
                                                                              exact ⟨a0_g0_w37 ⟨n - 39350, hr⟩, a1_g0_w37 ⟨n - 39350, hr⟩⟩
                                                                            · by_cases h38 : n < 39450
                                                                              · have hr : n - 39400 < 50 := by omega
                                                                                have heq : n = (n - 39400) + 39400 := by omega
                                                                                rw [heq]
                                                                                exact ⟨a0_g0_w38 ⟨n - 39400, hr⟩, a1_g0_w38 ⟨n - 39400, hr⟩⟩
                                                                              · by_cases h39 : n < 39500
                                                                                · have hr : n - 39450 < 50 := by omega
                                                                                  have heq : n = (n - 39450) + 39450 := by omega
                                                                                  rw [heq]
                                                                                  exact ⟨a0_g0_w39 ⟨n - 39450, hr⟩, a1_g0_w39 ⟨n - 39450, hr⟩⟩
                                                                                · by_cases h40 : n < 39550
                                                                                  · have hr : n - 39500 < 50 := by omega
                                                                                    have heq : n = (n - 39500) + 39500 := by omega
                                                                                    rw [heq]
                                                                                    exact ⟨a0_g0_w40 ⟨n - 39500, hr⟩, a1_g0_w40 ⟨n - 39500, hr⟩⟩
                                                                                  · by_cases h41 : n < 39600
                                                                                    · have hr : n - 39550 < 50 := by omega
                                                                                      have heq : n = (n - 39550) + 39550 := by omega
                                                                                      rw [heq]
                                                                                      exact ⟨a0_g0_w41 ⟨n - 39550, hr⟩, a1_g0_w41 ⟨n - 39550, hr⟩⟩
                                                                                    · by_cases h42 : n < 39650
                                                                                      · have hr : n - 39600 < 50 := by omega
                                                                                        have heq : n = (n - 39600) + 39600 := by omega
                                                                                        rw [heq]
                                                                                        exact ⟨a0_g0_w42 ⟨n - 39600, hr⟩, a1_g0_w42 ⟨n - 39600, hr⟩⟩
                                                                                      · by_cases h43 : n < 39700
                                                                                        · have hr : n - 39650 < 50 := by omega
                                                                                          have heq : n = (n - 39650) + 39650 := by omega
                                                                                          rw [heq]
                                                                                          exact ⟨a0_g0_w43 ⟨n - 39650, hr⟩, a1_g0_w43 ⟨n - 39650, hr⟩⟩
                                                                                        · by_cases h44 : n < 39750
                                                                                          · have hr : n - 39700 < 50 := by omega
                                                                                            have heq : n = (n - 39700) + 39700 := by omega
                                                                                            rw [heq]
                                                                                            exact ⟨a0_g0_w44 ⟨n - 39700, hr⟩, a1_g0_w44 ⟨n - 39700, hr⟩⟩
                                                                                          · by_cases h45 : n < 39800
                                                                                            · have hr : n - 39750 < 50 := by omega
                                                                                              have heq : n = (n - 39750) + 39750 := by omega
                                                                                              rw [heq]
                                                                                              exact ⟨a0_g0_w45 ⟨n - 39750, hr⟩, a1_g0_w45 ⟨n - 39750, hr⟩⟩
                                                                                            · by_cases h46 : n < 39850
                                                                                              · have hr : n - 39800 < 50 := by omega
                                                                                                have heq : n = (n - 39800) + 39800 := by omega
                                                                                                rw [heq]
                                                                                                exact ⟨a0_g0_w46 ⟨n - 39800, hr⟩, a1_g0_w46 ⟨n - 39800, hr⟩⟩
                                                                                              · by_cases h47 : n < 39900
                                                                                                · have hr : n - 39850 < 50 := by omega
                                                                                                  have heq : n = (n - 39850) + 39850 := by omega
                                                                                                  rw [heq]
                                                                                                  exact ⟨a0_g0_w47 ⟨n - 39850, hr⟩, a1_g0_w47 ⟨n - 39850, hr⟩⟩
                                                                                                · by_cases h48 : n < 39950
                                                                                                  · have hr : n - 39900 < 50 := by omega
                                                                                                    have heq : n = (n - 39900) + 39900 := by omega
                                                                                                    rw [heq]
                                                                                                    exact ⟨a0_g0_w48 ⟨n - 39900, hr⟩, a1_g0_w48 ⟨n - 39900, hr⟩⟩
                                                                                                  · have hr : n - 39950 < 50 := by omega
                                                                                                    have heq : n = (n - 39950) + 39950 := by omega
                                                                                                    rw [heq]
                                                                                                    exact ⟨a0_g0_w49 ⟨n - 39950, hr⟩, a1_g0_w49 ⟨n - 39950, hr⟩⟩

private theorem a0_g1_w0 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 40000)) 65535) ≤ dimF (n.val + 40000) := by decide
private theorem a1_g1_w0 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 40000)) 16) ≤ dimF (n.val + 40000) := by decide
private theorem a0_g1_w1 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 40050)) 65535) ≤ dimF (n.val + 40050) := by decide
private theorem a1_g1_w1 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 40050)) 16) ≤ dimF (n.val + 40050) := by decide
private theorem a0_g1_w2 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 40100)) 65535) ≤ dimF (n.val + 40100) := by decide
private theorem a1_g1_w2 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 40100)) 16) ≤ dimF (n.val + 40100) := by decide
private theorem a0_g1_w3 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 40150)) 65535) ≤ dimF (n.val + 40150) := by decide
private theorem a1_g1_w3 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 40150)) 16) ≤ dimF (n.val + 40150) := by decide
private theorem a0_g1_w4 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 40200)) 65535) ≤ dimF (n.val + 40200) := by decide
private theorem a1_g1_w4 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 40200)) 16) ≤ dimF (n.val + 40200) := by decide
private theorem a0_g1_w5 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 40250)) 65535) ≤ dimF (n.val + 40250) := by decide
private theorem a1_g1_w5 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 40250)) 16) ≤ dimF (n.val + 40250) := by decide
private theorem a0_g1_w6 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 40300)) 65535) ≤ dimF (n.val + 40300) := by decide
private theorem a1_g1_w6 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 40300)) 16) ≤ dimF (n.val + 40300) := by decide
private theorem a0_g1_w7 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 40350)) 65535) ≤ dimF (n.val + 40350) := by decide
private theorem a1_g1_w7 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 40350)) 16) ≤ dimF (n.val + 40350) := by decide
private theorem a0_g1_w8 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 40400)) 65535) ≤ dimF (n.val + 40400) := by decide
private theorem a1_g1_w8 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 40400)) 16) ≤ dimF (n.val + 40400) := by decide
private theorem a0_g1_w9 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 40450)) 65535) ≤ dimF (n.val + 40450) := by decide
private theorem a1_g1_w9 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 40450)) 16) ≤ dimF (n.val + 40450) := by decide
private theorem a0_g1_w10 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 40500)) 65535) ≤ dimF (n.val + 40500) := by decide
private theorem a1_g1_w10 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 40500)) 16) ≤ dimF (n.val + 40500) := by decide
private theorem a0_g1_w11 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 40550)) 65535) ≤ dimF (n.val + 40550) := by decide
private theorem a1_g1_w11 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 40550)) 16) ≤ dimF (n.val + 40550) := by decide
private theorem a0_g1_w12 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 40600)) 65535) ≤ dimF (n.val + 40600) := by decide
private theorem a1_g1_w12 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 40600)) 16) ≤ dimF (n.val + 40600) := by decide
private theorem a0_g1_w13 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 40650)) 65535) ≤ dimF (n.val + 40650) := by decide
private theorem a1_g1_w13 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 40650)) 16) ≤ dimF (n.val + 40650) := by decide
private theorem a0_g1_w14 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 40700)) 65535) ≤ dimF (n.val + 40700) := by decide
private theorem a1_g1_w14 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 40700)) 16) ≤ dimF (n.val + 40700) := by decide
private theorem a0_g1_w15 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 40750)) 65535) ≤ dimF (n.val + 40750) := by decide
private theorem a1_g1_w15 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 40750)) 16) ≤ dimF (n.val + 40750) := by decide
private theorem a0_g1_w16 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 40800)) 65535) ≤ dimF (n.val + 40800) := by decide
private theorem a1_g1_w16 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 40800)) 16) ≤ dimF (n.val + 40800) := by decide
private theorem a0_g1_w17 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 40850)) 65535) ≤ dimF (n.val + 40850) := by decide
private theorem a1_g1_w17 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 40850)) 16) ≤ dimF (n.val + 40850) := by decide
private theorem a0_g1_w18 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 40900)) 65535) ≤ dimF (n.val + 40900) := by decide
private theorem a1_g1_w18 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 40900)) 16) ≤ dimF (n.val + 40900) := by decide
private theorem a0_g1_w19 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 40950)) 65535) ≤ dimF (n.val + 40950) := by decide
private theorem a1_g1_w19 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 40950)) 16) ≤ dimF (n.val + 40950) := by decide
private theorem a0_g1_w20 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 41000)) 65535) ≤ dimF (n.val + 41000) := by decide
private theorem a1_g1_w20 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 41000)) 16) ≤ dimF (n.val + 41000) := by decide
private theorem a0_g1_w21 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 41050)) 65535) ≤ dimF (n.val + 41050) := by decide
private theorem a1_g1_w21 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 41050)) 16) ≤ dimF (n.val + 41050) := by decide
private theorem a0_g1_w22 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 41100)) 65535) ≤ dimF (n.val + 41100) := by decide
private theorem a1_g1_w22 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 41100)) 16) ≤ dimF (n.val + 41100) := by decide
private theorem a0_g1_w23 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 41150)) 65535) ≤ dimF (n.val + 41150) := by decide
private theorem a1_g1_w23 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 41150)) 16) ≤ dimF (n.val + 41150) := by decide
private theorem a0_g1_w24 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 41200)) 65535) ≤ dimF (n.val + 41200) := by decide
private theorem a1_g1_w24 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 41200)) 16) ≤ dimF (n.val + 41200) := by decide
private theorem a0_g1_w25 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 41250)) 65535) ≤ dimF (n.val + 41250) := by decide
private theorem a1_g1_w25 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 41250)) 16) ≤ dimF (n.val + 41250) := by decide
private theorem a0_g1_w26 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 41300)) 65535) ≤ dimF (n.val + 41300) := by decide
private theorem a1_g1_w26 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 41300)) 16) ≤ dimF (n.val + 41300) := by decide
private theorem a0_g1_w27 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 41350)) 65535) ≤ dimF (n.val + 41350) := by decide
private theorem a1_g1_w27 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 41350)) 16) ≤ dimF (n.val + 41350) := by decide
private theorem a0_g1_w28 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 41400)) 65535) ≤ dimF (n.val + 41400) := by decide
private theorem a1_g1_w28 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 41400)) 16) ≤ dimF (n.val + 41400) := by decide
private theorem a0_g1_w29 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 41450)) 65535) ≤ dimF (n.val + 41450) := by decide
private theorem a1_g1_w29 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 41450)) 16) ≤ dimF (n.val + 41450) := by decide
private theorem a0_g1_w30 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 41500)) 65535) ≤ dimF (n.val + 41500) := by decide
private theorem a1_g1_w30 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 41500)) 16) ≤ dimF (n.val + 41500) := by decide
private theorem a0_g1_w31 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 41550)) 65535) ≤ dimF (n.val + 41550) := by decide
private theorem a1_g1_w31 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 41550)) 16) ≤ dimF (n.val + 41550) := by decide
private theorem a0_g1_w32 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 41600)) 65535) ≤ dimF (n.val + 41600) := by decide
private theorem a1_g1_w32 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 41600)) 16) ≤ dimF (n.val + 41600) := by decide
private theorem a0_g1_w33 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 41650)) 65535) ≤ dimF (n.val + 41650) := by decide
private theorem a1_g1_w33 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 41650)) 16) ≤ dimF (n.val + 41650) := by decide
private theorem a0_g1_w34 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 41700)) 65535) ≤ dimF (n.val + 41700) := by decide
private theorem a1_g1_w34 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 41700)) 16) ≤ dimF (n.val + 41700) := by decide
private theorem a0_g1_w35 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 41750)) 65535) ≤ dimF (n.val + 41750) := by decide
private theorem a1_g1_w35 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 41750)) 16) ≤ dimF (n.val + 41750) := by decide
private theorem a0_g1_w36 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 41800)) 65535) ≤ dimF (n.val + 41800) := by decide
private theorem a1_g1_w36 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 41800)) 16) ≤ dimF (n.val + 41800) := by decide
private theorem a0_g1_w37 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 41850)) 65535) ≤ dimF (n.val + 41850) := by decide
private theorem a1_g1_w37 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 41850)) 16) ≤ dimF (n.val + 41850) := by decide
private theorem a0_g1_w38 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 41900)) 65535) ≤ dimF (n.val + 41900) := by decide
private theorem a1_g1_w38 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 41900)) 16) ≤ dimF (n.val + 41900) := by decide
private theorem a0_g1_w39 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 41950)) 65535) ≤ dimF (n.val + 41950) := by decide
private theorem a1_g1_w39 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 41950)) 16) ≤ dimF (n.val + 41950) := by decide
private theorem a0_g1_w40 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 42000)) 65535) ≤ dimF (n.val + 42000) := by decide
private theorem a1_g1_w40 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 42000)) 16) ≤ dimF (n.val + 42000) := by decide
private theorem a0_g1_w41 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 42050)) 65535) ≤ dimF (n.val + 42050) := by decide
private theorem a1_g1_w41 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 42050)) 16) ≤ dimF (n.val + 42050) := by decide
private theorem a0_g1_w42 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 42100)) 65535) ≤ dimF (n.val + 42100) := by decide
private theorem a1_g1_w42 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 42100)) 16) ≤ dimF (n.val + 42100) := by decide
private theorem a0_g1_w43 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 42150)) 65535) ≤ dimF (n.val + 42150) := by decide
private theorem a1_g1_w43 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 42150)) 16) ≤ dimF (n.val + 42150) := by decide
private theorem a0_g1_w44 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 42200)) 65535) ≤ dimF (n.val + 42200) := by decide
private theorem a1_g1_w44 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 42200)) 16) ≤ dimF (n.val + 42200) := by decide
private theorem a0_g1_w45 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 42250)) 65535) ≤ dimF (n.val + 42250) := by decide
private theorem a1_g1_w45 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 42250)) 16) ≤ dimF (n.val + 42250) := by decide
private theorem a0_g1_w46 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 42300)) 65535) ≤ dimF (n.val + 42300) := by decide
private theorem a1_g1_w46 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 42300)) 16) ≤ dimF (n.val + 42300) := by decide
private theorem a0_g1_w47 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 42350)) 65535) ≤ dimF (n.val + 42350) := by decide
private theorem a1_g1_w47 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 42350)) 16) ≤ dimF (n.val + 42350) := by decide
private theorem a0_g1_w48 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 42400)) 65535) ≤ dimF (n.val + 42400) := by decide
private theorem a1_g1_w48 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 42400)) 16) ≤ dimF (n.val + 42400) := by decide
private theorem a0_g1_w49 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 42450)) 65535) ≤ dimF (n.val + 42450) := by decide
private theorem a1_g1_w49 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 42450)) 16) ≤ dimF (n.val + 42450) := by decide

private theorem pair_g1 (n : ℕ) (hlo : 40000 ≤ n) (hhi : n < 42500) :
    dimF (Nat.land (argF n) 65535) ≤ dimF n ∧
    dimF (Nat.shiftRight (argF n) 16) ≤ dimF n := by
  by_cases h0 : n < 40050
  · have hr : n - 40000 < 50 := by omega
    have heq : n = (n - 40000) + 40000 := by omega
    rw [heq]
    exact ⟨a0_g1_w0 ⟨n - 40000, hr⟩, a1_g1_w0 ⟨n - 40000, hr⟩⟩
  · by_cases h1 : n < 40100
    · have hr : n - 40050 < 50 := by omega
      have heq : n = (n - 40050) + 40050 := by omega
      rw [heq]
      exact ⟨a0_g1_w1 ⟨n - 40050, hr⟩, a1_g1_w1 ⟨n - 40050, hr⟩⟩
    · by_cases h2 : n < 40150
      · have hr : n - 40100 < 50 := by omega
        have heq : n = (n - 40100) + 40100 := by omega
        rw [heq]
        exact ⟨a0_g1_w2 ⟨n - 40100, hr⟩, a1_g1_w2 ⟨n - 40100, hr⟩⟩
      · by_cases h3 : n < 40200
        · have hr : n - 40150 < 50 := by omega
          have heq : n = (n - 40150) + 40150 := by omega
          rw [heq]
          exact ⟨a0_g1_w3 ⟨n - 40150, hr⟩, a1_g1_w3 ⟨n - 40150, hr⟩⟩
        · by_cases h4 : n < 40250
          · have hr : n - 40200 < 50 := by omega
            have heq : n = (n - 40200) + 40200 := by omega
            rw [heq]
            exact ⟨a0_g1_w4 ⟨n - 40200, hr⟩, a1_g1_w4 ⟨n - 40200, hr⟩⟩
          · by_cases h5 : n < 40300
            · have hr : n - 40250 < 50 := by omega
              have heq : n = (n - 40250) + 40250 := by omega
              rw [heq]
              exact ⟨a0_g1_w5 ⟨n - 40250, hr⟩, a1_g1_w5 ⟨n - 40250, hr⟩⟩
            · by_cases h6 : n < 40350
              · have hr : n - 40300 < 50 := by omega
                have heq : n = (n - 40300) + 40300 := by omega
                rw [heq]
                exact ⟨a0_g1_w6 ⟨n - 40300, hr⟩, a1_g1_w6 ⟨n - 40300, hr⟩⟩
              · by_cases h7 : n < 40400
                · have hr : n - 40350 < 50 := by omega
                  have heq : n = (n - 40350) + 40350 := by omega
                  rw [heq]
                  exact ⟨a0_g1_w7 ⟨n - 40350, hr⟩, a1_g1_w7 ⟨n - 40350, hr⟩⟩
                · by_cases h8 : n < 40450
                  · have hr : n - 40400 < 50 := by omega
                    have heq : n = (n - 40400) + 40400 := by omega
                    rw [heq]
                    exact ⟨a0_g1_w8 ⟨n - 40400, hr⟩, a1_g1_w8 ⟨n - 40400, hr⟩⟩
                  · by_cases h9 : n < 40500
                    · have hr : n - 40450 < 50 := by omega
                      have heq : n = (n - 40450) + 40450 := by omega
                      rw [heq]
                      exact ⟨a0_g1_w9 ⟨n - 40450, hr⟩, a1_g1_w9 ⟨n - 40450, hr⟩⟩
                    · by_cases h10 : n < 40550
                      · have hr : n - 40500 < 50 := by omega
                        have heq : n = (n - 40500) + 40500 := by omega
                        rw [heq]
                        exact ⟨a0_g1_w10 ⟨n - 40500, hr⟩, a1_g1_w10 ⟨n - 40500, hr⟩⟩
                      · by_cases h11 : n < 40600
                        · have hr : n - 40550 < 50 := by omega
                          have heq : n = (n - 40550) + 40550 := by omega
                          rw [heq]
                          exact ⟨a0_g1_w11 ⟨n - 40550, hr⟩, a1_g1_w11 ⟨n - 40550, hr⟩⟩
                        · by_cases h12 : n < 40650
                          · have hr : n - 40600 < 50 := by omega
                            have heq : n = (n - 40600) + 40600 := by omega
                            rw [heq]
                            exact ⟨a0_g1_w12 ⟨n - 40600, hr⟩, a1_g1_w12 ⟨n - 40600, hr⟩⟩
                          · by_cases h13 : n < 40700
                            · have hr : n - 40650 < 50 := by omega
                              have heq : n = (n - 40650) + 40650 := by omega
                              rw [heq]
                              exact ⟨a0_g1_w13 ⟨n - 40650, hr⟩, a1_g1_w13 ⟨n - 40650, hr⟩⟩
                            · by_cases h14 : n < 40750
                              · have hr : n - 40700 < 50 := by omega
                                have heq : n = (n - 40700) + 40700 := by omega
                                rw [heq]
                                exact ⟨a0_g1_w14 ⟨n - 40700, hr⟩, a1_g1_w14 ⟨n - 40700, hr⟩⟩
                              · by_cases h15 : n < 40800
                                · have hr : n - 40750 < 50 := by omega
                                  have heq : n = (n - 40750) + 40750 := by omega
                                  rw [heq]
                                  exact ⟨a0_g1_w15 ⟨n - 40750, hr⟩, a1_g1_w15 ⟨n - 40750, hr⟩⟩
                                · by_cases h16 : n < 40850
                                  · have hr : n - 40800 < 50 := by omega
                                    have heq : n = (n - 40800) + 40800 := by omega
                                    rw [heq]
                                    exact ⟨a0_g1_w16 ⟨n - 40800, hr⟩, a1_g1_w16 ⟨n - 40800, hr⟩⟩
                                  · by_cases h17 : n < 40900
                                    · have hr : n - 40850 < 50 := by omega
                                      have heq : n = (n - 40850) + 40850 := by omega
                                      rw [heq]
                                      exact ⟨a0_g1_w17 ⟨n - 40850, hr⟩, a1_g1_w17 ⟨n - 40850, hr⟩⟩
                                    · by_cases h18 : n < 40950
                                      · have hr : n - 40900 < 50 := by omega
                                        have heq : n = (n - 40900) + 40900 := by omega
                                        rw [heq]
                                        exact ⟨a0_g1_w18 ⟨n - 40900, hr⟩, a1_g1_w18 ⟨n - 40900, hr⟩⟩
                                      · by_cases h19 : n < 41000
                                        · have hr : n - 40950 < 50 := by omega
                                          have heq : n = (n - 40950) + 40950 := by omega
                                          rw [heq]
                                          exact ⟨a0_g1_w19 ⟨n - 40950, hr⟩, a1_g1_w19 ⟨n - 40950, hr⟩⟩
                                        · by_cases h20 : n < 41050
                                          · have hr : n - 41000 < 50 := by omega
                                            have heq : n = (n - 41000) + 41000 := by omega
                                            rw [heq]
                                            exact ⟨a0_g1_w20 ⟨n - 41000, hr⟩, a1_g1_w20 ⟨n - 41000, hr⟩⟩
                                          · by_cases h21 : n < 41100
                                            · have hr : n - 41050 < 50 := by omega
                                              have heq : n = (n - 41050) + 41050 := by omega
                                              rw [heq]
                                              exact ⟨a0_g1_w21 ⟨n - 41050, hr⟩, a1_g1_w21 ⟨n - 41050, hr⟩⟩
                                            · by_cases h22 : n < 41150
                                              · have hr : n - 41100 < 50 := by omega
                                                have heq : n = (n - 41100) + 41100 := by omega
                                                rw [heq]
                                                exact ⟨a0_g1_w22 ⟨n - 41100, hr⟩, a1_g1_w22 ⟨n - 41100, hr⟩⟩
                                              · by_cases h23 : n < 41200
                                                · have hr : n - 41150 < 50 := by omega
                                                  have heq : n = (n - 41150) + 41150 := by omega
                                                  rw [heq]
                                                  exact ⟨a0_g1_w23 ⟨n - 41150, hr⟩, a1_g1_w23 ⟨n - 41150, hr⟩⟩
                                                · by_cases h24 : n < 41250
                                                  · have hr : n - 41200 < 50 := by omega
                                                    have heq : n = (n - 41200) + 41200 := by omega
                                                    rw [heq]
                                                    exact ⟨a0_g1_w24 ⟨n - 41200, hr⟩, a1_g1_w24 ⟨n - 41200, hr⟩⟩
                                                  · by_cases h25 : n < 41300
                                                    · have hr : n - 41250 < 50 := by omega
                                                      have heq : n = (n - 41250) + 41250 := by omega
                                                      rw [heq]
                                                      exact ⟨a0_g1_w25 ⟨n - 41250, hr⟩, a1_g1_w25 ⟨n - 41250, hr⟩⟩
                                                    · by_cases h26 : n < 41350
                                                      · have hr : n - 41300 < 50 := by omega
                                                        have heq : n = (n - 41300) + 41300 := by omega
                                                        rw [heq]
                                                        exact ⟨a0_g1_w26 ⟨n - 41300, hr⟩, a1_g1_w26 ⟨n - 41300, hr⟩⟩
                                                      · by_cases h27 : n < 41400
                                                        · have hr : n - 41350 < 50 := by omega
                                                          have heq : n = (n - 41350) + 41350 := by omega
                                                          rw [heq]
                                                          exact ⟨a0_g1_w27 ⟨n - 41350, hr⟩, a1_g1_w27 ⟨n - 41350, hr⟩⟩
                                                        · by_cases h28 : n < 41450
                                                          · have hr : n - 41400 < 50 := by omega
                                                            have heq : n = (n - 41400) + 41400 := by omega
                                                            rw [heq]
                                                            exact ⟨a0_g1_w28 ⟨n - 41400, hr⟩, a1_g1_w28 ⟨n - 41400, hr⟩⟩
                                                          · by_cases h29 : n < 41500
                                                            · have hr : n - 41450 < 50 := by omega
                                                              have heq : n = (n - 41450) + 41450 := by omega
                                                              rw [heq]
                                                              exact ⟨a0_g1_w29 ⟨n - 41450, hr⟩, a1_g1_w29 ⟨n - 41450, hr⟩⟩
                                                            · by_cases h30 : n < 41550
                                                              · have hr : n - 41500 < 50 := by omega
                                                                have heq : n = (n - 41500) + 41500 := by omega
                                                                rw [heq]
                                                                exact ⟨a0_g1_w30 ⟨n - 41500, hr⟩, a1_g1_w30 ⟨n - 41500, hr⟩⟩
                                                              · by_cases h31 : n < 41600
                                                                · have hr : n - 41550 < 50 := by omega
                                                                  have heq : n = (n - 41550) + 41550 := by omega
                                                                  rw [heq]
                                                                  exact ⟨a0_g1_w31 ⟨n - 41550, hr⟩, a1_g1_w31 ⟨n - 41550, hr⟩⟩
                                                                · by_cases h32 : n < 41650
                                                                  · have hr : n - 41600 < 50 := by omega
                                                                    have heq : n = (n - 41600) + 41600 := by omega
                                                                    rw [heq]
                                                                    exact ⟨a0_g1_w32 ⟨n - 41600, hr⟩, a1_g1_w32 ⟨n - 41600, hr⟩⟩
                                                                  · by_cases h33 : n < 41700
                                                                    · have hr : n - 41650 < 50 := by omega
                                                                      have heq : n = (n - 41650) + 41650 := by omega
                                                                      rw [heq]
                                                                      exact ⟨a0_g1_w33 ⟨n - 41650, hr⟩, a1_g1_w33 ⟨n - 41650, hr⟩⟩
                                                                    · by_cases h34 : n < 41750
                                                                      · have hr : n - 41700 < 50 := by omega
                                                                        have heq : n = (n - 41700) + 41700 := by omega
                                                                        rw [heq]
                                                                        exact ⟨a0_g1_w34 ⟨n - 41700, hr⟩, a1_g1_w34 ⟨n - 41700, hr⟩⟩
                                                                      · by_cases h35 : n < 41800
                                                                        · have hr : n - 41750 < 50 := by omega
                                                                          have heq : n = (n - 41750) + 41750 := by omega
                                                                          rw [heq]
                                                                          exact ⟨a0_g1_w35 ⟨n - 41750, hr⟩, a1_g1_w35 ⟨n - 41750, hr⟩⟩
                                                                        · by_cases h36 : n < 41850
                                                                          · have hr : n - 41800 < 50 := by omega
                                                                            have heq : n = (n - 41800) + 41800 := by omega
                                                                            rw [heq]
                                                                            exact ⟨a0_g1_w36 ⟨n - 41800, hr⟩, a1_g1_w36 ⟨n - 41800, hr⟩⟩
                                                                          · by_cases h37 : n < 41900
                                                                            · have hr : n - 41850 < 50 := by omega
                                                                              have heq : n = (n - 41850) + 41850 := by omega
                                                                              rw [heq]
                                                                              exact ⟨a0_g1_w37 ⟨n - 41850, hr⟩, a1_g1_w37 ⟨n - 41850, hr⟩⟩
                                                                            · by_cases h38 : n < 41950
                                                                              · have hr : n - 41900 < 50 := by omega
                                                                                have heq : n = (n - 41900) + 41900 := by omega
                                                                                rw [heq]
                                                                                exact ⟨a0_g1_w38 ⟨n - 41900, hr⟩, a1_g1_w38 ⟨n - 41900, hr⟩⟩
                                                                              · by_cases h39 : n < 42000
                                                                                · have hr : n - 41950 < 50 := by omega
                                                                                  have heq : n = (n - 41950) + 41950 := by omega
                                                                                  rw [heq]
                                                                                  exact ⟨a0_g1_w39 ⟨n - 41950, hr⟩, a1_g1_w39 ⟨n - 41950, hr⟩⟩
                                                                                · by_cases h40 : n < 42050
                                                                                  · have hr : n - 42000 < 50 := by omega
                                                                                    have heq : n = (n - 42000) + 42000 := by omega
                                                                                    rw [heq]
                                                                                    exact ⟨a0_g1_w40 ⟨n - 42000, hr⟩, a1_g1_w40 ⟨n - 42000, hr⟩⟩
                                                                                  · by_cases h41 : n < 42100
                                                                                    · have hr : n - 42050 < 50 := by omega
                                                                                      have heq : n = (n - 42050) + 42050 := by omega
                                                                                      rw [heq]
                                                                                      exact ⟨a0_g1_w41 ⟨n - 42050, hr⟩, a1_g1_w41 ⟨n - 42050, hr⟩⟩
                                                                                    · by_cases h42 : n < 42150
                                                                                      · have hr : n - 42100 < 50 := by omega
                                                                                        have heq : n = (n - 42100) + 42100 := by omega
                                                                                        rw [heq]
                                                                                        exact ⟨a0_g1_w42 ⟨n - 42100, hr⟩, a1_g1_w42 ⟨n - 42100, hr⟩⟩
                                                                                      · by_cases h43 : n < 42200
                                                                                        · have hr : n - 42150 < 50 := by omega
                                                                                          have heq : n = (n - 42150) + 42150 := by omega
                                                                                          rw [heq]
                                                                                          exact ⟨a0_g1_w43 ⟨n - 42150, hr⟩, a1_g1_w43 ⟨n - 42150, hr⟩⟩
                                                                                        · by_cases h44 : n < 42250
                                                                                          · have hr : n - 42200 < 50 := by omega
                                                                                            have heq : n = (n - 42200) + 42200 := by omega
                                                                                            rw [heq]
                                                                                            exact ⟨a0_g1_w44 ⟨n - 42200, hr⟩, a1_g1_w44 ⟨n - 42200, hr⟩⟩
                                                                                          · by_cases h45 : n < 42300
                                                                                            · have hr : n - 42250 < 50 := by omega
                                                                                              have heq : n = (n - 42250) + 42250 := by omega
                                                                                              rw [heq]
                                                                                              exact ⟨a0_g1_w45 ⟨n - 42250, hr⟩, a1_g1_w45 ⟨n - 42250, hr⟩⟩
                                                                                            · by_cases h46 : n < 42350
                                                                                              · have hr : n - 42300 < 50 := by omega
                                                                                                have heq : n = (n - 42300) + 42300 := by omega
                                                                                                rw [heq]
                                                                                                exact ⟨a0_g1_w46 ⟨n - 42300, hr⟩, a1_g1_w46 ⟨n - 42300, hr⟩⟩
                                                                                              · by_cases h47 : n < 42400
                                                                                                · have hr : n - 42350 < 50 := by omega
                                                                                                  have heq : n = (n - 42350) + 42350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact ⟨a0_g1_w47 ⟨n - 42350, hr⟩, a1_g1_w47 ⟨n - 42350, hr⟩⟩
                                                                                                · by_cases h48 : n < 42450
                                                                                                  · have hr : n - 42400 < 50 := by omega
                                                                                                    have heq : n = (n - 42400) + 42400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact ⟨a0_g1_w48 ⟨n - 42400, hr⟩, a1_g1_w48 ⟨n - 42400, hr⟩⟩
                                                                                                  · have hr : n - 42450 < 50 := by omega
                                                                                                    have heq : n = (n - 42450) + 42450 := by omega
                                                                                                    rw [heq]
                                                                                                    exact ⟨a0_g1_w49 ⟨n - 42450, hr⟩, a1_g1_w49 ⟨n - 42450, hr⟩⟩

private theorem a0_g2_w0 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 42500)) 65535) ≤ dimF (n.val + 42500) := by decide
private theorem a1_g2_w0 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 42500)) 16) ≤ dimF (n.val + 42500) := by decide
private theorem a0_g2_w1 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 42550)) 65535) ≤ dimF (n.val + 42550) := by decide
private theorem a1_g2_w1 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 42550)) 16) ≤ dimF (n.val + 42550) := by decide
private theorem a0_g2_w2 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 42600)) 65535) ≤ dimF (n.val + 42600) := by decide
private theorem a1_g2_w2 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 42600)) 16) ≤ dimF (n.val + 42600) := by decide
private theorem a0_g2_w3 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 42650)) 65535) ≤ dimF (n.val + 42650) := by decide
private theorem a1_g2_w3 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 42650)) 16) ≤ dimF (n.val + 42650) := by decide
private theorem a0_g2_w4 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 42700)) 65535) ≤ dimF (n.val + 42700) := by decide
private theorem a1_g2_w4 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 42700)) 16) ≤ dimF (n.val + 42700) := by decide
private theorem a0_g2_w5 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 42750)) 65535) ≤ dimF (n.val + 42750) := by decide
private theorem a1_g2_w5 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 42750)) 16) ≤ dimF (n.val + 42750) := by decide
private theorem a0_g2_w6 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 42800)) 65535) ≤ dimF (n.val + 42800) := by decide
private theorem a1_g2_w6 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 42800)) 16) ≤ dimF (n.val + 42800) := by decide
private theorem a0_g2_w7 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 42850)) 65535) ≤ dimF (n.val + 42850) := by decide
private theorem a1_g2_w7 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 42850)) 16) ≤ dimF (n.val + 42850) := by decide
private theorem a0_g2_w8 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 42900)) 65535) ≤ dimF (n.val + 42900) := by decide
private theorem a1_g2_w8 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 42900)) 16) ≤ dimF (n.val + 42900) := by decide
private theorem a0_g2_w9 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 42950)) 65535) ≤ dimF (n.val + 42950) := by decide
private theorem a1_g2_w9 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 42950)) 16) ≤ dimF (n.val + 42950) := by decide
private theorem a0_g2_w10 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 43000)) 65535) ≤ dimF (n.val + 43000) := by decide
private theorem a1_g2_w10 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 43000)) 16) ≤ dimF (n.val + 43000) := by decide
private theorem a0_g2_w11 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 43050)) 65535) ≤ dimF (n.val + 43050) := by decide
private theorem a1_g2_w11 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 43050)) 16) ≤ dimF (n.val + 43050) := by decide
private theorem a0_g2_w12 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 43100)) 65535) ≤ dimF (n.val + 43100) := by decide
private theorem a1_g2_w12 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 43100)) 16) ≤ dimF (n.val + 43100) := by decide
private theorem a0_g2_w13 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 43150)) 65535) ≤ dimF (n.val + 43150) := by decide
private theorem a1_g2_w13 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 43150)) 16) ≤ dimF (n.val + 43150) := by decide
private theorem a0_g2_w14 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 43200)) 65535) ≤ dimF (n.val + 43200) := by decide
private theorem a1_g2_w14 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 43200)) 16) ≤ dimF (n.val + 43200) := by decide
private theorem a0_g2_w15 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 43250)) 65535) ≤ dimF (n.val + 43250) := by decide
private theorem a1_g2_w15 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 43250)) 16) ≤ dimF (n.val + 43250) := by decide
private theorem a0_g2_w16 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 43300)) 65535) ≤ dimF (n.val + 43300) := by decide
private theorem a1_g2_w16 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 43300)) 16) ≤ dimF (n.val + 43300) := by decide
private theorem a0_g2_w17 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 43350)) 65535) ≤ dimF (n.val + 43350) := by decide
private theorem a1_g2_w17 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 43350)) 16) ≤ dimF (n.val + 43350) := by decide
private theorem a0_g2_w18 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 43400)) 65535) ≤ dimF (n.val + 43400) := by decide
private theorem a1_g2_w18 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 43400)) 16) ≤ dimF (n.val + 43400) := by decide
private theorem a0_g2_w19 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 43450)) 65535) ≤ dimF (n.val + 43450) := by decide
private theorem a1_g2_w19 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 43450)) 16) ≤ dimF (n.val + 43450) := by decide
private theorem a0_g2_w20 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 43500)) 65535) ≤ dimF (n.val + 43500) := by decide
private theorem a1_g2_w20 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 43500)) 16) ≤ dimF (n.val + 43500) := by decide
private theorem a0_g2_w21 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 43550)) 65535) ≤ dimF (n.val + 43550) := by decide
private theorem a1_g2_w21 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 43550)) 16) ≤ dimF (n.val + 43550) := by decide
private theorem a0_g2_w22 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 43600)) 65535) ≤ dimF (n.val + 43600) := by decide
private theorem a1_g2_w22 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 43600)) 16) ≤ dimF (n.val + 43600) := by decide
private theorem a0_g2_w23 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 43650)) 65535) ≤ dimF (n.val + 43650) := by decide
private theorem a1_g2_w23 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 43650)) 16) ≤ dimF (n.val + 43650) := by decide
private theorem a0_g2_w24 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 43700)) 65535) ≤ dimF (n.val + 43700) := by decide
private theorem a1_g2_w24 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 43700)) 16) ≤ dimF (n.val + 43700) := by decide
private theorem a0_g2_w25 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 43750)) 65535) ≤ dimF (n.val + 43750) := by decide
private theorem a1_g2_w25 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 43750)) 16) ≤ dimF (n.val + 43750) := by decide
private theorem a0_g2_w26 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 43800)) 65535) ≤ dimF (n.val + 43800) := by decide
private theorem a1_g2_w26 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 43800)) 16) ≤ dimF (n.val + 43800) := by decide
private theorem a0_g2_w27 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 43850)) 65535) ≤ dimF (n.val + 43850) := by decide
private theorem a1_g2_w27 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 43850)) 16) ≤ dimF (n.val + 43850) := by decide
private theorem a0_g2_w28 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 43900)) 65535) ≤ dimF (n.val + 43900) := by decide
private theorem a1_g2_w28 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 43900)) 16) ≤ dimF (n.val + 43900) := by decide
private theorem a0_g2_w29 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 43950)) 65535) ≤ dimF (n.val + 43950) := by decide
private theorem a1_g2_w29 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 43950)) 16) ≤ dimF (n.val + 43950) := by decide
private theorem a0_g2_w30 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 44000)) 65535) ≤ dimF (n.val + 44000) := by decide
private theorem a1_g2_w30 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 44000)) 16) ≤ dimF (n.val + 44000) := by decide
private theorem a0_g2_w31 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 44050)) 65535) ≤ dimF (n.val + 44050) := by decide
private theorem a1_g2_w31 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 44050)) 16) ≤ dimF (n.val + 44050) := by decide
private theorem a0_g2_w32 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 44100)) 65535) ≤ dimF (n.val + 44100) := by decide
private theorem a1_g2_w32 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 44100)) 16) ≤ dimF (n.val + 44100) := by decide
private theorem a0_g2_w33 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 44150)) 65535) ≤ dimF (n.val + 44150) := by decide
private theorem a1_g2_w33 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 44150)) 16) ≤ dimF (n.val + 44150) := by decide
private theorem a0_g2_w34 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 44200)) 65535) ≤ dimF (n.val + 44200) := by decide
private theorem a1_g2_w34 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 44200)) 16) ≤ dimF (n.val + 44200) := by decide
private theorem a0_g2_w35 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 44250)) 65535) ≤ dimF (n.val + 44250) := by decide
private theorem a1_g2_w35 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 44250)) 16) ≤ dimF (n.val + 44250) := by decide
private theorem a0_g2_w36 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 44300)) 65535) ≤ dimF (n.val + 44300) := by decide
private theorem a1_g2_w36 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 44300)) 16) ≤ dimF (n.val + 44300) := by decide
private theorem a0_g2_w37 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 44350)) 65535) ≤ dimF (n.val + 44350) := by decide
private theorem a1_g2_w37 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 44350)) 16) ≤ dimF (n.val + 44350) := by decide
private theorem a0_g2_w38 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 44400)) 65535) ≤ dimF (n.val + 44400) := by decide
private theorem a1_g2_w38 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 44400)) 16) ≤ dimF (n.val + 44400) := by decide
private theorem a0_g2_w39 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 44450)) 65535) ≤ dimF (n.val + 44450) := by decide
private theorem a1_g2_w39 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 44450)) 16) ≤ dimF (n.val + 44450) := by decide
private theorem a0_g2_w40 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 44500)) 65535) ≤ dimF (n.val + 44500) := by decide
private theorem a1_g2_w40 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 44500)) 16) ≤ dimF (n.val + 44500) := by decide
private theorem a0_g2_w41 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 44550)) 65535) ≤ dimF (n.val + 44550) := by decide
private theorem a1_g2_w41 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 44550)) 16) ≤ dimF (n.val + 44550) := by decide
private theorem a0_g2_w42 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 44600)) 65535) ≤ dimF (n.val + 44600) := by decide
private theorem a1_g2_w42 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 44600)) 16) ≤ dimF (n.val + 44600) := by decide
private theorem a0_g2_w43 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 44650)) 65535) ≤ dimF (n.val + 44650) := by decide
private theorem a1_g2_w43 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 44650)) 16) ≤ dimF (n.val + 44650) := by decide
private theorem a0_g2_w44 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 44700)) 65535) ≤ dimF (n.val + 44700) := by decide
private theorem a1_g2_w44 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 44700)) 16) ≤ dimF (n.val + 44700) := by decide
private theorem a0_g2_w45 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 44750)) 65535) ≤ dimF (n.val + 44750) := by decide
private theorem a1_g2_w45 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 44750)) 16) ≤ dimF (n.val + 44750) := by decide
private theorem a0_g2_w46 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 44800)) 65535) ≤ dimF (n.val + 44800) := by decide
private theorem a1_g2_w46 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 44800)) 16) ≤ dimF (n.val + 44800) := by decide
private theorem a0_g2_w47 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 44850)) 65535) ≤ dimF (n.val + 44850) := by decide
private theorem a1_g2_w47 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 44850)) 16) ≤ dimF (n.val + 44850) := by decide
private theorem a0_g2_w48 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 44900)) 65535) ≤ dimF (n.val + 44900) := by decide
private theorem a1_g2_w48 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 44900)) 16) ≤ dimF (n.val + 44900) := by decide
private theorem a0_g2_w49 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 44950)) 65535) ≤ dimF (n.val + 44950) := by decide
private theorem a1_g2_w49 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 44950)) 16) ≤ dimF (n.val + 44950) := by decide

private theorem pair_g2 (n : ℕ) (hlo : 42500 ≤ n) (hhi : n < 45000) :
    dimF (Nat.land (argF n) 65535) ≤ dimF n ∧
    dimF (Nat.shiftRight (argF n) 16) ≤ dimF n := by
  by_cases h0 : n < 42550
  · have hr : n - 42500 < 50 := by omega
    have heq : n = (n - 42500) + 42500 := by omega
    rw [heq]
    exact ⟨a0_g2_w0 ⟨n - 42500, hr⟩, a1_g2_w0 ⟨n - 42500, hr⟩⟩
  · by_cases h1 : n < 42600
    · have hr : n - 42550 < 50 := by omega
      have heq : n = (n - 42550) + 42550 := by omega
      rw [heq]
      exact ⟨a0_g2_w1 ⟨n - 42550, hr⟩, a1_g2_w1 ⟨n - 42550, hr⟩⟩
    · by_cases h2 : n < 42650
      · have hr : n - 42600 < 50 := by omega
        have heq : n = (n - 42600) + 42600 := by omega
        rw [heq]
        exact ⟨a0_g2_w2 ⟨n - 42600, hr⟩, a1_g2_w2 ⟨n - 42600, hr⟩⟩
      · by_cases h3 : n < 42700
        · have hr : n - 42650 < 50 := by omega
          have heq : n = (n - 42650) + 42650 := by omega
          rw [heq]
          exact ⟨a0_g2_w3 ⟨n - 42650, hr⟩, a1_g2_w3 ⟨n - 42650, hr⟩⟩
        · by_cases h4 : n < 42750
          · have hr : n - 42700 < 50 := by omega
            have heq : n = (n - 42700) + 42700 := by omega
            rw [heq]
            exact ⟨a0_g2_w4 ⟨n - 42700, hr⟩, a1_g2_w4 ⟨n - 42700, hr⟩⟩
          · by_cases h5 : n < 42800
            · have hr : n - 42750 < 50 := by omega
              have heq : n = (n - 42750) + 42750 := by omega
              rw [heq]
              exact ⟨a0_g2_w5 ⟨n - 42750, hr⟩, a1_g2_w5 ⟨n - 42750, hr⟩⟩
            · by_cases h6 : n < 42850
              · have hr : n - 42800 < 50 := by omega
                have heq : n = (n - 42800) + 42800 := by omega
                rw [heq]
                exact ⟨a0_g2_w6 ⟨n - 42800, hr⟩, a1_g2_w6 ⟨n - 42800, hr⟩⟩
              · by_cases h7 : n < 42900
                · have hr : n - 42850 < 50 := by omega
                  have heq : n = (n - 42850) + 42850 := by omega
                  rw [heq]
                  exact ⟨a0_g2_w7 ⟨n - 42850, hr⟩, a1_g2_w7 ⟨n - 42850, hr⟩⟩
                · by_cases h8 : n < 42950
                  · have hr : n - 42900 < 50 := by omega
                    have heq : n = (n - 42900) + 42900 := by omega
                    rw [heq]
                    exact ⟨a0_g2_w8 ⟨n - 42900, hr⟩, a1_g2_w8 ⟨n - 42900, hr⟩⟩
                  · by_cases h9 : n < 43000
                    · have hr : n - 42950 < 50 := by omega
                      have heq : n = (n - 42950) + 42950 := by omega
                      rw [heq]
                      exact ⟨a0_g2_w9 ⟨n - 42950, hr⟩, a1_g2_w9 ⟨n - 42950, hr⟩⟩
                    · by_cases h10 : n < 43050
                      · have hr : n - 43000 < 50 := by omega
                        have heq : n = (n - 43000) + 43000 := by omega
                        rw [heq]
                        exact ⟨a0_g2_w10 ⟨n - 43000, hr⟩, a1_g2_w10 ⟨n - 43000, hr⟩⟩
                      · by_cases h11 : n < 43100
                        · have hr : n - 43050 < 50 := by omega
                          have heq : n = (n - 43050) + 43050 := by omega
                          rw [heq]
                          exact ⟨a0_g2_w11 ⟨n - 43050, hr⟩, a1_g2_w11 ⟨n - 43050, hr⟩⟩
                        · by_cases h12 : n < 43150
                          · have hr : n - 43100 < 50 := by omega
                            have heq : n = (n - 43100) + 43100 := by omega
                            rw [heq]
                            exact ⟨a0_g2_w12 ⟨n - 43100, hr⟩, a1_g2_w12 ⟨n - 43100, hr⟩⟩
                          · by_cases h13 : n < 43200
                            · have hr : n - 43150 < 50 := by omega
                              have heq : n = (n - 43150) + 43150 := by omega
                              rw [heq]
                              exact ⟨a0_g2_w13 ⟨n - 43150, hr⟩, a1_g2_w13 ⟨n - 43150, hr⟩⟩
                            · by_cases h14 : n < 43250
                              · have hr : n - 43200 < 50 := by omega
                                have heq : n = (n - 43200) + 43200 := by omega
                                rw [heq]
                                exact ⟨a0_g2_w14 ⟨n - 43200, hr⟩, a1_g2_w14 ⟨n - 43200, hr⟩⟩
                              · by_cases h15 : n < 43300
                                · have hr : n - 43250 < 50 := by omega
                                  have heq : n = (n - 43250) + 43250 := by omega
                                  rw [heq]
                                  exact ⟨a0_g2_w15 ⟨n - 43250, hr⟩, a1_g2_w15 ⟨n - 43250, hr⟩⟩
                                · by_cases h16 : n < 43350
                                  · have hr : n - 43300 < 50 := by omega
                                    have heq : n = (n - 43300) + 43300 := by omega
                                    rw [heq]
                                    exact ⟨a0_g2_w16 ⟨n - 43300, hr⟩, a1_g2_w16 ⟨n - 43300, hr⟩⟩
                                  · by_cases h17 : n < 43400
                                    · have hr : n - 43350 < 50 := by omega
                                      have heq : n = (n - 43350) + 43350 := by omega
                                      rw [heq]
                                      exact ⟨a0_g2_w17 ⟨n - 43350, hr⟩, a1_g2_w17 ⟨n - 43350, hr⟩⟩
                                    · by_cases h18 : n < 43450
                                      · have hr : n - 43400 < 50 := by omega
                                        have heq : n = (n - 43400) + 43400 := by omega
                                        rw [heq]
                                        exact ⟨a0_g2_w18 ⟨n - 43400, hr⟩, a1_g2_w18 ⟨n - 43400, hr⟩⟩
                                      · by_cases h19 : n < 43500
                                        · have hr : n - 43450 < 50 := by omega
                                          have heq : n = (n - 43450) + 43450 := by omega
                                          rw [heq]
                                          exact ⟨a0_g2_w19 ⟨n - 43450, hr⟩, a1_g2_w19 ⟨n - 43450, hr⟩⟩
                                        · by_cases h20 : n < 43550
                                          · have hr : n - 43500 < 50 := by omega
                                            have heq : n = (n - 43500) + 43500 := by omega
                                            rw [heq]
                                            exact ⟨a0_g2_w20 ⟨n - 43500, hr⟩, a1_g2_w20 ⟨n - 43500, hr⟩⟩
                                          · by_cases h21 : n < 43600
                                            · have hr : n - 43550 < 50 := by omega
                                              have heq : n = (n - 43550) + 43550 := by omega
                                              rw [heq]
                                              exact ⟨a0_g2_w21 ⟨n - 43550, hr⟩, a1_g2_w21 ⟨n - 43550, hr⟩⟩
                                            · by_cases h22 : n < 43650
                                              · have hr : n - 43600 < 50 := by omega
                                                have heq : n = (n - 43600) + 43600 := by omega
                                                rw [heq]
                                                exact ⟨a0_g2_w22 ⟨n - 43600, hr⟩, a1_g2_w22 ⟨n - 43600, hr⟩⟩
                                              · by_cases h23 : n < 43700
                                                · have hr : n - 43650 < 50 := by omega
                                                  have heq : n = (n - 43650) + 43650 := by omega
                                                  rw [heq]
                                                  exact ⟨a0_g2_w23 ⟨n - 43650, hr⟩, a1_g2_w23 ⟨n - 43650, hr⟩⟩
                                                · by_cases h24 : n < 43750
                                                  · have hr : n - 43700 < 50 := by omega
                                                    have heq : n = (n - 43700) + 43700 := by omega
                                                    rw [heq]
                                                    exact ⟨a0_g2_w24 ⟨n - 43700, hr⟩, a1_g2_w24 ⟨n - 43700, hr⟩⟩
                                                  · by_cases h25 : n < 43800
                                                    · have hr : n - 43750 < 50 := by omega
                                                      have heq : n = (n - 43750) + 43750 := by omega
                                                      rw [heq]
                                                      exact ⟨a0_g2_w25 ⟨n - 43750, hr⟩, a1_g2_w25 ⟨n - 43750, hr⟩⟩
                                                    · by_cases h26 : n < 43850
                                                      · have hr : n - 43800 < 50 := by omega
                                                        have heq : n = (n - 43800) + 43800 := by omega
                                                        rw [heq]
                                                        exact ⟨a0_g2_w26 ⟨n - 43800, hr⟩, a1_g2_w26 ⟨n - 43800, hr⟩⟩
                                                      · by_cases h27 : n < 43900
                                                        · have hr : n - 43850 < 50 := by omega
                                                          have heq : n = (n - 43850) + 43850 := by omega
                                                          rw [heq]
                                                          exact ⟨a0_g2_w27 ⟨n - 43850, hr⟩, a1_g2_w27 ⟨n - 43850, hr⟩⟩
                                                        · by_cases h28 : n < 43950
                                                          · have hr : n - 43900 < 50 := by omega
                                                            have heq : n = (n - 43900) + 43900 := by omega
                                                            rw [heq]
                                                            exact ⟨a0_g2_w28 ⟨n - 43900, hr⟩, a1_g2_w28 ⟨n - 43900, hr⟩⟩
                                                          · by_cases h29 : n < 44000
                                                            · have hr : n - 43950 < 50 := by omega
                                                              have heq : n = (n - 43950) + 43950 := by omega
                                                              rw [heq]
                                                              exact ⟨a0_g2_w29 ⟨n - 43950, hr⟩, a1_g2_w29 ⟨n - 43950, hr⟩⟩
                                                            · by_cases h30 : n < 44050
                                                              · have hr : n - 44000 < 50 := by omega
                                                                have heq : n = (n - 44000) + 44000 := by omega
                                                                rw [heq]
                                                                exact ⟨a0_g2_w30 ⟨n - 44000, hr⟩, a1_g2_w30 ⟨n - 44000, hr⟩⟩
                                                              · by_cases h31 : n < 44100
                                                                · have hr : n - 44050 < 50 := by omega
                                                                  have heq : n = (n - 44050) + 44050 := by omega
                                                                  rw [heq]
                                                                  exact ⟨a0_g2_w31 ⟨n - 44050, hr⟩, a1_g2_w31 ⟨n - 44050, hr⟩⟩
                                                                · by_cases h32 : n < 44150
                                                                  · have hr : n - 44100 < 50 := by omega
                                                                    have heq : n = (n - 44100) + 44100 := by omega
                                                                    rw [heq]
                                                                    exact ⟨a0_g2_w32 ⟨n - 44100, hr⟩, a1_g2_w32 ⟨n - 44100, hr⟩⟩
                                                                  · by_cases h33 : n < 44200
                                                                    · have hr : n - 44150 < 50 := by omega
                                                                      have heq : n = (n - 44150) + 44150 := by omega
                                                                      rw [heq]
                                                                      exact ⟨a0_g2_w33 ⟨n - 44150, hr⟩, a1_g2_w33 ⟨n - 44150, hr⟩⟩
                                                                    · by_cases h34 : n < 44250
                                                                      · have hr : n - 44200 < 50 := by omega
                                                                        have heq : n = (n - 44200) + 44200 := by omega
                                                                        rw [heq]
                                                                        exact ⟨a0_g2_w34 ⟨n - 44200, hr⟩, a1_g2_w34 ⟨n - 44200, hr⟩⟩
                                                                      · by_cases h35 : n < 44300
                                                                        · have hr : n - 44250 < 50 := by omega
                                                                          have heq : n = (n - 44250) + 44250 := by omega
                                                                          rw [heq]
                                                                          exact ⟨a0_g2_w35 ⟨n - 44250, hr⟩, a1_g2_w35 ⟨n - 44250, hr⟩⟩
                                                                        · by_cases h36 : n < 44350
                                                                          · have hr : n - 44300 < 50 := by omega
                                                                            have heq : n = (n - 44300) + 44300 := by omega
                                                                            rw [heq]
                                                                            exact ⟨a0_g2_w36 ⟨n - 44300, hr⟩, a1_g2_w36 ⟨n - 44300, hr⟩⟩
                                                                          · by_cases h37 : n < 44400
                                                                            · have hr : n - 44350 < 50 := by omega
                                                                              have heq : n = (n - 44350) + 44350 := by omega
                                                                              rw [heq]
                                                                              exact ⟨a0_g2_w37 ⟨n - 44350, hr⟩, a1_g2_w37 ⟨n - 44350, hr⟩⟩
                                                                            · by_cases h38 : n < 44450
                                                                              · have hr : n - 44400 < 50 := by omega
                                                                                have heq : n = (n - 44400) + 44400 := by omega
                                                                                rw [heq]
                                                                                exact ⟨a0_g2_w38 ⟨n - 44400, hr⟩, a1_g2_w38 ⟨n - 44400, hr⟩⟩
                                                                              · by_cases h39 : n < 44500
                                                                                · have hr : n - 44450 < 50 := by omega
                                                                                  have heq : n = (n - 44450) + 44450 := by omega
                                                                                  rw [heq]
                                                                                  exact ⟨a0_g2_w39 ⟨n - 44450, hr⟩, a1_g2_w39 ⟨n - 44450, hr⟩⟩
                                                                                · by_cases h40 : n < 44550
                                                                                  · have hr : n - 44500 < 50 := by omega
                                                                                    have heq : n = (n - 44500) + 44500 := by omega
                                                                                    rw [heq]
                                                                                    exact ⟨a0_g2_w40 ⟨n - 44500, hr⟩, a1_g2_w40 ⟨n - 44500, hr⟩⟩
                                                                                  · by_cases h41 : n < 44600
                                                                                    · have hr : n - 44550 < 50 := by omega
                                                                                      have heq : n = (n - 44550) + 44550 := by omega
                                                                                      rw [heq]
                                                                                      exact ⟨a0_g2_w41 ⟨n - 44550, hr⟩, a1_g2_w41 ⟨n - 44550, hr⟩⟩
                                                                                    · by_cases h42 : n < 44650
                                                                                      · have hr : n - 44600 < 50 := by omega
                                                                                        have heq : n = (n - 44600) + 44600 := by omega
                                                                                        rw [heq]
                                                                                        exact ⟨a0_g2_w42 ⟨n - 44600, hr⟩, a1_g2_w42 ⟨n - 44600, hr⟩⟩
                                                                                      · by_cases h43 : n < 44700
                                                                                        · have hr : n - 44650 < 50 := by omega
                                                                                          have heq : n = (n - 44650) + 44650 := by omega
                                                                                          rw [heq]
                                                                                          exact ⟨a0_g2_w43 ⟨n - 44650, hr⟩, a1_g2_w43 ⟨n - 44650, hr⟩⟩
                                                                                        · by_cases h44 : n < 44750
                                                                                          · have hr : n - 44700 < 50 := by omega
                                                                                            have heq : n = (n - 44700) + 44700 := by omega
                                                                                            rw [heq]
                                                                                            exact ⟨a0_g2_w44 ⟨n - 44700, hr⟩, a1_g2_w44 ⟨n - 44700, hr⟩⟩
                                                                                          · by_cases h45 : n < 44800
                                                                                            · have hr : n - 44750 < 50 := by omega
                                                                                              have heq : n = (n - 44750) + 44750 := by omega
                                                                                              rw [heq]
                                                                                              exact ⟨a0_g2_w45 ⟨n - 44750, hr⟩, a1_g2_w45 ⟨n - 44750, hr⟩⟩
                                                                                            · by_cases h46 : n < 44850
                                                                                              · have hr : n - 44800 < 50 := by omega
                                                                                                have heq : n = (n - 44800) + 44800 := by omega
                                                                                                rw [heq]
                                                                                                exact ⟨a0_g2_w46 ⟨n - 44800, hr⟩, a1_g2_w46 ⟨n - 44800, hr⟩⟩
                                                                                              · by_cases h47 : n < 44900
                                                                                                · have hr : n - 44850 < 50 := by omega
                                                                                                  have heq : n = (n - 44850) + 44850 := by omega
                                                                                                  rw [heq]
                                                                                                  exact ⟨a0_g2_w47 ⟨n - 44850, hr⟩, a1_g2_w47 ⟨n - 44850, hr⟩⟩
                                                                                                · by_cases h48 : n < 44950
                                                                                                  · have hr : n - 44900 < 50 := by omega
                                                                                                    have heq : n = (n - 44900) + 44900 := by omega
                                                                                                    rw [heq]
                                                                                                    exact ⟨a0_g2_w48 ⟨n - 44900, hr⟩, a1_g2_w48 ⟨n - 44900, hr⟩⟩
                                                                                                  · have hr : n - 44950 < 50 := by omega
                                                                                                    have heq : n = (n - 44950) + 44950 := by omega
                                                                                                    rw [heq]
                                                                                                    exact ⟨a0_g2_w49 ⟨n - 44950, hr⟩, a1_g2_w49 ⟨n - 44950, hr⟩⟩

private theorem a0_g3_w0 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 45000)) 65535) ≤ dimF (n.val + 45000) := by decide
private theorem a1_g3_w0 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 45000)) 16) ≤ dimF (n.val + 45000) := by decide
private theorem a0_g3_w1 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 45050)) 65535) ≤ dimF (n.val + 45050) := by decide
private theorem a1_g3_w1 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 45050)) 16) ≤ dimF (n.val + 45050) := by decide
private theorem a0_g3_w2 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 45100)) 65535) ≤ dimF (n.val + 45100) := by decide
private theorem a1_g3_w2 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 45100)) 16) ≤ dimF (n.val + 45100) := by decide
private theorem a0_g3_w3 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 45150)) 65535) ≤ dimF (n.val + 45150) := by decide
private theorem a1_g3_w3 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 45150)) 16) ≤ dimF (n.val + 45150) := by decide
private theorem a0_g3_w4 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 45200)) 65535) ≤ dimF (n.val + 45200) := by decide
private theorem a1_g3_w4 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 45200)) 16) ≤ dimF (n.val + 45200) := by decide
private theorem a0_g3_w5 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 45250)) 65535) ≤ dimF (n.val + 45250) := by decide
private theorem a1_g3_w5 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 45250)) 16) ≤ dimF (n.val + 45250) := by decide
private theorem a0_g3_w6 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 45300)) 65535) ≤ dimF (n.val + 45300) := by decide
private theorem a1_g3_w6 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 45300)) 16) ≤ dimF (n.val + 45300) := by decide
private theorem a0_g3_w7 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 45350)) 65535) ≤ dimF (n.val + 45350) := by decide
private theorem a1_g3_w7 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 45350)) 16) ≤ dimF (n.val + 45350) := by decide
private theorem a0_g3_w8 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 45400)) 65535) ≤ dimF (n.val + 45400) := by decide
private theorem a1_g3_w8 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 45400)) 16) ≤ dimF (n.val + 45400) := by decide
private theorem a0_g3_w9 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 45450)) 65535) ≤ dimF (n.val + 45450) := by decide
private theorem a1_g3_w9 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 45450)) 16) ≤ dimF (n.val + 45450) := by decide
private theorem a0_g3_w10 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 45500)) 65535) ≤ dimF (n.val + 45500) := by decide
private theorem a1_g3_w10 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 45500)) 16) ≤ dimF (n.val + 45500) := by decide
private theorem a0_g3_w11 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 45550)) 65535) ≤ dimF (n.val + 45550) := by decide
private theorem a1_g3_w11 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 45550)) 16) ≤ dimF (n.val + 45550) := by decide
private theorem a0_g3_w12 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 45600)) 65535) ≤ dimF (n.val + 45600) := by decide
private theorem a1_g3_w12 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 45600)) 16) ≤ dimF (n.val + 45600) := by decide
private theorem a0_g3_w13 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 45650)) 65535) ≤ dimF (n.val + 45650) := by decide
private theorem a1_g3_w13 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 45650)) 16) ≤ dimF (n.val + 45650) := by decide
private theorem a0_g3_w14 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 45700)) 65535) ≤ dimF (n.val + 45700) := by decide
private theorem a1_g3_w14 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 45700)) 16) ≤ dimF (n.val + 45700) := by decide
private theorem a0_g3_w15 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 45750)) 65535) ≤ dimF (n.val + 45750) := by decide
private theorem a1_g3_w15 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 45750)) 16) ≤ dimF (n.val + 45750) := by decide
private theorem a0_g3_w16 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 45800)) 65535) ≤ dimF (n.val + 45800) := by decide
private theorem a1_g3_w16 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 45800)) 16) ≤ dimF (n.val + 45800) := by decide
private theorem a0_g3_w17 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 45850)) 65535) ≤ dimF (n.val + 45850) := by decide
private theorem a1_g3_w17 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 45850)) 16) ≤ dimF (n.val + 45850) := by decide
private theorem a0_g3_w18 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 45900)) 65535) ≤ dimF (n.val + 45900) := by decide
private theorem a1_g3_w18 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 45900)) 16) ≤ dimF (n.val + 45900) := by decide
private theorem a0_g3_w19 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 45950)) 65535) ≤ dimF (n.val + 45950) := by decide
private theorem a1_g3_w19 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 45950)) 16) ≤ dimF (n.val + 45950) := by decide
private theorem a0_g3_w20 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 46000)) 65535) ≤ dimF (n.val + 46000) := by decide
private theorem a1_g3_w20 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 46000)) 16) ≤ dimF (n.val + 46000) := by decide
private theorem a0_g3_w21 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 46050)) 65535) ≤ dimF (n.val + 46050) := by decide
private theorem a1_g3_w21 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 46050)) 16) ≤ dimF (n.val + 46050) := by decide
private theorem a0_g3_w22 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 46100)) 65535) ≤ dimF (n.val + 46100) := by decide
private theorem a1_g3_w22 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 46100)) 16) ≤ dimF (n.val + 46100) := by decide
private theorem a0_g3_w23 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 46150)) 65535) ≤ dimF (n.val + 46150) := by decide
private theorem a1_g3_w23 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 46150)) 16) ≤ dimF (n.val + 46150) := by decide
private theorem a0_g3_w24 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 46200)) 65535) ≤ dimF (n.val + 46200) := by decide
private theorem a1_g3_w24 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 46200)) 16) ≤ dimF (n.val + 46200) := by decide
private theorem a0_g3_w25 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 46250)) 65535) ≤ dimF (n.val + 46250) := by decide
private theorem a1_g3_w25 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 46250)) 16) ≤ dimF (n.val + 46250) := by decide
private theorem a0_g3_w26 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 46300)) 65535) ≤ dimF (n.val + 46300) := by decide
private theorem a1_g3_w26 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 46300)) 16) ≤ dimF (n.val + 46300) := by decide
private theorem a0_g3_w27 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 46350)) 65535) ≤ dimF (n.val + 46350) := by decide
private theorem a1_g3_w27 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 46350)) 16) ≤ dimF (n.val + 46350) := by decide
private theorem a0_g3_w28 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 46400)) 65535) ≤ dimF (n.val + 46400) := by decide
private theorem a1_g3_w28 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 46400)) 16) ≤ dimF (n.val + 46400) := by decide
private theorem a0_g3_w29 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 46450)) 65535) ≤ dimF (n.val + 46450) := by decide
private theorem a1_g3_w29 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 46450)) 16) ≤ dimF (n.val + 46450) := by decide
private theorem a0_g3_w30 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 46500)) 65535) ≤ dimF (n.val + 46500) := by decide
private theorem a1_g3_w30 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 46500)) 16) ≤ dimF (n.val + 46500) := by decide
private theorem a0_g3_w31 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 46550)) 65535) ≤ dimF (n.val + 46550) := by decide
private theorem a1_g3_w31 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 46550)) 16) ≤ dimF (n.val + 46550) := by decide
private theorem a0_g3_w32 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 46600)) 65535) ≤ dimF (n.val + 46600) := by decide
private theorem a1_g3_w32 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 46600)) 16) ≤ dimF (n.val + 46600) := by decide
private theorem a0_g3_w33 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 46650)) 65535) ≤ dimF (n.val + 46650) := by decide
private theorem a1_g3_w33 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 46650)) 16) ≤ dimF (n.val + 46650) := by decide
private theorem a0_g3_w34 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 46700)) 65535) ≤ dimF (n.val + 46700) := by decide
private theorem a1_g3_w34 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 46700)) 16) ≤ dimF (n.val + 46700) := by decide
private theorem a0_g3_w35 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 46750)) 65535) ≤ dimF (n.val + 46750) := by decide
private theorem a1_g3_w35 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 46750)) 16) ≤ dimF (n.val + 46750) := by decide
private theorem a0_g3_w36 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 46800)) 65535) ≤ dimF (n.val + 46800) := by decide
private theorem a1_g3_w36 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 46800)) 16) ≤ dimF (n.val + 46800) := by decide
private theorem a0_g3_w37 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 46850)) 65535) ≤ dimF (n.val + 46850) := by decide
private theorem a1_g3_w37 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 46850)) 16) ≤ dimF (n.val + 46850) := by decide
private theorem a0_g3_w38 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 46900)) 65535) ≤ dimF (n.val + 46900) := by decide
private theorem a1_g3_w38 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 46900)) 16) ≤ dimF (n.val + 46900) := by decide
private theorem a0_g3_w39 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 46950)) 65535) ≤ dimF (n.val + 46950) := by decide
private theorem a1_g3_w39 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 46950)) 16) ≤ dimF (n.val + 46950) := by decide
private theorem a0_g3_w40 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 47000)) 65535) ≤ dimF (n.val + 47000) := by decide
private theorem a1_g3_w40 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 47000)) 16) ≤ dimF (n.val + 47000) := by decide
private theorem a0_g3_w41 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 47050)) 65535) ≤ dimF (n.val + 47050) := by decide
private theorem a1_g3_w41 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 47050)) 16) ≤ dimF (n.val + 47050) := by decide
private theorem a0_g3_w42 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 47100)) 65535) ≤ dimF (n.val + 47100) := by decide
private theorem a1_g3_w42 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 47100)) 16) ≤ dimF (n.val + 47100) := by decide
private theorem a0_g3_w43 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 47150)) 65535) ≤ dimF (n.val + 47150) := by decide
private theorem a1_g3_w43 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 47150)) 16) ≤ dimF (n.val + 47150) := by decide
private theorem a0_g3_w44 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 47200)) 65535) ≤ dimF (n.val + 47200) := by decide
private theorem a1_g3_w44 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 47200)) 16) ≤ dimF (n.val + 47200) := by decide
private theorem a0_g3_w45 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 47250)) 65535) ≤ dimF (n.val + 47250) := by decide
private theorem a1_g3_w45 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 47250)) 16) ≤ dimF (n.val + 47250) := by decide
private theorem a0_g3_w46 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 47300)) 65535) ≤ dimF (n.val + 47300) := by decide
private theorem a1_g3_w46 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 47300)) 16) ≤ dimF (n.val + 47300) := by decide
private theorem a0_g3_w47 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 47350)) 65535) ≤ dimF (n.val + 47350) := by decide
private theorem a1_g3_w47 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 47350)) 16) ≤ dimF (n.val + 47350) := by decide
private theorem a0_g3_w48 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 47400)) 65535) ≤ dimF (n.val + 47400) := by decide
private theorem a1_g3_w48 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 47400)) 16) ≤ dimF (n.val + 47400) := by decide
private theorem a0_g3_w49 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 47450)) 65535) ≤ dimF (n.val + 47450) := by decide
private theorem a1_g3_w49 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 47450)) 16) ≤ dimF (n.val + 47450) := by decide

private theorem pair_g3 (n : ℕ) (hlo : 45000 ≤ n) (hhi : n < 47500) :
    dimF (Nat.land (argF n) 65535) ≤ dimF n ∧
    dimF (Nat.shiftRight (argF n) 16) ≤ dimF n := by
  by_cases h0 : n < 45050
  · have hr : n - 45000 < 50 := by omega
    have heq : n = (n - 45000) + 45000 := by omega
    rw [heq]
    exact ⟨a0_g3_w0 ⟨n - 45000, hr⟩, a1_g3_w0 ⟨n - 45000, hr⟩⟩
  · by_cases h1 : n < 45100
    · have hr : n - 45050 < 50 := by omega
      have heq : n = (n - 45050) + 45050 := by omega
      rw [heq]
      exact ⟨a0_g3_w1 ⟨n - 45050, hr⟩, a1_g3_w1 ⟨n - 45050, hr⟩⟩
    · by_cases h2 : n < 45150
      · have hr : n - 45100 < 50 := by omega
        have heq : n = (n - 45100) + 45100 := by omega
        rw [heq]
        exact ⟨a0_g3_w2 ⟨n - 45100, hr⟩, a1_g3_w2 ⟨n - 45100, hr⟩⟩
      · by_cases h3 : n < 45200
        · have hr : n - 45150 < 50 := by omega
          have heq : n = (n - 45150) + 45150 := by omega
          rw [heq]
          exact ⟨a0_g3_w3 ⟨n - 45150, hr⟩, a1_g3_w3 ⟨n - 45150, hr⟩⟩
        · by_cases h4 : n < 45250
          · have hr : n - 45200 < 50 := by omega
            have heq : n = (n - 45200) + 45200 := by omega
            rw [heq]
            exact ⟨a0_g3_w4 ⟨n - 45200, hr⟩, a1_g3_w4 ⟨n - 45200, hr⟩⟩
          · by_cases h5 : n < 45300
            · have hr : n - 45250 < 50 := by omega
              have heq : n = (n - 45250) + 45250 := by omega
              rw [heq]
              exact ⟨a0_g3_w5 ⟨n - 45250, hr⟩, a1_g3_w5 ⟨n - 45250, hr⟩⟩
            · by_cases h6 : n < 45350
              · have hr : n - 45300 < 50 := by omega
                have heq : n = (n - 45300) + 45300 := by omega
                rw [heq]
                exact ⟨a0_g3_w6 ⟨n - 45300, hr⟩, a1_g3_w6 ⟨n - 45300, hr⟩⟩
              · by_cases h7 : n < 45400
                · have hr : n - 45350 < 50 := by omega
                  have heq : n = (n - 45350) + 45350 := by omega
                  rw [heq]
                  exact ⟨a0_g3_w7 ⟨n - 45350, hr⟩, a1_g3_w7 ⟨n - 45350, hr⟩⟩
                · by_cases h8 : n < 45450
                  · have hr : n - 45400 < 50 := by omega
                    have heq : n = (n - 45400) + 45400 := by omega
                    rw [heq]
                    exact ⟨a0_g3_w8 ⟨n - 45400, hr⟩, a1_g3_w8 ⟨n - 45400, hr⟩⟩
                  · by_cases h9 : n < 45500
                    · have hr : n - 45450 < 50 := by omega
                      have heq : n = (n - 45450) + 45450 := by omega
                      rw [heq]
                      exact ⟨a0_g3_w9 ⟨n - 45450, hr⟩, a1_g3_w9 ⟨n - 45450, hr⟩⟩
                    · by_cases h10 : n < 45550
                      · have hr : n - 45500 < 50 := by omega
                        have heq : n = (n - 45500) + 45500 := by omega
                        rw [heq]
                        exact ⟨a0_g3_w10 ⟨n - 45500, hr⟩, a1_g3_w10 ⟨n - 45500, hr⟩⟩
                      · by_cases h11 : n < 45600
                        · have hr : n - 45550 < 50 := by omega
                          have heq : n = (n - 45550) + 45550 := by omega
                          rw [heq]
                          exact ⟨a0_g3_w11 ⟨n - 45550, hr⟩, a1_g3_w11 ⟨n - 45550, hr⟩⟩
                        · by_cases h12 : n < 45650
                          · have hr : n - 45600 < 50 := by omega
                            have heq : n = (n - 45600) + 45600 := by omega
                            rw [heq]
                            exact ⟨a0_g3_w12 ⟨n - 45600, hr⟩, a1_g3_w12 ⟨n - 45600, hr⟩⟩
                          · by_cases h13 : n < 45700
                            · have hr : n - 45650 < 50 := by omega
                              have heq : n = (n - 45650) + 45650 := by omega
                              rw [heq]
                              exact ⟨a0_g3_w13 ⟨n - 45650, hr⟩, a1_g3_w13 ⟨n - 45650, hr⟩⟩
                            · by_cases h14 : n < 45750
                              · have hr : n - 45700 < 50 := by omega
                                have heq : n = (n - 45700) + 45700 := by omega
                                rw [heq]
                                exact ⟨a0_g3_w14 ⟨n - 45700, hr⟩, a1_g3_w14 ⟨n - 45700, hr⟩⟩
                              · by_cases h15 : n < 45800
                                · have hr : n - 45750 < 50 := by omega
                                  have heq : n = (n - 45750) + 45750 := by omega
                                  rw [heq]
                                  exact ⟨a0_g3_w15 ⟨n - 45750, hr⟩, a1_g3_w15 ⟨n - 45750, hr⟩⟩
                                · by_cases h16 : n < 45850
                                  · have hr : n - 45800 < 50 := by omega
                                    have heq : n = (n - 45800) + 45800 := by omega
                                    rw [heq]
                                    exact ⟨a0_g3_w16 ⟨n - 45800, hr⟩, a1_g3_w16 ⟨n - 45800, hr⟩⟩
                                  · by_cases h17 : n < 45900
                                    · have hr : n - 45850 < 50 := by omega
                                      have heq : n = (n - 45850) + 45850 := by omega
                                      rw [heq]
                                      exact ⟨a0_g3_w17 ⟨n - 45850, hr⟩, a1_g3_w17 ⟨n - 45850, hr⟩⟩
                                    · by_cases h18 : n < 45950
                                      · have hr : n - 45900 < 50 := by omega
                                        have heq : n = (n - 45900) + 45900 := by omega
                                        rw [heq]
                                        exact ⟨a0_g3_w18 ⟨n - 45900, hr⟩, a1_g3_w18 ⟨n - 45900, hr⟩⟩
                                      · by_cases h19 : n < 46000
                                        · have hr : n - 45950 < 50 := by omega
                                          have heq : n = (n - 45950) + 45950 := by omega
                                          rw [heq]
                                          exact ⟨a0_g3_w19 ⟨n - 45950, hr⟩, a1_g3_w19 ⟨n - 45950, hr⟩⟩
                                        · by_cases h20 : n < 46050
                                          · have hr : n - 46000 < 50 := by omega
                                            have heq : n = (n - 46000) + 46000 := by omega
                                            rw [heq]
                                            exact ⟨a0_g3_w20 ⟨n - 46000, hr⟩, a1_g3_w20 ⟨n - 46000, hr⟩⟩
                                          · by_cases h21 : n < 46100
                                            · have hr : n - 46050 < 50 := by omega
                                              have heq : n = (n - 46050) + 46050 := by omega
                                              rw [heq]
                                              exact ⟨a0_g3_w21 ⟨n - 46050, hr⟩, a1_g3_w21 ⟨n - 46050, hr⟩⟩
                                            · by_cases h22 : n < 46150
                                              · have hr : n - 46100 < 50 := by omega
                                                have heq : n = (n - 46100) + 46100 := by omega
                                                rw [heq]
                                                exact ⟨a0_g3_w22 ⟨n - 46100, hr⟩, a1_g3_w22 ⟨n - 46100, hr⟩⟩
                                              · by_cases h23 : n < 46200
                                                · have hr : n - 46150 < 50 := by omega
                                                  have heq : n = (n - 46150) + 46150 := by omega
                                                  rw [heq]
                                                  exact ⟨a0_g3_w23 ⟨n - 46150, hr⟩, a1_g3_w23 ⟨n - 46150, hr⟩⟩
                                                · by_cases h24 : n < 46250
                                                  · have hr : n - 46200 < 50 := by omega
                                                    have heq : n = (n - 46200) + 46200 := by omega
                                                    rw [heq]
                                                    exact ⟨a0_g3_w24 ⟨n - 46200, hr⟩, a1_g3_w24 ⟨n - 46200, hr⟩⟩
                                                  · by_cases h25 : n < 46300
                                                    · have hr : n - 46250 < 50 := by omega
                                                      have heq : n = (n - 46250) + 46250 := by omega
                                                      rw [heq]
                                                      exact ⟨a0_g3_w25 ⟨n - 46250, hr⟩, a1_g3_w25 ⟨n - 46250, hr⟩⟩
                                                    · by_cases h26 : n < 46350
                                                      · have hr : n - 46300 < 50 := by omega
                                                        have heq : n = (n - 46300) + 46300 := by omega
                                                        rw [heq]
                                                        exact ⟨a0_g3_w26 ⟨n - 46300, hr⟩, a1_g3_w26 ⟨n - 46300, hr⟩⟩
                                                      · by_cases h27 : n < 46400
                                                        · have hr : n - 46350 < 50 := by omega
                                                          have heq : n = (n - 46350) + 46350 := by omega
                                                          rw [heq]
                                                          exact ⟨a0_g3_w27 ⟨n - 46350, hr⟩, a1_g3_w27 ⟨n - 46350, hr⟩⟩
                                                        · by_cases h28 : n < 46450
                                                          · have hr : n - 46400 < 50 := by omega
                                                            have heq : n = (n - 46400) + 46400 := by omega
                                                            rw [heq]
                                                            exact ⟨a0_g3_w28 ⟨n - 46400, hr⟩, a1_g3_w28 ⟨n - 46400, hr⟩⟩
                                                          · by_cases h29 : n < 46500
                                                            · have hr : n - 46450 < 50 := by omega
                                                              have heq : n = (n - 46450) + 46450 := by omega
                                                              rw [heq]
                                                              exact ⟨a0_g3_w29 ⟨n - 46450, hr⟩, a1_g3_w29 ⟨n - 46450, hr⟩⟩
                                                            · by_cases h30 : n < 46550
                                                              · have hr : n - 46500 < 50 := by omega
                                                                have heq : n = (n - 46500) + 46500 := by omega
                                                                rw [heq]
                                                                exact ⟨a0_g3_w30 ⟨n - 46500, hr⟩, a1_g3_w30 ⟨n - 46500, hr⟩⟩
                                                              · by_cases h31 : n < 46600
                                                                · have hr : n - 46550 < 50 := by omega
                                                                  have heq : n = (n - 46550) + 46550 := by omega
                                                                  rw [heq]
                                                                  exact ⟨a0_g3_w31 ⟨n - 46550, hr⟩, a1_g3_w31 ⟨n - 46550, hr⟩⟩
                                                                · by_cases h32 : n < 46650
                                                                  · have hr : n - 46600 < 50 := by omega
                                                                    have heq : n = (n - 46600) + 46600 := by omega
                                                                    rw [heq]
                                                                    exact ⟨a0_g3_w32 ⟨n - 46600, hr⟩, a1_g3_w32 ⟨n - 46600, hr⟩⟩
                                                                  · by_cases h33 : n < 46700
                                                                    · have hr : n - 46650 < 50 := by omega
                                                                      have heq : n = (n - 46650) + 46650 := by omega
                                                                      rw [heq]
                                                                      exact ⟨a0_g3_w33 ⟨n - 46650, hr⟩, a1_g3_w33 ⟨n - 46650, hr⟩⟩
                                                                    · by_cases h34 : n < 46750
                                                                      · have hr : n - 46700 < 50 := by omega
                                                                        have heq : n = (n - 46700) + 46700 := by omega
                                                                        rw [heq]
                                                                        exact ⟨a0_g3_w34 ⟨n - 46700, hr⟩, a1_g3_w34 ⟨n - 46700, hr⟩⟩
                                                                      · by_cases h35 : n < 46800
                                                                        · have hr : n - 46750 < 50 := by omega
                                                                          have heq : n = (n - 46750) + 46750 := by omega
                                                                          rw [heq]
                                                                          exact ⟨a0_g3_w35 ⟨n - 46750, hr⟩, a1_g3_w35 ⟨n - 46750, hr⟩⟩
                                                                        · by_cases h36 : n < 46850
                                                                          · have hr : n - 46800 < 50 := by omega
                                                                            have heq : n = (n - 46800) + 46800 := by omega
                                                                            rw [heq]
                                                                            exact ⟨a0_g3_w36 ⟨n - 46800, hr⟩, a1_g3_w36 ⟨n - 46800, hr⟩⟩
                                                                          · by_cases h37 : n < 46900
                                                                            · have hr : n - 46850 < 50 := by omega
                                                                              have heq : n = (n - 46850) + 46850 := by omega
                                                                              rw [heq]
                                                                              exact ⟨a0_g3_w37 ⟨n - 46850, hr⟩, a1_g3_w37 ⟨n - 46850, hr⟩⟩
                                                                            · by_cases h38 : n < 46950
                                                                              · have hr : n - 46900 < 50 := by omega
                                                                                have heq : n = (n - 46900) + 46900 := by omega
                                                                                rw [heq]
                                                                                exact ⟨a0_g3_w38 ⟨n - 46900, hr⟩, a1_g3_w38 ⟨n - 46900, hr⟩⟩
                                                                              · by_cases h39 : n < 47000
                                                                                · have hr : n - 46950 < 50 := by omega
                                                                                  have heq : n = (n - 46950) + 46950 := by omega
                                                                                  rw [heq]
                                                                                  exact ⟨a0_g3_w39 ⟨n - 46950, hr⟩, a1_g3_w39 ⟨n - 46950, hr⟩⟩
                                                                                · by_cases h40 : n < 47050
                                                                                  · have hr : n - 47000 < 50 := by omega
                                                                                    have heq : n = (n - 47000) + 47000 := by omega
                                                                                    rw [heq]
                                                                                    exact ⟨a0_g3_w40 ⟨n - 47000, hr⟩, a1_g3_w40 ⟨n - 47000, hr⟩⟩
                                                                                  · by_cases h41 : n < 47100
                                                                                    · have hr : n - 47050 < 50 := by omega
                                                                                      have heq : n = (n - 47050) + 47050 := by omega
                                                                                      rw [heq]
                                                                                      exact ⟨a0_g3_w41 ⟨n - 47050, hr⟩, a1_g3_w41 ⟨n - 47050, hr⟩⟩
                                                                                    · by_cases h42 : n < 47150
                                                                                      · have hr : n - 47100 < 50 := by omega
                                                                                        have heq : n = (n - 47100) + 47100 := by omega
                                                                                        rw [heq]
                                                                                        exact ⟨a0_g3_w42 ⟨n - 47100, hr⟩, a1_g3_w42 ⟨n - 47100, hr⟩⟩
                                                                                      · by_cases h43 : n < 47200
                                                                                        · have hr : n - 47150 < 50 := by omega
                                                                                          have heq : n = (n - 47150) + 47150 := by omega
                                                                                          rw [heq]
                                                                                          exact ⟨a0_g3_w43 ⟨n - 47150, hr⟩, a1_g3_w43 ⟨n - 47150, hr⟩⟩
                                                                                        · by_cases h44 : n < 47250
                                                                                          · have hr : n - 47200 < 50 := by omega
                                                                                            have heq : n = (n - 47200) + 47200 := by omega
                                                                                            rw [heq]
                                                                                            exact ⟨a0_g3_w44 ⟨n - 47200, hr⟩, a1_g3_w44 ⟨n - 47200, hr⟩⟩
                                                                                          · by_cases h45 : n < 47300
                                                                                            · have hr : n - 47250 < 50 := by omega
                                                                                              have heq : n = (n - 47250) + 47250 := by omega
                                                                                              rw [heq]
                                                                                              exact ⟨a0_g3_w45 ⟨n - 47250, hr⟩, a1_g3_w45 ⟨n - 47250, hr⟩⟩
                                                                                            · by_cases h46 : n < 47350
                                                                                              · have hr : n - 47300 < 50 := by omega
                                                                                                have heq : n = (n - 47300) + 47300 := by omega
                                                                                                rw [heq]
                                                                                                exact ⟨a0_g3_w46 ⟨n - 47300, hr⟩, a1_g3_w46 ⟨n - 47300, hr⟩⟩
                                                                                              · by_cases h47 : n < 47400
                                                                                                · have hr : n - 47350 < 50 := by omega
                                                                                                  have heq : n = (n - 47350) + 47350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact ⟨a0_g3_w47 ⟨n - 47350, hr⟩, a1_g3_w47 ⟨n - 47350, hr⟩⟩
                                                                                                · by_cases h48 : n < 47450
                                                                                                  · have hr : n - 47400 < 50 := by omega
                                                                                                    have heq : n = (n - 47400) + 47400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact ⟨a0_g3_w48 ⟨n - 47400, hr⟩, a1_g3_w48 ⟨n - 47400, hr⟩⟩
                                                                                                  · have hr : n - 47450 < 50 := by omega
                                                                                                    have heq : n = (n - 47450) + 47450 := by omega
                                                                                                    rw [heq]
                                                                                                    exact ⟨a0_g3_w49 ⟨n - 47450, hr⟩, a1_g3_w49 ⟨n - 47450, hr⟩⟩

private theorem a0_g4_w0 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 47500)) 65535) ≤ dimF (n.val + 47500) := by decide
private theorem a1_g4_w0 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 47500)) 16) ≤ dimF (n.val + 47500) := by decide
private theorem a0_g4_w1 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 47550)) 65535) ≤ dimF (n.val + 47550) := by decide
private theorem a1_g4_w1 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 47550)) 16) ≤ dimF (n.val + 47550) := by decide
private theorem a0_g4_w2 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 47600)) 65535) ≤ dimF (n.val + 47600) := by decide
private theorem a1_g4_w2 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 47600)) 16) ≤ dimF (n.val + 47600) := by decide
private theorem a0_g4_w3 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 47650)) 65535) ≤ dimF (n.val + 47650) := by decide
private theorem a1_g4_w3 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 47650)) 16) ≤ dimF (n.val + 47650) := by decide
private theorem a0_g4_w4 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 47700)) 65535) ≤ dimF (n.val + 47700) := by decide
private theorem a1_g4_w4 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 47700)) 16) ≤ dimF (n.val + 47700) := by decide
private theorem a0_g4_w5 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 47750)) 65535) ≤ dimF (n.val + 47750) := by decide
private theorem a1_g4_w5 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 47750)) 16) ≤ dimF (n.val + 47750) := by decide
private theorem a0_g4_w6 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 47800)) 65535) ≤ dimF (n.val + 47800) := by decide
private theorem a1_g4_w6 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 47800)) 16) ≤ dimF (n.val + 47800) := by decide
private theorem a0_g4_w7 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 47850)) 65535) ≤ dimF (n.val + 47850) := by decide
private theorem a1_g4_w7 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 47850)) 16) ≤ dimF (n.val + 47850) := by decide
private theorem a0_g4_w8 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 47900)) 65535) ≤ dimF (n.val + 47900) := by decide
private theorem a1_g4_w8 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 47900)) 16) ≤ dimF (n.val + 47900) := by decide
private theorem a0_g4_w9 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 47950)) 65535) ≤ dimF (n.val + 47950) := by decide
private theorem a1_g4_w9 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 47950)) 16) ≤ dimF (n.val + 47950) := by decide
private theorem a0_g4_w10 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 48000)) 65535) ≤ dimF (n.val + 48000) := by decide
private theorem a1_g4_w10 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 48000)) 16) ≤ dimF (n.val + 48000) := by decide
private theorem a0_g4_w11 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 48050)) 65535) ≤ dimF (n.val + 48050) := by decide
private theorem a1_g4_w11 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 48050)) 16) ≤ dimF (n.val + 48050) := by decide
private theorem a0_g4_w12 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 48100)) 65535) ≤ dimF (n.val + 48100) := by decide
private theorem a1_g4_w12 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 48100)) 16) ≤ dimF (n.val + 48100) := by decide
private theorem a0_g4_w13 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 48150)) 65535) ≤ dimF (n.val + 48150) := by decide
private theorem a1_g4_w13 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 48150)) 16) ≤ dimF (n.val + 48150) := by decide
private theorem a0_g4_w14 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 48200)) 65535) ≤ dimF (n.val + 48200) := by decide
private theorem a1_g4_w14 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 48200)) 16) ≤ dimF (n.val + 48200) := by decide
private theorem a0_g4_w15 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 48250)) 65535) ≤ dimF (n.val + 48250) := by decide
private theorem a1_g4_w15 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 48250)) 16) ≤ dimF (n.val + 48250) := by decide
private theorem a0_g4_w16 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 48300)) 65535) ≤ dimF (n.val + 48300) := by decide
private theorem a1_g4_w16 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 48300)) 16) ≤ dimF (n.val + 48300) := by decide
private theorem a0_g4_w17 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 48350)) 65535) ≤ dimF (n.val + 48350) := by decide
private theorem a1_g4_w17 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 48350)) 16) ≤ dimF (n.val + 48350) := by decide
private theorem a0_g4_w18 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 48400)) 65535) ≤ dimF (n.val + 48400) := by decide
private theorem a1_g4_w18 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 48400)) 16) ≤ dimF (n.val + 48400) := by decide
private theorem a0_g4_w19 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 48450)) 65535) ≤ dimF (n.val + 48450) := by decide
private theorem a1_g4_w19 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 48450)) 16) ≤ dimF (n.val + 48450) := by decide
private theorem a0_g4_w20 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 48500)) 65535) ≤ dimF (n.val + 48500) := by decide
private theorem a1_g4_w20 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 48500)) 16) ≤ dimF (n.val + 48500) := by decide
private theorem a0_g4_w21 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 48550)) 65535) ≤ dimF (n.val + 48550) := by decide
private theorem a1_g4_w21 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 48550)) 16) ≤ dimF (n.val + 48550) := by decide
private theorem a0_g4_w22 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 48600)) 65535) ≤ dimF (n.val + 48600) := by decide
private theorem a1_g4_w22 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 48600)) 16) ≤ dimF (n.val + 48600) := by decide
private theorem a0_g4_w23 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 48650)) 65535) ≤ dimF (n.val + 48650) := by decide
private theorem a1_g4_w23 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 48650)) 16) ≤ dimF (n.val + 48650) := by decide
private theorem a0_g4_w24 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 48700)) 65535) ≤ dimF (n.val + 48700) := by decide
private theorem a1_g4_w24 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 48700)) 16) ≤ dimF (n.val + 48700) := by decide
private theorem a0_g4_w25 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 48750)) 65535) ≤ dimF (n.val + 48750) := by decide
private theorem a1_g4_w25 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 48750)) 16) ≤ dimF (n.val + 48750) := by decide
private theorem a0_g4_w26 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 48800)) 65535) ≤ dimF (n.val + 48800) := by decide
private theorem a1_g4_w26 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 48800)) 16) ≤ dimF (n.val + 48800) := by decide
private theorem a0_g4_w27 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 48850)) 65535) ≤ dimF (n.val + 48850) := by decide
private theorem a1_g4_w27 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 48850)) 16) ≤ dimF (n.val + 48850) := by decide
private theorem a0_g4_w28 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 48900)) 65535) ≤ dimF (n.val + 48900) := by decide
private theorem a1_g4_w28 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 48900)) 16) ≤ dimF (n.val + 48900) := by decide
private theorem a0_g4_w29 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 48950)) 65535) ≤ dimF (n.val + 48950) := by decide
private theorem a1_g4_w29 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 48950)) 16) ≤ dimF (n.val + 48950) := by decide
private theorem a0_g4_w30 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 49000)) 65535) ≤ dimF (n.val + 49000) := by decide
private theorem a1_g4_w30 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 49000)) 16) ≤ dimF (n.val + 49000) := by decide
private theorem a0_g4_w31 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 49050)) 65535) ≤ dimF (n.val + 49050) := by decide
private theorem a1_g4_w31 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 49050)) 16) ≤ dimF (n.val + 49050) := by decide
private theorem a0_g4_w32 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 49100)) 65535) ≤ dimF (n.val + 49100) := by decide
private theorem a1_g4_w32 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 49100)) 16) ≤ dimF (n.val + 49100) := by decide
private theorem a0_g4_w33 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 49150)) 65535) ≤ dimF (n.val + 49150) := by decide
private theorem a1_g4_w33 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 49150)) 16) ≤ dimF (n.val + 49150) := by decide
private theorem a0_g4_w34 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 49200)) 65535) ≤ dimF (n.val + 49200) := by decide
private theorem a1_g4_w34 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 49200)) 16) ≤ dimF (n.val + 49200) := by decide
private theorem a0_g4_w35 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 49250)) 65535) ≤ dimF (n.val + 49250) := by decide
private theorem a1_g4_w35 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 49250)) 16) ≤ dimF (n.val + 49250) := by decide
private theorem a0_g4_w36 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 49300)) 65535) ≤ dimF (n.val + 49300) := by decide
private theorem a1_g4_w36 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 49300)) 16) ≤ dimF (n.val + 49300) := by decide
private theorem a0_g4_w37 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 49350)) 65535) ≤ dimF (n.val + 49350) := by decide
private theorem a1_g4_w37 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 49350)) 16) ≤ dimF (n.val + 49350) := by decide
private theorem a0_g4_w38 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 49400)) 65535) ≤ dimF (n.val + 49400) := by decide
private theorem a1_g4_w38 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 49400)) 16) ≤ dimF (n.val + 49400) := by decide
private theorem a0_g4_w39 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 49450)) 65535) ≤ dimF (n.val + 49450) := by decide
private theorem a1_g4_w39 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 49450)) 16) ≤ dimF (n.val + 49450) := by decide
private theorem a0_g4_w40 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 49500)) 65535) ≤ dimF (n.val + 49500) := by decide
private theorem a1_g4_w40 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 49500)) 16) ≤ dimF (n.val + 49500) := by decide
private theorem a0_g4_w41 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 49550)) 65535) ≤ dimF (n.val + 49550) := by decide
private theorem a1_g4_w41 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 49550)) 16) ≤ dimF (n.val + 49550) := by decide
private theorem a0_g4_w42 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 49600)) 65535) ≤ dimF (n.val + 49600) := by decide
private theorem a1_g4_w42 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 49600)) 16) ≤ dimF (n.val + 49600) := by decide
private theorem a0_g4_w43 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 49650)) 65535) ≤ dimF (n.val + 49650) := by decide
private theorem a1_g4_w43 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 49650)) 16) ≤ dimF (n.val + 49650) := by decide
private theorem a0_g4_w44 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 49700)) 65535) ≤ dimF (n.val + 49700) := by decide
private theorem a1_g4_w44 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 49700)) 16) ≤ dimF (n.val + 49700) := by decide
private theorem a0_g4_w45 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 49750)) 65535) ≤ dimF (n.val + 49750) := by decide
private theorem a1_g4_w45 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 49750)) 16) ≤ dimF (n.val + 49750) := by decide
private theorem a0_g4_w46 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 49800)) 65535) ≤ dimF (n.val + 49800) := by decide
private theorem a1_g4_w46 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 49800)) 16) ≤ dimF (n.val + 49800) := by decide
private theorem a0_g4_w47 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 49850)) 65535) ≤ dimF (n.val + 49850) := by decide
private theorem a1_g4_w47 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 49850)) 16) ≤ dimF (n.val + 49850) := by decide
private theorem a0_g4_w48 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 49900)) 65535) ≤ dimF (n.val + 49900) := by decide
private theorem a1_g4_w48 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 49900)) 16) ≤ dimF (n.val + 49900) := by decide
private theorem a0_g4_w49 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 49950)) 65535) ≤ dimF (n.val + 49950) := by decide
private theorem a1_g4_w49 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 49950)) 16) ≤ dimF (n.val + 49950) := by decide

private theorem pair_g4 (n : ℕ) (hlo : 47500 ≤ n) (hhi : n < 50000) :
    dimF (Nat.land (argF n) 65535) ≤ dimF n ∧
    dimF (Nat.shiftRight (argF n) 16) ≤ dimF n := by
  by_cases h0 : n < 47550
  · have hr : n - 47500 < 50 := by omega
    have heq : n = (n - 47500) + 47500 := by omega
    rw [heq]
    exact ⟨a0_g4_w0 ⟨n - 47500, hr⟩, a1_g4_w0 ⟨n - 47500, hr⟩⟩
  · by_cases h1 : n < 47600
    · have hr : n - 47550 < 50 := by omega
      have heq : n = (n - 47550) + 47550 := by omega
      rw [heq]
      exact ⟨a0_g4_w1 ⟨n - 47550, hr⟩, a1_g4_w1 ⟨n - 47550, hr⟩⟩
    · by_cases h2 : n < 47650
      · have hr : n - 47600 < 50 := by omega
        have heq : n = (n - 47600) + 47600 := by omega
        rw [heq]
        exact ⟨a0_g4_w2 ⟨n - 47600, hr⟩, a1_g4_w2 ⟨n - 47600, hr⟩⟩
      · by_cases h3 : n < 47700
        · have hr : n - 47650 < 50 := by omega
          have heq : n = (n - 47650) + 47650 := by omega
          rw [heq]
          exact ⟨a0_g4_w3 ⟨n - 47650, hr⟩, a1_g4_w3 ⟨n - 47650, hr⟩⟩
        · by_cases h4 : n < 47750
          · have hr : n - 47700 < 50 := by omega
            have heq : n = (n - 47700) + 47700 := by omega
            rw [heq]
            exact ⟨a0_g4_w4 ⟨n - 47700, hr⟩, a1_g4_w4 ⟨n - 47700, hr⟩⟩
          · by_cases h5 : n < 47800
            · have hr : n - 47750 < 50 := by omega
              have heq : n = (n - 47750) + 47750 := by omega
              rw [heq]
              exact ⟨a0_g4_w5 ⟨n - 47750, hr⟩, a1_g4_w5 ⟨n - 47750, hr⟩⟩
            · by_cases h6 : n < 47850
              · have hr : n - 47800 < 50 := by omega
                have heq : n = (n - 47800) + 47800 := by omega
                rw [heq]
                exact ⟨a0_g4_w6 ⟨n - 47800, hr⟩, a1_g4_w6 ⟨n - 47800, hr⟩⟩
              · by_cases h7 : n < 47900
                · have hr : n - 47850 < 50 := by omega
                  have heq : n = (n - 47850) + 47850 := by omega
                  rw [heq]
                  exact ⟨a0_g4_w7 ⟨n - 47850, hr⟩, a1_g4_w7 ⟨n - 47850, hr⟩⟩
                · by_cases h8 : n < 47950
                  · have hr : n - 47900 < 50 := by omega
                    have heq : n = (n - 47900) + 47900 := by omega
                    rw [heq]
                    exact ⟨a0_g4_w8 ⟨n - 47900, hr⟩, a1_g4_w8 ⟨n - 47900, hr⟩⟩
                  · by_cases h9 : n < 48000
                    · have hr : n - 47950 < 50 := by omega
                      have heq : n = (n - 47950) + 47950 := by omega
                      rw [heq]
                      exact ⟨a0_g4_w9 ⟨n - 47950, hr⟩, a1_g4_w9 ⟨n - 47950, hr⟩⟩
                    · by_cases h10 : n < 48050
                      · have hr : n - 48000 < 50 := by omega
                        have heq : n = (n - 48000) + 48000 := by omega
                        rw [heq]
                        exact ⟨a0_g4_w10 ⟨n - 48000, hr⟩, a1_g4_w10 ⟨n - 48000, hr⟩⟩
                      · by_cases h11 : n < 48100
                        · have hr : n - 48050 < 50 := by omega
                          have heq : n = (n - 48050) + 48050 := by omega
                          rw [heq]
                          exact ⟨a0_g4_w11 ⟨n - 48050, hr⟩, a1_g4_w11 ⟨n - 48050, hr⟩⟩
                        · by_cases h12 : n < 48150
                          · have hr : n - 48100 < 50 := by omega
                            have heq : n = (n - 48100) + 48100 := by omega
                            rw [heq]
                            exact ⟨a0_g4_w12 ⟨n - 48100, hr⟩, a1_g4_w12 ⟨n - 48100, hr⟩⟩
                          · by_cases h13 : n < 48200
                            · have hr : n - 48150 < 50 := by omega
                              have heq : n = (n - 48150) + 48150 := by omega
                              rw [heq]
                              exact ⟨a0_g4_w13 ⟨n - 48150, hr⟩, a1_g4_w13 ⟨n - 48150, hr⟩⟩
                            · by_cases h14 : n < 48250
                              · have hr : n - 48200 < 50 := by omega
                                have heq : n = (n - 48200) + 48200 := by omega
                                rw [heq]
                                exact ⟨a0_g4_w14 ⟨n - 48200, hr⟩, a1_g4_w14 ⟨n - 48200, hr⟩⟩
                              · by_cases h15 : n < 48300
                                · have hr : n - 48250 < 50 := by omega
                                  have heq : n = (n - 48250) + 48250 := by omega
                                  rw [heq]
                                  exact ⟨a0_g4_w15 ⟨n - 48250, hr⟩, a1_g4_w15 ⟨n - 48250, hr⟩⟩
                                · by_cases h16 : n < 48350
                                  · have hr : n - 48300 < 50 := by omega
                                    have heq : n = (n - 48300) + 48300 := by omega
                                    rw [heq]
                                    exact ⟨a0_g4_w16 ⟨n - 48300, hr⟩, a1_g4_w16 ⟨n - 48300, hr⟩⟩
                                  · by_cases h17 : n < 48400
                                    · have hr : n - 48350 < 50 := by omega
                                      have heq : n = (n - 48350) + 48350 := by omega
                                      rw [heq]
                                      exact ⟨a0_g4_w17 ⟨n - 48350, hr⟩, a1_g4_w17 ⟨n - 48350, hr⟩⟩
                                    · by_cases h18 : n < 48450
                                      · have hr : n - 48400 < 50 := by omega
                                        have heq : n = (n - 48400) + 48400 := by omega
                                        rw [heq]
                                        exact ⟨a0_g4_w18 ⟨n - 48400, hr⟩, a1_g4_w18 ⟨n - 48400, hr⟩⟩
                                      · by_cases h19 : n < 48500
                                        · have hr : n - 48450 < 50 := by omega
                                          have heq : n = (n - 48450) + 48450 := by omega
                                          rw [heq]
                                          exact ⟨a0_g4_w19 ⟨n - 48450, hr⟩, a1_g4_w19 ⟨n - 48450, hr⟩⟩
                                        · by_cases h20 : n < 48550
                                          · have hr : n - 48500 < 50 := by omega
                                            have heq : n = (n - 48500) + 48500 := by omega
                                            rw [heq]
                                            exact ⟨a0_g4_w20 ⟨n - 48500, hr⟩, a1_g4_w20 ⟨n - 48500, hr⟩⟩
                                          · by_cases h21 : n < 48600
                                            · have hr : n - 48550 < 50 := by omega
                                              have heq : n = (n - 48550) + 48550 := by omega
                                              rw [heq]
                                              exact ⟨a0_g4_w21 ⟨n - 48550, hr⟩, a1_g4_w21 ⟨n - 48550, hr⟩⟩
                                            · by_cases h22 : n < 48650
                                              · have hr : n - 48600 < 50 := by omega
                                                have heq : n = (n - 48600) + 48600 := by omega
                                                rw [heq]
                                                exact ⟨a0_g4_w22 ⟨n - 48600, hr⟩, a1_g4_w22 ⟨n - 48600, hr⟩⟩
                                              · by_cases h23 : n < 48700
                                                · have hr : n - 48650 < 50 := by omega
                                                  have heq : n = (n - 48650) + 48650 := by omega
                                                  rw [heq]
                                                  exact ⟨a0_g4_w23 ⟨n - 48650, hr⟩, a1_g4_w23 ⟨n - 48650, hr⟩⟩
                                                · by_cases h24 : n < 48750
                                                  · have hr : n - 48700 < 50 := by omega
                                                    have heq : n = (n - 48700) + 48700 := by omega
                                                    rw [heq]
                                                    exact ⟨a0_g4_w24 ⟨n - 48700, hr⟩, a1_g4_w24 ⟨n - 48700, hr⟩⟩
                                                  · by_cases h25 : n < 48800
                                                    · have hr : n - 48750 < 50 := by omega
                                                      have heq : n = (n - 48750) + 48750 := by omega
                                                      rw [heq]
                                                      exact ⟨a0_g4_w25 ⟨n - 48750, hr⟩, a1_g4_w25 ⟨n - 48750, hr⟩⟩
                                                    · by_cases h26 : n < 48850
                                                      · have hr : n - 48800 < 50 := by omega
                                                        have heq : n = (n - 48800) + 48800 := by omega
                                                        rw [heq]
                                                        exact ⟨a0_g4_w26 ⟨n - 48800, hr⟩, a1_g4_w26 ⟨n - 48800, hr⟩⟩
                                                      · by_cases h27 : n < 48900
                                                        · have hr : n - 48850 < 50 := by omega
                                                          have heq : n = (n - 48850) + 48850 := by omega
                                                          rw [heq]
                                                          exact ⟨a0_g4_w27 ⟨n - 48850, hr⟩, a1_g4_w27 ⟨n - 48850, hr⟩⟩
                                                        · by_cases h28 : n < 48950
                                                          · have hr : n - 48900 < 50 := by omega
                                                            have heq : n = (n - 48900) + 48900 := by omega
                                                            rw [heq]
                                                            exact ⟨a0_g4_w28 ⟨n - 48900, hr⟩, a1_g4_w28 ⟨n - 48900, hr⟩⟩
                                                          · by_cases h29 : n < 49000
                                                            · have hr : n - 48950 < 50 := by omega
                                                              have heq : n = (n - 48950) + 48950 := by omega
                                                              rw [heq]
                                                              exact ⟨a0_g4_w29 ⟨n - 48950, hr⟩, a1_g4_w29 ⟨n - 48950, hr⟩⟩
                                                            · by_cases h30 : n < 49050
                                                              · have hr : n - 49000 < 50 := by omega
                                                                have heq : n = (n - 49000) + 49000 := by omega
                                                                rw [heq]
                                                                exact ⟨a0_g4_w30 ⟨n - 49000, hr⟩, a1_g4_w30 ⟨n - 49000, hr⟩⟩
                                                              · by_cases h31 : n < 49100
                                                                · have hr : n - 49050 < 50 := by omega
                                                                  have heq : n = (n - 49050) + 49050 := by omega
                                                                  rw [heq]
                                                                  exact ⟨a0_g4_w31 ⟨n - 49050, hr⟩, a1_g4_w31 ⟨n - 49050, hr⟩⟩
                                                                · by_cases h32 : n < 49150
                                                                  · have hr : n - 49100 < 50 := by omega
                                                                    have heq : n = (n - 49100) + 49100 := by omega
                                                                    rw [heq]
                                                                    exact ⟨a0_g4_w32 ⟨n - 49100, hr⟩, a1_g4_w32 ⟨n - 49100, hr⟩⟩
                                                                  · by_cases h33 : n < 49200
                                                                    · have hr : n - 49150 < 50 := by omega
                                                                      have heq : n = (n - 49150) + 49150 := by omega
                                                                      rw [heq]
                                                                      exact ⟨a0_g4_w33 ⟨n - 49150, hr⟩, a1_g4_w33 ⟨n - 49150, hr⟩⟩
                                                                    · by_cases h34 : n < 49250
                                                                      · have hr : n - 49200 < 50 := by omega
                                                                        have heq : n = (n - 49200) + 49200 := by omega
                                                                        rw [heq]
                                                                        exact ⟨a0_g4_w34 ⟨n - 49200, hr⟩, a1_g4_w34 ⟨n - 49200, hr⟩⟩
                                                                      · by_cases h35 : n < 49300
                                                                        · have hr : n - 49250 < 50 := by omega
                                                                          have heq : n = (n - 49250) + 49250 := by omega
                                                                          rw [heq]
                                                                          exact ⟨a0_g4_w35 ⟨n - 49250, hr⟩, a1_g4_w35 ⟨n - 49250, hr⟩⟩
                                                                        · by_cases h36 : n < 49350
                                                                          · have hr : n - 49300 < 50 := by omega
                                                                            have heq : n = (n - 49300) + 49300 := by omega
                                                                            rw [heq]
                                                                            exact ⟨a0_g4_w36 ⟨n - 49300, hr⟩, a1_g4_w36 ⟨n - 49300, hr⟩⟩
                                                                          · by_cases h37 : n < 49400
                                                                            · have hr : n - 49350 < 50 := by omega
                                                                              have heq : n = (n - 49350) + 49350 := by omega
                                                                              rw [heq]
                                                                              exact ⟨a0_g4_w37 ⟨n - 49350, hr⟩, a1_g4_w37 ⟨n - 49350, hr⟩⟩
                                                                            · by_cases h38 : n < 49450
                                                                              · have hr : n - 49400 < 50 := by omega
                                                                                have heq : n = (n - 49400) + 49400 := by omega
                                                                                rw [heq]
                                                                                exact ⟨a0_g4_w38 ⟨n - 49400, hr⟩, a1_g4_w38 ⟨n - 49400, hr⟩⟩
                                                                              · by_cases h39 : n < 49500
                                                                                · have hr : n - 49450 < 50 := by omega
                                                                                  have heq : n = (n - 49450) + 49450 := by omega
                                                                                  rw [heq]
                                                                                  exact ⟨a0_g4_w39 ⟨n - 49450, hr⟩, a1_g4_w39 ⟨n - 49450, hr⟩⟩
                                                                                · by_cases h40 : n < 49550
                                                                                  · have hr : n - 49500 < 50 := by omega
                                                                                    have heq : n = (n - 49500) + 49500 := by omega
                                                                                    rw [heq]
                                                                                    exact ⟨a0_g4_w40 ⟨n - 49500, hr⟩, a1_g4_w40 ⟨n - 49500, hr⟩⟩
                                                                                  · by_cases h41 : n < 49600
                                                                                    · have hr : n - 49550 < 50 := by omega
                                                                                      have heq : n = (n - 49550) + 49550 := by omega
                                                                                      rw [heq]
                                                                                      exact ⟨a0_g4_w41 ⟨n - 49550, hr⟩, a1_g4_w41 ⟨n - 49550, hr⟩⟩
                                                                                    · by_cases h42 : n < 49650
                                                                                      · have hr : n - 49600 < 50 := by omega
                                                                                        have heq : n = (n - 49600) + 49600 := by omega
                                                                                        rw [heq]
                                                                                        exact ⟨a0_g4_w42 ⟨n - 49600, hr⟩, a1_g4_w42 ⟨n - 49600, hr⟩⟩
                                                                                      · by_cases h43 : n < 49700
                                                                                        · have hr : n - 49650 < 50 := by omega
                                                                                          have heq : n = (n - 49650) + 49650 := by omega
                                                                                          rw [heq]
                                                                                          exact ⟨a0_g4_w43 ⟨n - 49650, hr⟩, a1_g4_w43 ⟨n - 49650, hr⟩⟩
                                                                                        · by_cases h44 : n < 49750
                                                                                          · have hr : n - 49700 < 50 := by omega
                                                                                            have heq : n = (n - 49700) + 49700 := by omega
                                                                                            rw [heq]
                                                                                            exact ⟨a0_g4_w44 ⟨n - 49700, hr⟩, a1_g4_w44 ⟨n - 49700, hr⟩⟩
                                                                                          · by_cases h45 : n < 49800
                                                                                            · have hr : n - 49750 < 50 := by omega
                                                                                              have heq : n = (n - 49750) + 49750 := by omega
                                                                                              rw [heq]
                                                                                              exact ⟨a0_g4_w45 ⟨n - 49750, hr⟩, a1_g4_w45 ⟨n - 49750, hr⟩⟩
                                                                                            · by_cases h46 : n < 49850
                                                                                              · have hr : n - 49800 < 50 := by omega
                                                                                                have heq : n = (n - 49800) + 49800 := by omega
                                                                                                rw [heq]
                                                                                                exact ⟨a0_g4_w46 ⟨n - 49800, hr⟩, a1_g4_w46 ⟨n - 49800, hr⟩⟩
                                                                                              · by_cases h47 : n < 49900
                                                                                                · have hr : n - 49850 < 50 := by omega
                                                                                                  have heq : n = (n - 49850) + 49850 := by omega
                                                                                                  rw [heq]
                                                                                                  exact ⟨a0_g4_w47 ⟨n - 49850, hr⟩, a1_g4_w47 ⟨n - 49850, hr⟩⟩
                                                                                                · by_cases h48 : n < 49950
                                                                                                  · have hr : n - 49900 < 50 := by omega
                                                                                                    have heq : n = (n - 49900) + 49900 := by omega
                                                                                                    rw [heq]
                                                                                                    exact ⟨a0_g4_w48 ⟨n - 49900, hr⟩, a1_g4_w48 ⟨n - 49900, hr⟩⟩
                                                                                                  · have hr : n - 49950 < 50 := by omega
                                                                                                    have heq : n = (n - 49950) + 49950 := by omega
                                                                                                    rw [heq]
                                                                                                    exact ⟨a0_g4_w49 ⟨n - 49950, hr⟩, a1_g4_w49 ⟨n - 49950, hr⟩⟩

theorem solution (n : ℕ) (hn0 : 37500 ≤ n) (hn1 : n < 50000) :
    dimF (Nat.land (argF n) 65535) ≤ dimF n ∧
    dimF (Nat.shiftRight (argF n) 16) ≤ dimF n := by
  by_cases hg0 : n < 40000
  · exact pair_g0 n (by omega) hg0
  · by_cases hg1 : n < 42500
    · exact pair_g1 n (by omega) hg1
    · by_cases hg2 : n < 45000
      · exact pair_g2 n (by omega) hg2
      · by_cases hg3 : n < 47500
        · exact pair_g3 n (by omega) hg3
        · exact pair_g4 n (by omega) hn1
