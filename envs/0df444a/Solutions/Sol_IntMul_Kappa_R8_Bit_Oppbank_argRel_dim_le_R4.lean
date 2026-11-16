-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.argRel_dim_le_R4
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T09:36:57.125553+00:00
-- url     : https://prove2.me/submissions/70a4873f-f9a6-43c4-a98e-b6477913141e

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG

private theorem a0_g0_w0 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 50000)) 65535) ≤ dimF (n.val + 50000) := by decide
private theorem a1_g0_w0 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 50000)) 16) ≤ dimF (n.val + 50000) := by decide
private theorem a0_g0_w1 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 50050)) 65535) ≤ dimF (n.val + 50050) := by decide
private theorem a1_g0_w1 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 50050)) 16) ≤ dimF (n.val + 50050) := by decide
private theorem a0_g0_w2 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 50100)) 65535) ≤ dimF (n.val + 50100) := by decide
private theorem a1_g0_w2 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 50100)) 16) ≤ dimF (n.val + 50100) := by decide
private theorem a0_g0_w3 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 50150)) 65535) ≤ dimF (n.val + 50150) := by decide
private theorem a1_g0_w3 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 50150)) 16) ≤ dimF (n.val + 50150) := by decide
private theorem a0_g0_w4 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 50200)) 65535) ≤ dimF (n.val + 50200) := by decide
private theorem a1_g0_w4 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 50200)) 16) ≤ dimF (n.val + 50200) := by decide
private theorem a0_g0_w5 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 50250)) 65535) ≤ dimF (n.val + 50250) := by decide
private theorem a1_g0_w5 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 50250)) 16) ≤ dimF (n.val + 50250) := by decide
private theorem a0_g0_w6 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 50300)) 65535) ≤ dimF (n.val + 50300) := by decide
private theorem a1_g0_w6 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 50300)) 16) ≤ dimF (n.val + 50300) := by decide
private theorem a0_g0_w7 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 50350)) 65535) ≤ dimF (n.val + 50350) := by decide
private theorem a1_g0_w7 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 50350)) 16) ≤ dimF (n.val + 50350) := by decide
private theorem a0_g0_w8 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 50400)) 65535) ≤ dimF (n.val + 50400) := by decide
private theorem a1_g0_w8 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 50400)) 16) ≤ dimF (n.val + 50400) := by decide
private theorem a0_g0_w9 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 50450)) 65535) ≤ dimF (n.val + 50450) := by decide
private theorem a1_g0_w9 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 50450)) 16) ≤ dimF (n.val + 50450) := by decide
private theorem a0_g0_w10 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 50500)) 65535) ≤ dimF (n.val + 50500) := by decide
private theorem a1_g0_w10 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 50500)) 16) ≤ dimF (n.val + 50500) := by decide
private theorem a0_g0_w11 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 50550)) 65535) ≤ dimF (n.val + 50550) := by decide
private theorem a1_g0_w11 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 50550)) 16) ≤ dimF (n.val + 50550) := by decide
private theorem a0_g0_w12 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 50600)) 65535) ≤ dimF (n.val + 50600) := by decide
private theorem a1_g0_w12 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 50600)) 16) ≤ dimF (n.val + 50600) := by decide
private theorem a0_g0_w13 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 50650)) 65535) ≤ dimF (n.val + 50650) := by decide
private theorem a1_g0_w13 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 50650)) 16) ≤ dimF (n.val + 50650) := by decide
private theorem a0_g0_w14 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 50700)) 65535) ≤ dimF (n.val + 50700) := by decide
private theorem a1_g0_w14 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 50700)) 16) ≤ dimF (n.val + 50700) := by decide
private theorem a0_g0_w15 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 50750)) 65535) ≤ dimF (n.val + 50750) := by decide
private theorem a1_g0_w15 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 50750)) 16) ≤ dimF (n.val + 50750) := by decide
private theorem a0_g0_w16 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 50800)) 65535) ≤ dimF (n.val + 50800) := by decide
private theorem a1_g0_w16 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 50800)) 16) ≤ dimF (n.val + 50800) := by decide
private theorem a0_g0_w17 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 50850)) 65535) ≤ dimF (n.val + 50850) := by decide
private theorem a1_g0_w17 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 50850)) 16) ≤ dimF (n.val + 50850) := by decide
private theorem a0_g0_w18 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 50900)) 65535) ≤ dimF (n.val + 50900) := by decide
private theorem a1_g0_w18 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 50900)) 16) ≤ dimF (n.val + 50900) := by decide
private theorem a0_g0_w19 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 50950)) 65535) ≤ dimF (n.val + 50950) := by decide
private theorem a1_g0_w19 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 50950)) 16) ≤ dimF (n.val + 50950) := by decide
private theorem a0_g0_w20 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 51000)) 65535) ≤ dimF (n.val + 51000) := by decide
private theorem a1_g0_w20 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 51000)) 16) ≤ dimF (n.val + 51000) := by decide
private theorem a0_g0_w21 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 51050)) 65535) ≤ dimF (n.val + 51050) := by decide
private theorem a1_g0_w21 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 51050)) 16) ≤ dimF (n.val + 51050) := by decide
private theorem a0_g0_w22 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 51100)) 65535) ≤ dimF (n.val + 51100) := by decide
private theorem a1_g0_w22 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 51100)) 16) ≤ dimF (n.val + 51100) := by decide
private theorem a0_g0_w23 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 51150)) 65535) ≤ dimF (n.val + 51150) := by decide
private theorem a1_g0_w23 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 51150)) 16) ≤ dimF (n.val + 51150) := by decide
private theorem a0_g0_w24 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 51200)) 65535) ≤ dimF (n.val + 51200) := by decide
private theorem a1_g0_w24 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 51200)) 16) ≤ dimF (n.val + 51200) := by decide
private theorem a0_g0_w25 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 51250)) 65535) ≤ dimF (n.val + 51250) := by decide
private theorem a1_g0_w25 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 51250)) 16) ≤ dimF (n.val + 51250) := by decide
private theorem a0_g0_w26 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 51300)) 65535) ≤ dimF (n.val + 51300) := by decide
private theorem a1_g0_w26 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 51300)) 16) ≤ dimF (n.val + 51300) := by decide
private theorem a0_g0_w27 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 51350)) 65535) ≤ dimF (n.val + 51350) := by decide
private theorem a1_g0_w27 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 51350)) 16) ≤ dimF (n.val + 51350) := by decide
private theorem a0_g0_w28 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 51400)) 65535) ≤ dimF (n.val + 51400) := by decide
private theorem a1_g0_w28 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 51400)) 16) ≤ dimF (n.val + 51400) := by decide
private theorem a0_g0_w29 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 51450)) 65535) ≤ dimF (n.val + 51450) := by decide
private theorem a1_g0_w29 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 51450)) 16) ≤ dimF (n.val + 51450) := by decide
private theorem a0_g0_w30 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 51500)) 65535) ≤ dimF (n.val + 51500) := by decide
private theorem a1_g0_w30 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 51500)) 16) ≤ dimF (n.val + 51500) := by decide
private theorem a0_g0_w31 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 51550)) 65535) ≤ dimF (n.val + 51550) := by decide
private theorem a1_g0_w31 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 51550)) 16) ≤ dimF (n.val + 51550) := by decide
private theorem a0_g0_w32 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 51600)) 65535) ≤ dimF (n.val + 51600) := by decide
private theorem a1_g0_w32 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 51600)) 16) ≤ dimF (n.val + 51600) := by decide
private theorem a0_g0_w33 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 51650)) 65535) ≤ dimF (n.val + 51650) := by decide
private theorem a1_g0_w33 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 51650)) 16) ≤ dimF (n.val + 51650) := by decide
private theorem a0_g0_w34 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 51700)) 65535) ≤ dimF (n.val + 51700) := by decide
private theorem a1_g0_w34 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 51700)) 16) ≤ dimF (n.val + 51700) := by decide
private theorem a0_g0_w35 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 51750)) 65535) ≤ dimF (n.val + 51750) := by decide
private theorem a1_g0_w35 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 51750)) 16) ≤ dimF (n.val + 51750) := by decide
private theorem a0_g0_w36 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 51800)) 65535) ≤ dimF (n.val + 51800) := by decide
private theorem a1_g0_w36 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 51800)) 16) ≤ dimF (n.val + 51800) := by decide
private theorem a0_g0_w37 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 51850)) 65535) ≤ dimF (n.val + 51850) := by decide
private theorem a1_g0_w37 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 51850)) 16) ≤ dimF (n.val + 51850) := by decide
private theorem a0_g0_w38 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 51900)) 65535) ≤ dimF (n.val + 51900) := by decide
private theorem a1_g0_w38 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 51900)) 16) ≤ dimF (n.val + 51900) := by decide
private theorem a0_g0_w39 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 51950)) 65535) ≤ dimF (n.val + 51950) := by decide
private theorem a1_g0_w39 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 51950)) 16) ≤ dimF (n.val + 51950) := by decide
private theorem a0_g0_w40 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 52000)) 65535) ≤ dimF (n.val + 52000) := by decide
private theorem a1_g0_w40 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 52000)) 16) ≤ dimF (n.val + 52000) := by decide
private theorem a0_g0_w41 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 52050)) 65535) ≤ dimF (n.val + 52050) := by decide
private theorem a1_g0_w41 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 52050)) 16) ≤ dimF (n.val + 52050) := by decide
private theorem a0_g0_w42 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 52100)) 65535) ≤ dimF (n.val + 52100) := by decide
private theorem a1_g0_w42 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 52100)) 16) ≤ dimF (n.val + 52100) := by decide
private theorem a0_g0_w43 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 52150)) 65535) ≤ dimF (n.val + 52150) := by decide
private theorem a1_g0_w43 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 52150)) 16) ≤ dimF (n.val + 52150) := by decide
private theorem a0_g0_w44 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 52200)) 65535) ≤ dimF (n.val + 52200) := by decide
private theorem a1_g0_w44 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 52200)) 16) ≤ dimF (n.val + 52200) := by decide
private theorem a0_g0_w45 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 52250)) 65535) ≤ dimF (n.val + 52250) := by decide
private theorem a1_g0_w45 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 52250)) 16) ≤ dimF (n.val + 52250) := by decide
private theorem a0_g0_w46 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 52300)) 65535) ≤ dimF (n.val + 52300) := by decide
private theorem a1_g0_w46 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 52300)) 16) ≤ dimF (n.val + 52300) := by decide
private theorem a0_g0_w47 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 52350)) 65535) ≤ dimF (n.val + 52350) := by decide
private theorem a1_g0_w47 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 52350)) 16) ≤ dimF (n.val + 52350) := by decide
private theorem a0_g0_w48 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 52400)) 65535) ≤ dimF (n.val + 52400) := by decide
private theorem a1_g0_w48 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 52400)) 16) ≤ dimF (n.val + 52400) := by decide
private theorem a0_g0_w49 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 52450)) 65535) ≤ dimF (n.val + 52450) := by decide
private theorem a1_g0_w49 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 52450)) 16) ≤ dimF (n.val + 52450) := by decide

private theorem pair_g0 (n : ℕ) (hlo : 50000 ≤ n) (hhi : n < 52500) :
    dimF (Nat.land (argF n) 65535) ≤ dimF n ∧
    dimF (Nat.shiftRight (argF n) 16) ≤ dimF n := by
  by_cases h0 : n < 50050
  · have hr : n - 50000 < 50 := by omega
    have heq : n = (n - 50000) + 50000 := by omega
    rw [heq]
    exact ⟨a0_g0_w0 ⟨n - 50000, hr⟩, a1_g0_w0 ⟨n - 50000, hr⟩⟩
  · by_cases h1 : n < 50100
    · have hr : n - 50050 < 50 := by omega
      have heq : n = (n - 50050) + 50050 := by omega
      rw [heq]
      exact ⟨a0_g0_w1 ⟨n - 50050, hr⟩, a1_g0_w1 ⟨n - 50050, hr⟩⟩
    · by_cases h2 : n < 50150
      · have hr : n - 50100 < 50 := by omega
        have heq : n = (n - 50100) + 50100 := by omega
        rw [heq]
        exact ⟨a0_g0_w2 ⟨n - 50100, hr⟩, a1_g0_w2 ⟨n - 50100, hr⟩⟩
      · by_cases h3 : n < 50200
        · have hr : n - 50150 < 50 := by omega
          have heq : n = (n - 50150) + 50150 := by omega
          rw [heq]
          exact ⟨a0_g0_w3 ⟨n - 50150, hr⟩, a1_g0_w3 ⟨n - 50150, hr⟩⟩
        · by_cases h4 : n < 50250
          · have hr : n - 50200 < 50 := by omega
            have heq : n = (n - 50200) + 50200 := by omega
            rw [heq]
            exact ⟨a0_g0_w4 ⟨n - 50200, hr⟩, a1_g0_w4 ⟨n - 50200, hr⟩⟩
          · by_cases h5 : n < 50300
            · have hr : n - 50250 < 50 := by omega
              have heq : n = (n - 50250) + 50250 := by omega
              rw [heq]
              exact ⟨a0_g0_w5 ⟨n - 50250, hr⟩, a1_g0_w5 ⟨n - 50250, hr⟩⟩
            · by_cases h6 : n < 50350
              · have hr : n - 50300 < 50 := by omega
                have heq : n = (n - 50300) + 50300 := by omega
                rw [heq]
                exact ⟨a0_g0_w6 ⟨n - 50300, hr⟩, a1_g0_w6 ⟨n - 50300, hr⟩⟩
              · by_cases h7 : n < 50400
                · have hr : n - 50350 < 50 := by omega
                  have heq : n = (n - 50350) + 50350 := by omega
                  rw [heq]
                  exact ⟨a0_g0_w7 ⟨n - 50350, hr⟩, a1_g0_w7 ⟨n - 50350, hr⟩⟩
                · by_cases h8 : n < 50450
                  · have hr : n - 50400 < 50 := by omega
                    have heq : n = (n - 50400) + 50400 := by omega
                    rw [heq]
                    exact ⟨a0_g0_w8 ⟨n - 50400, hr⟩, a1_g0_w8 ⟨n - 50400, hr⟩⟩
                  · by_cases h9 : n < 50500
                    · have hr : n - 50450 < 50 := by omega
                      have heq : n = (n - 50450) + 50450 := by omega
                      rw [heq]
                      exact ⟨a0_g0_w9 ⟨n - 50450, hr⟩, a1_g0_w9 ⟨n - 50450, hr⟩⟩
                    · by_cases h10 : n < 50550
                      · have hr : n - 50500 < 50 := by omega
                        have heq : n = (n - 50500) + 50500 := by omega
                        rw [heq]
                        exact ⟨a0_g0_w10 ⟨n - 50500, hr⟩, a1_g0_w10 ⟨n - 50500, hr⟩⟩
                      · by_cases h11 : n < 50600
                        · have hr : n - 50550 < 50 := by omega
                          have heq : n = (n - 50550) + 50550 := by omega
                          rw [heq]
                          exact ⟨a0_g0_w11 ⟨n - 50550, hr⟩, a1_g0_w11 ⟨n - 50550, hr⟩⟩
                        · by_cases h12 : n < 50650
                          · have hr : n - 50600 < 50 := by omega
                            have heq : n = (n - 50600) + 50600 := by omega
                            rw [heq]
                            exact ⟨a0_g0_w12 ⟨n - 50600, hr⟩, a1_g0_w12 ⟨n - 50600, hr⟩⟩
                          · by_cases h13 : n < 50700
                            · have hr : n - 50650 < 50 := by omega
                              have heq : n = (n - 50650) + 50650 := by omega
                              rw [heq]
                              exact ⟨a0_g0_w13 ⟨n - 50650, hr⟩, a1_g0_w13 ⟨n - 50650, hr⟩⟩
                            · by_cases h14 : n < 50750
                              · have hr : n - 50700 < 50 := by omega
                                have heq : n = (n - 50700) + 50700 := by omega
                                rw [heq]
                                exact ⟨a0_g0_w14 ⟨n - 50700, hr⟩, a1_g0_w14 ⟨n - 50700, hr⟩⟩
                              · by_cases h15 : n < 50800
                                · have hr : n - 50750 < 50 := by omega
                                  have heq : n = (n - 50750) + 50750 := by omega
                                  rw [heq]
                                  exact ⟨a0_g0_w15 ⟨n - 50750, hr⟩, a1_g0_w15 ⟨n - 50750, hr⟩⟩
                                · by_cases h16 : n < 50850
                                  · have hr : n - 50800 < 50 := by omega
                                    have heq : n = (n - 50800) + 50800 := by omega
                                    rw [heq]
                                    exact ⟨a0_g0_w16 ⟨n - 50800, hr⟩, a1_g0_w16 ⟨n - 50800, hr⟩⟩
                                  · by_cases h17 : n < 50900
                                    · have hr : n - 50850 < 50 := by omega
                                      have heq : n = (n - 50850) + 50850 := by omega
                                      rw [heq]
                                      exact ⟨a0_g0_w17 ⟨n - 50850, hr⟩, a1_g0_w17 ⟨n - 50850, hr⟩⟩
                                    · by_cases h18 : n < 50950
                                      · have hr : n - 50900 < 50 := by omega
                                        have heq : n = (n - 50900) + 50900 := by omega
                                        rw [heq]
                                        exact ⟨a0_g0_w18 ⟨n - 50900, hr⟩, a1_g0_w18 ⟨n - 50900, hr⟩⟩
                                      · by_cases h19 : n < 51000
                                        · have hr : n - 50950 < 50 := by omega
                                          have heq : n = (n - 50950) + 50950 := by omega
                                          rw [heq]
                                          exact ⟨a0_g0_w19 ⟨n - 50950, hr⟩, a1_g0_w19 ⟨n - 50950, hr⟩⟩
                                        · by_cases h20 : n < 51050
                                          · have hr : n - 51000 < 50 := by omega
                                            have heq : n = (n - 51000) + 51000 := by omega
                                            rw [heq]
                                            exact ⟨a0_g0_w20 ⟨n - 51000, hr⟩, a1_g0_w20 ⟨n - 51000, hr⟩⟩
                                          · by_cases h21 : n < 51100
                                            · have hr : n - 51050 < 50 := by omega
                                              have heq : n = (n - 51050) + 51050 := by omega
                                              rw [heq]
                                              exact ⟨a0_g0_w21 ⟨n - 51050, hr⟩, a1_g0_w21 ⟨n - 51050, hr⟩⟩
                                            · by_cases h22 : n < 51150
                                              · have hr : n - 51100 < 50 := by omega
                                                have heq : n = (n - 51100) + 51100 := by omega
                                                rw [heq]
                                                exact ⟨a0_g0_w22 ⟨n - 51100, hr⟩, a1_g0_w22 ⟨n - 51100, hr⟩⟩
                                              · by_cases h23 : n < 51200
                                                · have hr : n - 51150 < 50 := by omega
                                                  have heq : n = (n - 51150) + 51150 := by omega
                                                  rw [heq]
                                                  exact ⟨a0_g0_w23 ⟨n - 51150, hr⟩, a1_g0_w23 ⟨n - 51150, hr⟩⟩
                                                · by_cases h24 : n < 51250
                                                  · have hr : n - 51200 < 50 := by omega
                                                    have heq : n = (n - 51200) + 51200 := by omega
                                                    rw [heq]
                                                    exact ⟨a0_g0_w24 ⟨n - 51200, hr⟩, a1_g0_w24 ⟨n - 51200, hr⟩⟩
                                                  · by_cases h25 : n < 51300
                                                    · have hr : n - 51250 < 50 := by omega
                                                      have heq : n = (n - 51250) + 51250 := by omega
                                                      rw [heq]
                                                      exact ⟨a0_g0_w25 ⟨n - 51250, hr⟩, a1_g0_w25 ⟨n - 51250, hr⟩⟩
                                                    · by_cases h26 : n < 51350
                                                      · have hr : n - 51300 < 50 := by omega
                                                        have heq : n = (n - 51300) + 51300 := by omega
                                                        rw [heq]
                                                        exact ⟨a0_g0_w26 ⟨n - 51300, hr⟩, a1_g0_w26 ⟨n - 51300, hr⟩⟩
                                                      · by_cases h27 : n < 51400
                                                        · have hr : n - 51350 < 50 := by omega
                                                          have heq : n = (n - 51350) + 51350 := by omega
                                                          rw [heq]
                                                          exact ⟨a0_g0_w27 ⟨n - 51350, hr⟩, a1_g0_w27 ⟨n - 51350, hr⟩⟩
                                                        · by_cases h28 : n < 51450
                                                          · have hr : n - 51400 < 50 := by omega
                                                            have heq : n = (n - 51400) + 51400 := by omega
                                                            rw [heq]
                                                            exact ⟨a0_g0_w28 ⟨n - 51400, hr⟩, a1_g0_w28 ⟨n - 51400, hr⟩⟩
                                                          · by_cases h29 : n < 51500
                                                            · have hr : n - 51450 < 50 := by omega
                                                              have heq : n = (n - 51450) + 51450 := by omega
                                                              rw [heq]
                                                              exact ⟨a0_g0_w29 ⟨n - 51450, hr⟩, a1_g0_w29 ⟨n - 51450, hr⟩⟩
                                                            · by_cases h30 : n < 51550
                                                              · have hr : n - 51500 < 50 := by omega
                                                                have heq : n = (n - 51500) + 51500 := by omega
                                                                rw [heq]
                                                                exact ⟨a0_g0_w30 ⟨n - 51500, hr⟩, a1_g0_w30 ⟨n - 51500, hr⟩⟩
                                                              · by_cases h31 : n < 51600
                                                                · have hr : n - 51550 < 50 := by omega
                                                                  have heq : n = (n - 51550) + 51550 := by omega
                                                                  rw [heq]
                                                                  exact ⟨a0_g0_w31 ⟨n - 51550, hr⟩, a1_g0_w31 ⟨n - 51550, hr⟩⟩
                                                                · by_cases h32 : n < 51650
                                                                  · have hr : n - 51600 < 50 := by omega
                                                                    have heq : n = (n - 51600) + 51600 := by omega
                                                                    rw [heq]
                                                                    exact ⟨a0_g0_w32 ⟨n - 51600, hr⟩, a1_g0_w32 ⟨n - 51600, hr⟩⟩
                                                                  · by_cases h33 : n < 51700
                                                                    · have hr : n - 51650 < 50 := by omega
                                                                      have heq : n = (n - 51650) + 51650 := by omega
                                                                      rw [heq]
                                                                      exact ⟨a0_g0_w33 ⟨n - 51650, hr⟩, a1_g0_w33 ⟨n - 51650, hr⟩⟩
                                                                    · by_cases h34 : n < 51750
                                                                      · have hr : n - 51700 < 50 := by omega
                                                                        have heq : n = (n - 51700) + 51700 := by omega
                                                                        rw [heq]
                                                                        exact ⟨a0_g0_w34 ⟨n - 51700, hr⟩, a1_g0_w34 ⟨n - 51700, hr⟩⟩
                                                                      · by_cases h35 : n < 51800
                                                                        · have hr : n - 51750 < 50 := by omega
                                                                          have heq : n = (n - 51750) + 51750 := by omega
                                                                          rw [heq]
                                                                          exact ⟨a0_g0_w35 ⟨n - 51750, hr⟩, a1_g0_w35 ⟨n - 51750, hr⟩⟩
                                                                        · by_cases h36 : n < 51850
                                                                          · have hr : n - 51800 < 50 := by omega
                                                                            have heq : n = (n - 51800) + 51800 := by omega
                                                                            rw [heq]
                                                                            exact ⟨a0_g0_w36 ⟨n - 51800, hr⟩, a1_g0_w36 ⟨n - 51800, hr⟩⟩
                                                                          · by_cases h37 : n < 51900
                                                                            · have hr : n - 51850 < 50 := by omega
                                                                              have heq : n = (n - 51850) + 51850 := by omega
                                                                              rw [heq]
                                                                              exact ⟨a0_g0_w37 ⟨n - 51850, hr⟩, a1_g0_w37 ⟨n - 51850, hr⟩⟩
                                                                            · by_cases h38 : n < 51950
                                                                              · have hr : n - 51900 < 50 := by omega
                                                                                have heq : n = (n - 51900) + 51900 := by omega
                                                                                rw [heq]
                                                                                exact ⟨a0_g0_w38 ⟨n - 51900, hr⟩, a1_g0_w38 ⟨n - 51900, hr⟩⟩
                                                                              · by_cases h39 : n < 52000
                                                                                · have hr : n - 51950 < 50 := by omega
                                                                                  have heq : n = (n - 51950) + 51950 := by omega
                                                                                  rw [heq]
                                                                                  exact ⟨a0_g0_w39 ⟨n - 51950, hr⟩, a1_g0_w39 ⟨n - 51950, hr⟩⟩
                                                                                · by_cases h40 : n < 52050
                                                                                  · have hr : n - 52000 < 50 := by omega
                                                                                    have heq : n = (n - 52000) + 52000 := by omega
                                                                                    rw [heq]
                                                                                    exact ⟨a0_g0_w40 ⟨n - 52000, hr⟩, a1_g0_w40 ⟨n - 52000, hr⟩⟩
                                                                                  · by_cases h41 : n < 52100
                                                                                    · have hr : n - 52050 < 50 := by omega
                                                                                      have heq : n = (n - 52050) + 52050 := by omega
                                                                                      rw [heq]
                                                                                      exact ⟨a0_g0_w41 ⟨n - 52050, hr⟩, a1_g0_w41 ⟨n - 52050, hr⟩⟩
                                                                                    · by_cases h42 : n < 52150
                                                                                      · have hr : n - 52100 < 50 := by omega
                                                                                        have heq : n = (n - 52100) + 52100 := by omega
                                                                                        rw [heq]
                                                                                        exact ⟨a0_g0_w42 ⟨n - 52100, hr⟩, a1_g0_w42 ⟨n - 52100, hr⟩⟩
                                                                                      · by_cases h43 : n < 52200
                                                                                        · have hr : n - 52150 < 50 := by omega
                                                                                          have heq : n = (n - 52150) + 52150 := by omega
                                                                                          rw [heq]
                                                                                          exact ⟨a0_g0_w43 ⟨n - 52150, hr⟩, a1_g0_w43 ⟨n - 52150, hr⟩⟩
                                                                                        · by_cases h44 : n < 52250
                                                                                          · have hr : n - 52200 < 50 := by omega
                                                                                            have heq : n = (n - 52200) + 52200 := by omega
                                                                                            rw [heq]
                                                                                            exact ⟨a0_g0_w44 ⟨n - 52200, hr⟩, a1_g0_w44 ⟨n - 52200, hr⟩⟩
                                                                                          · by_cases h45 : n < 52300
                                                                                            · have hr : n - 52250 < 50 := by omega
                                                                                              have heq : n = (n - 52250) + 52250 := by omega
                                                                                              rw [heq]
                                                                                              exact ⟨a0_g0_w45 ⟨n - 52250, hr⟩, a1_g0_w45 ⟨n - 52250, hr⟩⟩
                                                                                            · by_cases h46 : n < 52350
                                                                                              · have hr : n - 52300 < 50 := by omega
                                                                                                have heq : n = (n - 52300) + 52300 := by omega
                                                                                                rw [heq]
                                                                                                exact ⟨a0_g0_w46 ⟨n - 52300, hr⟩, a1_g0_w46 ⟨n - 52300, hr⟩⟩
                                                                                              · by_cases h47 : n < 52400
                                                                                                · have hr : n - 52350 < 50 := by omega
                                                                                                  have heq : n = (n - 52350) + 52350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact ⟨a0_g0_w47 ⟨n - 52350, hr⟩, a1_g0_w47 ⟨n - 52350, hr⟩⟩
                                                                                                · by_cases h48 : n < 52450
                                                                                                  · have hr : n - 52400 < 50 := by omega
                                                                                                    have heq : n = (n - 52400) + 52400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact ⟨a0_g0_w48 ⟨n - 52400, hr⟩, a1_g0_w48 ⟨n - 52400, hr⟩⟩
                                                                                                  · have hr : n - 52450 < 50 := by omega
                                                                                                    have heq : n = (n - 52450) + 52450 := by omega
                                                                                                    rw [heq]
                                                                                                    exact ⟨a0_g0_w49 ⟨n - 52450, hr⟩, a1_g0_w49 ⟨n - 52450, hr⟩⟩

private theorem a0_g1_w0 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 52500)) 65535) ≤ dimF (n.val + 52500) := by decide
private theorem a1_g1_w0 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 52500)) 16) ≤ dimF (n.val + 52500) := by decide
private theorem a0_g1_w1 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 52550)) 65535) ≤ dimF (n.val + 52550) := by decide
private theorem a1_g1_w1 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 52550)) 16) ≤ dimF (n.val + 52550) := by decide
private theorem a0_g1_w2 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 52600)) 65535) ≤ dimF (n.val + 52600) := by decide
private theorem a1_g1_w2 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 52600)) 16) ≤ dimF (n.val + 52600) := by decide
private theorem a0_g1_w3 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 52650)) 65535) ≤ dimF (n.val + 52650) := by decide
private theorem a1_g1_w3 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 52650)) 16) ≤ dimF (n.val + 52650) := by decide
private theorem a0_g1_w4 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 52700)) 65535) ≤ dimF (n.val + 52700) := by decide
private theorem a1_g1_w4 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 52700)) 16) ≤ dimF (n.val + 52700) := by decide
private theorem a0_g1_w5 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 52750)) 65535) ≤ dimF (n.val + 52750) := by decide
private theorem a1_g1_w5 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 52750)) 16) ≤ dimF (n.val + 52750) := by decide
private theorem a0_g1_w6 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 52800)) 65535) ≤ dimF (n.val + 52800) := by decide
private theorem a1_g1_w6 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 52800)) 16) ≤ dimF (n.val + 52800) := by decide
private theorem a0_g1_w7 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 52850)) 65535) ≤ dimF (n.val + 52850) := by decide
private theorem a1_g1_w7 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 52850)) 16) ≤ dimF (n.val + 52850) := by decide
private theorem a0_g1_w8 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 52900)) 65535) ≤ dimF (n.val + 52900) := by decide
private theorem a1_g1_w8 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 52900)) 16) ≤ dimF (n.val + 52900) := by decide
private theorem a0_g1_w9 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 52950)) 65535) ≤ dimF (n.val + 52950) := by decide
private theorem a1_g1_w9 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 52950)) 16) ≤ dimF (n.val + 52950) := by decide
private theorem a0_g1_w10 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 53000)) 65535) ≤ dimF (n.val + 53000) := by decide
private theorem a1_g1_w10 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 53000)) 16) ≤ dimF (n.val + 53000) := by decide
private theorem a0_g1_w11 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 53050)) 65535) ≤ dimF (n.val + 53050) := by decide
private theorem a1_g1_w11 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 53050)) 16) ≤ dimF (n.val + 53050) := by decide
private theorem a0_g1_w12 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 53100)) 65535) ≤ dimF (n.val + 53100) := by decide
private theorem a1_g1_w12 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 53100)) 16) ≤ dimF (n.val + 53100) := by decide
private theorem a0_g1_w13 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 53150)) 65535) ≤ dimF (n.val + 53150) := by decide
private theorem a1_g1_w13 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 53150)) 16) ≤ dimF (n.val + 53150) := by decide
private theorem a0_g1_w14 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 53200)) 65535) ≤ dimF (n.val + 53200) := by decide
private theorem a1_g1_w14 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 53200)) 16) ≤ dimF (n.val + 53200) := by decide
private theorem a0_g1_w15 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 53250)) 65535) ≤ dimF (n.val + 53250) := by decide
private theorem a1_g1_w15 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 53250)) 16) ≤ dimF (n.val + 53250) := by decide
private theorem a0_g1_w16 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 53300)) 65535) ≤ dimF (n.val + 53300) := by decide
private theorem a1_g1_w16 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 53300)) 16) ≤ dimF (n.val + 53300) := by decide
private theorem a0_g1_w17 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 53350)) 65535) ≤ dimF (n.val + 53350) := by decide
private theorem a1_g1_w17 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 53350)) 16) ≤ dimF (n.val + 53350) := by decide
private theorem a0_g1_w18 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 53400)) 65535) ≤ dimF (n.val + 53400) := by decide
private theorem a1_g1_w18 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 53400)) 16) ≤ dimF (n.val + 53400) := by decide
private theorem a0_g1_w19 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 53450)) 65535) ≤ dimF (n.val + 53450) := by decide
private theorem a1_g1_w19 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 53450)) 16) ≤ dimF (n.val + 53450) := by decide
private theorem a0_g1_w20 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 53500)) 65535) ≤ dimF (n.val + 53500) := by decide
private theorem a1_g1_w20 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 53500)) 16) ≤ dimF (n.val + 53500) := by decide
private theorem a0_g1_w21 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 53550)) 65535) ≤ dimF (n.val + 53550) := by decide
private theorem a1_g1_w21 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 53550)) 16) ≤ dimF (n.val + 53550) := by decide
private theorem a0_g1_w22 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 53600)) 65535) ≤ dimF (n.val + 53600) := by decide
private theorem a1_g1_w22 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 53600)) 16) ≤ dimF (n.val + 53600) := by decide
private theorem a0_g1_w23 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 53650)) 65535) ≤ dimF (n.val + 53650) := by decide
private theorem a1_g1_w23 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 53650)) 16) ≤ dimF (n.val + 53650) := by decide
private theorem a0_g1_w24 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 53700)) 65535) ≤ dimF (n.val + 53700) := by decide
private theorem a1_g1_w24 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 53700)) 16) ≤ dimF (n.val + 53700) := by decide
private theorem a0_g1_w25 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 53750)) 65535) ≤ dimF (n.val + 53750) := by decide
private theorem a1_g1_w25 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 53750)) 16) ≤ dimF (n.val + 53750) := by decide
private theorem a0_g1_w26 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 53800)) 65535) ≤ dimF (n.val + 53800) := by decide
private theorem a1_g1_w26 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 53800)) 16) ≤ dimF (n.val + 53800) := by decide
private theorem a0_g1_w27 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 53850)) 65535) ≤ dimF (n.val + 53850) := by decide
private theorem a1_g1_w27 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 53850)) 16) ≤ dimF (n.val + 53850) := by decide
private theorem a0_g1_w28 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 53900)) 65535) ≤ dimF (n.val + 53900) := by decide
private theorem a1_g1_w28 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 53900)) 16) ≤ dimF (n.val + 53900) := by decide
private theorem a0_g1_w29 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 53950)) 65535) ≤ dimF (n.val + 53950) := by decide
private theorem a1_g1_w29 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 53950)) 16) ≤ dimF (n.val + 53950) := by decide
private theorem a0_g1_w30 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 54000)) 65535) ≤ dimF (n.val + 54000) := by decide
private theorem a1_g1_w30 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 54000)) 16) ≤ dimF (n.val + 54000) := by decide
private theorem a0_g1_w31 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 54050)) 65535) ≤ dimF (n.val + 54050) := by decide
private theorem a1_g1_w31 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 54050)) 16) ≤ dimF (n.val + 54050) := by decide
private theorem a0_g1_w32 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 54100)) 65535) ≤ dimF (n.val + 54100) := by decide
private theorem a1_g1_w32 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 54100)) 16) ≤ dimF (n.val + 54100) := by decide
private theorem a0_g1_w33 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 54150)) 65535) ≤ dimF (n.val + 54150) := by decide
private theorem a1_g1_w33 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 54150)) 16) ≤ dimF (n.val + 54150) := by decide
private theorem a0_g1_w34 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 54200)) 65535) ≤ dimF (n.val + 54200) := by decide
private theorem a1_g1_w34 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 54200)) 16) ≤ dimF (n.val + 54200) := by decide
private theorem a0_g1_w35 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 54250)) 65535) ≤ dimF (n.val + 54250) := by decide
private theorem a1_g1_w35 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 54250)) 16) ≤ dimF (n.val + 54250) := by decide
private theorem a0_g1_w36 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 54300)) 65535) ≤ dimF (n.val + 54300) := by decide
private theorem a1_g1_w36 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 54300)) 16) ≤ dimF (n.val + 54300) := by decide
private theorem a0_g1_w37 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 54350)) 65535) ≤ dimF (n.val + 54350) := by decide
private theorem a1_g1_w37 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 54350)) 16) ≤ dimF (n.val + 54350) := by decide
private theorem a0_g1_w38 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 54400)) 65535) ≤ dimF (n.val + 54400) := by decide
private theorem a1_g1_w38 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 54400)) 16) ≤ dimF (n.val + 54400) := by decide
private theorem a0_g1_w39 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 54450)) 65535) ≤ dimF (n.val + 54450) := by decide
private theorem a1_g1_w39 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 54450)) 16) ≤ dimF (n.val + 54450) := by decide
private theorem a0_g1_w40 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 54500)) 65535) ≤ dimF (n.val + 54500) := by decide
private theorem a1_g1_w40 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 54500)) 16) ≤ dimF (n.val + 54500) := by decide
private theorem a0_g1_w41 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 54550)) 65535) ≤ dimF (n.val + 54550) := by decide
private theorem a1_g1_w41 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 54550)) 16) ≤ dimF (n.val + 54550) := by decide
private theorem a0_g1_w42 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 54600)) 65535) ≤ dimF (n.val + 54600) := by decide
private theorem a1_g1_w42 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 54600)) 16) ≤ dimF (n.val + 54600) := by decide
private theorem a0_g1_w43 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 54650)) 65535) ≤ dimF (n.val + 54650) := by decide
private theorem a1_g1_w43 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 54650)) 16) ≤ dimF (n.val + 54650) := by decide
private theorem a0_g1_w44 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 54700)) 65535) ≤ dimF (n.val + 54700) := by decide
private theorem a1_g1_w44 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 54700)) 16) ≤ dimF (n.val + 54700) := by decide
private theorem a0_g1_w45 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 54750)) 65535) ≤ dimF (n.val + 54750) := by decide
private theorem a1_g1_w45 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 54750)) 16) ≤ dimF (n.val + 54750) := by decide
private theorem a0_g1_w46 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 54800)) 65535) ≤ dimF (n.val + 54800) := by decide
private theorem a1_g1_w46 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 54800)) 16) ≤ dimF (n.val + 54800) := by decide
private theorem a0_g1_w47 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 54850)) 65535) ≤ dimF (n.val + 54850) := by decide
private theorem a1_g1_w47 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 54850)) 16) ≤ dimF (n.val + 54850) := by decide
private theorem a0_g1_w48 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 54900)) 65535) ≤ dimF (n.val + 54900) := by decide
private theorem a1_g1_w48 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 54900)) 16) ≤ dimF (n.val + 54900) := by decide
private theorem a0_g1_w49 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 54950)) 65535) ≤ dimF (n.val + 54950) := by decide
private theorem a1_g1_w49 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 54950)) 16) ≤ dimF (n.val + 54950) := by decide

private theorem pair_g1 (n : ℕ) (hlo : 52500 ≤ n) (hhi : n < 55000) :
    dimF (Nat.land (argF n) 65535) ≤ dimF n ∧
    dimF (Nat.shiftRight (argF n) 16) ≤ dimF n := by
  by_cases h0 : n < 52550
  · have hr : n - 52500 < 50 := by omega
    have heq : n = (n - 52500) + 52500 := by omega
    rw [heq]
    exact ⟨a0_g1_w0 ⟨n - 52500, hr⟩, a1_g1_w0 ⟨n - 52500, hr⟩⟩
  · by_cases h1 : n < 52600
    · have hr : n - 52550 < 50 := by omega
      have heq : n = (n - 52550) + 52550 := by omega
      rw [heq]
      exact ⟨a0_g1_w1 ⟨n - 52550, hr⟩, a1_g1_w1 ⟨n - 52550, hr⟩⟩
    · by_cases h2 : n < 52650
      · have hr : n - 52600 < 50 := by omega
        have heq : n = (n - 52600) + 52600 := by omega
        rw [heq]
        exact ⟨a0_g1_w2 ⟨n - 52600, hr⟩, a1_g1_w2 ⟨n - 52600, hr⟩⟩
      · by_cases h3 : n < 52700
        · have hr : n - 52650 < 50 := by omega
          have heq : n = (n - 52650) + 52650 := by omega
          rw [heq]
          exact ⟨a0_g1_w3 ⟨n - 52650, hr⟩, a1_g1_w3 ⟨n - 52650, hr⟩⟩
        · by_cases h4 : n < 52750
          · have hr : n - 52700 < 50 := by omega
            have heq : n = (n - 52700) + 52700 := by omega
            rw [heq]
            exact ⟨a0_g1_w4 ⟨n - 52700, hr⟩, a1_g1_w4 ⟨n - 52700, hr⟩⟩
          · by_cases h5 : n < 52800
            · have hr : n - 52750 < 50 := by omega
              have heq : n = (n - 52750) + 52750 := by omega
              rw [heq]
              exact ⟨a0_g1_w5 ⟨n - 52750, hr⟩, a1_g1_w5 ⟨n - 52750, hr⟩⟩
            · by_cases h6 : n < 52850
              · have hr : n - 52800 < 50 := by omega
                have heq : n = (n - 52800) + 52800 := by omega
                rw [heq]
                exact ⟨a0_g1_w6 ⟨n - 52800, hr⟩, a1_g1_w6 ⟨n - 52800, hr⟩⟩
              · by_cases h7 : n < 52900
                · have hr : n - 52850 < 50 := by omega
                  have heq : n = (n - 52850) + 52850 := by omega
                  rw [heq]
                  exact ⟨a0_g1_w7 ⟨n - 52850, hr⟩, a1_g1_w7 ⟨n - 52850, hr⟩⟩
                · by_cases h8 : n < 52950
                  · have hr : n - 52900 < 50 := by omega
                    have heq : n = (n - 52900) + 52900 := by omega
                    rw [heq]
                    exact ⟨a0_g1_w8 ⟨n - 52900, hr⟩, a1_g1_w8 ⟨n - 52900, hr⟩⟩
                  · by_cases h9 : n < 53000
                    · have hr : n - 52950 < 50 := by omega
                      have heq : n = (n - 52950) + 52950 := by omega
                      rw [heq]
                      exact ⟨a0_g1_w9 ⟨n - 52950, hr⟩, a1_g1_w9 ⟨n - 52950, hr⟩⟩
                    · by_cases h10 : n < 53050
                      · have hr : n - 53000 < 50 := by omega
                        have heq : n = (n - 53000) + 53000 := by omega
                        rw [heq]
                        exact ⟨a0_g1_w10 ⟨n - 53000, hr⟩, a1_g1_w10 ⟨n - 53000, hr⟩⟩
                      · by_cases h11 : n < 53100
                        · have hr : n - 53050 < 50 := by omega
                          have heq : n = (n - 53050) + 53050 := by omega
                          rw [heq]
                          exact ⟨a0_g1_w11 ⟨n - 53050, hr⟩, a1_g1_w11 ⟨n - 53050, hr⟩⟩
                        · by_cases h12 : n < 53150
                          · have hr : n - 53100 < 50 := by omega
                            have heq : n = (n - 53100) + 53100 := by omega
                            rw [heq]
                            exact ⟨a0_g1_w12 ⟨n - 53100, hr⟩, a1_g1_w12 ⟨n - 53100, hr⟩⟩
                          · by_cases h13 : n < 53200
                            · have hr : n - 53150 < 50 := by omega
                              have heq : n = (n - 53150) + 53150 := by omega
                              rw [heq]
                              exact ⟨a0_g1_w13 ⟨n - 53150, hr⟩, a1_g1_w13 ⟨n - 53150, hr⟩⟩
                            · by_cases h14 : n < 53250
                              · have hr : n - 53200 < 50 := by omega
                                have heq : n = (n - 53200) + 53200 := by omega
                                rw [heq]
                                exact ⟨a0_g1_w14 ⟨n - 53200, hr⟩, a1_g1_w14 ⟨n - 53200, hr⟩⟩
                              · by_cases h15 : n < 53300
                                · have hr : n - 53250 < 50 := by omega
                                  have heq : n = (n - 53250) + 53250 := by omega
                                  rw [heq]
                                  exact ⟨a0_g1_w15 ⟨n - 53250, hr⟩, a1_g1_w15 ⟨n - 53250, hr⟩⟩
                                · by_cases h16 : n < 53350
                                  · have hr : n - 53300 < 50 := by omega
                                    have heq : n = (n - 53300) + 53300 := by omega
                                    rw [heq]
                                    exact ⟨a0_g1_w16 ⟨n - 53300, hr⟩, a1_g1_w16 ⟨n - 53300, hr⟩⟩
                                  · by_cases h17 : n < 53400
                                    · have hr : n - 53350 < 50 := by omega
                                      have heq : n = (n - 53350) + 53350 := by omega
                                      rw [heq]
                                      exact ⟨a0_g1_w17 ⟨n - 53350, hr⟩, a1_g1_w17 ⟨n - 53350, hr⟩⟩
                                    · by_cases h18 : n < 53450
                                      · have hr : n - 53400 < 50 := by omega
                                        have heq : n = (n - 53400) + 53400 := by omega
                                        rw [heq]
                                        exact ⟨a0_g1_w18 ⟨n - 53400, hr⟩, a1_g1_w18 ⟨n - 53400, hr⟩⟩
                                      · by_cases h19 : n < 53500
                                        · have hr : n - 53450 < 50 := by omega
                                          have heq : n = (n - 53450) + 53450 := by omega
                                          rw [heq]
                                          exact ⟨a0_g1_w19 ⟨n - 53450, hr⟩, a1_g1_w19 ⟨n - 53450, hr⟩⟩
                                        · by_cases h20 : n < 53550
                                          · have hr : n - 53500 < 50 := by omega
                                            have heq : n = (n - 53500) + 53500 := by omega
                                            rw [heq]
                                            exact ⟨a0_g1_w20 ⟨n - 53500, hr⟩, a1_g1_w20 ⟨n - 53500, hr⟩⟩
                                          · by_cases h21 : n < 53600
                                            · have hr : n - 53550 < 50 := by omega
                                              have heq : n = (n - 53550) + 53550 := by omega
                                              rw [heq]
                                              exact ⟨a0_g1_w21 ⟨n - 53550, hr⟩, a1_g1_w21 ⟨n - 53550, hr⟩⟩
                                            · by_cases h22 : n < 53650
                                              · have hr : n - 53600 < 50 := by omega
                                                have heq : n = (n - 53600) + 53600 := by omega
                                                rw [heq]
                                                exact ⟨a0_g1_w22 ⟨n - 53600, hr⟩, a1_g1_w22 ⟨n - 53600, hr⟩⟩
                                              · by_cases h23 : n < 53700
                                                · have hr : n - 53650 < 50 := by omega
                                                  have heq : n = (n - 53650) + 53650 := by omega
                                                  rw [heq]
                                                  exact ⟨a0_g1_w23 ⟨n - 53650, hr⟩, a1_g1_w23 ⟨n - 53650, hr⟩⟩
                                                · by_cases h24 : n < 53750
                                                  · have hr : n - 53700 < 50 := by omega
                                                    have heq : n = (n - 53700) + 53700 := by omega
                                                    rw [heq]
                                                    exact ⟨a0_g1_w24 ⟨n - 53700, hr⟩, a1_g1_w24 ⟨n - 53700, hr⟩⟩
                                                  · by_cases h25 : n < 53800
                                                    · have hr : n - 53750 < 50 := by omega
                                                      have heq : n = (n - 53750) + 53750 := by omega
                                                      rw [heq]
                                                      exact ⟨a0_g1_w25 ⟨n - 53750, hr⟩, a1_g1_w25 ⟨n - 53750, hr⟩⟩
                                                    · by_cases h26 : n < 53850
                                                      · have hr : n - 53800 < 50 := by omega
                                                        have heq : n = (n - 53800) + 53800 := by omega
                                                        rw [heq]
                                                        exact ⟨a0_g1_w26 ⟨n - 53800, hr⟩, a1_g1_w26 ⟨n - 53800, hr⟩⟩
                                                      · by_cases h27 : n < 53900
                                                        · have hr : n - 53850 < 50 := by omega
                                                          have heq : n = (n - 53850) + 53850 := by omega
                                                          rw [heq]
                                                          exact ⟨a0_g1_w27 ⟨n - 53850, hr⟩, a1_g1_w27 ⟨n - 53850, hr⟩⟩
                                                        · by_cases h28 : n < 53950
                                                          · have hr : n - 53900 < 50 := by omega
                                                            have heq : n = (n - 53900) + 53900 := by omega
                                                            rw [heq]
                                                            exact ⟨a0_g1_w28 ⟨n - 53900, hr⟩, a1_g1_w28 ⟨n - 53900, hr⟩⟩
                                                          · by_cases h29 : n < 54000
                                                            · have hr : n - 53950 < 50 := by omega
                                                              have heq : n = (n - 53950) + 53950 := by omega
                                                              rw [heq]
                                                              exact ⟨a0_g1_w29 ⟨n - 53950, hr⟩, a1_g1_w29 ⟨n - 53950, hr⟩⟩
                                                            · by_cases h30 : n < 54050
                                                              · have hr : n - 54000 < 50 := by omega
                                                                have heq : n = (n - 54000) + 54000 := by omega
                                                                rw [heq]
                                                                exact ⟨a0_g1_w30 ⟨n - 54000, hr⟩, a1_g1_w30 ⟨n - 54000, hr⟩⟩
                                                              · by_cases h31 : n < 54100
                                                                · have hr : n - 54050 < 50 := by omega
                                                                  have heq : n = (n - 54050) + 54050 := by omega
                                                                  rw [heq]
                                                                  exact ⟨a0_g1_w31 ⟨n - 54050, hr⟩, a1_g1_w31 ⟨n - 54050, hr⟩⟩
                                                                · by_cases h32 : n < 54150
                                                                  · have hr : n - 54100 < 50 := by omega
                                                                    have heq : n = (n - 54100) + 54100 := by omega
                                                                    rw [heq]
                                                                    exact ⟨a0_g1_w32 ⟨n - 54100, hr⟩, a1_g1_w32 ⟨n - 54100, hr⟩⟩
                                                                  · by_cases h33 : n < 54200
                                                                    · have hr : n - 54150 < 50 := by omega
                                                                      have heq : n = (n - 54150) + 54150 := by omega
                                                                      rw [heq]
                                                                      exact ⟨a0_g1_w33 ⟨n - 54150, hr⟩, a1_g1_w33 ⟨n - 54150, hr⟩⟩
                                                                    · by_cases h34 : n < 54250
                                                                      · have hr : n - 54200 < 50 := by omega
                                                                        have heq : n = (n - 54200) + 54200 := by omega
                                                                        rw [heq]
                                                                        exact ⟨a0_g1_w34 ⟨n - 54200, hr⟩, a1_g1_w34 ⟨n - 54200, hr⟩⟩
                                                                      · by_cases h35 : n < 54300
                                                                        · have hr : n - 54250 < 50 := by omega
                                                                          have heq : n = (n - 54250) + 54250 := by omega
                                                                          rw [heq]
                                                                          exact ⟨a0_g1_w35 ⟨n - 54250, hr⟩, a1_g1_w35 ⟨n - 54250, hr⟩⟩
                                                                        · by_cases h36 : n < 54350
                                                                          · have hr : n - 54300 < 50 := by omega
                                                                            have heq : n = (n - 54300) + 54300 := by omega
                                                                            rw [heq]
                                                                            exact ⟨a0_g1_w36 ⟨n - 54300, hr⟩, a1_g1_w36 ⟨n - 54300, hr⟩⟩
                                                                          · by_cases h37 : n < 54400
                                                                            · have hr : n - 54350 < 50 := by omega
                                                                              have heq : n = (n - 54350) + 54350 := by omega
                                                                              rw [heq]
                                                                              exact ⟨a0_g1_w37 ⟨n - 54350, hr⟩, a1_g1_w37 ⟨n - 54350, hr⟩⟩
                                                                            · by_cases h38 : n < 54450
                                                                              · have hr : n - 54400 < 50 := by omega
                                                                                have heq : n = (n - 54400) + 54400 := by omega
                                                                                rw [heq]
                                                                                exact ⟨a0_g1_w38 ⟨n - 54400, hr⟩, a1_g1_w38 ⟨n - 54400, hr⟩⟩
                                                                              · by_cases h39 : n < 54500
                                                                                · have hr : n - 54450 < 50 := by omega
                                                                                  have heq : n = (n - 54450) + 54450 := by omega
                                                                                  rw [heq]
                                                                                  exact ⟨a0_g1_w39 ⟨n - 54450, hr⟩, a1_g1_w39 ⟨n - 54450, hr⟩⟩
                                                                                · by_cases h40 : n < 54550
                                                                                  · have hr : n - 54500 < 50 := by omega
                                                                                    have heq : n = (n - 54500) + 54500 := by omega
                                                                                    rw [heq]
                                                                                    exact ⟨a0_g1_w40 ⟨n - 54500, hr⟩, a1_g1_w40 ⟨n - 54500, hr⟩⟩
                                                                                  · by_cases h41 : n < 54600
                                                                                    · have hr : n - 54550 < 50 := by omega
                                                                                      have heq : n = (n - 54550) + 54550 := by omega
                                                                                      rw [heq]
                                                                                      exact ⟨a0_g1_w41 ⟨n - 54550, hr⟩, a1_g1_w41 ⟨n - 54550, hr⟩⟩
                                                                                    · by_cases h42 : n < 54650
                                                                                      · have hr : n - 54600 < 50 := by omega
                                                                                        have heq : n = (n - 54600) + 54600 := by omega
                                                                                        rw [heq]
                                                                                        exact ⟨a0_g1_w42 ⟨n - 54600, hr⟩, a1_g1_w42 ⟨n - 54600, hr⟩⟩
                                                                                      · by_cases h43 : n < 54700
                                                                                        · have hr : n - 54650 < 50 := by omega
                                                                                          have heq : n = (n - 54650) + 54650 := by omega
                                                                                          rw [heq]
                                                                                          exact ⟨a0_g1_w43 ⟨n - 54650, hr⟩, a1_g1_w43 ⟨n - 54650, hr⟩⟩
                                                                                        · by_cases h44 : n < 54750
                                                                                          · have hr : n - 54700 < 50 := by omega
                                                                                            have heq : n = (n - 54700) + 54700 := by omega
                                                                                            rw [heq]
                                                                                            exact ⟨a0_g1_w44 ⟨n - 54700, hr⟩, a1_g1_w44 ⟨n - 54700, hr⟩⟩
                                                                                          · by_cases h45 : n < 54800
                                                                                            · have hr : n - 54750 < 50 := by omega
                                                                                              have heq : n = (n - 54750) + 54750 := by omega
                                                                                              rw [heq]
                                                                                              exact ⟨a0_g1_w45 ⟨n - 54750, hr⟩, a1_g1_w45 ⟨n - 54750, hr⟩⟩
                                                                                            · by_cases h46 : n < 54850
                                                                                              · have hr : n - 54800 < 50 := by omega
                                                                                                have heq : n = (n - 54800) + 54800 := by omega
                                                                                                rw [heq]
                                                                                                exact ⟨a0_g1_w46 ⟨n - 54800, hr⟩, a1_g1_w46 ⟨n - 54800, hr⟩⟩
                                                                                              · by_cases h47 : n < 54900
                                                                                                · have hr : n - 54850 < 50 := by omega
                                                                                                  have heq : n = (n - 54850) + 54850 := by omega
                                                                                                  rw [heq]
                                                                                                  exact ⟨a0_g1_w47 ⟨n - 54850, hr⟩, a1_g1_w47 ⟨n - 54850, hr⟩⟩
                                                                                                · by_cases h48 : n < 54950
                                                                                                  · have hr : n - 54900 < 50 := by omega
                                                                                                    have heq : n = (n - 54900) + 54900 := by omega
                                                                                                    rw [heq]
                                                                                                    exact ⟨a0_g1_w48 ⟨n - 54900, hr⟩, a1_g1_w48 ⟨n - 54900, hr⟩⟩
                                                                                                  · have hr : n - 54950 < 50 := by omega
                                                                                                    have heq : n = (n - 54950) + 54950 := by omega
                                                                                                    rw [heq]
                                                                                                    exact ⟨a0_g1_w49 ⟨n - 54950, hr⟩, a1_g1_w49 ⟨n - 54950, hr⟩⟩

private theorem a0_g2_w0 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 55000)) 65535) ≤ dimF (n.val + 55000) := by decide
private theorem a1_g2_w0 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 55000)) 16) ≤ dimF (n.val + 55000) := by decide
private theorem a0_g2_w1 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 55050)) 65535) ≤ dimF (n.val + 55050) := by decide
private theorem a1_g2_w1 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 55050)) 16) ≤ dimF (n.val + 55050) := by decide
private theorem a0_g2_w2 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 55100)) 65535) ≤ dimF (n.val + 55100) := by decide
private theorem a1_g2_w2 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 55100)) 16) ≤ dimF (n.val + 55100) := by decide
private theorem a0_g2_w3 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 55150)) 65535) ≤ dimF (n.val + 55150) := by decide
private theorem a1_g2_w3 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 55150)) 16) ≤ dimF (n.val + 55150) := by decide
private theorem a0_g2_w4 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 55200)) 65535) ≤ dimF (n.val + 55200) := by decide
private theorem a1_g2_w4 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 55200)) 16) ≤ dimF (n.val + 55200) := by decide
private theorem a0_g2_w5 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 55250)) 65535) ≤ dimF (n.val + 55250) := by decide
private theorem a1_g2_w5 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 55250)) 16) ≤ dimF (n.val + 55250) := by decide
private theorem a0_g2_w6 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 55300)) 65535) ≤ dimF (n.val + 55300) := by decide
private theorem a1_g2_w6 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 55300)) 16) ≤ dimF (n.val + 55300) := by decide
private theorem a0_g2_w7 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 55350)) 65535) ≤ dimF (n.val + 55350) := by decide
private theorem a1_g2_w7 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 55350)) 16) ≤ dimF (n.val + 55350) := by decide
private theorem a0_g2_w8 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 55400)) 65535) ≤ dimF (n.val + 55400) := by decide
private theorem a1_g2_w8 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 55400)) 16) ≤ dimF (n.val + 55400) := by decide
private theorem a0_g2_w9 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 55450)) 65535) ≤ dimF (n.val + 55450) := by decide
private theorem a1_g2_w9 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 55450)) 16) ≤ dimF (n.val + 55450) := by decide
private theorem a0_g2_w10 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 55500)) 65535) ≤ dimF (n.val + 55500) := by decide
private theorem a1_g2_w10 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 55500)) 16) ≤ dimF (n.val + 55500) := by decide
private theorem a0_g2_w11 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 55550)) 65535) ≤ dimF (n.val + 55550) := by decide
private theorem a1_g2_w11 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 55550)) 16) ≤ dimF (n.val + 55550) := by decide
private theorem a0_g2_w12 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 55600)) 65535) ≤ dimF (n.val + 55600) := by decide
private theorem a1_g2_w12 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 55600)) 16) ≤ dimF (n.val + 55600) := by decide
private theorem a0_g2_w13 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 55650)) 65535) ≤ dimF (n.val + 55650) := by decide
private theorem a1_g2_w13 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 55650)) 16) ≤ dimF (n.val + 55650) := by decide
private theorem a0_g2_w14 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 55700)) 65535) ≤ dimF (n.val + 55700) := by decide
private theorem a1_g2_w14 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 55700)) 16) ≤ dimF (n.val + 55700) := by decide
private theorem a0_g2_w15 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 55750)) 65535) ≤ dimF (n.val + 55750) := by decide
private theorem a1_g2_w15 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 55750)) 16) ≤ dimF (n.val + 55750) := by decide
private theorem a0_g2_w16 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 55800)) 65535) ≤ dimF (n.val + 55800) := by decide
private theorem a1_g2_w16 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 55800)) 16) ≤ dimF (n.val + 55800) := by decide
private theorem a0_g2_w17 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 55850)) 65535) ≤ dimF (n.val + 55850) := by decide
private theorem a1_g2_w17 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 55850)) 16) ≤ dimF (n.val + 55850) := by decide
private theorem a0_g2_w18 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 55900)) 65535) ≤ dimF (n.val + 55900) := by decide
private theorem a1_g2_w18 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 55900)) 16) ≤ dimF (n.val + 55900) := by decide
private theorem a0_g2_w19 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 55950)) 65535) ≤ dimF (n.val + 55950) := by decide
private theorem a1_g2_w19 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 55950)) 16) ≤ dimF (n.val + 55950) := by decide
private theorem a0_g2_w20 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 56000)) 65535) ≤ dimF (n.val + 56000) := by decide
private theorem a1_g2_w20 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 56000)) 16) ≤ dimF (n.val + 56000) := by decide
private theorem a0_g2_w21 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 56050)) 65535) ≤ dimF (n.val + 56050) := by decide
private theorem a1_g2_w21 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 56050)) 16) ≤ dimF (n.val + 56050) := by decide
private theorem a0_g2_w22 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 56100)) 65535) ≤ dimF (n.val + 56100) := by decide
private theorem a1_g2_w22 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 56100)) 16) ≤ dimF (n.val + 56100) := by decide
private theorem a0_g2_w23 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 56150)) 65535) ≤ dimF (n.val + 56150) := by decide
private theorem a1_g2_w23 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 56150)) 16) ≤ dimF (n.val + 56150) := by decide
private theorem a0_g2_w24 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 56200)) 65535) ≤ dimF (n.val + 56200) := by decide
private theorem a1_g2_w24 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 56200)) 16) ≤ dimF (n.val + 56200) := by decide
private theorem a0_g2_w25 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 56250)) 65535) ≤ dimF (n.val + 56250) := by decide
private theorem a1_g2_w25 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 56250)) 16) ≤ dimF (n.val + 56250) := by decide
private theorem a0_g2_w26 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 56300)) 65535) ≤ dimF (n.val + 56300) := by decide
private theorem a1_g2_w26 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 56300)) 16) ≤ dimF (n.val + 56300) := by decide
private theorem a0_g2_w27 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 56350)) 65535) ≤ dimF (n.val + 56350) := by decide
private theorem a1_g2_w27 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 56350)) 16) ≤ dimF (n.val + 56350) := by decide
private theorem a0_g2_w28 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 56400)) 65535) ≤ dimF (n.val + 56400) := by decide
private theorem a1_g2_w28 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 56400)) 16) ≤ dimF (n.val + 56400) := by decide
private theorem a0_g2_w29 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 56450)) 65535) ≤ dimF (n.val + 56450) := by decide
private theorem a1_g2_w29 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 56450)) 16) ≤ dimF (n.val + 56450) := by decide
private theorem a0_g2_w30 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 56500)) 65535) ≤ dimF (n.val + 56500) := by decide
private theorem a1_g2_w30 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 56500)) 16) ≤ dimF (n.val + 56500) := by decide
private theorem a0_g2_w31 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 56550)) 65535) ≤ dimF (n.val + 56550) := by decide
private theorem a1_g2_w31 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 56550)) 16) ≤ dimF (n.val + 56550) := by decide
private theorem a0_g2_w32 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 56600)) 65535) ≤ dimF (n.val + 56600) := by decide
private theorem a1_g2_w32 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 56600)) 16) ≤ dimF (n.val + 56600) := by decide
private theorem a0_g2_w33 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 56650)) 65535) ≤ dimF (n.val + 56650) := by decide
private theorem a1_g2_w33 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 56650)) 16) ≤ dimF (n.val + 56650) := by decide
private theorem a0_g2_w34 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 56700)) 65535) ≤ dimF (n.val + 56700) := by decide
private theorem a1_g2_w34 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 56700)) 16) ≤ dimF (n.val + 56700) := by decide
private theorem a0_g2_w35 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 56750)) 65535) ≤ dimF (n.val + 56750) := by decide
private theorem a1_g2_w35 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 56750)) 16) ≤ dimF (n.val + 56750) := by decide
private theorem a0_g2_w36 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 56800)) 65535) ≤ dimF (n.val + 56800) := by decide
private theorem a1_g2_w36 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 56800)) 16) ≤ dimF (n.val + 56800) := by decide
private theorem a0_g2_w37 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 56850)) 65535) ≤ dimF (n.val + 56850) := by decide
private theorem a1_g2_w37 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 56850)) 16) ≤ dimF (n.val + 56850) := by decide
private theorem a0_g2_w38 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 56900)) 65535) ≤ dimF (n.val + 56900) := by decide
private theorem a1_g2_w38 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 56900)) 16) ≤ dimF (n.val + 56900) := by decide
private theorem a0_g2_w39 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 56950)) 65535) ≤ dimF (n.val + 56950) := by decide
private theorem a1_g2_w39 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 56950)) 16) ≤ dimF (n.val + 56950) := by decide
private theorem a0_g2_w40 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 57000)) 65535) ≤ dimF (n.val + 57000) := by decide
private theorem a1_g2_w40 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 57000)) 16) ≤ dimF (n.val + 57000) := by decide
private theorem a0_g2_w41 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 57050)) 65535) ≤ dimF (n.val + 57050) := by decide
private theorem a1_g2_w41 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 57050)) 16) ≤ dimF (n.val + 57050) := by decide
private theorem a0_g2_w42 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 57100)) 65535) ≤ dimF (n.val + 57100) := by decide
private theorem a1_g2_w42 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 57100)) 16) ≤ dimF (n.val + 57100) := by decide
private theorem a0_g2_w43 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 57150)) 65535) ≤ dimF (n.val + 57150) := by decide
private theorem a1_g2_w43 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 57150)) 16) ≤ dimF (n.val + 57150) := by decide
private theorem a0_g2_w44 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 57200)) 65535) ≤ dimF (n.val + 57200) := by decide
private theorem a1_g2_w44 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 57200)) 16) ≤ dimF (n.val + 57200) := by decide
private theorem a0_g2_w45 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 57250)) 65535) ≤ dimF (n.val + 57250) := by decide
private theorem a1_g2_w45 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 57250)) 16) ≤ dimF (n.val + 57250) := by decide
private theorem a0_g2_w46 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 57300)) 65535) ≤ dimF (n.val + 57300) := by decide
private theorem a1_g2_w46 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 57300)) 16) ≤ dimF (n.val + 57300) := by decide
private theorem a0_g2_w47 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 57350)) 65535) ≤ dimF (n.val + 57350) := by decide
private theorem a1_g2_w47 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 57350)) 16) ≤ dimF (n.val + 57350) := by decide
private theorem a0_g2_w48 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 57400)) 65535) ≤ dimF (n.val + 57400) := by decide
private theorem a1_g2_w48 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 57400)) 16) ≤ dimF (n.val + 57400) := by decide
private theorem a0_g2_w49 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 57450)) 65535) ≤ dimF (n.val + 57450) := by decide
private theorem a1_g2_w49 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 57450)) 16) ≤ dimF (n.val + 57450) := by decide

private theorem pair_g2 (n : ℕ) (hlo : 55000 ≤ n) (hhi : n < 57500) :
    dimF (Nat.land (argF n) 65535) ≤ dimF n ∧
    dimF (Nat.shiftRight (argF n) 16) ≤ dimF n := by
  by_cases h0 : n < 55050
  · have hr : n - 55000 < 50 := by omega
    have heq : n = (n - 55000) + 55000 := by omega
    rw [heq]
    exact ⟨a0_g2_w0 ⟨n - 55000, hr⟩, a1_g2_w0 ⟨n - 55000, hr⟩⟩
  · by_cases h1 : n < 55100
    · have hr : n - 55050 < 50 := by omega
      have heq : n = (n - 55050) + 55050 := by omega
      rw [heq]
      exact ⟨a0_g2_w1 ⟨n - 55050, hr⟩, a1_g2_w1 ⟨n - 55050, hr⟩⟩
    · by_cases h2 : n < 55150
      · have hr : n - 55100 < 50 := by omega
        have heq : n = (n - 55100) + 55100 := by omega
        rw [heq]
        exact ⟨a0_g2_w2 ⟨n - 55100, hr⟩, a1_g2_w2 ⟨n - 55100, hr⟩⟩
      · by_cases h3 : n < 55200
        · have hr : n - 55150 < 50 := by omega
          have heq : n = (n - 55150) + 55150 := by omega
          rw [heq]
          exact ⟨a0_g2_w3 ⟨n - 55150, hr⟩, a1_g2_w3 ⟨n - 55150, hr⟩⟩
        · by_cases h4 : n < 55250
          · have hr : n - 55200 < 50 := by omega
            have heq : n = (n - 55200) + 55200 := by omega
            rw [heq]
            exact ⟨a0_g2_w4 ⟨n - 55200, hr⟩, a1_g2_w4 ⟨n - 55200, hr⟩⟩
          · by_cases h5 : n < 55300
            · have hr : n - 55250 < 50 := by omega
              have heq : n = (n - 55250) + 55250 := by omega
              rw [heq]
              exact ⟨a0_g2_w5 ⟨n - 55250, hr⟩, a1_g2_w5 ⟨n - 55250, hr⟩⟩
            · by_cases h6 : n < 55350
              · have hr : n - 55300 < 50 := by omega
                have heq : n = (n - 55300) + 55300 := by omega
                rw [heq]
                exact ⟨a0_g2_w6 ⟨n - 55300, hr⟩, a1_g2_w6 ⟨n - 55300, hr⟩⟩
              · by_cases h7 : n < 55400
                · have hr : n - 55350 < 50 := by omega
                  have heq : n = (n - 55350) + 55350 := by omega
                  rw [heq]
                  exact ⟨a0_g2_w7 ⟨n - 55350, hr⟩, a1_g2_w7 ⟨n - 55350, hr⟩⟩
                · by_cases h8 : n < 55450
                  · have hr : n - 55400 < 50 := by omega
                    have heq : n = (n - 55400) + 55400 := by omega
                    rw [heq]
                    exact ⟨a0_g2_w8 ⟨n - 55400, hr⟩, a1_g2_w8 ⟨n - 55400, hr⟩⟩
                  · by_cases h9 : n < 55500
                    · have hr : n - 55450 < 50 := by omega
                      have heq : n = (n - 55450) + 55450 := by omega
                      rw [heq]
                      exact ⟨a0_g2_w9 ⟨n - 55450, hr⟩, a1_g2_w9 ⟨n - 55450, hr⟩⟩
                    · by_cases h10 : n < 55550
                      · have hr : n - 55500 < 50 := by omega
                        have heq : n = (n - 55500) + 55500 := by omega
                        rw [heq]
                        exact ⟨a0_g2_w10 ⟨n - 55500, hr⟩, a1_g2_w10 ⟨n - 55500, hr⟩⟩
                      · by_cases h11 : n < 55600
                        · have hr : n - 55550 < 50 := by omega
                          have heq : n = (n - 55550) + 55550 := by omega
                          rw [heq]
                          exact ⟨a0_g2_w11 ⟨n - 55550, hr⟩, a1_g2_w11 ⟨n - 55550, hr⟩⟩
                        · by_cases h12 : n < 55650
                          · have hr : n - 55600 < 50 := by omega
                            have heq : n = (n - 55600) + 55600 := by omega
                            rw [heq]
                            exact ⟨a0_g2_w12 ⟨n - 55600, hr⟩, a1_g2_w12 ⟨n - 55600, hr⟩⟩
                          · by_cases h13 : n < 55700
                            · have hr : n - 55650 < 50 := by omega
                              have heq : n = (n - 55650) + 55650 := by omega
                              rw [heq]
                              exact ⟨a0_g2_w13 ⟨n - 55650, hr⟩, a1_g2_w13 ⟨n - 55650, hr⟩⟩
                            · by_cases h14 : n < 55750
                              · have hr : n - 55700 < 50 := by omega
                                have heq : n = (n - 55700) + 55700 := by omega
                                rw [heq]
                                exact ⟨a0_g2_w14 ⟨n - 55700, hr⟩, a1_g2_w14 ⟨n - 55700, hr⟩⟩
                              · by_cases h15 : n < 55800
                                · have hr : n - 55750 < 50 := by omega
                                  have heq : n = (n - 55750) + 55750 := by omega
                                  rw [heq]
                                  exact ⟨a0_g2_w15 ⟨n - 55750, hr⟩, a1_g2_w15 ⟨n - 55750, hr⟩⟩
                                · by_cases h16 : n < 55850
                                  · have hr : n - 55800 < 50 := by omega
                                    have heq : n = (n - 55800) + 55800 := by omega
                                    rw [heq]
                                    exact ⟨a0_g2_w16 ⟨n - 55800, hr⟩, a1_g2_w16 ⟨n - 55800, hr⟩⟩
                                  · by_cases h17 : n < 55900
                                    · have hr : n - 55850 < 50 := by omega
                                      have heq : n = (n - 55850) + 55850 := by omega
                                      rw [heq]
                                      exact ⟨a0_g2_w17 ⟨n - 55850, hr⟩, a1_g2_w17 ⟨n - 55850, hr⟩⟩
                                    · by_cases h18 : n < 55950
                                      · have hr : n - 55900 < 50 := by omega
                                        have heq : n = (n - 55900) + 55900 := by omega
                                        rw [heq]
                                        exact ⟨a0_g2_w18 ⟨n - 55900, hr⟩, a1_g2_w18 ⟨n - 55900, hr⟩⟩
                                      · by_cases h19 : n < 56000
                                        · have hr : n - 55950 < 50 := by omega
                                          have heq : n = (n - 55950) + 55950 := by omega
                                          rw [heq]
                                          exact ⟨a0_g2_w19 ⟨n - 55950, hr⟩, a1_g2_w19 ⟨n - 55950, hr⟩⟩
                                        · by_cases h20 : n < 56050
                                          · have hr : n - 56000 < 50 := by omega
                                            have heq : n = (n - 56000) + 56000 := by omega
                                            rw [heq]
                                            exact ⟨a0_g2_w20 ⟨n - 56000, hr⟩, a1_g2_w20 ⟨n - 56000, hr⟩⟩
                                          · by_cases h21 : n < 56100
                                            · have hr : n - 56050 < 50 := by omega
                                              have heq : n = (n - 56050) + 56050 := by omega
                                              rw [heq]
                                              exact ⟨a0_g2_w21 ⟨n - 56050, hr⟩, a1_g2_w21 ⟨n - 56050, hr⟩⟩
                                            · by_cases h22 : n < 56150
                                              · have hr : n - 56100 < 50 := by omega
                                                have heq : n = (n - 56100) + 56100 := by omega
                                                rw [heq]
                                                exact ⟨a0_g2_w22 ⟨n - 56100, hr⟩, a1_g2_w22 ⟨n - 56100, hr⟩⟩
                                              · by_cases h23 : n < 56200
                                                · have hr : n - 56150 < 50 := by omega
                                                  have heq : n = (n - 56150) + 56150 := by omega
                                                  rw [heq]
                                                  exact ⟨a0_g2_w23 ⟨n - 56150, hr⟩, a1_g2_w23 ⟨n - 56150, hr⟩⟩
                                                · by_cases h24 : n < 56250
                                                  · have hr : n - 56200 < 50 := by omega
                                                    have heq : n = (n - 56200) + 56200 := by omega
                                                    rw [heq]
                                                    exact ⟨a0_g2_w24 ⟨n - 56200, hr⟩, a1_g2_w24 ⟨n - 56200, hr⟩⟩
                                                  · by_cases h25 : n < 56300
                                                    · have hr : n - 56250 < 50 := by omega
                                                      have heq : n = (n - 56250) + 56250 := by omega
                                                      rw [heq]
                                                      exact ⟨a0_g2_w25 ⟨n - 56250, hr⟩, a1_g2_w25 ⟨n - 56250, hr⟩⟩
                                                    · by_cases h26 : n < 56350
                                                      · have hr : n - 56300 < 50 := by omega
                                                        have heq : n = (n - 56300) + 56300 := by omega
                                                        rw [heq]
                                                        exact ⟨a0_g2_w26 ⟨n - 56300, hr⟩, a1_g2_w26 ⟨n - 56300, hr⟩⟩
                                                      · by_cases h27 : n < 56400
                                                        · have hr : n - 56350 < 50 := by omega
                                                          have heq : n = (n - 56350) + 56350 := by omega
                                                          rw [heq]
                                                          exact ⟨a0_g2_w27 ⟨n - 56350, hr⟩, a1_g2_w27 ⟨n - 56350, hr⟩⟩
                                                        · by_cases h28 : n < 56450
                                                          · have hr : n - 56400 < 50 := by omega
                                                            have heq : n = (n - 56400) + 56400 := by omega
                                                            rw [heq]
                                                            exact ⟨a0_g2_w28 ⟨n - 56400, hr⟩, a1_g2_w28 ⟨n - 56400, hr⟩⟩
                                                          · by_cases h29 : n < 56500
                                                            · have hr : n - 56450 < 50 := by omega
                                                              have heq : n = (n - 56450) + 56450 := by omega
                                                              rw [heq]
                                                              exact ⟨a0_g2_w29 ⟨n - 56450, hr⟩, a1_g2_w29 ⟨n - 56450, hr⟩⟩
                                                            · by_cases h30 : n < 56550
                                                              · have hr : n - 56500 < 50 := by omega
                                                                have heq : n = (n - 56500) + 56500 := by omega
                                                                rw [heq]
                                                                exact ⟨a0_g2_w30 ⟨n - 56500, hr⟩, a1_g2_w30 ⟨n - 56500, hr⟩⟩
                                                              · by_cases h31 : n < 56600
                                                                · have hr : n - 56550 < 50 := by omega
                                                                  have heq : n = (n - 56550) + 56550 := by omega
                                                                  rw [heq]
                                                                  exact ⟨a0_g2_w31 ⟨n - 56550, hr⟩, a1_g2_w31 ⟨n - 56550, hr⟩⟩
                                                                · by_cases h32 : n < 56650
                                                                  · have hr : n - 56600 < 50 := by omega
                                                                    have heq : n = (n - 56600) + 56600 := by omega
                                                                    rw [heq]
                                                                    exact ⟨a0_g2_w32 ⟨n - 56600, hr⟩, a1_g2_w32 ⟨n - 56600, hr⟩⟩
                                                                  · by_cases h33 : n < 56700
                                                                    · have hr : n - 56650 < 50 := by omega
                                                                      have heq : n = (n - 56650) + 56650 := by omega
                                                                      rw [heq]
                                                                      exact ⟨a0_g2_w33 ⟨n - 56650, hr⟩, a1_g2_w33 ⟨n - 56650, hr⟩⟩
                                                                    · by_cases h34 : n < 56750
                                                                      · have hr : n - 56700 < 50 := by omega
                                                                        have heq : n = (n - 56700) + 56700 := by omega
                                                                        rw [heq]
                                                                        exact ⟨a0_g2_w34 ⟨n - 56700, hr⟩, a1_g2_w34 ⟨n - 56700, hr⟩⟩
                                                                      · by_cases h35 : n < 56800
                                                                        · have hr : n - 56750 < 50 := by omega
                                                                          have heq : n = (n - 56750) + 56750 := by omega
                                                                          rw [heq]
                                                                          exact ⟨a0_g2_w35 ⟨n - 56750, hr⟩, a1_g2_w35 ⟨n - 56750, hr⟩⟩
                                                                        · by_cases h36 : n < 56850
                                                                          · have hr : n - 56800 < 50 := by omega
                                                                            have heq : n = (n - 56800) + 56800 := by omega
                                                                            rw [heq]
                                                                            exact ⟨a0_g2_w36 ⟨n - 56800, hr⟩, a1_g2_w36 ⟨n - 56800, hr⟩⟩
                                                                          · by_cases h37 : n < 56900
                                                                            · have hr : n - 56850 < 50 := by omega
                                                                              have heq : n = (n - 56850) + 56850 := by omega
                                                                              rw [heq]
                                                                              exact ⟨a0_g2_w37 ⟨n - 56850, hr⟩, a1_g2_w37 ⟨n - 56850, hr⟩⟩
                                                                            · by_cases h38 : n < 56950
                                                                              · have hr : n - 56900 < 50 := by omega
                                                                                have heq : n = (n - 56900) + 56900 := by omega
                                                                                rw [heq]
                                                                                exact ⟨a0_g2_w38 ⟨n - 56900, hr⟩, a1_g2_w38 ⟨n - 56900, hr⟩⟩
                                                                              · by_cases h39 : n < 57000
                                                                                · have hr : n - 56950 < 50 := by omega
                                                                                  have heq : n = (n - 56950) + 56950 := by omega
                                                                                  rw [heq]
                                                                                  exact ⟨a0_g2_w39 ⟨n - 56950, hr⟩, a1_g2_w39 ⟨n - 56950, hr⟩⟩
                                                                                · by_cases h40 : n < 57050
                                                                                  · have hr : n - 57000 < 50 := by omega
                                                                                    have heq : n = (n - 57000) + 57000 := by omega
                                                                                    rw [heq]
                                                                                    exact ⟨a0_g2_w40 ⟨n - 57000, hr⟩, a1_g2_w40 ⟨n - 57000, hr⟩⟩
                                                                                  · by_cases h41 : n < 57100
                                                                                    · have hr : n - 57050 < 50 := by omega
                                                                                      have heq : n = (n - 57050) + 57050 := by omega
                                                                                      rw [heq]
                                                                                      exact ⟨a0_g2_w41 ⟨n - 57050, hr⟩, a1_g2_w41 ⟨n - 57050, hr⟩⟩
                                                                                    · by_cases h42 : n < 57150
                                                                                      · have hr : n - 57100 < 50 := by omega
                                                                                        have heq : n = (n - 57100) + 57100 := by omega
                                                                                        rw [heq]
                                                                                        exact ⟨a0_g2_w42 ⟨n - 57100, hr⟩, a1_g2_w42 ⟨n - 57100, hr⟩⟩
                                                                                      · by_cases h43 : n < 57200
                                                                                        · have hr : n - 57150 < 50 := by omega
                                                                                          have heq : n = (n - 57150) + 57150 := by omega
                                                                                          rw [heq]
                                                                                          exact ⟨a0_g2_w43 ⟨n - 57150, hr⟩, a1_g2_w43 ⟨n - 57150, hr⟩⟩
                                                                                        · by_cases h44 : n < 57250
                                                                                          · have hr : n - 57200 < 50 := by omega
                                                                                            have heq : n = (n - 57200) + 57200 := by omega
                                                                                            rw [heq]
                                                                                            exact ⟨a0_g2_w44 ⟨n - 57200, hr⟩, a1_g2_w44 ⟨n - 57200, hr⟩⟩
                                                                                          · by_cases h45 : n < 57300
                                                                                            · have hr : n - 57250 < 50 := by omega
                                                                                              have heq : n = (n - 57250) + 57250 := by omega
                                                                                              rw [heq]
                                                                                              exact ⟨a0_g2_w45 ⟨n - 57250, hr⟩, a1_g2_w45 ⟨n - 57250, hr⟩⟩
                                                                                            · by_cases h46 : n < 57350
                                                                                              · have hr : n - 57300 < 50 := by omega
                                                                                                have heq : n = (n - 57300) + 57300 := by omega
                                                                                                rw [heq]
                                                                                                exact ⟨a0_g2_w46 ⟨n - 57300, hr⟩, a1_g2_w46 ⟨n - 57300, hr⟩⟩
                                                                                              · by_cases h47 : n < 57400
                                                                                                · have hr : n - 57350 < 50 := by omega
                                                                                                  have heq : n = (n - 57350) + 57350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact ⟨a0_g2_w47 ⟨n - 57350, hr⟩, a1_g2_w47 ⟨n - 57350, hr⟩⟩
                                                                                                · by_cases h48 : n < 57450
                                                                                                  · have hr : n - 57400 < 50 := by omega
                                                                                                    have heq : n = (n - 57400) + 57400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact ⟨a0_g2_w48 ⟨n - 57400, hr⟩, a1_g2_w48 ⟨n - 57400, hr⟩⟩
                                                                                                  · have hr : n - 57450 < 50 := by omega
                                                                                                    have heq : n = (n - 57450) + 57450 := by omega
                                                                                                    rw [heq]
                                                                                                    exact ⟨a0_g2_w49 ⟨n - 57450, hr⟩, a1_g2_w49 ⟨n - 57450, hr⟩⟩

private theorem a0_g3_w0 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 57500)) 65535) ≤ dimF (n.val + 57500) := by decide
private theorem a1_g3_w0 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 57500)) 16) ≤ dimF (n.val + 57500) := by decide
private theorem a0_g3_w1 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 57550)) 65535) ≤ dimF (n.val + 57550) := by decide
private theorem a1_g3_w1 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 57550)) 16) ≤ dimF (n.val + 57550) := by decide
private theorem a0_g3_w2 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 57600)) 65535) ≤ dimF (n.val + 57600) := by decide
private theorem a1_g3_w2 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 57600)) 16) ≤ dimF (n.val + 57600) := by decide
private theorem a0_g3_w3 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 57650)) 65535) ≤ dimF (n.val + 57650) := by decide
private theorem a1_g3_w3 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 57650)) 16) ≤ dimF (n.val + 57650) := by decide
private theorem a0_g3_w4 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 57700)) 65535) ≤ dimF (n.val + 57700) := by decide
private theorem a1_g3_w4 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 57700)) 16) ≤ dimF (n.val + 57700) := by decide
private theorem a0_g3_w5 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 57750)) 65535) ≤ dimF (n.val + 57750) := by decide
private theorem a1_g3_w5 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 57750)) 16) ≤ dimF (n.val + 57750) := by decide
private theorem a0_g3_w6 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 57800)) 65535) ≤ dimF (n.val + 57800) := by decide
private theorem a1_g3_w6 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 57800)) 16) ≤ dimF (n.val + 57800) := by decide
private theorem a0_g3_w7 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 57850)) 65535) ≤ dimF (n.val + 57850) := by decide
private theorem a1_g3_w7 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 57850)) 16) ≤ dimF (n.val + 57850) := by decide
private theorem a0_g3_w8 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 57900)) 65535) ≤ dimF (n.val + 57900) := by decide
private theorem a1_g3_w8 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 57900)) 16) ≤ dimF (n.val + 57900) := by decide
private theorem a0_g3_w9 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 57950)) 65535) ≤ dimF (n.val + 57950) := by decide
private theorem a1_g3_w9 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 57950)) 16) ≤ dimF (n.val + 57950) := by decide
private theorem a0_g3_w10 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 58000)) 65535) ≤ dimF (n.val + 58000) := by decide
private theorem a1_g3_w10 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 58000)) 16) ≤ dimF (n.val + 58000) := by decide
private theorem a0_g3_w11 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 58050)) 65535) ≤ dimF (n.val + 58050) := by decide
private theorem a1_g3_w11 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 58050)) 16) ≤ dimF (n.val + 58050) := by decide
private theorem a0_g3_w12 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 58100)) 65535) ≤ dimF (n.val + 58100) := by decide
private theorem a1_g3_w12 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 58100)) 16) ≤ dimF (n.val + 58100) := by decide
private theorem a0_g3_w13 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 58150)) 65535) ≤ dimF (n.val + 58150) := by decide
private theorem a1_g3_w13 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 58150)) 16) ≤ dimF (n.val + 58150) := by decide
private theorem a0_g3_w14 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 58200)) 65535) ≤ dimF (n.val + 58200) := by decide
private theorem a1_g3_w14 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 58200)) 16) ≤ dimF (n.val + 58200) := by decide
private theorem a0_g3_w15 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 58250)) 65535) ≤ dimF (n.val + 58250) := by decide
private theorem a1_g3_w15 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 58250)) 16) ≤ dimF (n.val + 58250) := by decide
private theorem a0_g3_w16 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 58300)) 65535) ≤ dimF (n.val + 58300) := by decide
private theorem a1_g3_w16 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 58300)) 16) ≤ dimF (n.val + 58300) := by decide
private theorem a0_g3_w17 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 58350)) 65535) ≤ dimF (n.val + 58350) := by decide
private theorem a1_g3_w17 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 58350)) 16) ≤ dimF (n.val + 58350) := by decide
private theorem a0_g3_w18 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 58400)) 65535) ≤ dimF (n.val + 58400) := by decide
private theorem a1_g3_w18 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 58400)) 16) ≤ dimF (n.val + 58400) := by decide
private theorem a0_g3_w19 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 58450)) 65535) ≤ dimF (n.val + 58450) := by decide
private theorem a1_g3_w19 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 58450)) 16) ≤ dimF (n.val + 58450) := by decide
private theorem a0_g3_w20 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 58500)) 65535) ≤ dimF (n.val + 58500) := by decide
private theorem a1_g3_w20 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 58500)) 16) ≤ dimF (n.val + 58500) := by decide
private theorem a0_g3_w21 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 58550)) 65535) ≤ dimF (n.val + 58550) := by decide
private theorem a1_g3_w21 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 58550)) 16) ≤ dimF (n.val + 58550) := by decide
private theorem a0_g3_w22 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 58600)) 65535) ≤ dimF (n.val + 58600) := by decide
private theorem a1_g3_w22 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 58600)) 16) ≤ dimF (n.val + 58600) := by decide
private theorem a0_g3_w23 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 58650)) 65535) ≤ dimF (n.val + 58650) := by decide
private theorem a1_g3_w23 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 58650)) 16) ≤ dimF (n.val + 58650) := by decide
private theorem a0_g3_w24 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 58700)) 65535) ≤ dimF (n.val + 58700) := by decide
private theorem a1_g3_w24 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 58700)) 16) ≤ dimF (n.val + 58700) := by decide
private theorem a0_g3_w25 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 58750)) 65535) ≤ dimF (n.val + 58750) := by decide
private theorem a1_g3_w25 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 58750)) 16) ≤ dimF (n.val + 58750) := by decide
private theorem a0_g3_w26 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 58800)) 65535) ≤ dimF (n.val + 58800) := by decide
private theorem a1_g3_w26 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 58800)) 16) ≤ dimF (n.val + 58800) := by decide
private theorem a0_g3_w27 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 58850)) 65535) ≤ dimF (n.val + 58850) := by decide
private theorem a1_g3_w27 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 58850)) 16) ≤ dimF (n.val + 58850) := by decide
private theorem a0_g3_w28 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 58900)) 65535) ≤ dimF (n.val + 58900) := by decide
private theorem a1_g3_w28 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 58900)) 16) ≤ dimF (n.val + 58900) := by decide
private theorem a0_g3_w29 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 58950)) 65535) ≤ dimF (n.val + 58950) := by decide
private theorem a1_g3_w29 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 58950)) 16) ≤ dimF (n.val + 58950) := by decide
private theorem a0_g3_w30 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 59000)) 65535) ≤ dimF (n.val + 59000) := by decide
private theorem a1_g3_w30 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 59000)) 16) ≤ dimF (n.val + 59000) := by decide
private theorem a0_g3_w31 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 59050)) 65535) ≤ dimF (n.val + 59050) := by decide
private theorem a1_g3_w31 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 59050)) 16) ≤ dimF (n.val + 59050) := by decide
private theorem a0_g3_w32 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 59100)) 65535) ≤ dimF (n.val + 59100) := by decide
private theorem a1_g3_w32 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 59100)) 16) ≤ dimF (n.val + 59100) := by decide
private theorem a0_g3_w33 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 59150)) 65535) ≤ dimF (n.val + 59150) := by decide
private theorem a1_g3_w33 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 59150)) 16) ≤ dimF (n.val + 59150) := by decide
private theorem a0_g3_w34 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 59200)) 65535) ≤ dimF (n.val + 59200) := by decide
private theorem a1_g3_w34 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 59200)) 16) ≤ dimF (n.val + 59200) := by decide
private theorem a0_g3_w35 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 59250)) 65535) ≤ dimF (n.val + 59250) := by decide
private theorem a1_g3_w35 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 59250)) 16) ≤ dimF (n.val + 59250) := by decide
private theorem a0_g3_w36 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 59300)) 65535) ≤ dimF (n.val + 59300) := by decide
private theorem a1_g3_w36 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 59300)) 16) ≤ dimF (n.val + 59300) := by decide
private theorem a0_g3_w37 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 59350)) 65535) ≤ dimF (n.val + 59350) := by decide
private theorem a1_g3_w37 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 59350)) 16) ≤ dimF (n.val + 59350) := by decide
private theorem a0_g3_w38 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 59400)) 65535) ≤ dimF (n.val + 59400) := by decide
private theorem a1_g3_w38 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 59400)) 16) ≤ dimF (n.val + 59400) := by decide
private theorem a0_g3_w39 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 59450)) 65535) ≤ dimF (n.val + 59450) := by decide
private theorem a1_g3_w39 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 59450)) 16) ≤ dimF (n.val + 59450) := by decide
private theorem a0_g3_w40 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 59500)) 65535) ≤ dimF (n.val + 59500) := by decide
private theorem a1_g3_w40 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 59500)) 16) ≤ dimF (n.val + 59500) := by decide
private theorem a0_g3_w41 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 59550)) 65535) ≤ dimF (n.val + 59550) := by decide
private theorem a1_g3_w41 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 59550)) 16) ≤ dimF (n.val + 59550) := by decide
private theorem a0_g3_w42 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 59600)) 65535) ≤ dimF (n.val + 59600) := by decide
private theorem a1_g3_w42 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 59600)) 16) ≤ dimF (n.val + 59600) := by decide
private theorem a0_g3_w43 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 59650)) 65535) ≤ dimF (n.val + 59650) := by decide
private theorem a1_g3_w43 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 59650)) 16) ≤ dimF (n.val + 59650) := by decide
private theorem a0_g3_w44 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 59700)) 65535) ≤ dimF (n.val + 59700) := by decide
private theorem a1_g3_w44 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 59700)) 16) ≤ dimF (n.val + 59700) := by decide
private theorem a0_g3_w45 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 59750)) 65535) ≤ dimF (n.val + 59750) := by decide
private theorem a1_g3_w45 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 59750)) 16) ≤ dimF (n.val + 59750) := by decide
private theorem a0_g3_w46 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 59800)) 65535) ≤ dimF (n.val + 59800) := by decide
private theorem a1_g3_w46 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 59800)) 16) ≤ dimF (n.val + 59800) := by decide
private theorem a0_g3_w47 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 59850)) 65535) ≤ dimF (n.val + 59850) := by decide
private theorem a1_g3_w47 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 59850)) 16) ≤ dimF (n.val + 59850) := by decide
private theorem a0_g3_w48 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 59900)) 65535) ≤ dimF (n.val + 59900) := by decide
private theorem a1_g3_w48 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 59900)) 16) ≤ dimF (n.val + 59900) := by decide
private theorem a0_g3_w49 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 59950)) 65535) ≤ dimF (n.val + 59950) := by decide
private theorem a1_g3_w49 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 59950)) 16) ≤ dimF (n.val + 59950) := by decide

private theorem pair_g3 (n : ℕ) (hlo : 57500 ≤ n) (hhi : n < 60000) :
    dimF (Nat.land (argF n) 65535) ≤ dimF n ∧
    dimF (Nat.shiftRight (argF n) 16) ≤ dimF n := by
  by_cases h0 : n < 57550
  · have hr : n - 57500 < 50 := by omega
    have heq : n = (n - 57500) + 57500 := by omega
    rw [heq]
    exact ⟨a0_g3_w0 ⟨n - 57500, hr⟩, a1_g3_w0 ⟨n - 57500, hr⟩⟩
  · by_cases h1 : n < 57600
    · have hr : n - 57550 < 50 := by omega
      have heq : n = (n - 57550) + 57550 := by omega
      rw [heq]
      exact ⟨a0_g3_w1 ⟨n - 57550, hr⟩, a1_g3_w1 ⟨n - 57550, hr⟩⟩
    · by_cases h2 : n < 57650
      · have hr : n - 57600 < 50 := by omega
        have heq : n = (n - 57600) + 57600 := by omega
        rw [heq]
        exact ⟨a0_g3_w2 ⟨n - 57600, hr⟩, a1_g3_w2 ⟨n - 57600, hr⟩⟩
      · by_cases h3 : n < 57700
        · have hr : n - 57650 < 50 := by omega
          have heq : n = (n - 57650) + 57650 := by omega
          rw [heq]
          exact ⟨a0_g3_w3 ⟨n - 57650, hr⟩, a1_g3_w3 ⟨n - 57650, hr⟩⟩
        · by_cases h4 : n < 57750
          · have hr : n - 57700 < 50 := by omega
            have heq : n = (n - 57700) + 57700 := by omega
            rw [heq]
            exact ⟨a0_g3_w4 ⟨n - 57700, hr⟩, a1_g3_w4 ⟨n - 57700, hr⟩⟩
          · by_cases h5 : n < 57800
            · have hr : n - 57750 < 50 := by omega
              have heq : n = (n - 57750) + 57750 := by omega
              rw [heq]
              exact ⟨a0_g3_w5 ⟨n - 57750, hr⟩, a1_g3_w5 ⟨n - 57750, hr⟩⟩
            · by_cases h6 : n < 57850
              · have hr : n - 57800 < 50 := by omega
                have heq : n = (n - 57800) + 57800 := by omega
                rw [heq]
                exact ⟨a0_g3_w6 ⟨n - 57800, hr⟩, a1_g3_w6 ⟨n - 57800, hr⟩⟩
              · by_cases h7 : n < 57900
                · have hr : n - 57850 < 50 := by omega
                  have heq : n = (n - 57850) + 57850 := by omega
                  rw [heq]
                  exact ⟨a0_g3_w7 ⟨n - 57850, hr⟩, a1_g3_w7 ⟨n - 57850, hr⟩⟩
                · by_cases h8 : n < 57950
                  · have hr : n - 57900 < 50 := by omega
                    have heq : n = (n - 57900) + 57900 := by omega
                    rw [heq]
                    exact ⟨a0_g3_w8 ⟨n - 57900, hr⟩, a1_g3_w8 ⟨n - 57900, hr⟩⟩
                  · by_cases h9 : n < 58000
                    · have hr : n - 57950 < 50 := by omega
                      have heq : n = (n - 57950) + 57950 := by omega
                      rw [heq]
                      exact ⟨a0_g3_w9 ⟨n - 57950, hr⟩, a1_g3_w9 ⟨n - 57950, hr⟩⟩
                    · by_cases h10 : n < 58050
                      · have hr : n - 58000 < 50 := by omega
                        have heq : n = (n - 58000) + 58000 := by omega
                        rw [heq]
                        exact ⟨a0_g3_w10 ⟨n - 58000, hr⟩, a1_g3_w10 ⟨n - 58000, hr⟩⟩
                      · by_cases h11 : n < 58100
                        · have hr : n - 58050 < 50 := by omega
                          have heq : n = (n - 58050) + 58050 := by omega
                          rw [heq]
                          exact ⟨a0_g3_w11 ⟨n - 58050, hr⟩, a1_g3_w11 ⟨n - 58050, hr⟩⟩
                        · by_cases h12 : n < 58150
                          · have hr : n - 58100 < 50 := by omega
                            have heq : n = (n - 58100) + 58100 := by omega
                            rw [heq]
                            exact ⟨a0_g3_w12 ⟨n - 58100, hr⟩, a1_g3_w12 ⟨n - 58100, hr⟩⟩
                          · by_cases h13 : n < 58200
                            · have hr : n - 58150 < 50 := by omega
                              have heq : n = (n - 58150) + 58150 := by omega
                              rw [heq]
                              exact ⟨a0_g3_w13 ⟨n - 58150, hr⟩, a1_g3_w13 ⟨n - 58150, hr⟩⟩
                            · by_cases h14 : n < 58250
                              · have hr : n - 58200 < 50 := by omega
                                have heq : n = (n - 58200) + 58200 := by omega
                                rw [heq]
                                exact ⟨a0_g3_w14 ⟨n - 58200, hr⟩, a1_g3_w14 ⟨n - 58200, hr⟩⟩
                              · by_cases h15 : n < 58300
                                · have hr : n - 58250 < 50 := by omega
                                  have heq : n = (n - 58250) + 58250 := by omega
                                  rw [heq]
                                  exact ⟨a0_g3_w15 ⟨n - 58250, hr⟩, a1_g3_w15 ⟨n - 58250, hr⟩⟩
                                · by_cases h16 : n < 58350
                                  · have hr : n - 58300 < 50 := by omega
                                    have heq : n = (n - 58300) + 58300 := by omega
                                    rw [heq]
                                    exact ⟨a0_g3_w16 ⟨n - 58300, hr⟩, a1_g3_w16 ⟨n - 58300, hr⟩⟩
                                  · by_cases h17 : n < 58400
                                    · have hr : n - 58350 < 50 := by omega
                                      have heq : n = (n - 58350) + 58350 := by omega
                                      rw [heq]
                                      exact ⟨a0_g3_w17 ⟨n - 58350, hr⟩, a1_g3_w17 ⟨n - 58350, hr⟩⟩
                                    · by_cases h18 : n < 58450
                                      · have hr : n - 58400 < 50 := by omega
                                        have heq : n = (n - 58400) + 58400 := by omega
                                        rw [heq]
                                        exact ⟨a0_g3_w18 ⟨n - 58400, hr⟩, a1_g3_w18 ⟨n - 58400, hr⟩⟩
                                      · by_cases h19 : n < 58500
                                        · have hr : n - 58450 < 50 := by omega
                                          have heq : n = (n - 58450) + 58450 := by omega
                                          rw [heq]
                                          exact ⟨a0_g3_w19 ⟨n - 58450, hr⟩, a1_g3_w19 ⟨n - 58450, hr⟩⟩
                                        · by_cases h20 : n < 58550
                                          · have hr : n - 58500 < 50 := by omega
                                            have heq : n = (n - 58500) + 58500 := by omega
                                            rw [heq]
                                            exact ⟨a0_g3_w20 ⟨n - 58500, hr⟩, a1_g3_w20 ⟨n - 58500, hr⟩⟩
                                          · by_cases h21 : n < 58600
                                            · have hr : n - 58550 < 50 := by omega
                                              have heq : n = (n - 58550) + 58550 := by omega
                                              rw [heq]
                                              exact ⟨a0_g3_w21 ⟨n - 58550, hr⟩, a1_g3_w21 ⟨n - 58550, hr⟩⟩
                                            · by_cases h22 : n < 58650
                                              · have hr : n - 58600 < 50 := by omega
                                                have heq : n = (n - 58600) + 58600 := by omega
                                                rw [heq]
                                                exact ⟨a0_g3_w22 ⟨n - 58600, hr⟩, a1_g3_w22 ⟨n - 58600, hr⟩⟩
                                              · by_cases h23 : n < 58700
                                                · have hr : n - 58650 < 50 := by omega
                                                  have heq : n = (n - 58650) + 58650 := by omega
                                                  rw [heq]
                                                  exact ⟨a0_g3_w23 ⟨n - 58650, hr⟩, a1_g3_w23 ⟨n - 58650, hr⟩⟩
                                                · by_cases h24 : n < 58750
                                                  · have hr : n - 58700 < 50 := by omega
                                                    have heq : n = (n - 58700) + 58700 := by omega
                                                    rw [heq]
                                                    exact ⟨a0_g3_w24 ⟨n - 58700, hr⟩, a1_g3_w24 ⟨n - 58700, hr⟩⟩
                                                  · by_cases h25 : n < 58800
                                                    · have hr : n - 58750 < 50 := by omega
                                                      have heq : n = (n - 58750) + 58750 := by omega
                                                      rw [heq]
                                                      exact ⟨a0_g3_w25 ⟨n - 58750, hr⟩, a1_g3_w25 ⟨n - 58750, hr⟩⟩
                                                    · by_cases h26 : n < 58850
                                                      · have hr : n - 58800 < 50 := by omega
                                                        have heq : n = (n - 58800) + 58800 := by omega
                                                        rw [heq]
                                                        exact ⟨a0_g3_w26 ⟨n - 58800, hr⟩, a1_g3_w26 ⟨n - 58800, hr⟩⟩
                                                      · by_cases h27 : n < 58900
                                                        · have hr : n - 58850 < 50 := by omega
                                                          have heq : n = (n - 58850) + 58850 := by omega
                                                          rw [heq]
                                                          exact ⟨a0_g3_w27 ⟨n - 58850, hr⟩, a1_g3_w27 ⟨n - 58850, hr⟩⟩
                                                        · by_cases h28 : n < 58950
                                                          · have hr : n - 58900 < 50 := by omega
                                                            have heq : n = (n - 58900) + 58900 := by omega
                                                            rw [heq]
                                                            exact ⟨a0_g3_w28 ⟨n - 58900, hr⟩, a1_g3_w28 ⟨n - 58900, hr⟩⟩
                                                          · by_cases h29 : n < 59000
                                                            · have hr : n - 58950 < 50 := by omega
                                                              have heq : n = (n - 58950) + 58950 := by omega
                                                              rw [heq]
                                                              exact ⟨a0_g3_w29 ⟨n - 58950, hr⟩, a1_g3_w29 ⟨n - 58950, hr⟩⟩
                                                            · by_cases h30 : n < 59050
                                                              · have hr : n - 59000 < 50 := by omega
                                                                have heq : n = (n - 59000) + 59000 := by omega
                                                                rw [heq]
                                                                exact ⟨a0_g3_w30 ⟨n - 59000, hr⟩, a1_g3_w30 ⟨n - 59000, hr⟩⟩
                                                              · by_cases h31 : n < 59100
                                                                · have hr : n - 59050 < 50 := by omega
                                                                  have heq : n = (n - 59050) + 59050 := by omega
                                                                  rw [heq]
                                                                  exact ⟨a0_g3_w31 ⟨n - 59050, hr⟩, a1_g3_w31 ⟨n - 59050, hr⟩⟩
                                                                · by_cases h32 : n < 59150
                                                                  · have hr : n - 59100 < 50 := by omega
                                                                    have heq : n = (n - 59100) + 59100 := by omega
                                                                    rw [heq]
                                                                    exact ⟨a0_g3_w32 ⟨n - 59100, hr⟩, a1_g3_w32 ⟨n - 59100, hr⟩⟩
                                                                  · by_cases h33 : n < 59200
                                                                    · have hr : n - 59150 < 50 := by omega
                                                                      have heq : n = (n - 59150) + 59150 := by omega
                                                                      rw [heq]
                                                                      exact ⟨a0_g3_w33 ⟨n - 59150, hr⟩, a1_g3_w33 ⟨n - 59150, hr⟩⟩
                                                                    · by_cases h34 : n < 59250
                                                                      · have hr : n - 59200 < 50 := by omega
                                                                        have heq : n = (n - 59200) + 59200 := by omega
                                                                        rw [heq]
                                                                        exact ⟨a0_g3_w34 ⟨n - 59200, hr⟩, a1_g3_w34 ⟨n - 59200, hr⟩⟩
                                                                      · by_cases h35 : n < 59300
                                                                        · have hr : n - 59250 < 50 := by omega
                                                                          have heq : n = (n - 59250) + 59250 := by omega
                                                                          rw [heq]
                                                                          exact ⟨a0_g3_w35 ⟨n - 59250, hr⟩, a1_g3_w35 ⟨n - 59250, hr⟩⟩
                                                                        · by_cases h36 : n < 59350
                                                                          · have hr : n - 59300 < 50 := by omega
                                                                            have heq : n = (n - 59300) + 59300 := by omega
                                                                            rw [heq]
                                                                            exact ⟨a0_g3_w36 ⟨n - 59300, hr⟩, a1_g3_w36 ⟨n - 59300, hr⟩⟩
                                                                          · by_cases h37 : n < 59400
                                                                            · have hr : n - 59350 < 50 := by omega
                                                                              have heq : n = (n - 59350) + 59350 := by omega
                                                                              rw [heq]
                                                                              exact ⟨a0_g3_w37 ⟨n - 59350, hr⟩, a1_g3_w37 ⟨n - 59350, hr⟩⟩
                                                                            · by_cases h38 : n < 59450
                                                                              · have hr : n - 59400 < 50 := by omega
                                                                                have heq : n = (n - 59400) + 59400 := by omega
                                                                                rw [heq]
                                                                                exact ⟨a0_g3_w38 ⟨n - 59400, hr⟩, a1_g3_w38 ⟨n - 59400, hr⟩⟩
                                                                              · by_cases h39 : n < 59500
                                                                                · have hr : n - 59450 < 50 := by omega
                                                                                  have heq : n = (n - 59450) + 59450 := by omega
                                                                                  rw [heq]
                                                                                  exact ⟨a0_g3_w39 ⟨n - 59450, hr⟩, a1_g3_w39 ⟨n - 59450, hr⟩⟩
                                                                                · by_cases h40 : n < 59550
                                                                                  · have hr : n - 59500 < 50 := by omega
                                                                                    have heq : n = (n - 59500) + 59500 := by omega
                                                                                    rw [heq]
                                                                                    exact ⟨a0_g3_w40 ⟨n - 59500, hr⟩, a1_g3_w40 ⟨n - 59500, hr⟩⟩
                                                                                  · by_cases h41 : n < 59600
                                                                                    · have hr : n - 59550 < 50 := by omega
                                                                                      have heq : n = (n - 59550) + 59550 := by omega
                                                                                      rw [heq]
                                                                                      exact ⟨a0_g3_w41 ⟨n - 59550, hr⟩, a1_g3_w41 ⟨n - 59550, hr⟩⟩
                                                                                    · by_cases h42 : n < 59650
                                                                                      · have hr : n - 59600 < 50 := by omega
                                                                                        have heq : n = (n - 59600) + 59600 := by omega
                                                                                        rw [heq]
                                                                                        exact ⟨a0_g3_w42 ⟨n - 59600, hr⟩, a1_g3_w42 ⟨n - 59600, hr⟩⟩
                                                                                      · by_cases h43 : n < 59700
                                                                                        · have hr : n - 59650 < 50 := by omega
                                                                                          have heq : n = (n - 59650) + 59650 := by omega
                                                                                          rw [heq]
                                                                                          exact ⟨a0_g3_w43 ⟨n - 59650, hr⟩, a1_g3_w43 ⟨n - 59650, hr⟩⟩
                                                                                        · by_cases h44 : n < 59750
                                                                                          · have hr : n - 59700 < 50 := by omega
                                                                                            have heq : n = (n - 59700) + 59700 := by omega
                                                                                            rw [heq]
                                                                                            exact ⟨a0_g3_w44 ⟨n - 59700, hr⟩, a1_g3_w44 ⟨n - 59700, hr⟩⟩
                                                                                          · by_cases h45 : n < 59800
                                                                                            · have hr : n - 59750 < 50 := by omega
                                                                                              have heq : n = (n - 59750) + 59750 := by omega
                                                                                              rw [heq]
                                                                                              exact ⟨a0_g3_w45 ⟨n - 59750, hr⟩, a1_g3_w45 ⟨n - 59750, hr⟩⟩
                                                                                            · by_cases h46 : n < 59850
                                                                                              · have hr : n - 59800 < 50 := by omega
                                                                                                have heq : n = (n - 59800) + 59800 := by omega
                                                                                                rw [heq]
                                                                                                exact ⟨a0_g3_w46 ⟨n - 59800, hr⟩, a1_g3_w46 ⟨n - 59800, hr⟩⟩
                                                                                              · by_cases h47 : n < 59900
                                                                                                · have hr : n - 59850 < 50 := by omega
                                                                                                  have heq : n = (n - 59850) + 59850 := by omega
                                                                                                  rw [heq]
                                                                                                  exact ⟨a0_g3_w47 ⟨n - 59850, hr⟩, a1_g3_w47 ⟨n - 59850, hr⟩⟩
                                                                                                · by_cases h48 : n < 59950
                                                                                                  · have hr : n - 59900 < 50 := by omega
                                                                                                    have heq : n = (n - 59900) + 59900 := by omega
                                                                                                    rw [heq]
                                                                                                    exact ⟨a0_g3_w48 ⟨n - 59900, hr⟩, a1_g3_w48 ⟨n - 59900, hr⟩⟩
                                                                                                  · have hr : n - 59950 < 50 := by omega
                                                                                                    have heq : n = (n - 59950) + 59950 := by omega
                                                                                                    rw [heq]
                                                                                                    exact ⟨a0_g3_w49 ⟨n - 59950, hr⟩, a1_g3_w49 ⟨n - 59950, hr⟩⟩

private theorem a0_g4_w0 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 60000)) 65535) ≤ dimF (n.val + 60000) := by decide
private theorem a1_g4_w0 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 60000)) 16) ≤ dimF (n.val + 60000) := by decide
private theorem a0_g4_w1 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 60050)) 65535) ≤ dimF (n.val + 60050) := by decide
private theorem a1_g4_w1 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 60050)) 16) ≤ dimF (n.val + 60050) := by decide
private theorem a0_g4_w2 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 60100)) 65535) ≤ dimF (n.val + 60100) := by decide
private theorem a1_g4_w2 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 60100)) 16) ≤ dimF (n.val + 60100) := by decide
private theorem a0_g4_w3 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 60150)) 65535) ≤ dimF (n.val + 60150) := by decide
private theorem a1_g4_w3 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 60150)) 16) ≤ dimF (n.val + 60150) := by decide
private theorem a0_g4_w4 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 60200)) 65535) ≤ dimF (n.val + 60200) := by decide
private theorem a1_g4_w4 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 60200)) 16) ≤ dimF (n.val + 60200) := by decide
private theorem a0_g4_w5 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 60250)) 65535) ≤ dimF (n.val + 60250) := by decide
private theorem a1_g4_w5 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 60250)) 16) ≤ dimF (n.val + 60250) := by decide
private theorem a0_g4_w6 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 60300)) 65535) ≤ dimF (n.val + 60300) := by decide
private theorem a1_g4_w6 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 60300)) 16) ≤ dimF (n.val + 60300) := by decide
private theorem a0_g4_w7 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 60350)) 65535) ≤ dimF (n.val + 60350) := by decide
private theorem a1_g4_w7 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 60350)) 16) ≤ dimF (n.val + 60350) := by decide
private theorem a0_g4_w8 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 60400)) 65535) ≤ dimF (n.val + 60400) := by decide
private theorem a1_g4_w8 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 60400)) 16) ≤ dimF (n.val + 60400) := by decide
private theorem a0_g4_w9 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 60450)) 65535) ≤ dimF (n.val + 60450) := by decide
private theorem a1_g4_w9 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 60450)) 16) ≤ dimF (n.val + 60450) := by decide
private theorem a0_g4_w10 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 60500)) 65535) ≤ dimF (n.val + 60500) := by decide
private theorem a1_g4_w10 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 60500)) 16) ≤ dimF (n.val + 60500) := by decide
private theorem a0_g4_w11 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 60550)) 65535) ≤ dimF (n.val + 60550) := by decide
private theorem a1_g4_w11 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 60550)) 16) ≤ dimF (n.val + 60550) := by decide
private theorem a0_g4_w12 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 60600)) 65535) ≤ dimF (n.val + 60600) := by decide
private theorem a1_g4_w12 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 60600)) 16) ≤ dimF (n.val + 60600) := by decide
private theorem a0_g4_w13 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 60650)) 65535) ≤ dimF (n.val + 60650) := by decide
private theorem a1_g4_w13 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 60650)) 16) ≤ dimF (n.val + 60650) := by decide
private theorem a0_g4_w14 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 60700)) 65535) ≤ dimF (n.val + 60700) := by decide
private theorem a1_g4_w14 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 60700)) 16) ≤ dimF (n.val + 60700) := by decide
private theorem a0_g4_w15 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 60750)) 65535) ≤ dimF (n.val + 60750) := by decide
private theorem a1_g4_w15 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 60750)) 16) ≤ dimF (n.val + 60750) := by decide
private theorem a0_g4_w16 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 60800)) 65535) ≤ dimF (n.val + 60800) := by decide
private theorem a1_g4_w16 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 60800)) 16) ≤ dimF (n.val + 60800) := by decide
private theorem a0_g4_w17 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 60850)) 65535) ≤ dimF (n.val + 60850) := by decide
private theorem a1_g4_w17 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 60850)) 16) ≤ dimF (n.val + 60850) := by decide
private theorem a0_g4_w18 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 60900)) 65535) ≤ dimF (n.val + 60900) := by decide
private theorem a1_g4_w18 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 60900)) 16) ≤ dimF (n.val + 60900) := by decide
private theorem a0_g4_w19 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 60950)) 65535) ≤ dimF (n.val + 60950) := by decide
private theorem a1_g4_w19 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 60950)) 16) ≤ dimF (n.val + 60950) := by decide
private theorem a0_g4_w20 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 61000)) 65535) ≤ dimF (n.val + 61000) := by decide
private theorem a1_g4_w20 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 61000)) 16) ≤ dimF (n.val + 61000) := by decide
private theorem a0_g4_w21 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 61050)) 65535) ≤ dimF (n.val + 61050) := by decide
private theorem a1_g4_w21 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 61050)) 16) ≤ dimF (n.val + 61050) := by decide
private theorem a0_g4_w22 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 61100)) 65535) ≤ dimF (n.val + 61100) := by decide
private theorem a1_g4_w22 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 61100)) 16) ≤ dimF (n.val + 61100) := by decide
private theorem a0_g4_w23 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 61150)) 65535) ≤ dimF (n.val + 61150) := by decide
private theorem a1_g4_w23 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 61150)) 16) ≤ dimF (n.val + 61150) := by decide
private theorem a0_g4_w24 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 61200)) 65535) ≤ dimF (n.val + 61200) := by decide
private theorem a1_g4_w24 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 61200)) 16) ≤ dimF (n.val + 61200) := by decide
private theorem a0_g4_w25 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 61250)) 65535) ≤ dimF (n.val + 61250) := by decide
private theorem a1_g4_w25 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 61250)) 16) ≤ dimF (n.val + 61250) := by decide
private theorem a0_g4_w26 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 61300)) 65535) ≤ dimF (n.val + 61300) := by decide
private theorem a1_g4_w26 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 61300)) 16) ≤ dimF (n.val + 61300) := by decide
private theorem a0_g4_w27 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 61350)) 65535) ≤ dimF (n.val + 61350) := by decide
private theorem a1_g4_w27 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 61350)) 16) ≤ dimF (n.val + 61350) := by decide
private theorem a0_g4_w28 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 61400)) 65535) ≤ dimF (n.val + 61400) := by decide
private theorem a1_g4_w28 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 61400)) 16) ≤ dimF (n.val + 61400) := by decide
private theorem a0_g4_w29 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 61450)) 65535) ≤ dimF (n.val + 61450) := by decide
private theorem a1_g4_w29 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 61450)) 16) ≤ dimF (n.val + 61450) := by decide
private theorem a0_g4_w30 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 61500)) 65535) ≤ dimF (n.val + 61500) := by decide
private theorem a1_g4_w30 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 61500)) 16) ≤ dimF (n.val + 61500) := by decide
private theorem a0_g4_w31 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 61550)) 65535) ≤ dimF (n.val + 61550) := by decide
private theorem a1_g4_w31 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 61550)) 16) ≤ dimF (n.val + 61550) := by decide
private theorem a0_g4_w32 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 61600)) 65535) ≤ dimF (n.val + 61600) := by decide
private theorem a1_g4_w32 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 61600)) 16) ≤ dimF (n.val + 61600) := by decide
private theorem a0_g4_w33 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 61650)) 65535) ≤ dimF (n.val + 61650) := by decide
private theorem a1_g4_w33 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 61650)) 16) ≤ dimF (n.val + 61650) := by decide
private theorem a0_g4_w34 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 61700)) 65535) ≤ dimF (n.val + 61700) := by decide
private theorem a1_g4_w34 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 61700)) 16) ≤ dimF (n.val + 61700) := by decide
private theorem a0_g4_w35 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 61750)) 65535) ≤ dimF (n.val + 61750) := by decide
private theorem a1_g4_w35 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 61750)) 16) ≤ dimF (n.val + 61750) := by decide
private theorem a0_g4_w36 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 61800)) 65535) ≤ dimF (n.val + 61800) := by decide
private theorem a1_g4_w36 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 61800)) 16) ≤ dimF (n.val + 61800) := by decide
private theorem a0_g4_w37 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 61850)) 65535) ≤ dimF (n.val + 61850) := by decide
private theorem a1_g4_w37 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 61850)) 16) ≤ dimF (n.val + 61850) := by decide
private theorem a0_g4_w38 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 61900)) 65535) ≤ dimF (n.val + 61900) := by decide
private theorem a1_g4_w38 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 61900)) 16) ≤ dimF (n.val + 61900) := by decide
private theorem a0_g4_w39 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 61950)) 65535) ≤ dimF (n.val + 61950) := by decide
private theorem a1_g4_w39 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 61950)) 16) ≤ dimF (n.val + 61950) := by decide
private theorem a0_g4_w40 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 62000)) 65535) ≤ dimF (n.val + 62000) := by decide
private theorem a1_g4_w40 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 62000)) 16) ≤ dimF (n.val + 62000) := by decide
private theorem a0_g4_w41 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 62050)) 65535) ≤ dimF (n.val + 62050) := by decide
private theorem a1_g4_w41 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 62050)) 16) ≤ dimF (n.val + 62050) := by decide
private theorem a0_g4_w42 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 62100)) 65535) ≤ dimF (n.val + 62100) := by decide
private theorem a1_g4_w42 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 62100)) 16) ≤ dimF (n.val + 62100) := by decide
private theorem a0_g4_w43 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 62150)) 65535) ≤ dimF (n.val + 62150) := by decide
private theorem a1_g4_w43 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 62150)) 16) ≤ dimF (n.val + 62150) := by decide
private theorem a0_g4_w44 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 62200)) 65535) ≤ dimF (n.val + 62200) := by decide
private theorem a1_g4_w44 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 62200)) 16) ≤ dimF (n.val + 62200) := by decide
private theorem a0_g4_w45 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 62250)) 65535) ≤ dimF (n.val + 62250) := by decide
private theorem a1_g4_w45 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 62250)) 16) ≤ dimF (n.val + 62250) := by decide
private theorem a0_g4_w46 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 62300)) 65535) ≤ dimF (n.val + 62300) := by decide
private theorem a1_g4_w46 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 62300)) 16) ≤ dimF (n.val + 62300) := by decide
private theorem a0_g4_w47 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 62350)) 65535) ≤ dimF (n.val + 62350) := by decide
private theorem a1_g4_w47 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 62350)) 16) ≤ dimF (n.val + 62350) := by decide
private theorem a0_g4_w48 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 62400)) 65535) ≤ dimF (n.val + 62400) := by decide
private theorem a1_g4_w48 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 62400)) 16) ≤ dimF (n.val + 62400) := by decide
private theorem a0_g4_w49 : ∀ n : Fin 28, dimF (Nat.land (argF (n.val + 62450)) 65535) ≤ dimF (n.val + 62450) := by decide
private theorem a1_g4_w49 : ∀ n : Fin 28, dimF (Nat.shiftRight (argF (n.val + 62450)) 16) ≤ dimF (n.val + 62450) := by decide

private theorem pair_g4 (n : ℕ) (hlo : 60000 ≤ n) (hhi : n < 62478) :
    dimF (Nat.land (argF n) 65535) ≤ dimF n ∧
    dimF (Nat.shiftRight (argF n) 16) ≤ dimF n := by
  by_cases h0 : n < 60050
  · have hr : n - 60000 < 50 := by omega
    have heq : n = (n - 60000) + 60000 := by omega
    rw [heq]
    exact ⟨a0_g4_w0 ⟨n - 60000, hr⟩, a1_g4_w0 ⟨n - 60000, hr⟩⟩
  · by_cases h1 : n < 60100
    · have hr : n - 60050 < 50 := by omega
      have heq : n = (n - 60050) + 60050 := by omega
      rw [heq]
      exact ⟨a0_g4_w1 ⟨n - 60050, hr⟩, a1_g4_w1 ⟨n - 60050, hr⟩⟩
    · by_cases h2 : n < 60150
      · have hr : n - 60100 < 50 := by omega
        have heq : n = (n - 60100) + 60100 := by omega
        rw [heq]
        exact ⟨a0_g4_w2 ⟨n - 60100, hr⟩, a1_g4_w2 ⟨n - 60100, hr⟩⟩
      · by_cases h3 : n < 60200
        · have hr : n - 60150 < 50 := by omega
          have heq : n = (n - 60150) + 60150 := by omega
          rw [heq]
          exact ⟨a0_g4_w3 ⟨n - 60150, hr⟩, a1_g4_w3 ⟨n - 60150, hr⟩⟩
        · by_cases h4 : n < 60250
          · have hr : n - 60200 < 50 := by omega
            have heq : n = (n - 60200) + 60200 := by omega
            rw [heq]
            exact ⟨a0_g4_w4 ⟨n - 60200, hr⟩, a1_g4_w4 ⟨n - 60200, hr⟩⟩
          · by_cases h5 : n < 60300
            · have hr : n - 60250 < 50 := by omega
              have heq : n = (n - 60250) + 60250 := by omega
              rw [heq]
              exact ⟨a0_g4_w5 ⟨n - 60250, hr⟩, a1_g4_w5 ⟨n - 60250, hr⟩⟩
            · by_cases h6 : n < 60350
              · have hr : n - 60300 < 50 := by omega
                have heq : n = (n - 60300) + 60300 := by omega
                rw [heq]
                exact ⟨a0_g4_w6 ⟨n - 60300, hr⟩, a1_g4_w6 ⟨n - 60300, hr⟩⟩
              · by_cases h7 : n < 60400
                · have hr : n - 60350 < 50 := by omega
                  have heq : n = (n - 60350) + 60350 := by omega
                  rw [heq]
                  exact ⟨a0_g4_w7 ⟨n - 60350, hr⟩, a1_g4_w7 ⟨n - 60350, hr⟩⟩
                · by_cases h8 : n < 60450
                  · have hr : n - 60400 < 50 := by omega
                    have heq : n = (n - 60400) + 60400 := by omega
                    rw [heq]
                    exact ⟨a0_g4_w8 ⟨n - 60400, hr⟩, a1_g4_w8 ⟨n - 60400, hr⟩⟩
                  · by_cases h9 : n < 60500
                    · have hr : n - 60450 < 50 := by omega
                      have heq : n = (n - 60450) + 60450 := by omega
                      rw [heq]
                      exact ⟨a0_g4_w9 ⟨n - 60450, hr⟩, a1_g4_w9 ⟨n - 60450, hr⟩⟩
                    · by_cases h10 : n < 60550
                      · have hr : n - 60500 < 50 := by omega
                        have heq : n = (n - 60500) + 60500 := by omega
                        rw [heq]
                        exact ⟨a0_g4_w10 ⟨n - 60500, hr⟩, a1_g4_w10 ⟨n - 60500, hr⟩⟩
                      · by_cases h11 : n < 60600
                        · have hr : n - 60550 < 50 := by omega
                          have heq : n = (n - 60550) + 60550 := by omega
                          rw [heq]
                          exact ⟨a0_g4_w11 ⟨n - 60550, hr⟩, a1_g4_w11 ⟨n - 60550, hr⟩⟩
                        · by_cases h12 : n < 60650
                          · have hr : n - 60600 < 50 := by omega
                            have heq : n = (n - 60600) + 60600 := by omega
                            rw [heq]
                            exact ⟨a0_g4_w12 ⟨n - 60600, hr⟩, a1_g4_w12 ⟨n - 60600, hr⟩⟩
                          · by_cases h13 : n < 60700
                            · have hr : n - 60650 < 50 := by omega
                              have heq : n = (n - 60650) + 60650 := by omega
                              rw [heq]
                              exact ⟨a0_g4_w13 ⟨n - 60650, hr⟩, a1_g4_w13 ⟨n - 60650, hr⟩⟩
                            · by_cases h14 : n < 60750
                              · have hr : n - 60700 < 50 := by omega
                                have heq : n = (n - 60700) + 60700 := by omega
                                rw [heq]
                                exact ⟨a0_g4_w14 ⟨n - 60700, hr⟩, a1_g4_w14 ⟨n - 60700, hr⟩⟩
                              · by_cases h15 : n < 60800
                                · have hr : n - 60750 < 50 := by omega
                                  have heq : n = (n - 60750) + 60750 := by omega
                                  rw [heq]
                                  exact ⟨a0_g4_w15 ⟨n - 60750, hr⟩, a1_g4_w15 ⟨n - 60750, hr⟩⟩
                                · by_cases h16 : n < 60850
                                  · have hr : n - 60800 < 50 := by omega
                                    have heq : n = (n - 60800) + 60800 := by omega
                                    rw [heq]
                                    exact ⟨a0_g4_w16 ⟨n - 60800, hr⟩, a1_g4_w16 ⟨n - 60800, hr⟩⟩
                                  · by_cases h17 : n < 60900
                                    · have hr : n - 60850 < 50 := by omega
                                      have heq : n = (n - 60850) + 60850 := by omega
                                      rw [heq]
                                      exact ⟨a0_g4_w17 ⟨n - 60850, hr⟩, a1_g4_w17 ⟨n - 60850, hr⟩⟩
                                    · by_cases h18 : n < 60950
                                      · have hr : n - 60900 < 50 := by omega
                                        have heq : n = (n - 60900) + 60900 := by omega
                                        rw [heq]
                                        exact ⟨a0_g4_w18 ⟨n - 60900, hr⟩, a1_g4_w18 ⟨n - 60900, hr⟩⟩
                                      · by_cases h19 : n < 61000
                                        · have hr : n - 60950 < 50 := by omega
                                          have heq : n = (n - 60950) + 60950 := by omega
                                          rw [heq]
                                          exact ⟨a0_g4_w19 ⟨n - 60950, hr⟩, a1_g4_w19 ⟨n - 60950, hr⟩⟩
                                        · by_cases h20 : n < 61050
                                          · have hr : n - 61000 < 50 := by omega
                                            have heq : n = (n - 61000) + 61000 := by omega
                                            rw [heq]
                                            exact ⟨a0_g4_w20 ⟨n - 61000, hr⟩, a1_g4_w20 ⟨n - 61000, hr⟩⟩
                                          · by_cases h21 : n < 61100
                                            · have hr : n - 61050 < 50 := by omega
                                              have heq : n = (n - 61050) + 61050 := by omega
                                              rw [heq]
                                              exact ⟨a0_g4_w21 ⟨n - 61050, hr⟩, a1_g4_w21 ⟨n - 61050, hr⟩⟩
                                            · by_cases h22 : n < 61150
                                              · have hr : n - 61100 < 50 := by omega
                                                have heq : n = (n - 61100) + 61100 := by omega
                                                rw [heq]
                                                exact ⟨a0_g4_w22 ⟨n - 61100, hr⟩, a1_g4_w22 ⟨n - 61100, hr⟩⟩
                                              · by_cases h23 : n < 61200
                                                · have hr : n - 61150 < 50 := by omega
                                                  have heq : n = (n - 61150) + 61150 := by omega
                                                  rw [heq]
                                                  exact ⟨a0_g4_w23 ⟨n - 61150, hr⟩, a1_g4_w23 ⟨n - 61150, hr⟩⟩
                                                · by_cases h24 : n < 61250
                                                  · have hr : n - 61200 < 50 := by omega
                                                    have heq : n = (n - 61200) + 61200 := by omega
                                                    rw [heq]
                                                    exact ⟨a0_g4_w24 ⟨n - 61200, hr⟩, a1_g4_w24 ⟨n - 61200, hr⟩⟩
                                                  · by_cases h25 : n < 61300
                                                    · have hr : n - 61250 < 50 := by omega
                                                      have heq : n = (n - 61250) + 61250 := by omega
                                                      rw [heq]
                                                      exact ⟨a0_g4_w25 ⟨n - 61250, hr⟩, a1_g4_w25 ⟨n - 61250, hr⟩⟩
                                                    · by_cases h26 : n < 61350
                                                      · have hr : n - 61300 < 50 := by omega
                                                        have heq : n = (n - 61300) + 61300 := by omega
                                                        rw [heq]
                                                        exact ⟨a0_g4_w26 ⟨n - 61300, hr⟩, a1_g4_w26 ⟨n - 61300, hr⟩⟩
                                                      · by_cases h27 : n < 61400
                                                        · have hr : n - 61350 < 50 := by omega
                                                          have heq : n = (n - 61350) + 61350 := by omega
                                                          rw [heq]
                                                          exact ⟨a0_g4_w27 ⟨n - 61350, hr⟩, a1_g4_w27 ⟨n - 61350, hr⟩⟩
                                                        · by_cases h28 : n < 61450
                                                          · have hr : n - 61400 < 50 := by omega
                                                            have heq : n = (n - 61400) + 61400 := by omega
                                                            rw [heq]
                                                            exact ⟨a0_g4_w28 ⟨n - 61400, hr⟩, a1_g4_w28 ⟨n - 61400, hr⟩⟩
                                                          · by_cases h29 : n < 61500
                                                            · have hr : n - 61450 < 50 := by omega
                                                              have heq : n = (n - 61450) + 61450 := by omega
                                                              rw [heq]
                                                              exact ⟨a0_g4_w29 ⟨n - 61450, hr⟩, a1_g4_w29 ⟨n - 61450, hr⟩⟩
                                                            · by_cases h30 : n < 61550
                                                              · have hr : n - 61500 < 50 := by omega
                                                                have heq : n = (n - 61500) + 61500 := by omega
                                                                rw [heq]
                                                                exact ⟨a0_g4_w30 ⟨n - 61500, hr⟩, a1_g4_w30 ⟨n - 61500, hr⟩⟩
                                                              · by_cases h31 : n < 61600
                                                                · have hr : n - 61550 < 50 := by omega
                                                                  have heq : n = (n - 61550) + 61550 := by omega
                                                                  rw [heq]
                                                                  exact ⟨a0_g4_w31 ⟨n - 61550, hr⟩, a1_g4_w31 ⟨n - 61550, hr⟩⟩
                                                                · by_cases h32 : n < 61650
                                                                  · have hr : n - 61600 < 50 := by omega
                                                                    have heq : n = (n - 61600) + 61600 := by omega
                                                                    rw [heq]
                                                                    exact ⟨a0_g4_w32 ⟨n - 61600, hr⟩, a1_g4_w32 ⟨n - 61600, hr⟩⟩
                                                                  · by_cases h33 : n < 61700
                                                                    · have hr : n - 61650 < 50 := by omega
                                                                      have heq : n = (n - 61650) + 61650 := by omega
                                                                      rw [heq]
                                                                      exact ⟨a0_g4_w33 ⟨n - 61650, hr⟩, a1_g4_w33 ⟨n - 61650, hr⟩⟩
                                                                    · by_cases h34 : n < 61750
                                                                      · have hr : n - 61700 < 50 := by omega
                                                                        have heq : n = (n - 61700) + 61700 := by omega
                                                                        rw [heq]
                                                                        exact ⟨a0_g4_w34 ⟨n - 61700, hr⟩, a1_g4_w34 ⟨n - 61700, hr⟩⟩
                                                                      · by_cases h35 : n < 61800
                                                                        · have hr : n - 61750 < 50 := by omega
                                                                          have heq : n = (n - 61750) + 61750 := by omega
                                                                          rw [heq]
                                                                          exact ⟨a0_g4_w35 ⟨n - 61750, hr⟩, a1_g4_w35 ⟨n - 61750, hr⟩⟩
                                                                        · by_cases h36 : n < 61850
                                                                          · have hr : n - 61800 < 50 := by omega
                                                                            have heq : n = (n - 61800) + 61800 := by omega
                                                                            rw [heq]
                                                                            exact ⟨a0_g4_w36 ⟨n - 61800, hr⟩, a1_g4_w36 ⟨n - 61800, hr⟩⟩
                                                                          · by_cases h37 : n < 61900
                                                                            · have hr : n - 61850 < 50 := by omega
                                                                              have heq : n = (n - 61850) + 61850 := by omega
                                                                              rw [heq]
                                                                              exact ⟨a0_g4_w37 ⟨n - 61850, hr⟩, a1_g4_w37 ⟨n - 61850, hr⟩⟩
                                                                            · by_cases h38 : n < 61950
                                                                              · have hr : n - 61900 < 50 := by omega
                                                                                have heq : n = (n - 61900) + 61900 := by omega
                                                                                rw [heq]
                                                                                exact ⟨a0_g4_w38 ⟨n - 61900, hr⟩, a1_g4_w38 ⟨n - 61900, hr⟩⟩
                                                                              · by_cases h39 : n < 62000
                                                                                · have hr : n - 61950 < 50 := by omega
                                                                                  have heq : n = (n - 61950) + 61950 := by omega
                                                                                  rw [heq]
                                                                                  exact ⟨a0_g4_w39 ⟨n - 61950, hr⟩, a1_g4_w39 ⟨n - 61950, hr⟩⟩
                                                                                · by_cases h40 : n < 62050
                                                                                  · have hr : n - 62000 < 50 := by omega
                                                                                    have heq : n = (n - 62000) + 62000 := by omega
                                                                                    rw [heq]
                                                                                    exact ⟨a0_g4_w40 ⟨n - 62000, hr⟩, a1_g4_w40 ⟨n - 62000, hr⟩⟩
                                                                                  · by_cases h41 : n < 62100
                                                                                    · have hr : n - 62050 < 50 := by omega
                                                                                      have heq : n = (n - 62050) + 62050 := by omega
                                                                                      rw [heq]
                                                                                      exact ⟨a0_g4_w41 ⟨n - 62050, hr⟩, a1_g4_w41 ⟨n - 62050, hr⟩⟩
                                                                                    · by_cases h42 : n < 62150
                                                                                      · have hr : n - 62100 < 50 := by omega
                                                                                        have heq : n = (n - 62100) + 62100 := by omega
                                                                                        rw [heq]
                                                                                        exact ⟨a0_g4_w42 ⟨n - 62100, hr⟩, a1_g4_w42 ⟨n - 62100, hr⟩⟩
                                                                                      · by_cases h43 : n < 62200
                                                                                        · have hr : n - 62150 < 50 := by omega
                                                                                          have heq : n = (n - 62150) + 62150 := by omega
                                                                                          rw [heq]
                                                                                          exact ⟨a0_g4_w43 ⟨n - 62150, hr⟩, a1_g4_w43 ⟨n - 62150, hr⟩⟩
                                                                                        · by_cases h44 : n < 62250
                                                                                          · have hr : n - 62200 < 50 := by omega
                                                                                            have heq : n = (n - 62200) + 62200 := by omega
                                                                                            rw [heq]
                                                                                            exact ⟨a0_g4_w44 ⟨n - 62200, hr⟩, a1_g4_w44 ⟨n - 62200, hr⟩⟩
                                                                                          · by_cases h45 : n < 62300
                                                                                            · have hr : n - 62250 < 50 := by omega
                                                                                              have heq : n = (n - 62250) + 62250 := by omega
                                                                                              rw [heq]
                                                                                              exact ⟨a0_g4_w45 ⟨n - 62250, hr⟩, a1_g4_w45 ⟨n - 62250, hr⟩⟩
                                                                                            · by_cases h46 : n < 62350
                                                                                              · have hr : n - 62300 < 50 := by omega
                                                                                                have heq : n = (n - 62300) + 62300 := by omega
                                                                                                rw [heq]
                                                                                                exact ⟨a0_g4_w46 ⟨n - 62300, hr⟩, a1_g4_w46 ⟨n - 62300, hr⟩⟩
                                                                                              · by_cases h47 : n < 62400
                                                                                                · have hr : n - 62350 < 50 := by omega
                                                                                                  have heq : n = (n - 62350) + 62350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact ⟨a0_g4_w47 ⟨n - 62350, hr⟩, a1_g4_w47 ⟨n - 62350, hr⟩⟩
                                                                                                · by_cases h48 : n < 62450
                                                                                                  · have hr : n - 62400 < 50 := by omega
                                                                                                    have heq : n = (n - 62400) + 62400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact ⟨a0_g4_w48 ⟨n - 62400, hr⟩, a1_g4_w48 ⟨n - 62400, hr⟩⟩
                                                                                                  · have hr : n - 62450 < 28 := by omega
                                                                                                    have heq : n = (n - 62450) + 62450 := by omega
                                                                                                    rw [heq]
                                                                                                    exact ⟨a0_g4_w49 ⟨n - 62450, hr⟩, a1_g4_w49 ⟨n - 62450, hr⟩⟩

theorem solution (n : ℕ) (hn0 : 50000 ≤ n) (hn1 : n < 62478) :
    dimF (Nat.land (argF n) 65535) ≤ dimF n ∧
    dimF (Nat.shiftRight (argF n) 16) ≤ dimF n := by
  by_cases hg0 : n < 52500
  · exact pair_g0 n (by omega) hg0
  · by_cases hg1 : n < 55000
    · exact pair_g1 n (by omega) hg1
    · by_cases hg2 : n < 57500
      · exact pair_g2 n (by omega) hg2
      · by_cases hg3 : n < 60000
        · exact pair_g3 n (by omega) hg3
        · exact pair_g4 n (by omega) hn1
