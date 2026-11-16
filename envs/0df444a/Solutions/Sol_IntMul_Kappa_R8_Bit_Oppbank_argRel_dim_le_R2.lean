-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.argRel_dim_le_R2
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T09:36:56.088416+00:00
-- url     : https://prove2.me/submissions/877bf3f3-1d56-497c-a8d5-5292db836db2

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG

private theorem a0_g0_w0 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 25000)) 65535) ≤ dimF (n.val + 25000) := by decide
private theorem a1_g0_w0 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 25000)) 16) ≤ dimF (n.val + 25000) := by decide
private theorem a0_g0_w1 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 25050)) 65535) ≤ dimF (n.val + 25050) := by decide
private theorem a1_g0_w1 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 25050)) 16) ≤ dimF (n.val + 25050) := by decide
private theorem a0_g0_w2 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 25100)) 65535) ≤ dimF (n.val + 25100) := by decide
private theorem a1_g0_w2 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 25100)) 16) ≤ dimF (n.val + 25100) := by decide
private theorem a0_g0_w3 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 25150)) 65535) ≤ dimF (n.val + 25150) := by decide
private theorem a1_g0_w3 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 25150)) 16) ≤ dimF (n.val + 25150) := by decide
private theorem a0_g0_w4 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 25200)) 65535) ≤ dimF (n.val + 25200) := by decide
private theorem a1_g0_w4 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 25200)) 16) ≤ dimF (n.val + 25200) := by decide
private theorem a0_g0_w5 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 25250)) 65535) ≤ dimF (n.val + 25250) := by decide
private theorem a1_g0_w5 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 25250)) 16) ≤ dimF (n.val + 25250) := by decide
private theorem a0_g0_w6 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 25300)) 65535) ≤ dimF (n.val + 25300) := by decide
private theorem a1_g0_w6 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 25300)) 16) ≤ dimF (n.val + 25300) := by decide
private theorem a0_g0_w7 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 25350)) 65535) ≤ dimF (n.val + 25350) := by decide
private theorem a1_g0_w7 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 25350)) 16) ≤ dimF (n.val + 25350) := by decide
private theorem a0_g0_w8 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 25400)) 65535) ≤ dimF (n.val + 25400) := by decide
private theorem a1_g0_w8 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 25400)) 16) ≤ dimF (n.val + 25400) := by decide
private theorem a0_g0_w9 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 25450)) 65535) ≤ dimF (n.val + 25450) := by decide
private theorem a1_g0_w9 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 25450)) 16) ≤ dimF (n.val + 25450) := by decide
private theorem a0_g0_w10 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 25500)) 65535) ≤ dimF (n.val + 25500) := by decide
private theorem a1_g0_w10 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 25500)) 16) ≤ dimF (n.val + 25500) := by decide
private theorem a0_g0_w11 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 25550)) 65535) ≤ dimF (n.val + 25550) := by decide
private theorem a1_g0_w11 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 25550)) 16) ≤ dimF (n.val + 25550) := by decide
private theorem a0_g0_w12 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 25600)) 65535) ≤ dimF (n.val + 25600) := by decide
private theorem a1_g0_w12 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 25600)) 16) ≤ dimF (n.val + 25600) := by decide
private theorem a0_g0_w13 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 25650)) 65535) ≤ dimF (n.val + 25650) := by decide
private theorem a1_g0_w13 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 25650)) 16) ≤ dimF (n.val + 25650) := by decide
private theorem a0_g0_w14 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 25700)) 65535) ≤ dimF (n.val + 25700) := by decide
private theorem a1_g0_w14 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 25700)) 16) ≤ dimF (n.val + 25700) := by decide
private theorem a0_g0_w15 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 25750)) 65535) ≤ dimF (n.val + 25750) := by decide
private theorem a1_g0_w15 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 25750)) 16) ≤ dimF (n.val + 25750) := by decide
private theorem a0_g0_w16 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 25800)) 65535) ≤ dimF (n.val + 25800) := by decide
private theorem a1_g0_w16 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 25800)) 16) ≤ dimF (n.val + 25800) := by decide
private theorem a0_g0_w17 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 25850)) 65535) ≤ dimF (n.val + 25850) := by decide
private theorem a1_g0_w17 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 25850)) 16) ≤ dimF (n.val + 25850) := by decide
private theorem a0_g0_w18 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 25900)) 65535) ≤ dimF (n.val + 25900) := by decide
private theorem a1_g0_w18 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 25900)) 16) ≤ dimF (n.val + 25900) := by decide
private theorem a0_g0_w19 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 25950)) 65535) ≤ dimF (n.val + 25950) := by decide
private theorem a1_g0_w19 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 25950)) 16) ≤ dimF (n.val + 25950) := by decide
private theorem a0_g0_w20 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 26000)) 65535) ≤ dimF (n.val + 26000) := by decide
private theorem a1_g0_w20 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 26000)) 16) ≤ dimF (n.val + 26000) := by decide
private theorem a0_g0_w21 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 26050)) 65535) ≤ dimF (n.val + 26050) := by decide
private theorem a1_g0_w21 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 26050)) 16) ≤ dimF (n.val + 26050) := by decide
private theorem a0_g0_w22 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 26100)) 65535) ≤ dimF (n.val + 26100) := by decide
private theorem a1_g0_w22 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 26100)) 16) ≤ dimF (n.val + 26100) := by decide
private theorem a0_g0_w23 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 26150)) 65535) ≤ dimF (n.val + 26150) := by decide
private theorem a1_g0_w23 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 26150)) 16) ≤ dimF (n.val + 26150) := by decide
private theorem a0_g0_w24 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 26200)) 65535) ≤ dimF (n.val + 26200) := by decide
private theorem a1_g0_w24 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 26200)) 16) ≤ dimF (n.val + 26200) := by decide
private theorem a0_g0_w25 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 26250)) 65535) ≤ dimF (n.val + 26250) := by decide
private theorem a1_g0_w25 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 26250)) 16) ≤ dimF (n.val + 26250) := by decide
private theorem a0_g0_w26 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 26300)) 65535) ≤ dimF (n.val + 26300) := by decide
private theorem a1_g0_w26 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 26300)) 16) ≤ dimF (n.val + 26300) := by decide
private theorem a0_g0_w27 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 26350)) 65535) ≤ dimF (n.val + 26350) := by decide
private theorem a1_g0_w27 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 26350)) 16) ≤ dimF (n.val + 26350) := by decide
private theorem a0_g0_w28 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 26400)) 65535) ≤ dimF (n.val + 26400) := by decide
private theorem a1_g0_w28 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 26400)) 16) ≤ dimF (n.val + 26400) := by decide
private theorem a0_g0_w29 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 26450)) 65535) ≤ dimF (n.val + 26450) := by decide
private theorem a1_g0_w29 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 26450)) 16) ≤ dimF (n.val + 26450) := by decide
private theorem a0_g0_w30 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 26500)) 65535) ≤ dimF (n.val + 26500) := by decide
private theorem a1_g0_w30 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 26500)) 16) ≤ dimF (n.val + 26500) := by decide
private theorem a0_g0_w31 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 26550)) 65535) ≤ dimF (n.val + 26550) := by decide
private theorem a1_g0_w31 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 26550)) 16) ≤ dimF (n.val + 26550) := by decide
private theorem a0_g0_w32 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 26600)) 65535) ≤ dimF (n.val + 26600) := by decide
private theorem a1_g0_w32 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 26600)) 16) ≤ dimF (n.val + 26600) := by decide
private theorem a0_g0_w33 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 26650)) 65535) ≤ dimF (n.val + 26650) := by decide
private theorem a1_g0_w33 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 26650)) 16) ≤ dimF (n.val + 26650) := by decide
private theorem a0_g0_w34 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 26700)) 65535) ≤ dimF (n.val + 26700) := by decide
private theorem a1_g0_w34 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 26700)) 16) ≤ dimF (n.val + 26700) := by decide
private theorem a0_g0_w35 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 26750)) 65535) ≤ dimF (n.val + 26750) := by decide
private theorem a1_g0_w35 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 26750)) 16) ≤ dimF (n.val + 26750) := by decide
private theorem a0_g0_w36 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 26800)) 65535) ≤ dimF (n.val + 26800) := by decide
private theorem a1_g0_w36 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 26800)) 16) ≤ dimF (n.val + 26800) := by decide
private theorem a0_g0_w37 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 26850)) 65535) ≤ dimF (n.val + 26850) := by decide
private theorem a1_g0_w37 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 26850)) 16) ≤ dimF (n.val + 26850) := by decide
private theorem a0_g0_w38 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 26900)) 65535) ≤ dimF (n.val + 26900) := by decide
private theorem a1_g0_w38 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 26900)) 16) ≤ dimF (n.val + 26900) := by decide
private theorem a0_g0_w39 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 26950)) 65535) ≤ dimF (n.val + 26950) := by decide
private theorem a1_g0_w39 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 26950)) 16) ≤ dimF (n.val + 26950) := by decide
private theorem a0_g0_w40 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 27000)) 65535) ≤ dimF (n.val + 27000) := by decide
private theorem a1_g0_w40 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 27000)) 16) ≤ dimF (n.val + 27000) := by decide
private theorem a0_g0_w41 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 27050)) 65535) ≤ dimF (n.val + 27050) := by decide
private theorem a1_g0_w41 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 27050)) 16) ≤ dimF (n.val + 27050) := by decide
private theorem a0_g0_w42 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 27100)) 65535) ≤ dimF (n.val + 27100) := by decide
private theorem a1_g0_w42 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 27100)) 16) ≤ dimF (n.val + 27100) := by decide
private theorem a0_g0_w43 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 27150)) 65535) ≤ dimF (n.val + 27150) := by decide
private theorem a1_g0_w43 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 27150)) 16) ≤ dimF (n.val + 27150) := by decide
private theorem a0_g0_w44 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 27200)) 65535) ≤ dimF (n.val + 27200) := by decide
private theorem a1_g0_w44 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 27200)) 16) ≤ dimF (n.val + 27200) := by decide
private theorem a0_g0_w45 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 27250)) 65535) ≤ dimF (n.val + 27250) := by decide
private theorem a1_g0_w45 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 27250)) 16) ≤ dimF (n.val + 27250) := by decide
private theorem a0_g0_w46 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 27300)) 65535) ≤ dimF (n.val + 27300) := by decide
private theorem a1_g0_w46 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 27300)) 16) ≤ dimF (n.val + 27300) := by decide
private theorem a0_g0_w47 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 27350)) 65535) ≤ dimF (n.val + 27350) := by decide
private theorem a1_g0_w47 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 27350)) 16) ≤ dimF (n.val + 27350) := by decide
private theorem a0_g0_w48 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 27400)) 65535) ≤ dimF (n.val + 27400) := by decide
private theorem a1_g0_w48 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 27400)) 16) ≤ dimF (n.val + 27400) := by decide
private theorem a0_g0_w49 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 27450)) 65535) ≤ dimF (n.val + 27450) := by decide
private theorem a1_g0_w49 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 27450)) 16) ≤ dimF (n.val + 27450) := by decide

private theorem pair_g0 (n : ℕ) (hlo : 25000 ≤ n) (hhi : n < 27500) :
    dimF (Nat.land (argF n) 65535) ≤ dimF n ∧
    dimF (Nat.shiftRight (argF n) 16) ≤ dimF n := by
  by_cases h0 : n < 25050
  · have hr : n - 25000 < 50 := by omega
    have heq : n = (n - 25000) + 25000 := by omega
    rw [heq]
    exact ⟨a0_g0_w0 ⟨n - 25000, hr⟩, a1_g0_w0 ⟨n - 25000, hr⟩⟩
  · by_cases h1 : n < 25100
    · have hr : n - 25050 < 50 := by omega
      have heq : n = (n - 25050) + 25050 := by omega
      rw [heq]
      exact ⟨a0_g0_w1 ⟨n - 25050, hr⟩, a1_g0_w1 ⟨n - 25050, hr⟩⟩
    · by_cases h2 : n < 25150
      · have hr : n - 25100 < 50 := by omega
        have heq : n = (n - 25100) + 25100 := by omega
        rw [heq]
        exact ⟨a0_g0_w2 ⟨n - 25100, hr⟩, a1_g0_w2 ⟨n - 25100, hr⟩⟩
      · by_cases h3 : n < 25200
        · have hr : n - 25150 < 50 := by omega
          have heq : n = (n - 25150) + 25150 := by omega
          rw [heq]
          exact ⟨a0_g0_w3 ⟨n - 25150, hr⟩, a1_g0_w3 ⟨n - 25150, hr⟩⟩
        · by_cases h4 : n < 25250
          · have hr : n - 25200 < 50 := by omega
            have heq : n = (n - 25200) + 25200 := by omega
            rw [heq]
            exact ⟨a0_g0_w4 ⟨n - 25200, hr⟩, a1_g0_w4 ⟨n - 25200, hr⟩⟩
          · by_cases h5 : n < 25300
            · have hr : n - 25250 < 50 := by omega
              have heq : n = (n - 25250) + 25250 := by omega
              rw [heq]
              exact ⟨a0_g0_w5 ⟨n - 25250, hr⟩, a1_g0_w5 ⟨n - 25250, hr⟩⟩
            · by_cases h6 : n < 25350
              · have hr : n - 25300 < 50 := by omega
                have heq : n = (n - 25300) + 25300 := by omega
                rw [heq]
                exact ⟨a0_g0_w6 ⟨n - 25300, hr⟩, a1_g0_w6 ⟨n - 25300, hr⟩⟩
              · by_cases h7 : n < 25400
                · have hr : n - 25350 < 50 := by omega
                  have heq : n = (n - 25350) + 25350 := by omega
                  rw [heq]
                  exact ⟨a0_g0_w7 ⟨n - 25350, hr⟩, a1_g0_w7 ⟨n - 25350, hr⟩⟩
                · by_cases h8 : n < 25450
                  · have hr : n - 25400 < 50 := by omega
                    have heq : n = (n - 25400) + 25400 := by omega
                    rw [heq]
                    exact ⟨a0_g0_w8 ⟨n - 25400, hr⟩, a1_g0_w8 ⟨n - 25400, hr⟩⟩
                  · by_cases h9 : n < 25500
                    · have hr : n - 25450 < 50 := by omega
                      have heq : n = (n - 25450) + 25450 := by omega
                      rw [heq]
                      exact ⟨a0_g0_w9 ⟨n - 25450, hr⟩, a1_g0_w9 ⟨n - 25450, hr⟩⟩
                    · by_cases h10 : n < 25550
                      · have hr : n - 25500 < 50 := by omega
                        have heq : n = (n - 25500) + 25500 := by omega
                        rw [heq]
                        exact ⟨a0_g0_w10 ⟨n - 25500, hr⟩, a1_g0_w10 ⟨n - 25500, hr⟩⟩
                      · by_cases h11 : n < 25600
                        · have hr : n - 25550 < 50 := by omega
                          have heq : n = (n - 25550) + 25550 := by omega
                          rw [heq]
                          exact ⟨a0_g0_w11 ⟨n - 25550, hr⟩, a1_g0_w11 ⟨n - 25550, hr⟩⟩
                        · by_cases h12 : n < 25650
                          · have hr : n - 25600 < 50 := by omega
                            have heq : n = (n - 25600) + 25600 := by omega
                            rw [heq]
                            exact ⟨a0_g0_w12 ⟨n - 25600, hr⟩, a1_g0_w12 ⟨n - 25600, hr⟩⟩
                          · by_cases h13 : n < 25700
                            · have hr : n - 25650 < 50 := by omega
                              have heq : n = (n - 25650) + 25650 := by omega
                              rw [heq]
                              exact ⟨a0_g0_w13 ⟨n - 25650, hr⟩, a1_g0_w13 ⟨n - 25650, hr⟩⟩
                            · by_cases h14 : n < 25750
                              · have hr : n - 25700 < 50 := by omega
                                have heq : n = (n - 25700) + 25700 := by omega
                                rw [heq]
                                exact ⟨a0_g0_w14 ⟨n - 25700, hr⟩, a1_g0_w14 ⟨n - 25700, hr⟩⟩
                              · by_cases h15 : n < 25800
                                · have hr : n - 25750 < 50 := by omega
                                  have heq : n = (n - 25750) + 25750 := by omega
                                  rw [heq]
                                  exact ⟨a0_g0_w15 ⟨n - 25750, hr⟩, a1_g0_w15 ⟨n - 25750, hr⟩⟩
                                · by_cases h16 : n < 25850
                                  · have hr : n - 25800 < 50 := by omega
                                    have heq : n = (n - 25800) + 25800 := by omega
                                    rw [heq]
                                    exact ⟨a0_g0_w16 ⟨n - 25800, hr⟩, a1_g0_w16 ⟨n - 25800, hr⟩⟩
                                  · by_cases h17 : n < 25900
                                    · have hr : n - 25850 < 50 := by omega
                                      have heq : n = (n - 25850) + 25850 := by omega
                                      rw [heq]
                                      exact ⟨a0_g0_w17 ⟨n - 25850, hr⟩, a1_g0_w17 ⟨n - 25850, hr⟩⟩
                                    · by_cases h18 : n < 25950
                                      · have hr : n - 25900 < 50 := by omega
                                        have heq : n = (n - 25900) + 25900 := by omega
                                        rw [heq]
                                        exact ⟨a0_g0_w18 ⟨n - 25900, hr⟩, a1_g0_w18 ⟨n - 25900, hr⟩⟩
                                      · by_cases h19 : n < 26000
                                        · have hr : n - 25950 < 50 := by omega
                                          have heq : n = (n - 25950) + 25950 := by omega
                                          rw [heq]
                                          exact ⟨a0_g0_w19 ⟨n - 25950, hr⟩, a1_g0_w19 ⟨n - 25950, hr⟩⟩
                                        · by_cases h20 : n < 26050
                                          · have hr : n - 26000 < 50 := by omega
                                            have heq : n = (n - 26000) + 26000 := by omega
                                            rw [heq]
                                            exact ⟨a0_g0_w20 ⟨n - 26000, hr⟩, a1_g0_w20 ⟨n - 26000, hr⟩⟩
                                          · by_cases h21 : n < 26100
                                            · have hr : n - 26050 < 50 := by omega
                                              have heq : n = (n - 26050) + 26050 := by omega
                                              rw [heq]
                                              exact ⟨a0_g0_w21 ⟨n - 26050, hr⟩, a1_g0_w21 ⟨n - 26050, hr⟩⟩
                                            · by_cases h22 : n < 26150
                                              · have hr : n - 26100 < 50 := by omega
                                                have heq : n = (n - 26100) + 26100 := by omega
                                                rw [heq]
                                                exact ⟨a0_g0_w22 ⟨n - 26100, hr⟩, a1_g0_w22 ⟨n - 26100, hr⟩⟩
                                              · by_cases h23 : n < 26200
                                                · have hr : n - 26150 < 50 := by omega
                                                  have heq : n = (n - 26150) + 26150 := by omega
                                                  rw [heq]
                                                  exact ⟨a0_g0_w23 ⟨n - 26150, hr⟩, a1_g0_w23 ⟨n - 26150, hr⟩⟩
                                                · by_cases h24 : n < 26250
                                                  · have hr : n - 26200 < 50 := by omega
                                                    have heq : n = (n - 26200) + 26200 := by omega
                                                    rw [heq]
                                                    exact ⟨a0_g0_w24 ⟨n - 26200, hr⟩, a1_g0_w24 ⟨n - 26200, hr⟩⟩
                                                  · by_cases h25 : n < 26300
                                                    · have hr : n - 26250 < 50 := by omega
                                                      have heq : n = (n - 26250) + 26250 := by omega
                                                      rw [heq]
                                                      exact ⟨a0_g0_w25 ⟨n - 26250, hr⟩, a1_g0_w25 ⟨n - 26250, hr⟩⟩
                                                    · by_cases h26 : n < 26350
                                                      · have hr : n - 26300 < 50 := by omega
                                                        have heq : n = (n - 26300) + 26300 := by omega
                                                        rw [heq]
                                                        exact ⟨a0_g0_w26 ⟨n - 26300, hr⟩, a1_g0_w26 ⟨n - 26300, hr⟩⟩
                                                      · by_cases h27 : n < 26400
                                                        · have hr : n - 26350 < 50 := by omega
                                                          have heq : n = (n - 26350) + 26350 := by omega
                                                          rw [heq]
                                                          exact ⟨a0_g0_w27 ⟨n - 26350, hr⟩, a1_g0_w27 ⟨n - 26350, hr⟩⟩
                                                        · by_cases h28 : n < 26450
                                                          · have hr : n - 26400 < 50 := by omega
                                                            have heq : n = (n - 26400) + 26400 := by omega
                                                            rw [heq]
                                                            exact ⟨a0_g0_w28 ⟨n - 26400, hr⟩, a1_g0_w28 ⟨n - 26400, hr⟩⟩
                                                          · by_cases h29 : n < 26500
                                                            · have hr : n - 26450 < 50 := by omega
                                                              have heq : n = (n - 26450) + 26450 := by omega
                                                              rw [heq]
                                                              exact ⟨a0_g0_w29 ⟨n - 26450, hr⟩, a1_g0_w29 ⟨n - 26450, hr⟩⟩
                                                            · by_cases h30 : n < 26550
                                                              · have hr : n - 26500 < 50 := by omega
                                                                have heq : n = (n - 26500) + 26500 := by omega
                                                                rw [heq]
                                                                exact ⟨a0_g0_w30 ⟨n - 26500, hr⟩, a1_g0_w30 ⟨n - 26500, hr⟩⟩
                                                              · by_cases h31 : n < 26600
                                                                · have hr : n - 26550 < 50 := by omega
                                                                  have heq : n = (n - 26550) + 26550 := by omega
                                                                  rw [heq]
                                                                  exact ⟨a0_g0_w31 ⟨n - 26550, hr⟩, a1_g0_w31 ⟨n - 26550, hr⟩⟩
                                                                · by_cases h32 : n < 26650
                                                                  · have hr : n - 26600 < 50 := by omega
                                                                    have heq : n = (n - 26600) + 26600 := by omega
                                                                    rw [heq]
                                                                    exact ⟨a0_g0_w32 ⟨n - 26600, hr⟩, a1_g0_w32 ⟨n - 26600, hr⟩⟩
                                                                  · by_cases h33 : n < 26700
                                                                    · have hr : n - 26650 < 50 := by omega
                                                                      have heq : n = (n - 26650) + 26650 := by omega
                                                                      rw [heq]
                                                                      exact ⟨a0_g0_w33 ⟨n - 26650, hr⟩, a1_g0_w33 ⟨n - 26650, hr⟩⟩
                                                                    · by_cases h34 : n < 26750
                                                                      · have hr : n - 26700 < 50 := by omega
                                                                        have heq : n = (n - 26700) + 26700 := by omega
                                                                        rw [heq]
                                                                        exact ⟨a0_g0_w34 ⟨n - 26700, hr⟩, a1_g0_w34 ⟨n - 26700, hr⟩⟩
                                                                      · by_cases h35 : n < 26800
                                                                        · have hr : n - 26750 < 50 := by omega
                                                                          have heq : n = (n - 26750) + 26750 := by omega
                                                                          rw [heq]
                                                                          exact ⟨a0_g0_w35 ⟨n - 26750, hr⟩, a1_g0_w35 ⟨n - 26750, hr⟩⟩
                                                                        · by_cases h36 : n < 26850
                                                                          · have hr : n - 26800 < 50 := by omega
                                                                            have heq : n = (n - 26800) + 26800 := by omega
                                                                            rw [heq]
                                                                            exact ⟨a0_g0_w36 ⟨n - 26800, hr⟩, a1_g0_w36 ⟨n - 26800, hr⟩⟩
                                                                          · by_cases h37 : n < 26900
                                                                            · have hr : n - 26850 < 50 := by omega
                                                                              have heq : n = (n - 26850) + 26850 := by omega
                                                                              rw [heq]
                                                                              exact ⟨a0_g0_w37 ⟨n - 26850, hr⟩, a1_g0_w37 ⟨n - 26850, hr⟩⟩
                                                                            · by_cases h38 : n < 26950
                                                                              · have hr : n - 26900 < 50 := by omega
                                                                                have heq : n = (n - 26900) + 26900 := by omega
                                                                                rw [heq]
                                                                                exact ⟨a0_g0_w38 ⟨n - 26900, hr⟩, a1_g0_w38 ⟨n - 26900, hr⟩⟩
                                                                              · by_cases h39 : n < 27000
                                                                                · have hr : n - 26950 < 50 := by omega
                                                                                  have heq : n = (n - 26950) + 26950 := by omega
                                                                                  rw [heq]
                                                                                  exact ⟨a0_g0_w39 ⟨n - 26950, hr⟩, a1_g0_w39 ⟨n - 26950, hr⟩⟩
                                                                                · by_cases h40 : n < 27050
                                                                                  · have hr : n - 27000 < 50 := by omega
                                                                                    have heq : n = (n - 27000) + 27000 := by omega
                                                                                    rw [heq]
                                                                                    exact ⟨a0_g0_w40 ⟨n - 27000, hr⟩, a1_g0_w40 ⟨n - 27000, hr⟩⟩
                                                                                  · by_cases h41 : n < 27100
                                                                                    · have hr : n - 27050 < 50 := by omega
                                                                                      have heq : n = (n - 27050) + 27050 := by omega
                                                                                      rw [heq]
                                                                                      exact ⟨a0_g0_w41 ⟨n - 27050, hr⟩, a1_g0_w41 ⟨n - 27050, hr⟩⟩
                                                                                    · by_cases h42 : n < 27150
                                                                                      · have hr : n - 27100 < 50 := by omega
                                                                                        have heq : n = (n - 27100) + 27100 := by omega
                                                                                        rw [heq]
                                                                                        exact ⟨a0_g0_w42 ⟨n - 27100, hr⟩, a1_g0_w42 ⟨n - 27100, hr⟩⟩
                                                                                      · by_cases h43 : n < 27200
                                                                                        · have hr : n - 27150 < 50 := by omega
                                                                                          have heq : n = (n - 27150) + 27150 := by omega
                                                                                          rw [heq]
                                                                                          exact ⟨a0_g0_w43 ⟨n - 27150, hr⟩, a1_g0_w43 ⟨n - 27150, hr⟩⟩
                                                                                        · by_cases h44 : n < 27250
                                                                                          · have hr : n - 27200 < 50 := by omega
                                                                                            have heq : n = (n - 27200) + 27200 := by omega
                                                                                            rw [heq]
                                                                                            exact ⟨a0_g0_w44 ⟨n - 27200, hr⟩, a1_g0_w44 ⟨n - 27200, hr⟩⟩
                                                                                          · by_cases h45 : n < 27300
                                                                                            · have hr : n - 27250 < 50 := by omega
                                                                                              have heq : n = (n - 27250) + 27250 := by omega
                                                                                              rw [heq]
                                                                                              exact ⟨a0_g0_w45 ⟨n - 27250, hr⟩, a1_g0_w45 ⟨n - 27250, hr⟩⟩
                                                                                            · by_cases h46 : n < 27350
                                                                                              · have hr : n - 27300 < 50 := by omega
                                                                                                have heq : n = (n - 27300) + 27300 := by omega
                                                                                                rw [heq]
                                                                                                exact ⟨a0_g0_w46 ⟨n - 27300, hr⟩, a1_g0_w46 ⟨n - 27300, hr⟩⟩
                                                                                              · by_cases h47 : n < 27400
                                                                                                · have hr : n - 27350 < 50 := by omega
                                                                                                  have heq : n = (n - 27350) + 27350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact ⟨a0_g0_w47 ⟨n - 27350, hr⟩, a1_g0_w47 ⟨n - 27350, hr⟩⟩
                                                                                                · by_cases h48 : n < 27450
                                                                                                  · have hr : n - 27400 < 50 := by omega
                                                                                                    have heq : n = (n - 27400) + 27400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact ⟨a0_g0_w48 ⟨n - 27400, hr⟩, a1_g0_w48 ⟨n - 27400, hr⟩⟩
                                                                                                  · have hr : n - 27450 < 50 := by omega
                                                                                                    have heq : n = (n - 27450) + 27450 := by omega
                                                                                                    rw [heq]
                                                                                                    exact ⟨a0_g0_w49 ⟨n - 27450, hr⟩, a1_g0_w49 ⟨n - 27450, hr⟩⟩

private theorem a0_g1_w0 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 27500)) 65535) ≤ dimF (n.val + 27500) := by decide
private theorem a1_g1_w0 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 27500)) 16) ≤ dimF (n.val + 27500) := by decide
private theorem a0_g1_w1 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 27550)) 65535) ≤ dimF (n.val + 27550) := by decide
private theorem a1_g1_w1 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 27550)) 16) ≤ dimF (n.val + 27550) := by decide
private theorem a0_g1_w2 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 27600)) 65535) ≤ dimF (n.val + 27600) := by decide
private theorem a1_g1_w2 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 27600)) 16) ≤ dimF (n.val + 27600) := by decide
private theorem a0_g1_w3 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 27650)) 65535) ≤ dimF (n.val + 27650) := by decide
private theorem a1_g1_w3 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 27650)) 16) ≤ dimF (n.val + 27650) := by decide
private theorem a0_g1_w4 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 27700)) 65535) ≤ dimF (n.val + 27700) := by decide
private theorem a1_g1_w4 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 27700)) 16) ≤ dimF (n.val + 27700) := by decide
private theorem a0_g1_w5 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 27750)) 65535) ≤ dimF (n.val + 27750) := by decide
private theorem a1_g1_w5 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 27750)) 16) ≤ dimF (n.val + 27750) := by decide
private theorem a0_g1_w6 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 27800)) 65535) ≤ dimF (n.val + 27800) := by decide
private theorem a1_g1_w6 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 27800)) 16) ≤ dimF (n.val + 27800) := by decide
private theorem a0_g1_w7 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 27850)) 65535) ≤ dimF (n.val + 27850) := by decide
private theorem a1_g1_w7 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 27850)) 16) ≤ dimF (n.val + 27850) := by decide
private theorem a0_g1_w8 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 27900)) 65535) ≤ dimF (n.val + 27900) := by decide
private theorem a1_g1_w8 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 27900)) 16) ≤ dimF (n.val + 27900) := by decide
private theorem a0_g1_w9 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 27950)) 65535) ≤ dimF (n.val + 27950) := by decide
private theorem a1_g1_w9 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 27950)) 16) ≤ dimF (n.val + 27950) := by decide
private theorem a0_g1_w10 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 28000)) 65535) ≤ dimF (n.val + 28000) := by decide
private theorem a1_g1_w10 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 28000)) 16) ≤ dimF (n.val + 28000) := by decide
private theorem a0_g1_w11 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 28050)) 65535) ≤ dimF (n.val + 28050) := by decide
private theorem a1_g1_w11 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 28050)) 16) ≤ dimF (n.val + 28050) := by decide
private theorem a0_g1_w12 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 28100)) 65535) ≤ dimF (n.val + 28100) := by decide
private theorem a1_g1_w12 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 28100)) 16) ≤ dimF (n.val + 28100) := by decide
private theorem a0_g1_w13 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 28150)) 65535) ≤ dimF (n.val + 28150) := by decide
private theorem a1_g1_w13 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 28150)) 16) ≤ dimF (n.val + 28150) := by decide
private theorem a0_g1_w14 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 28200)) 65535) ≤ dimF (n.val + 28200) := by decide
private theorem a1_g1_w14 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 28200)) 16) ≤ dimF (n.val + 28200) := by decide
private theorem a0_g1_w15 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 28250)) 65535) ≤ dimF (n.val + 28250) := by decide
private theorem a1_g1_w15 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 28250)) 16) ≤ dimF (n.val + 28250) := by decide
private theorem a0_g1_w16 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 28300)) 65535) ≤ dimF (n.val + 28300) := by decide
private theorem a1_g1_w16 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 28300)) 16) ≤ dimF (n.val + 28300) := by decide
private theorem a0_g1_w17 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 28350)) 65535) ≤ dimF (n.val + 28350) := by decide
private theorem a1_g1_w17 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 28350)) 16) ≤ dimF (n.val + 28350) := by decide
private theorem a0_g1_w18 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 28400)) 65535) ≤ dimF (n.val + 28400) := by decide
private theorem a1_g1_w18 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 28400)) 16) ≤ dimF (n.val + 28400) := by decide
private theorem a0_g1_w19 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 28450)) 65535) ≤ dimF (n.val + 28450) := by decide
private theorem a1_g1_w19 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 28450)) 16) ≤ dimF (n.val + 28450) := by decide
private theorem a0_g1_w20 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 28500)) 65535) ≤ dimF (n.val + 28500) := by decide
private theorem a1_g1_w20 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 28500)) 16) ≤ dimF (n.val + 28500) := by decide
private theorem a0_g1_w21 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 28550)) 65535) ≤ dimF (n.val + 28550) := by decide
private theorem a1_g1_w21 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 28550)) 16) ≤ dimF (n.val + 28550) := by decide
private theorem a0_g1_w22 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 28600)) 65535) ≤ dimF (n.val + 28600) := by decide
private theorem a1_g1_w22 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 28600)) 16) ≤ dimF (n.val + 28600) := by decide
private theorem a0_g1_w23 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 28650)) 65535) ≤ dimF (n.val + 28650) := by decide
private theorem a1_g1_w23 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 28650)) 16) ≤ dimF (n.val + 28650) := by decide
private theorem a0_g1_w24 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 28700)) 65535) ≤ dimF (n.val + 28700) := by decide
private theorem a1_g1_w24 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 28700)) 16) ≤ dimF (n.val + 28700) := by decide
private theorem a0_g1_w25 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 28750)) 65535) ≤ dimF (n.val + 28750) := by decide
private theorem a1_g1_w25 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 28750)) 16) ≤ dimF (n.val + 28750) := by decide
private theorem a0_g1_w26 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 28800)) 65535) ≤ dimF (n.val + 28800) := by decide
private theorem a1_g1_w26 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 28800)) 16) ≤ dimF (n.val + 28800) := by decide
private theorem a0_g1_w27 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 28850)) 65535) ≤ dimF (n.val + 28850) := by decide
private theorem a1_g1_w27 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 28850)) 16) ≤ dimF (n.val + 28850) := by decide
private theorem a0_g1_w28 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 28900)) 65535) ≤ dimF (n.val + 28900) := by decide
private theorem a1_g1_w28 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 28900)) 16) ≤ dimF (n.val + 28900) := by decide
private theorem a0_g1_w29 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 28950)) 65535) ≤ dimF (n.val + 28950) := by decide
private theorem a1_g1_w29 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 28950)) 16) ≤ dimF (n.val + 28950) := by decide
private theorem a0_g1_w30 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 29000)) 65535) ≤ dimF (n.val + 29000) := by decide
private theorem a1_g1_w30 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 29000)) 16) ≤ dimF (n.val + 29000) := by decide
private theorem a0_g1_w31 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 29050)) 65535) ≤ dimF (n.val + 29050) := by decide
private theorem a1_g1_w31 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 29050)) 16) ≤ dimF (n.val + 29050) := by decide
private theorem a0_g1_w32 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 29100)) 65535) ≤ dimF (n.val + 29100) := by decide
private theorem a1_g1_w32 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 29100)) 16) ≤ dimF (n.val + 29100) := by decide
private theorem a0_g1_w33 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 29150)) 65535) ≤ dimF (n.val + 29150) := by decide
private theorem a1_g1_w33 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 29150)) 16) ≤ dimF (n.val + 29150) := by decide
private theorem a0_g1_w34 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 29200)) 65535) ≤ dimF (n.val + 29200) := by decide
private theorem a1_g1_w34 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 29200)) 16) ≤ dimF (n.val + 29200) := by decide
private theorem a0_g1_w35 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 29250)) 65535) ≤ dimF (n.val + 29250) := by decide
private theorem a1_g1_w35 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 29250)) 16) ≤ dimF (n.val + 29250) := by decide
private theorem a0_g1_w36 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 29300)) 65535) ≤ dimF (n.val + 29300) := by decide
private theorem a1_g1_w36 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 29300)) 16) ≤ dimF (n.val + 29300) := by decide
private theorem a0_g1_w37 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 29350)) 65535) ≤ dimF (n.val + 29350) := by decide
private theorem a1_g1_w37 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 29350)) 16) ≤ dimF (n.val + 29350) := by decide
private theorem a0_g1_w38 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 29400)) 65535) ≤ dimF (n.val + 29400) := by decide
private theorem a1_g1_w38 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 29400)) 16) ≤ dimF (n.val + 29400) := by decide
private theorem a0_g1_w39 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 29450)) 65535) ≤ dimF (n.val + 29450) := by decide
private theorem a1_g1_w39 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 29450)) 16) ≤ dimF (n.val + 29450) := by decide
private theorem a0_g1_w40 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 29500)) 65535) ≤ dimF (n.val + 29500) := by decide
private theorem a1_g1_w40 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 29500)) 16) ≤ dimF (n.val + 29500) := by decide
private theorem a0_g1_w41 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 29550)) 65535) ≤ dimF (n.val + 29550) := by decide
private theorem a1_g1_w41 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 29550)) 16) ≤ dimF (n.val + 29550) := by decide
private theorem a0_g1_w42 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 29600)) 65535) ≤ dimF (n.val + 29600) := by decide
private theorem a1_g1_w42 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 29600)) 16) ≤ dimF (n.val + 29600) := by decide
private theorem a0_g1_w43 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 29650)) 65535) ≤ dimF (n.val + 29650) := by decide
private theorem a1_g1_w43 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 29650)) 16) ≤ dimF (n.val + 29650) := by decide
private theorem a0_g1_w44 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 29700)) 65535) ≤ dimF (n.val + 29700) := by decide
private theorem a1_g1_w44 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 29700)) 16) ≤ dimF (n.val + 29700) := by decide
private theorem a0_g1_w45 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 29750)) 65535) ≤ dimF (n.val + 29750) := by decide
private theorem a1_g1_w45 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 29750)) 16) ≤ dimF (n.val + 29750) := by decide
private theorem a0_g1_w46 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 29800)) 65535) ≤ dimF (n.val + 29800) := by decide
private theorem a1_g1_w46 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 29800)) 16) ≤ dimF (n.val + 29800) := by decide
private theorem a0_g1_w47 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 29850)) 65535) ≤ dimF (n.val + 29850) := by decide
private theorem a1_g1_w47 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 29850)) 16) ≤ dimF (n.val + 29850) := by decide
private theorem a0_g1_w48 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 29900)) 65535) ≤ dimF (n.val + 29900) := by decide
private theorem a1_g1_w48 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 29900)) 16) ≤ dimF (n.val + 29900) := by decide
private theorem a0_g1_w49 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 29950)) 65535) ≤ dimF (n.val + 29950) := by decide
private theorem a1_g1_w49 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 29950)) 16) ≤ dimF (n.val + 29950) := by decide

private theorem pair_g1 (n : ℕ) (hlo : 27500 ≤ n) (hhi : n < 30000) :
    dimF (Nat.land (argF n) 65535) ≤ dimF n ∧
    dimF (Nat.shiftRight (argF n) 16) ≤ dimF n := by
  by_cases h0 : n < 27550
  · have hr : n - 27500 < 50 := by omega
    have heq : n = (n - 27500) + 27500 := by omega
    rw [heq]
    exact ⟨a0_g1_w0 ⟨n - 27500, hr⟩, a1_g1_w0 ⟨n - 27500, hr⟩⟩
  · by_cases h1 : n < 27600
    · have hr : n - 27550 < 50 := by omega
      have heq : n = (n - 27550) + 27550 := by omega
      rw [heq]
      exact ⟨a0_g1_w1 ⟨n - 27550, hr⟩, a1_g1_w1 ⟨n - 27550, hr⟩⟩
    · by_cases h2 : n < 27650
      · have hr : n - 27600 < 50 := by omega
        have heq : n = (n - 27600) + 27600 := by omega
        rw [heq]
        exact ⟨a0_g1_w2 ⟨n - 27600, hr⟩, a1_g1_w2 ⟨n - 27600, hr⟩⟩
      · by_cases h3 : n < 27700
        · have hr : n - 27650 < 50 := by omega
          have heq : n = (n - 27650) + 27650 := by omega
          rw [heq]
          exact ⟨a0_g1_w3 ⟨n - 27650, hr⟩, a1_g1_w3 ⟨n - 27650, hr⟩⟩
        · by_cases h4 : n < 27750
          · have hr : n - 27700 < 50 := by omega
            have heq : n = (n - 27700) + 27700 := by omega
            rw [heq]
            exact ⟨a0_g1_w4 ⟨n - 27700, hr⟩, a1_g1_w4 ⟨n - 27700, hr⟩⟩
          · by_cases h5 : n < 27800
            · have hr : n - 27750 < 50 := by omega
              have heq : n = (n - 27750) + 27750 := by omega
              rw [heq]
              exact ⟨a0_g1_w5 ⟨n - 27750, hr⟩, a1_g1_w5 ⟨n - 27750, hr⟩⟩
            · by_cases h6 : n < 27850
              · have hr : n - 27800 < 50 := by omega
                have heq : n = (n - 27800) + 27800 := by omega
                rw [heq]
                exact ⟨a0_g1_w6 ⟨n - 27800, hr⟩, a1_g1_w6 ⟨n - 27800, hr⟩⟩
              · by_cases h7 : n < 27900
                · have hr : n - 27850 < 50 := by omega
                  have heq : n = (n - 27850) + 27850 := by omega
                  rw [heq]
                  exact ⟨a0_g1_w7 ⟨n - 27850, hr⟩, a1_g1_w7 ⟨n - 27850, hr⟩⟩
                · by_cases h8 : n < 27950
                  · have hr : n - 27900 < 50 := by omega
                    have heq : n = (n - 27900) + 27900 := by omega
                    rw [heq]
                    exact ⟨a0_g1_w8 ⟨n - 27900, hr⟩, a1_g1_w8 ⟨n - 27900, hr⟩⟩
                  · by_cases h9 : n < 28000
                    · have hr : n - 27950 < 50 := by omega
                      have heq : n = (n - 27950) + 27950 := by omega
                      rw [heq]
                      exact ⟨a0_g1_w9 ⟨n - 27950, hr⟩, a1_g1_w9 ⟨n - 27950, hr⟩⟩
                    · by_cases h10 : n < 28050
                      · have hr : n - 28000 < 50 := by omega
                        have heq : n = (n - 28000) + 28000 := by omega
                        rw [heq]
                        exact ⟨a0_g1_w10 ⟨n - 28000, hr⟩, a1_g1_w10 ⟨n - 28000, hr⟩⟩
                      · by_cases h11 : n < 28100
                        · have hr : n - 28050 < 50 := by omega
                          have heq : n = (n - 28050) + 28050 := by omega
                          rw [heq]
                          exact ⟨a0_g1_w11 ⟨n - 28050, hr⟩, a1_g1_w11 ⟨n - 28050, hr⟩⟩
                        · by_cases h12 : n < 28150
                          · have hr : n - 28100 < 50 := by omega
                            have heq : n = (n - 28100) + 28100 := by omega
                            rw [heq]
                            exact ⟨a0_g1_w12 ⟨n - 28100, hr⟩, a1_g1_w12 ⟨n - 28100, hr⟩⟩
                          · by_cases h13 : n < 28200
                            · have hr : n - 28150 < 50 := by omega
                              have heq : n = (n - 28150) + 28150 := by omega
                              rw [heq]
                              exact ⟨a0_g1_w13 ⟨n - 28150, hr⟩, a1_g1_w13 ⟨n - 28150, hr⟩⟩
                            · by_cases h14 : n < 28250
                              · have hr : n - 28200 < 50 := by omega
                                have heq : n = (n - 28200) + 28200 := by omega
                                rw [heq]
                                exact ⟨a0_g1_w14 ⟨n - 28200, hr⟩, a1_g1_w14 ⟨n - 28200, hr⟩⟩
                              · by_cases h15 : n < 28300
                                · have hr : n - 28250 < 50 := by omega
                                  have heq : n = (n - 28250) + 28250 := by omega
                                  rw [heq]
                                  exact ⟨a0_g1_w15 ⟨n - 28250, hr⟩, a1_g1_w15 ⟨n - 28250, hr⟩⟩
                                · by_cases h16 : n < 28350
                                  · have hr : n - 28300 < 50 := by omega
                                    have heq : n = (n - 28300) + 28300 := by omega
                                    rw [heq]
                                    exact ⟨a0_g1_w16 ⟨n - 28300, hr⟩, a1_g1_w16 ⟨n - 28300, hr⟩⟩
                                  · by_cases h17 : n < 28400
                                    · have hr : n - 28350 < 50 := by omega
                                      have heq : n = (n - 28350) + 28350 := by omega
                                      rw [heq]
                                      exact ⟨a0_g1_w17 ⟨n - 28350, hr⟩, a1_g1_w17 ⟨n - 28350, hr⟩⟩
                                    · by_cases h18 : n < 28450
                                      · have hr : n - 28400 < 50 := by omega
                                        have heq : n = (n - 28400) + 28400 := by omega
                                        rw [heq]
                                        exact ⟨a0_g1_w18 ⟨n - 28400, hr⟩, a1_g1_w18 ⟨n - 28400, hr⟩⟩
                                      · by_cases h19 : n < 28500
                                        · have hr : n - 28450 < 50 := by omega
                                          have heq : n = (n - 28450) + 28450 := by omega
                                          rw [heq]
                                          exact ⟨a0_g1_w19 ⟨n - 28450, hr⟩, a1_g1_w19 ⟨n - 28450, hr⟩⟩
                                        · by_cases h20 : n < 28550
                                          · have hr : n - 28500 < 50 := by omega
                                            have heq : n = (n - 28500) + 28500 := by omega
                                            rw [heq]
                                            exact ⟨a0_g1_w20 ⟨n - 28500, hr⟩, a1_g1_w20 ⟨n - 28500, hr⟩⟩
                                          · by_cases h21 : n < 28600
                                            · have hr : n - 28550 < 50 := by omega
                                              have heq : n = (n - 28550) + 28550 := by omega
                                              rw [heq]
                                              exact ⟨a0_g1_w21 ⟨n - 28550, hr⟩, a1_g1_w21 ⟨n - 28550, hr⟩⟩
                                            · by_cases h22 : n < 28650
                                              · have hr : n - 28600 < 50 := by omega
                                                have heq : n = (n - 28600) + 28600 := by omega
                                                rw [heq]
                                                exact ⟨a0_g1_w22 ⟨n - 28600, hr⟩, a1_g1_w22 ⟨n - 28600, hr⟩⟩
                                              · by_cases h23 : n < 28700
                                                · have hr : n - 28650 < 50 := by omega
                                                  have heq : n = (n - 28650) + 28650 := by omega
                                                  rw [heq]
                                                  exact ⟨a0_g1_w23 ⟨n - 28650, hr⟩, a1_g1_w23 ⟨n - 28650, hr⟩⟩
                                                · by_cases h24 : n < 28750
                                                  · have hr : n - 28700 < 50 := by omega
                                                    have heq : n = (n - 28700) + 28700 := by omega
                                                    rw [heq]
                                                    exact ⟨a0_g1_w24 ⟨n - 28700, hr⟩, a1_g1_w24 ⟨n - 28700, hr⟩⟩
                                                  · by_cases h25 : n < 28800
                                                    · have hr : n - 28750 < 50 := by omega
                                                      have heq : n = (n - 28750) + 28750 := by omega
                                                      rw [heq]
                                                      exact ⟨a0_g1_w25 ⟨n - 28750, hr⟩, a1_g1_w25 ⟨n - 28750, hr⟩⟩
                                                    · by_cases h26 : n < 28850
                                                      · have hr : n - 28800 < 50 := by omega
                                                        have heq : n = (n - 28800) + 28800 := by omega
                                                        rw [heq]
                                                        exact ⟨a0_g1_w26 ⟨n - 28800, hr⟩, a1_g1_w26 ⟨n - 28800, hr⟩⟩
                                                      · by_cases h27 : n < 28900
                                                        · have hr : n - 28850 < 50 := by omega
                                                          have heq : n = (n - 28850) + 28850 := by omega
                                                          rw [heq]
                                                          exact ⟨a0_g1_w27 ⟨n - 28850, hr⟩, a1_g1_w27 ⟨n - 28850, hr⟩⟩
                                                        · by_cases h28 : n < 28950
                                                          · have hr : n - 28900 < 50 := by omega
                                                            have heq : n = (n - 28900) + 28900 := by omega
                                                            rw [heq]
                                                            exact ⟨a0_g1_w28 ⟨n - 28900, hr⟩, a1_g1_w28 ⟨n - 28900, hr⟩⟩
                                                          · by_cases h29 : n < 29000
                                                            · have hr : n - 28950 < 50 := by omega
                                                              have heq : n = (n - 28950) + 28950 := by omega
                                                              rw [heq]
                                                              exact ⟨a0_g1_w29 ⟨n - 28950, hr⟩, a1_g1_w29 ⟨n - 28950, hr⟩⟩
                                                            · by_cases h30 : n < 29050
                                                              · have hr : n - 29000 < 50 := by omega
                                                                have heq : n = (n - 29000) + 29000 := by omega
                                                                rw [heq]
                                                                exact ⟨a0_g1_w30 ⟨n - 29000, hr⟩, a1_g1_w30 ⟨n - 29000, hr⟩⟩
                                                              · by_cases h31 : n < 29100
                                                                · have hr : n - 29050 < 50 := by omega
                                                                  have heq : n = (n - 29050) + 29050 := by omega
                                                                  rw [heq]
                                                                  exact ⟨a0_g1_w31 ⟨n - 29050, hr⟩, a1_g1_w31 ⟨n - 29050, hr⟩⟩
                                                                · by_cases h32 : n < 29150
                                                                  · have hr : n - 29100 < 50 := by omega
                                                                    have heq : n = (n - 29100) + 29100 := by omega
                                                                    rw [heq]
                                                                    exact ⟨a0_g1_w32 ⟨n - 29100, hr⟩, a1_g1_w32 ⟨n - 29100, hr⟩⟩
                                                                  · by_cases h33 : n < 29200
                                                                    · have hr : n - 29150 < 50 := by omega
                                                                      have heq : n = (n - 29150) + 29150 := by omega
                                                                      rw [heq]
                                                                      exact ⟨a0_g1_w33 ⟨n - 29150, hr⟩, a1_g1_w33 ⟨n - 29150, hr⟩⟩
                                                                    · by_cases h34 : n < 29250
                                                                      · have hr : n - 29200 < 50 := by omega
                                                                        have heq : n = (n - 29200) + 29200 := by omega
                                                                        rw [heq]
                                                                        exact ⟨a0_g1_w34 ⟨n - 29200, hr⟩, a1_g1_w34 ⟨n - 29200, hr⟩⟩
                                                                      · by_cases h35 : n < 29300
                                                                        · have hr : n - 29250 < 50 := by omega
                                                                          have heq : n = (n - 29250) + 29250 := by omega
                                                                          rw [heq]
                                                                          exact ⟨a0_g1_w35 ⟨n - 29250, hr⟩, a1_g1_w35 ⟨n - 29250, hr⟩⟩
                                                                        · by_cases h36 : n < 29350
                                                                          · have hr : n - 29300 < 50 := by omega
                                                                            have heq : n = (n - 29300) + 29300 := by omega
                                                                            rw [heq]
                                                                            exact ⟨a0_g1_w36 ⟨n - 29300, hr⟩, a1_g1_w36 ⟨n - 29300, hr⟩⟩
                                                                          · by_cases h37 : n < 29400
                                                                            · have hr : n - 29350 < 50 := by omega
                                                                              have heq : n = (n - 29350) + 29350 := by omega
                                                                              rw [heq]
                                                                              exact ⟨a0_g1_w37 ⟨n - 29350, hr⟩, a1_g1_w37 ⟨n - 29350, hr⟩⟩
                                                                            · by_cases h38 : n < 29450
                                                                              · have hr : n - 29400 < 50 := by omega
                                                                                have heq : n = (n - 29400) + 29400 := by omega
                                                                                rw [heq]
                                                                                exact ⟨a0_g1_w38 ⟨n - 29400, hr⟩, a1_g1_w38 ⟨n - 29400, hr⟩⟩
                                                                              · by_cases h39 : n < 29500
                                                                                · have hr : n - 29450 < 50 := by omega
                                                                                  have heq : n = (n - 29450) + 29450 := by omega
                                                                                  rw [heq]
                                                                                  exact ⟨a0_g1_w39 ⟨n - 29450, hr⟩, a1_g1_w39 ⟨n - 29450, hr⟩⟩
                                                                                · by_cases h40 : n < 29550
                                                                                  · have hr : n - 29500 < 50 := by omega
                                                                                    have heq : n = (n - 29500) + 29500 := by omega
                                                                                    rw [heq]
                                                                                    exact ⟨a0_g1_w40 ⟨n - 29500, hr⟩, a1_g1_w40 ⟨n - 29500, hr⟩⟩
                                                                                  · by_cases h41 : n < 29600
                                                                                    · have hr : n - 29550 < 50 := by omega
                                                                                      have heq : n = (n - 29550) + 29550 := by omega
                                                                                      rw [heq]
                                                                                      exact ⟨a0_g1_w41 ⟨n - 29550, hr⟩, a1_g1_w41 ⟨n - 29550, hr⟩⟩
                                                                                    · by_cases h42 : n < 29650
                                                                                      · have hr : n - 29600 < 50 := by omega
                                                                                        have heq : n = (n - 29600) + 29600 := by omega
                                                                                        rw [heq]
                                                                                        exact ⟨a0_g1_w42 ⟨n - 29600, hr⟩, a1_g1_w42 ⟨n - 29600, hr⟩⟩
                                                                                      · by_cases h43 : n < 29700
                                                                                        · have hr : n - 29650 < 50 := by omega
                                                                                          have heq : n = (n - 29650) + 29650 := by omega
                                                                                          rw [heq]
                                                                                          exact ⟨a0_g1_w43 ⟨n - 29650, hr⟩, a1_g1_w43 ⟨n - 29650, hr⟩⟩
                                                                                        · by_cases h44 : n < 29750
                                                                                          · have hr : n - 29700 < 50 := by omega
                                                                                            have heq : n = (n - 29700) + 29700 := by omega
                                                                                            rw [heq]
                                                                                            exact ⟨a0_g1_w44 ⟨n - 29700, hr⟩, a1_g1_w44 ⟨n - 29700, hr⟩⟩
                                                                                          · by_cases h45 : n < 29800
                                                                                            · have hr : n - 29750 < 50 := by omega
                                                                                              have heq : n = (n - 29750) + 29750 := by omega
                                                                                              rw [heq]
                                                                                              exact ⟨a0_g1_w45 ⟨n - 29750, hr⟩, a1_g1_w45 ⟨n - 29750, hr⟩⟩
                                                                                            · by_cases h46 : n < 29850
                                                                                              · have hr : n - 29800 < 50 := by omega
                                                                                                have heq : n = (n - 29800) + 29800 := by omega
                                                                                                rw [heq]
                                                                                                exact ⟨a0_g1_w46 ⟨n - 29800, hr⟩, a1_g1_w46 ⟨n - 29800, hr⟩⟩
                                                                                              · by_cases h47 : n < 29900
                                                                                                · have hr : n - 29850 < 50 := by omega
                                                                                                  have heq : n = (n - 29850) + 29850 := by omega
                                                                                                  rw [heq]
                                                                                                  exact ⟨a0_g1_w47 ⟨n - 29850, hr⟩, a1_g1_w47 ⟨n - 29850, hr⟩⟩
                                                                                                · by_cases h48 : n < 29950
                                                                                                  · have hr : n - 29900 < 50 := by omega
                                                                                                    have heq : n = (n - 29900) + 29900 := by omega
                                                                                                    rw [heq]
                                                                                                    exact ⟨a0_g1_w48 ⟨n - 29900, hr⟩, a1_g1_w48 ⟨n - 29900, hr⟩⟩
                                                                                                  · have hr : n - 29950 < 50 := by omega
                                                                                                    have heq : n = (n - 29950) + 29950 := by omega
                                                                                                    rw [heq]
                                                                                                    exact ⟨a0_g1_w49 ⟨n - 29950, hr⟩, a1_g1_w49 ⟨n - 29950, hr⟩⟩

private theorem a0_g2_w0 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 30000)) 65535) ≤ dimF (n.val + 30000) := by decide
private theorem a1_g2_w0 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 30000)) 16) ≤ dimF (n.val + 30000) := by decide
private theorem a0_g2_w1 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 30050)) 65535) ≤ dimF (n.val + 30050) := by decide
private theorem a1_g2_w1 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 30050)) 16) ≤ dimF (n.val + 30050) := by decide
private theorem a0_g2_w2 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 30100)) 65535) ≤ dimF (n.val + 30100) := by decide
private theorem a1_g2_w2 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 30100)) 16) ≤ dimF (n.val + 30100) := by decide
private theorem a0_g2_w3 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 30150)) 65535) ≤ dimF (n.val + 30150) := by decide
private theorem a1_g2_w3 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 30150)) 16) ≤ dimF (n.val + 30150) := by decide
private theorem a0_g2_w4 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 30200)) 65535) ≤ dimF (n.val + 30200) := by decide
private theorem a1_g2_w4 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 30200)) 16) ≤ dimF (n.val + 30200) := by decide
private theorem a0_g2_w5 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 30250)) 65535) ≤ dimF (n.val + 30250) := by decide
private theorem a1_g2_w5 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 30250)) 16) ≤ dimF (n.val + 30250) := by decide
private theorem a0_g2_w6 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 30300)) 65535) ≤ dimF (n.val + 30300) := by decide
private theorem a1_g2_w6 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 30300)) 16) ≤ dimF (n.val + 30300) := by decide
private theorem a0_g2_w7 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 30350)) 65535) ≤ dimF (n.val + 30350) := by decide
private theorem a1_g2_w7 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 30350)) 16) ≤ dimF (n.val + 30350) := by decide
private theorem a0_g2_w8 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 30400)) 65535) ≤ dimF (n.val + 30400) := by decide
private theorem a1_g2_w8 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 30400)) 16) ≤ dimF (n.val + 30400) := by decide
private theorem a0_g2_w9 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 30450)) 65535) ≤ dimF (n.val + 30450) := by decide
private theorem a1_g2_w9 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 30450)) 16) ≤ dimF (n.val + 30450) := by decide
private theorem a0_g2_w10 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 30500)) 65535) ≤ dimF (n.val + 30500) := by decide
private theorem a1_g2_w10 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 30500)) 16) ≤ dimF (n.val + 30500) := by decide
private theorem a0_g2_w11 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 30550)) 65535) ≤ dimF (n.val + 30550) := by decide
private theorem a1_g2_w11 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 30550)) 16) ≤ dimF (n.val + 30550) := by decide
private theorem a0_g2_w12 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 30600)) 65535) ≤ dimF (n.val + 30600) := by decide
private theorem a1_g2_w12 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 30600)) 16) ≤ dimF (n.val + 30600) := by decide
private theorem a0_g2_w13 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 30650)) 65535) ≤ dimF (n.val + 30650) := by decide
private theorem a1_g2_w13 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 30650)) 16) ≤ dimF (n.val + 30650) := by decide
private theorem a0_g2_w14 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 30700)) 65535) ≤ dimF (n.val + 30700) := by decide
private theorem a1_g2_w14 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 30700)) 16) ≤ dimF (n.val + 30700) := by decide
private theorem a0_g2_w15 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 30750)) 65535) ≤ dimF (n.val + 30750) := by decide
private theorem a1_g2_w15 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 30750)) 16) ≤ dimF (n.val + 30750) := by decide
private theorem a0_g2_w16 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 30800)) 65535) ≤ dimF (n.val + 30800) := by decide
private theorem a1_g2_w16 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 30800)) 16) ≤ dimF (n.val + 30800) := by decide
private theorem a0_g2_w17 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 30850)) 65535) ≤ dimF (n.val + 30850) := by decide
private theorem a1_g2_w17 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 30850)) 16) ≤ dimF (n.val + 30850) := by decide
private theorem a0_g2_w18 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 30900)) 65535) ≤ dimF (n.val + 30900) := by decide
private theorem a1_g2_w18 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 30900)) 16) ≤ dimF (n.val + 30900) := by decide
private theorem a0_g2_w19 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 30950)) 65535) ≤ dimF (n.val + 30950) := by decide
private theorem a1_g2_w19 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 30950)) 16) ≤ dimF (n.val + 30950) := by decide
private theorem a0_g2_w20 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 31000)) 65535) ≤ dimF (n.val + 31000) := by decide
private theorem a1_g2_w20 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 31000)) 16) ≤ dimF (n.val + 31000) := by decide
private theorem a0_g2_w21 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 31050)) 65535) ≤ dimF (n.val + 31050) := by decide
private theorem a1_g2_w21 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 31050)) 16) ≤ dimF (n.val + 31050) := by decide
private theorem a0_g2_w22 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 31100)) 65535) ≤ dimF (n.val + 31100) := by decide
private theorem a1_g2_w22 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 31100)) 16) ≤ dimF (n.val + 31100) := by decide
private theorem a0_g2_w23 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 31150)) 65535) ≤ dimF (n.val + 31150) := by decide
private theorem a1_g2_w23 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 31150)) 16) ≤ dimF (n.val + 31150) := by decide
private theorem a0_g2_w24 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 31200)) 65535) ≤ dimF (n.val + 31200) := by decide
private theorem a1_g2_w24 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 31200)) 16) ≤ dimF (n.val + 31200) := by decide
private theorem a0_g2_w25 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 31250)) 65535) ≤ dimF (n.val + 31250) := by decide
private theorem a1_g2_w25 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 31250)) 16) ≤ dimF (n.val + 31250) := by decide
private theorem a0_g2_w26 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 31300)) 65535) ≤ dimF (n.val + 31300) := by decide
private theorem a1_g2_w26 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 31300)) 16) ≤ dimF (n.val + 31300) := by decide
private theorem a0_g2_w27 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 31350)) 65535) ≤ dimF (n.val + 31350) := by decide
private theorem a1_g2_w27 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 31350)) 16) ≤ dimF (n.val + 31350) := by decide
private theorem a0_g2_w28 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 31400)) 65535) ≤ dimF (n.val + 31400) := by decide
private theorem a1_g2_w28 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 31400)) 16) ≤ dimF (n.val + 31400) := by decide
private theorem a0_g2_w29 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 31450)) 65535) ≤ dimF (n.val + 31450) := by decide
private theorem a1_g2_w29 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 31450)) 16) ≤ dimF (n.val + 31450) := by decide
private theorem a0_g2_w30 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 31500)) 65535) ≤ dimF (n.val + 31500) := by decide
private theorem a1_g2_w30 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 31500)) 16) ≤ dimF (n.val + 31500) := by decide
private theorem a0_g2_w31 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 31550)) 65535) ≤ dimF (n.val + 31550) := by decide
private theorem a1_g2_w31 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 31550)) 16) ≤ dimF (n.val + 31550) := by decide
private theorem a0_g2_w32 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 31600)) 65535) ≤ dimF (n.val + 31600) := by decide
private theorem a1_g2_w32 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 31600)) 16) ≤ dimF (n.val + 31600) := by decide
private theorem a0_g2_w33 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 31650)) 65535) ≤ dimF (n.val + 31650) := by decide
private theorem a1_g2_w33 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 31650)) 16) ≤ dimF (n.val + 31650) := by decide
private theorem a0_g2_w34 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 31700)) 65535) ≤ dimF (n.val + 31700) := by decide
private theorem a1_g2_w34 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 31700)) 16) ≤ dimF (n.val + 31700) := by decide
private theorem a0_g2_w35 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 31750)) 65535) ≤ dimF (n.val + 31750) := by decide
private theorem a1_g2_w35 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 31750)) 16) ≤ dimF (n.val + 31750) := by decide
private theorem a0_g2_w36 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 31800)) 65535) ≤ dimF (n.val + 31800) := by decide
private theorem a1_g2_w36 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 31800)) 16) ≤ dimF (n.val + 31800) := by decide
private theorem a0_g2_w37 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 31850)) 65535) ≤ dimF (n.val + 31850) := by decide
private theorem a1_g2_w37 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 31850)) 16) ≤ dimF (n.val + 31850) := by decide
private theorem a0_g2_w38 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 31900)) 65535) ≤ dimF (n.val + 31900) := by decide
private theorem a1_g2_w38 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 31900)) 16) ≤ dimF (n.val + 31900) := by decide
private theorem a0_g2_w39 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 31950)) 65535) ≤ dimF (n.val + 31950) := by decide
private theorem a1_g2_w39 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 31950)) 16) ≤ dimF (n.val + 31950) := by decide
private theorem a0_g2_w40 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 32000)) 65535) ≤ dimF (n.val + 32000) := by decide
private theorem a1_g2_w40 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 32000)) 16) ≤ dimF (n.val + 32000) := by decide
private theorem a0_g2_w41 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 32050)) 65535) ≤ dimF (n.val + 32050) := by decide
private theorem a1_g2_w41 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 32050)) 16) ≤ dimF (n.val + 32050) := by decide
private theorem a0_g2_w42 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 32100)) 65535) ≤ dimF (n.val + 32100) := by decide
private theorem a1_g2_w42 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 32100)) 16) ≤ dimF (n.val + 32100) := by decide
private theorem a0_g2_w43 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 32150)) 65535) ≤ dimF (n.val + 32150) := by decide
private theorem a1_g2_w43 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 32150)) 16) ≤ dimF (n.val + 32150) := by decide
private theorem a0_g2_w44 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 32200)) 65535) ≤ dimF (n.val + 32200) := by decide
private theorem a1_g2_w44 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 32200)) 16) ≤ dimF (n.val + 32200) := by decide
private theorem a0_g2_w45 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 32250)) 65535) ≤ dimF (n.val + 32250) := by decide
private theorem a1_g2_w45 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 32250)) 16) ≤ dimF (n.val + 32250) := by decide
private theorem a0_g2_w46 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 32300)) 65535) ≤ dimF (n.val + 32300) := by decide
private theorem a1_g2_w46 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 32300)) 16) ≤ dimF (n.val + 32300) := by decide
private theorem a0_g2_w47 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 32350)) 65535) ≤ dimF (n.val + 32350) := by decide
private theorem a1_g2_w47 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 32350)) 16) ≤ dimF (n.val + 32350) := by decide
private theorem a0_g2_w48 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 32400)) 65535) ≤ dimF (n.val + 32400) := by decide
private theorem a1_g2_w48 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 32400)) 16) ≤ dimF (n.val + 32400) := by decide
private theorem a0_g2_w49 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 32450)) 65535) ≤ dimF (n.val + 32450) := by decide
private theorem a1_g2_w49 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 32450)) 16) ≤ dimF (n.val + 32450) := by decide

private theorem pair_g2 (n : ℕ) (hlo : 30000 ≤ n) (hhi : n < 32500) :
    dimF (Nat.land (argF n) 65535) ≤ dimF n ∧
    dimF (Nat.shiftRight (argF n) 16) ≤ dimF n := by
  by_cases h0 : n < 30050
  · have hr : n - 30000 < 50 := by omega
    have heq : n = (n - 30000) + 30000 := by omega
    rw [heq]
    exact ⟨a0_g2_w0 ⟨n - 30000, hr⟩, a1_g2_w0 ⟨n - 30000, hr⟩⟩
  · by_cases h1 : n < 30100
    · have hr : n - 30050 < 50 := by omega
      have heq : n = (n - 30050) + 30050 := by omega
      rw [heq]
      exact ⟨a0_g2_w1 ⟨n - 30050, hr⟩, a1_g2_w1 ⟨n - 30050, hr⟩⟩
    · by_cases h2 : n < 30150
      · have hr : n - 30100 < 50 := by omega
        have heq : n = (n - 30100) + 30100 := by omega
        rw [heq]
        exact ⟨a0_g2_w2 ⟨n - 30100, hr⟩, a1_g2_w2 ⟨n - 30100, hr⟩⟩
      · by_cases h3 : n < 30200
        · have hr : n - 30150 < 50 := by omega
          have heq : n = (n - 30150) + 30150 := by omega
          rw [heq]
          exact ⟨a0_g2_w3 ⟨n - 30150, hr⟩, a1_g2_w3 ⟨n - 30150, hr⟩⟩
        · by_cases h4 : n < 30250
          · have hr : n - 30200 < 50 := by omega
            have heq : n = (n - 30200) + 30200 := by omega
            rw [heq]
            exact ⟨a0_g2_w4 ⟨n - 30200, hr⟩, a1_g2_w4 ⟨n - 30200, hr⟩⟩
          · by_cases h5 : n < 30300
            · have hr : n - 30250 < 50 := by omega
              have heq : n = (n - 30250) + 30250 := by omega
              rw [heq]
              exact ⟨a0_g2_w5 ⟨n - 30250, hr⟩, a1_g2_w5 ⟨n - 30250, hr⟩⟩
            · by_cases h6 : n < 30350
              · have hr : n - 30300 < 50 := by omega
                have heq : n = (n - 30300) + 30300 := by omega
                rw [heq]
                exact ⟨a0_g2_w6 ⟨n - 30300, hr⟩, a1_g2_w6 ⟨n - 30300, hr⟩⟩
              · by_cases h7 : n < 30400
                · have hr : n - 30350 < 50 := by omega
                  have heq : n = (n - 30350) + 30350 := by omega
                  rw [heq]
                  exact ⟨a0_g2_w7 ⟨n - 30350, hr⟩, a1_g2_w7 ⟨n - 30350, hr⟩⟩
                · by_cases h8 : n < 30450
                  · have hr : n - 30400 < 50 := by omega
                    have heq : n = (n - 30400) + 30400 := by omega
                    rw [heq]
                    exact ⟨a0_g2_w8 ⟨n - 30400, hr⟩, a1_g2_w8 ⟨n - 30400, hr⟩⟩
                  · by_cases h9 : n < 30500
                    · have hr : n - 30450 < 50 := by omega
                      have heq : n = (n - 30450) + 30450 := by omega
                      rw [heq]
                      exact ⟨a0_g2_w9 ⟨n - 30450, hr⟩, a1_g2_w9 ⟨n - 30450, hr⟩⟩
                    · by_cases h10 : n < 30550
                      · have hr : n - 30500 < 50 := by omega
                        have heq : n = (n - 30500) + 30500 := by omega
                        rw [heq]
                        exact ⟨a0_g2_w10 ⟨n - 30500, hr⟩, a1_g2_w10 ⟨n - 30500, hr⟩⟩
                      · by_cases h11 : n < 30600
                        · have hr : n - 30550 < 50 := by omega
                          have heq : n = (n - 30550) + 30550 := by omega
                          rw [heq]
                          exact ⟨a0_g2_w11 ⟨n - 30550, hr⟩, a1_g2_w11 ⟨n - 30550, hr⟩⟩
                        · by_cases h12 : n < 30650
                          · have hr : n - 30600 < 50 := by omega
                            have heq : n = (n - 30600) + 30600 := by omega
                            rw [heq]
                            exact ⟨a0_g2_w12 ⟨n - 30600, hr⟩, a1_g2_w12 ⟨n - 30600, hr⟩⟩
                          · by_cases h13 : n < 30700
                            · have hr : n - 30650 < 50 := by omega
                              have heq : n = (n - 30650) + 30650 := by omega
                              rw [heq]
                              exact ⟨a0_g2_w13 ⟨n - 30650, hr⟩, a1_g2_w13 ⟨n - 30650, hr⟩⟩
                            · by_cases h14 : n < 30750
                              · have hr : n - 30700 < 50 := by omega
                                have heq : n = (n - 30700) + 30700 := by omega
                                rw [heq]
                                exact ⟨a0_g2_w14 ⟨n - 30700, hr⟩, a1_g2_w14 ⟨n - 30700, hr⟩⟩
                              · by_cases h15 : n < 30800
                                · have hr : n - 30750 < 50 := by omega
                                  have heq : n = (n - 30750) + 30750 := by omega
                                  rw [heq]
                                  exact ⟨a0_g2_w15 ⟨n - 30750, hr⟩, a1_g2_w15 ⟨n - 30750, hr⟩⟩
                                · by_cases h16 : n < 30850
                                  · have hr : n - 30800 < 50 := by omega
                                    have heq : n = (n - 30800) + 30800 := by omega
                                    rw [heq]
                                    exact ⟨a0_g2_w16 ⟨n - 30800, hr⟩, a1_g2_w16 ⟨n - 30800, hr⟩⟩
                                  · by_cases h17 : n < 30900
                                    · have hr : n - 30850 < 50 := by omega
                                      have heq : n = (n - 30850) + 30850 := by omega
                                      rw [heq]
                                      exact ⟨a0_g2_w17 ⟨n - 30850, hr⟩, a1_g2_w17 ⟨n - 30850, hr⟩⟩
                                    · by_cases h18 : n < 30950
                                      · have hr : n - 30900 < 50 := by omega
                                        have heq : n = (n - 30900) + 30900 := by omega
                                        rw [heq]
                                        exact ⟨a0_g2_w18 ⟨n - 30900, hr⟩, a1_g2_w18 ⟨n - 30900, hr⟩⟩
                                      · by_cases h19 : n < 31000
                                        · have hr : n - 30950 < 50 := by omega
                                          have heq : n = (n - 30950) + 30950 := by omega
                                          rw [heq]
                                          exact ⟨a0_g2_w19 ⟨n - 30950, hr⟩, a1_g2_w19 ⟨n - 30950, hr⟩⟩
                                        · by_cases h20 : n < 31050
                                          · have hr : n - 31000 < 50 := by omega
                                            have heq : n = (n - 31000) + 31000 := by omega
                                            rw [heq]
                                            exact ⟨a0_g2_w20 ⟨n - 31000, hr⟩, a1_g2_w20 ⟨n - 31000, hr⟩⟩
                                          · by_cases h21 : n < 31100
                                            · have hr : n - 31050 < 50 := by omega
                                              have heq : n = (n - 31050) + 31050 := by omega
                                              rw [heq]
                                              exact ⟨a0_g2_w21 ⟨n - 31050, hr⟩, a1_g2_w21 ⟨n - 31050, hr⟩⟩
                                            · by_cases h22 : n < 31150
                                              · have hr : n - 31100 < 50 := by omega
                                                have heq : n = (n - 31100) + 31100 := by omega
                                                rw [heq]
                                                exact ⟨a0_g2_w22 ⟨n - 31100, hr⟩, a1_g2_w22 ⟨n - 31100, hr⟩⟩
                                              · by_cases h23 : n < 31200
                                                · have hr : n - 31150 < 50 := by omega
                                                  have heq : n = (n - 31150) + 31150 := by omega
                                                  rw [heq]
                                                  exact ⟨a0_g2_w23 ⟨n - 31150, hr⟩, a1_g2_w23 ⟨n - 31150, hr⟩⟩
                                                · by_cases h24 : n < 31250
                                                  · have hr : n - 31200 < 50 := by omega
                                                    have heq : n = (n - 31200) + 31200 := by omega
                                                    rw [heq]
                                                    exact ⟨a0_g2_w24 ⟨n - 31200, hr⟩, a1_g2_w24 ⟨n - 31200, hr⟩⟩
                                                  · by_cases h25 : n < 31300
                                                    · have hr : n - 31250 < 50 := by omega
                                                      have heq : n = (n - 31250) + 31250 := by omega
                                                      rw [heq]
                                                      exact ⟨a0_g2_w25 ⟨n - 31250, hr⟩, a1_g2_w25 ⟨n - 31250, hr⟩⟩
                                                    · by_cases h26 : n < 31350
                                                      · have hr : n - 31300 < 50 := by omega
                                                        have heq : n = (n - 31300) + 31300 := by omega
                                                        rw [heq]
                                                        exact ⟨a0_g2_w26 ⟨n - 31300, hr⟩, a1_g2_w26 ⟨n - 31300, hr⟩⟩
                                                      · by_cases h27 : n < 31400
                                                        · have hr : n - 31350 < 50 := by omega
                                                          have heq : n = (n - 31350) + 31350 := by omega
                                                          rw [heq]
                                                          exact ⟨a0_g2_w27 ⟨n - 31350, hr⟩, a1_g2_w27 ⟨n - 31350, hr⟩⟩
                                                        · by_cases h28 : n < 31450
                                                          · have hr : n - 31400 < 50 := by omega
                                                            have heq : n = (n - 31400) + 31400 := by omega
                                                            rw [heq]
                                                            exact ⟨a0_g2_w28 ⟨n - 31400, hr⟩, a1_g2_w28 ⟨n - 31400, hr⟩⟩
                                                          · by_cases h29 : n < 31500
                                                            · have hr : n - 31450 < 50 := by omega
                                                              have heq : n = (n - 31450) + 31450 := by omega
                                                              rw [heq]
                                                              exact ⟨a0_g2_w29 ⟨n - 31450, hr⟩, a1_g2_w29 ⟨n - 31450, hr⟩⟩
                                                            · by_cases h30 : n < 31550
                                                              · have hr : n - 31500 < 50 := by omega
                                                                have heq : n = (n - 31500) + 31500 := by omega
                                                                rw [heq]
                                                                exact ⟨a0_g2_w30 ⟨n - 31500, hr⟩, a1_g2_w30 ⟨n - 31500, hr⟩⟩
                                                              · by_cases h31 : n < 31600
                                                                · have hr : n - 31550 < 50 := by omega
                                                                  have heq : n = (n - 31550) + 31550 := by omega
                                                                  rw [heq]
                                                                  exact ⟨a0_g2_w31 ⟨n - 31550, hr⟩, a1_g2_w31 ⟨n - 31550, hr⟩⟩
                                                                · by_cases h32 : n < 31650
                                                                  · have hr : n - 31600 < 50 := by omega
                                                                    have heq : n = (n - 31600) + 31600 := by omega
                                                                    rw [heq]
                                                                    exact ⟨a0_g2_w32 ⟨n - 31600, hr⟩, a1_g2_w32 ⟨n - 31600, hr⟩⟩
                                                                  · by_cases h33 : n < 31700
                                                                    · have hr : n - 31650 < 50 := by omega
                                                                      have heq : n = (n - 31650) + 31650 := by omega
                                                                      rw [heq]
                                                                      exact ⟨a0_g2_w33 ⟨n - 31650, hr⟩, a1_g2_w33 ⟨n - 31650, hr⟩⟩
                                                                    · by_cases h34 : n < 31750
                                                                      · have hr : n - 31700 < 50 := by omega
                                                                        have heq : n = (n - 31700) + 31700 := by omega
                                                                        rw [heq]
                                                                        exact ⟨a0_g2_w34 ⟨n - 31700, hr⟩, a1_g2_w34 ⟨n - 31700, hr⟩⟩
                                                                      · by_cases h35 : n < 31800
                                                                        · have hr : n - 31750 < 50 := by omega
                                                                          have heq : n = (n - 31750) + 31750 := by omega
                                                                          rw [heq]
                                                                          exact ⟨a0_g2_w35 ⟨n - 31750, hr⟩, a1_g2_w35 ⟨n - 31750, hr⟩⟩
                                                                        · by_cases h36 : n < 31850
                                                                          · have hr : n - 31800 < 50 := by omega
                                                                            have heq : n = (n - 31800) + 31800 := by omega
                                                                            rw [heq]
                                                                            exact ⟨a0_g2_w36 ⟨n - 31800, hr⟩, a1_g2_w36 ⟨n - 31800, hr⟩⟩
                                                                          · by_cases h37 : n < 31900
                                                                            · have hr : n - 31850 < 50 := by omega
                                                                              have heq : n = (n - 31850) + 31850 := by omega
                                                                              rw [heq]
                                                                              exact ⟨a0_g2_w37 ⟨n - 31850, hr⟩, a1_g2_w37 ⟨n - 31850, hr⟩⟩
                                                                            · by_cases h38 : n < 31950
                                                                              · have hr : n - 31900 < 50 := by omega
                                                                                have heq : n = (n - 31900) + 31900 := by omega
                                                                                rw [heq]
                                                                                exact ⟨a0_g2_w38 ⟨n - 31900, hr⟩, a1_g2_w38 ⟨n - 31900, hr⟩⟩
                                                                              · by_cases h39 : n < 32000
                                                                                · have hr : n - 31950 < 50 := by omega
                                                                                  have heq : n = (n - 31950) + 31950 := by omega
                                                                                  rw [heq]
                                                                                  exact ⟨a0_g2_w39 ⟨n - 31950, hr⟩, a1_g2_w39 ⟨n - 31950, hr⟩⟩
                                                                                · by_cases h40 : n < 32050
                                                                                  · have hr : n - 32000 < 50 := by omega
                                                                                    have heq : n = (n - 32000) + 32000 := by omega
                                                                                    rw [heq]
                                                                                    exact ⟨a0_g2_w40 ⟨n - 32000, hr⟩, a1_g2_w40 ⟨n - 32000, hr⟩⟩
                                                                                  · by_cases h41 : n < 32100
                                                                                    · have hr : n - 32050 < 50 := by omega
                                                                                      have heq : n = (n - 32050) + 32050 := by omega
                                                                                      rw [heq]
                                                                                      exact ⟨a0_g2_w41 ⟨n - 32050, hr⟩, a1_g2_w41 ⟨n - 32050, hr⟩⟩
                                                                                    · by_cases h42 : n < 32150
                                                                                      · have hr : n - 32100 < 50 := by omega
                                                                                        have heq : n = (n - 32100) + 32100 := by omega
                                                                                        rw [heq]
                                                                                        exact ⟨a0_g2_w42 ⟨n - 32100, hr⟩, a1_g2_w42 ⟨n - 32100, hr⟩⟩
                                                                                      · by_cases h43 : n < 32200
                                                                                        · have hr : n - 32150 < 50 := by omega
                                                                                          have heq : n = (n - 32150) + 32150 := by omega
                                                                                          rw [heq]
                                                                                          exact ⟨a0_g2_w43 ⟨n - 32150, hr⟩, a1_g2_w43 ⟨n - 32150, hr⟩⟩
                                                                                        · by_cases h44 : n < 32250
                                                                                          · have hr : n - 32200 < 50 := by omega
                                                                                            have heq : n = (n - 32200) + 32200 := by omega
                                                                                            rw [heq]
                                                                                            exact ⟨a0_g2_w44 ⟨n - 32200, hr⟩, a1_g2_w44 ⟨n - 32200, hr⟩⟩
                                                                                          · by_cases h45 : n < 32300
                                                                                            · have hr : n - 32250 < 50 := by omega
                                                                                              have heq : n = (n - 32250) + 32250 := by omega
                                                                                              rw [heq]
                                                                                              exact ⟨a0_g2_w45 ⟨n - 32250, hr⟩, a1_g2_w45 ⟨n - 32250, hr⟩⟩
                                                                                            · by_cases h46 : n < 32350
                                                                                              · have hr : n - 32300 < 50 := by omega
                                                                                                have heq : n = (n - 32300) + 32300 := by omega
                                                                                                rw [heq]
                                                                                                exact ⟨a0_g2_w46 ⟨n - 32300, hr⟩, a1_g2_w46 ⟨n - 32300, hr⟩⟩
                                                                                              · by_cases h47 : n < 32400
                                                                                                · have hr : n - 32350 < 50 := by omega
                                                                                                  have heq : n = (n - 32350) + 32350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact ⟨a0_g2_w47 ⟨n - 32350, hr⟩, a1_g2_w47 ⟨n - 32350, hr⟩⟩
                                                                                                · by_cases h48 : n < 32450
                                                                                                  · have hr : n - 32400 < 50 := by omega
                                                                                                    have heq : n = (n - 32400) + 32400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact ⟨a0_g2_w48 ⟨n - 32400, hr⟩, a1_g2_w48 ⟨n - 32400, hr⟩⟩
                                                                                                  · have hr : n - 32450 < 50 := by omega
                                                                                                    have heq : n = (n - 32450) + 32450 := by omega
                                                                                                    rw [heq]
                                                                                                    exact ⟨a0_g2_w49 ⟨n - 32450, hr⟩, a1_g2_w49 ⟨n - 32450, hr⟩⟩

private theorem a0_g3_w0 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 32500)) 65535) ≤ dimF (n.val + 32500) := by decide
private theorem a1_g3_w0 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 32500)) 16) ≤ dimF (n.val + 32500) := by decide
private theorem a0_g3_w1 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 32550)) 65535) ≤ dimF (n.val + 32550) := by decide
private theorem a1_g3_w1 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 32550)) 16) ≤ dimF (n.val + 32550) := by decide
private theorem a0_g3_w2 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 32600)) 65535) ≤ dimF (n.val + 32600) := by decide
private theorem a1_g3_w2 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 32600)) 16) ≤ dimF (n.val + 32600) := by decide
private theorem a0_g3_w3 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 32650)) 65535) ≤ dimF (n.val + 32650) := by decide
private theorem a1_g3_w3 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 32650)) 16) ≤ dimF (n.val + 32650) := by decide
private theorem a0_g3_w4 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 32700)) 65535) ≤ dimF (n.val + 32700) := by decide
private theorem a1_g3_w4 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 32700)) 16) ≤ dimF (n.val + 32700) := by decide
private theorem a0_g3_w5 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 32750)) 65535) ≤ dimF (n.val + 32750) := by decide
private theorem a1_g3_w5 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 32750)) 16) ≤ dimF (n.val + 32750) := by decide
private theorem a0_g3_w6 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 32800)) 65535) ≤ dimF (n.val + 32800) := by decide
private theorem a1_g3_w6 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 32800)) 16) ≤ dimF (n.val + 32800) := by decide
private theorem a0_g3_w7 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 32850)) 65535) ≤ dimF (n.val + 32850) := by decide
private theorem a1_g3_w7 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 32850)) 16) ≤ dimF (n.val + 32850) := by decide
private theorem a0_g3_w8 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 32900)) 65535) ≤ dimF (n.val + 32900) := by decide
private theorem a1_g3_w8 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 32900)) 16) ≤ dimF (n.val + 32900) := by decide
private theorem a0_g3_w9 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 32950)) 65535) ≤ dimF (n.val + 32950) := by decide
private theorem a1_g3_w9 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 32950)) 16) ≤ dimF (n.val + 32950) := by decide
private theorem a0_g3_w10 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 33000)) 65535) ≤ dimF (n.val + 33000) := by decide
private theorem a1_g3_w10 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 33000)) 16) ≤ dimF (n.val + 33000) := by decide
private theorem a0_g3_w11 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 33050)) 65535) ≤ dimF (n.val + 33050) := by decide
private theorem a1_g3_w11 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 33050)) 16) ≤ dimF (n.val + 33050) := by decide
private theorem a0_g3_w12 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 33100)) 65535) ≤ dimF (n.val + 33100) := by decide
private theorem a1_g3_w12 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 33100)) 16) ≤ dimF (n.val + 33100) := by decide
private theorem a0_g3_w13 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 33150)) 65535) ≤ dimF (n.val + 33150) := by decide
private theorem a1_g3_w13 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 33150)) 16) ≤ dimF (n.val + 33150) := by decide
private theorem a0_g3_w14 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 33200)) 65535) ≤ dimF (n.val + 33200) := by decide
private theorem a1_g3_w14 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 33200)) 16) ≤ dimF (n.val + 33200) := by decide
private theorem a0_g3_w15 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 33250)) 65535) ≤ dimF (n.val + 33250) := by decide
private theorem a1_g3_w15 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 33250)) 16) ≤ dimF (n.val + 33250) := by decide
private theorem a0_g3_w16 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 33300)) 65535) ≤ dimF (n.val + 33300) := by decide
private theorem a1_g3_w16 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 33300)) 16) ≤ dimF (n.val + 33300) := by decide
private theorem a0_g3_w17 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 33350)) 65535) ≤ dimF (n.val + 33350) := by decide
private theorem a1_g3_w17 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 33350)) 16) ≤ dimF (n.val + 33350) := by decide
private theorem a0_g3_w18 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 33400)) 65535) ≤ dimF (n.val + 33400) := by decide
private theorem a1_g3_w18 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 33400)) 16) ≤ dimF (n.val + 33400) := by decide
private theorem a0_g3_w19 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 33450)) 65535) ≤ dimF (n.val + 33450) := by decide
private theorem a1_g3_w19 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 33450)) 16) ≤ dimF (n.val + 33450) := by decide
private theorem a0_g3_w20 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 33500)) 65535) ≤ dimF (n.val + 33500) := by decide
private theorem a1_g3_w20 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 33500)) 16) ≤ dimF (n.val + 33500) := by decide
private theorem a0_g3_w21 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 33550)) 65535) ≤ dimF (n.val + 33550) := by decide
private theorem a1_g3_w21 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 33550)) 16) ≤ dimF (n.val + 33550) := by decide
private theorem a0_g3_w22 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 33600)) 65535) ≤ dimF (n.val + 33600) := by decide
private theorem a1_g3_w22 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 33600)) 16) ≤ dimF (n.val + 33600) := by decide
private theorem a0_g3_w23 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 33650)) 65535) ≤ dimF (n.val + 33650) := by decide
private theorem a1_g3_w23 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 33650)) 16) ≤ dimF (n.val + 33650) := by decide
private theorem a0_g3_w24 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 33700)) 65535) ≤ dimF (n.val + 33700) := by decide
private theorem a1_g3_w24 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 33700)) 16) ≤ dimF (n.val + 33700) := by decide
private theorem a0_g3_w25 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 33750)) 65535) ≤ dimF (n.val + 33750) := by decide
private theorem a1_g3_w25 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 33750)) 16) ≤ dimF (n.val + 33750) := by decide
private theorem a0_g3_w26 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 33800)) 65535) ≤ dimF (n.val + 33800) := by decide
private theorem a1_g3_w26 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 33800)) 16) ≤ dimF (n.val + 33800) := by decide
private theorem a0_g3_w27 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 33850)) 65535) ≤ dimF (n.val + 33850) := by decide
private theorem a1_g3_w27 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 33850)) 16) ≤ dimF (n.val + 33850) := by decide
private theorem a0_g3_w28 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 33900)) 65535) ≤ dimF (n.val + 33900) := by decide
private theorem a1_g3_w28 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 33900)) 16) ≤ dimF (n.val + 33900) := by decide
private theorem a0_g3_w29 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 33950)) 65535) ≤ dimF (n.val + 33950) := by decide
private theorem a1_g3_w29 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 33950)) 16) ≤ dimF (n.val + 33950) := by decide
private theorem a0_g3_w30 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 34000)) 65535) ≤ dimF (n.val + 34000) := by decide
private theorem a1_g3_w30 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 34000)) 16) ≤ dimF (n.val + 34000) := by decide
private theorem a0_g3_w31 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 34050)) 65535) ≤ dimF (n.val + 34050) := by decide
private theorem a1_g3_w31 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 34050)) 16) ≤ dimF (n.val + 34050) := by decide
private theorem a0_g3_w32 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 34100)) 65535) ≤ dimF (n.val + 34100) := by decide
private theorem a1_g3_w32 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 34100)) 16) ≤ dimF (n.val + 34100) := by decide
private theorem a0_g3_w33 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 34150)) 65535) ≤ dimF (n.val + 34150) := by decide
private theorem a1_g3_w33 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 34150)) 16) ≤ dimF (n.val + 34150) := by decide
private theorem a0_g3_w34 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 34200)) 65535) ≤ dimF (n.val + 34200) := by decide
private theorem a1_g3_w34 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 34200)) 16) ≤ dimF (n.val + 34200) := by decide
private theorem a0_g3_w35 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 34250)) 65535) ≤ dimF (n.val + 34250) := by decide
private theorem a1_g3_w35 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 34250)) 16) ≤ dimF (n.val + 34250) := by decide
private theorem a0_g3_w36 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 34300)) 65535) ≤ dimF (n.val + 34300) := by decide
private theorem a1_g3_w36 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 34300)) 16) ≤ dimF (n.val + 34300) := by decide
private theorem a0_g3_w37 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 34350)) 65535) ≤ dimF (n.val + 34350) := by decide
private theorem a1_g3_w37 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 34350)) 16) ≤ dimF (n.val + 34350) := by decide
private theorem a0_g3_w38 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 34400)) 65535) ≤ dimF (n.val + 34400) := by decide
private theorem a1_g3_w38 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 34400)) 16) ≤ dimF (n.val + 34400) := by decide
private theorem a0_g3_w39 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 34450)) 65535) ≤ dimF (n.val + 34450) := by decide
private theorem a1_g3_w39 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 34450)) 16) ≤ dimF (n.val + 34450) := by decide
private theorem a0_g3_w40 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 34500)) 65535) ≤ dimF (n.val + 34500) := by decide
private theorem a1_g3_w40 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 34500)) 16) ≤ dimF (n.val + 34500) := by decide
private theorem a0_g3_w41 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 34550)) 65535) ≤ dimF (n.val + 34550) := by decide
private theorem a1_g3_w41 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 34550)) 16) ≤ dimF (n.val + 34550) := by decide
private theorem a0_g3_w42 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 34600)) 65535) ≤ dimF (n.val + 34600) := by decide
private theorem a1_g3_w42 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 34600)) 16) ≤ dimF (n.val + 34600) := by decide
private theorem a0_g3_w43 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 34650)) 65535) ≤ dimF (n.val + 34650) := by decide
private theorem a1_g3_w43 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 34650)) 16) ≤ dimF (n.val + 34650) := by decide
private theorem a0_g3_w44 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 34700)) 65535) ≤ dimF (n.val + 34700) := by decide
private theorem a1_g3_w44 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 34700)) 16) ≤ dimF (n.val + 34700) := by decide
private theorem a0_g3_w45 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 34750)) 65535) ≤ dimF (n.val + 34750) := by decide
private theorem a1_g3_w45 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 34750)) 16) ≤ dimF (n.val + 34750) := by decide
private theorem a0_g3_w46 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 34800)) 65535) ≤ dimF (n.val + 34800) := by decide
private theorem a1_g3_w46 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 34800)) 16) ≤ dimF (n.val + 34800) := by decide
private theorem a0_g3_w47 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 34850)) 65535) ≤ dimF (n.val + 34850) := by decide
private theorem a1_g3_w47 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 34850)) 16) ≤ dimF (n.val + 34850) := by decide
private theorem a0_g3_w48 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 34900)) 65535) ≤ dimF (n.val + 34900) := by decide
private theorem a1_g3_w48 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 34900)) 16) ≤ dimF (n.val + 34900) := by decide
private theorem a0_g3_w49 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 34950)) 65535) ≤ dimF (n.val + 34950) := by decide
private theorem a1_g3_w49 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 34950)) 16) ≤ dimF (n.val + 34950) := by decide

private theorem pair_g3 (n : ℕ) (hlo : 32500 ≤ n) (hhi : n < 35000) :
    dimF (Nat.land (argF n) 65535) ≤ dimF n ∧
    dimF (Nat.shiftRight (argF n) 16) ≤ dimF n := by
  by_cases h0 : n < 32550
  · have hr : n - 32500 < 50 := by omega
    have heq : n = (n - 32500) + 32500 := by omega
    rw [heq]
    exact ⟨a0_g3_w0 ⟨n - 32500, hr⟩, a1_g3_w0 ⟨n - 32500, hr⟩⟩
  · by_cases h1 : n < 32600
    · have hr : n - 32550 < 50 := by omega
      have heq : n = (n - 32550) + 32550 := by omega
      rw [heq]
      exact ⟨a0_g3_w1 ⟨n - 32550, hr⟩, a1_g3_w1 ⟨n - 32550, hr⟩⟩
    · by_cases h2 : n < 32650
      · have hr : n - 32600 < 50 := by omega
        have heq : n = (n - 32600) + 32600 := by omega
        rw [heq]
        exact ⟨a0_g3_w2 ⟨n - 32600, hr⟩, a1_g3_w2 ⟨n - 32600, hr⟩⟩
      · by_cases h3 : n < 32700
        · have hr : n - 32650 < 50 := by omega
          have heq : n = (n - 32650) + 32650 := by omega
          rw [heq]
          exact ⟨a0_g3_w3 ⟨n - 32650, hr⟩, a1_g3_w3 ⟨n - 32650, hr⟩⟩
        · by_cases h4 : n < 32750
          · have hr : n - 32700 < 50 := by omega
            have heq : n = (n - 32700) + 32700 := by omega
            rw [heq]
            exact ⟨a0_g3_w4 ⟨n - 32700, hr⟩, a1_g3_w4 ⟨n - 32700, hr⟩⟩
          · by_cases h5 : n < 32800
            · have hr : n - 32750 < 50 := by omega
              have heq : n = (n - 32750) + 32750 := by omega
              rw [heq]
              exact ⟨a0_g3_w5 ⟨n - 32750, hr⟩, a1_g3_w5 ⟨n - 32750, hr⟩⟩
            · by_cases h6 : n < 32850
              · have hr : n - 32800 < 50 := by omega
                have heq : n = (n - 32800) + 32800 := by omega
                rw [heq]
                exact ⟨a0_g3_w6 ⟨n - 32800, hr⟩, a1_g3_w6 ⟨n - 32800, hr⟩⟩
              · by_cases h7 : n < 32900
                · have hr : n - 32850 < 50 := by omega
                  have heq : n = (n - 32850) + 32850 := by omega
                  rw [heq]
                  exact ⟨a0_g3_w7 ⟨n - 32850, hr⟩, a1_g3_w7 ⟨n - 32850, hr⟩⟩
                · by_cases h8 : n < 32950
                  · have hr : n - 32900 < 50 := by omega
                    have heq : n = (n - 32900) + 32900 := by omega
                    rw [heq]
                    exact ⟨a0_g3_w8 ⟨n - 32900, hr⟩, a1_g3_w8 ⟨n - 32900, hr⟩⟩
                  · by_cases h9 : n < 33000
                    · have hr : n - 32950 < 50 := by omega
                      have heq : n = (n - 32950) + 32950 := by omega
                      rw [heq]
                      exact ⟨a0_g3_w9 ⟨n - 32950, hr⟩, a1_g3_w9 ⟨n - 32950, hr⟩⟩
                    · by_cases h10 : n < 33050
                      · have hr : n - 33000 < 50 := by omega
                        have heq : n = (n - 33000) + 33000 := by omega
                        rw [heq]
                        exact ⟨a0_g3_w10 ⟨n - 33000, hr⟩, a1_g3_w10 ⟨n - 33000, hr⟩⟩
                      · by_cases h11 : n < 33100
                        · have hr : n - 33050 < 50 := by omega
                          have heq : n = (n - 33050) + 33050 := by omega
                          rw [heq]
                          exact ⟨a0_g3_w11 ⟨n - 33050, hr⟩, a1_g3_w11 ⟨n - 33050, hr⟩⟩
                        · by_cases h12 : n < 33150
                          · have hr : n - 33100 < 50 := by omega
                            have heq : n = (n - 33100) + 33100 := by omega
                            rw [heq]
                            exact ⟨a0_g3_w12 ⟨n - 33100, hr⟩, a1_g3_w12 ⟨n - 33100, hr⟩⟩
                          · by_cases h13 : n < 33200
                            · have hr : n - 33150 < 50 := by omega
                              have heq : n = (n - 33150) + 33150 := by omega
                              rw [heq]
                              exact ⟨a0_g3_w13 ⟨n - 33150, hr⟩, a1_g3_w13 ⟨n - 33150, hr⟩⟩
                            · by_cases h14 : n < 33250
                              · have hr : n - 33200 < 50 := by omega
                                have heq : n = (n - 33200) + 33200 := by omega
                                rw [heq]
                                exact ⟨a0_g3_w14 ⟨n - 33200, hr⟩, a1_g3_w14 ⟨n - 33200, hr⟩⟩
                              · by_cases h15 : n < 33300
                                · have hr : n - 33250 < 50 := by omega
                                  have heq : n = (n - 33250) + 33250 := by omega
                                  rw [heq]
                                  exact ⟨a0_g3_w15 ⟨n - 33250, hr⟩, a1_g3_w15 ⟨n - 33250, hr⟩⟩
                                · by_cases h16 : n < 33350
                                  · have hr : n - 33300 < 50 := by omega
                                    have heq : n = (n - 33300) + 33300 := by omega
                                    rw [heq]
                                    exact ⟨a0_g3_w16 ⟨n - 33300, hr⟩, a1_g3_w16 ⟨n - 33300, hr⟩⟩
                                  · by_cases h17 : n < 33400
                                    · have hr : n - 33350 < 50 := by omega
                                      have heq : n = (n - 33350) + 33350 := by omega
                                      rw [heq]
                                      exact ⟨a0_g3_w17 ⟨n - 33350, hr⟩, a1_g3_w17 ⟨n - 33350, hr⟩⟩
                                    · by_cases h18 : n < 33450
                                      · have hr : n - 33400 < 50 := by omega
                                        have heq : n = (n - 33400) + 33400 := by omega
                                        rw [heq]
                                        exact ⟨a0_g3_w18 ⟨n - 33400, hr⟩, a1_g3_w18 ⟨n - 33400, hr⟩⟩
                                      · by_cases h19 : n < 33500
                                        · have hr : n - 33450 < 50 := by omega
                                          have heq : n = (n - 33450) + 33450 := by omega
                                          rw [heq]
                                          exact ⟨a0_g3_w19 ⟨n - 33450, hr⟩, a1_g3_w19 ⟨n - 33450, hr⟩⟩
                                        · by_cases h20 : n < 33550
                                          · have hr : n - 33500 < 50 := by omega
                                            have heq : n = (n - 33500) + 33500 := by omega
                                            rw [heq]
                                            exact ⟨a0_g3_w20 ⟨n - 33500, hr⟩, a1_g3_w20 ⟨n - 33500, hr⟩⟩
                                          · by_cases h21 : n < 33600
                                            · have hr : n - 33550 < 50 := by omega
                                              have heq : n = (n - 33550) + 33550 := by omega
                                              rw [heq]
                                              exact ⟨a0_g3_w21 ⟨n - 33550, hr⟩, a1_g3_w21 ⟨n - 33550, hr⟩⟩
                                            · by_cases h22 : n < 33650
                                              · have hr : n - 33600 < 50 := by omega
                                                have heq : n = (n - 33600) + 33600 := by omega
                                                rw [heq]
                                                exact ⟨a0_g3_w22 ⟨n - 33600, hr⟩, a1_g3_w22 ⟨n - 33600, hr⟩⟩
                                              · by_cases h23 : n < 33700
                                                · have hr : n - 33650 < 50 := by omega
                                                  have heq : n = (n - 33650) + 33650 := by omega
                                                  rw [heq]
                                                  exact ⟨a0_g3_w23 ⟨n - 33650, hr⟩, a1_g3_w23 ⟨n - 33650, hr⟩⟩
                                                · by_cases h24 : n < 33750
                                                  · have hr : n - 33700 < 50 := by omega
                                                    have heq : n = (n - 33700) + 33700 := by omega
                                                    rw [heq]
                                                    exact ⟨a0_g3_w24 ⟨n - 33700, hr⟩, a1_g3_w24 ⟨n - 33700, hr⟩⟩
                                                  · by_cases h25 : n < 33800
                                                    · have hr : n - 33750 < 50 := by omega
                                                      have heq : n = (n - 33750) + 33750 := by omega
                                                      rw [heq]
                                                      exact ⟨a0_g3_w25 ⟨n - 33750, hr⟩, a1_g3_w25 ⟨n - 33750, hr⟩⟩
                                                    · by_cases h26 : n < 33850
                                                      · have hr : n - 33800 < 50 := by omega
                                                        have heq : n = (n - 33800) + 33800 := by omega
                                                        rw [heq]
                                                        exact ⟨a0_g3_w26 ⟨n - 33800, hr⟩, a1_g3_w26 ⟨n - 33800, hr⟩⟩
                                                      · by_cases h27 : n < 33900
                                                        · have hr : n - 33850 < 50 := by omega
                                                          have heq : n = (n - 33850) + 33850 := by omega
                                                          rw [heq]
                                                          exact ⟨a0_g3_w27 ⟨n - 33850, hr⟩, a1_g3_w27 ⟨n - 33850, hr⟩⟩
                                                        · by_cases h28 : n < 33950
                                                          · have hr : n - 33900 < 50 := by omega
                                                            have heq : n = (n - 33900) + 33900 := by omega
                                                            rw [heq]
                                                            exact ⟨a0_g3_w28 ⟨n - 33900, hr⟩, a1_g3_w28 ⟨n - 33900, hr⟩⟩
                                                          · by_cases h29 : n < 34000
                                                            · have hr : n - 33950 < 50 := by omega
                                                              have heq : n = (n - 33950) + 33950 := by omega
                                                              rw [heq]
                                                              exact ⟨a0_g3_w29 ⟨n - 33950, hr⟩, a1_g3_w29 ⟨n - 33950, hr⟩⟩
                                                            · by_cases h30 : n < 34050
                                                              · have hr : n - 34000 < 50 := by omega
                                                                have heq : n = (n - 34000) + 34000 := by omega
                                                                rw [heq]
                                                                exact ⟨a0_g3_w30 ⟨n - 34000, hr⟩, a1_g3_w30 ⟨n - 34000, hr⟩⟩
                                                              · by_cases h31 : n < 34100
                                                                · have hr : n - 34050 < 50 := by omega
                                                                  have heq : n = (n - 34050) + 34050 := by omega
                                                                  rw [heq]
                                                                  exact ⟨a0_g3_w31 ⟨n - 34050, hr⟩, a1_g3_w31 ⟨n - 34050, hr⟩⟩
                                                                · by_cases h32 : n < 34150
                                                                  · have hr : n - 34100 < 50 := by omega
                                                                    have heq : n = (n - 34100) + 34100 := by omega
                                                                    rw [heq]
                                                                    exact ⟨a0_g3_w32 ⟨n - 34100, hr⟩, a1_g3_w32 ⟨n - 34100, hr⟩⟩
                                                                  · by_cases h33 : n < 34200
                                                                    · have hr : n - 34150 < 50 := by omega
                                                                      have heq : n = (n - 34150) + 34150 := by omega
                                                                      rw [heq]
                                                                      exact ⟨a0_g3_w33 ⟨n - 34150, hr⟩, a1_g3_w33 ⟨n - 34150, hr⟩⟩
                                                                    · by_cases h34 : n < 34250
                                                                      · have hr : n - 34200 < 50 := by omega
                                                                        have heq : n = (n - 34200) + 34200 := by omega
                                                                        rw [heq]
                                                                        exact ⟨a0_g3_w34 ⟨n - 34200, hr⟩, a1_g3_w34 ⟨n - 34200, hr⟩⟩
                                                                      · by_cases h35 : n < 34300
                                                                        · have hr : n - 34250 < 50 := by omega
                                                                          have heq : n = (n - 34250) + 34250 := by omega
                                                                          rw [heq]
                                                                          exact ⟨a0_g3_w35 ⟨n - 34250, hr⟩, a1_g3_w35 ⟨n - 34250, hr⟩⟩
                                                                        · by_cases h36 : n < 34350
                                                                          · have hr : n - 34300 < 50 := by omega
                                                                            have heq : n = (n - 34300) + 34300 := by omega
                                                                            rw [heq]
                                                                            exact ⟨a0_g3_w36 ⟨n - 34300, hr⟩, a1_g3_w36 ⟨n - 34300, hr⟩⟩
                                                                          · by_cases h37 : n < 34400
                                                                            · have hr : n - 34350 < 50 := by omega
                                                                              have heq : n = (n - 34350) + 34350 := by omega
                                                                              rw [heq]
                                                                              exact ⟨a0_g3_w37 ⟨n - 34350, hr⟩, a1_g3_w37 ⟨n - 34350, hr⟩⟩
                                                                            · by_cases h38 : n < 34450
                                                                              · have hr : n - 34400 < 50 := by omega
                                                                                have heq : n = (n - 34400) + 34400 := by omega
                                                                                rw [heq]
                                                                                exact ⟨a0_g3_w38 ⟨n - 34400, hr⟩, a1_g3_w38 ⟨n - 34400, hr⟩⟩
                                                                              · by_cases h39 : n < 34500
                                                                                · have hr : n - 34450 < 50 := by omega
                                                                                  have heq : n = (n - 34450) + 34450 := by omega
                                                                                  rw [heq]
                                                                                  exact ⟨a0_g3_w39 ⟨n - 34450, hr⟩, a1_g3_w39 ⟨n - 34450, hr⟩⟩
                                                                                · by_cases h40 : n < 34550
                                                                                  · have hr : n - 34500 < 50 := by omega
                                                                                    have heq : n = (n - 34500) + 34500 := by omega
                                                                                    rw [heq]
                                                                                    exact ⟨a0_g3_w40 ⟨n - 34500, hr⟩, a1_g3_w40 ⟨n - 34500, hr⟩⟩
                                                                                  · by_cases h41 : n < 34600
                                                                                    · have hr : n - 34550 < 50 := by omega
                                                                                      have heq : n = (n - 34550) + 34550 := by omega
                                                                                      rw [heq]
                                                                                      exact ⟨a0_g3_w41 ⟨n - 34550, hr⟩, a1_g3_w41 ⟨n - 34550, hr⟩⟩
                                                                                    · by_cases h42 : n < 34650
                                                                                      · have hr : n - 34600 < 50 := by omega
                                                                                        have heq : n = (n - 34600) + 34600 := by omega
                                                                                        rw [heq]
                                                                                        exact ⟨a0_g3_w42 ⟨n - 34600, hr⟩, a1_g3_w42 ⟨n - 34600, hr⟩⟩
                                                                                      · by_cases h43 : n < 34700
                                                                                        · have hr : n - 34650 < 50 := by omega
                                                                                          have heq : n = (n - 34650) + 34650 := by omega
                                                                                          rw [heq]
                                                                                          exact ⟨a0_g3_w43 ⟨n - 34650, hr⟩, a1_g3_w43 ⟨n - 34650, hr⟩⟩
                                                                                        · by_cases h44 : n < 34750
                                                                                          · have hr : n - 34700 < 50 := by omega
                                                                                            have heq : n = (n - 34700) + 34700 := by omega
                                                                                            rw [heq]
                                                                                            exact ⟨a0_g3_w44 ⟨n - 34700, hr⟩, a1_g3_w44 ⟨n - 34700, hr⟩⟩
                                                                                          · by_cases h45 : n < 34800
                                                                                            · have hr : n - 34750 < 50 := by omega
                                                                                              have heq : n = (n - 34750) + 34750 := by omega
                                                                                              rw [heq]
                                                                                              exact ⟨a0_g3_w45 ⟨n - 34750, hr⟩, a1_g3_w45 ⟨n - 34750, hr⟩⟩
                                                                                            · by_cases h46 : n < 34850
                                                                                              · have hr : n - 34800 < 50 := by omega
                                                                                                have heq : n = (n - 34800) + 34800 := by omega
                                                                                                rw [heq]
                                                                                                exact ⟨a0_g3_w46 ⟨n - 34800, hr⟩, a1_g3_w46 ⟨n - 34800, hr⟩⟩
                                                                                              · by_cases h47 : n < 34900
                                                                                                · have hr : n - 34850 < 50 := by omega
                                                                                                  have heq : n = (n - 34850) + 34850 := by omega
                                                                                                  rw [heq]
                                                                                                  exact ⟨a0_g3_w47 ⟨n - 34850, hr⟩, a1_g3_w47 ⟨n - 34850, hr⟩⟩
                                                                                                · by_cases h48 : n < 34950
                                                                                                  · have hr : n - 34900 < 50 := by omega
                                                                                                    have heq : n = (n - 34900) + 34900 := by omega
                                                                                                    rw [heq]
                                                                                                    exact ⟨a0_g3_w48 ⟨n - 34900, hr⟩, a1_g3_w48 ⟨n - 34900, hr⟩⟩
                                                                                                  · have hr : n - 34950 < 50 := by omega
                                                                                                    have heq : n = (n - 34950) + 34950 := by omega
                                                                                                    rw [heq]
                                                                                                    exact ⟨a0_g3_w49 ⟨n - 34950, hr⟩, a1_g3_w49 ⟨n - 34950, hr⟩⟩

private theorem a0_g4_w0 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 35000)) 65535) ≤ dimF (n.val + 35000) := by decide
private theorem a1_g4_w0 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 35000)) 16) ≤ dimF (n.val + 35000) := by decide
private theorem a0_g4_w1 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 35050)) 65535) ≤ dimF (n.val + 35050) := by decide
private theorem a1_g4_w1 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 35050)) 16) ≤ dimF (n.val + 35050) := by decide
private theorem a0_g4_w2 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 35100)) 65535) ≤ dimF (n.val + 35100) := by decide
private theorem a1_g4_w2 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 35100)) 16) ≤ dimF (n.val + 35100) := by decide
private theorem a0_g4_w3 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 35150)) 65535) ≤ dimF (n.val + 35150) := by decide
private theorem a1_g4_w3 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 35150)) 16) ≤ dimF (n.val + 35150) := by decide
private theorem a0_g4_w4 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 35200)) 65535) ≤ dimF (n.val + 35200) := by decide
private theorem a1_g4_w4 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 35200)) 16) ≤ dimF (n.val + 35200) := by decide
private theorem a0_g4_w5 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 35250)) 65535) ≤ dimF (n.val + 35250) := by decide
private theorem a1_g4_w5 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 35250)) 16) ≤ dimF (n.val + 35250) := by decide
private theorem a0_g4_w6 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 35300)) 65535) ≤ dimF (n.val + 35300) := by decide
private theorem a1_g4_w6 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 35300)) 16) ≤ dimF (n.val + 35300) := by decide
private theorem a0_g4_w7 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 35350)) 65535) ≤ dimF (n.val + 35350) := by decide
private theorem a1_g4_w7 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 35350)) 16) ≤ dimF (n.val + 35350) := by decide
private theorem a0_g4_w8 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 35400)) 65535) ≤ dimF (n.val + 35400) := by decide
private theorem a1_g4_w8 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 35400)) 16) ≤ dimF (n.val + 35400) := by decide
private theorem a0_g4_w9 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 35450)) 65535) ≤ dimF (n.val + 35450) := by decide
private theorem a1_g4_w9 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 35450)) 16) ≤ dimF (n.val + 35450) := by decide
private theorem a0_g4_w10 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 35500)) 65535) ≤ dimF (n.val + 35500) := by decide
private theorem a1_g4_w10 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 35500)) 16) ≤ dimF (n.val + 35500) := by decide
private theorem a0_g4_w11 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 35550)) 65535) ≤ dimF (n.val + 35550) := by decide
private theorem a1_g4_w11 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 35550)) 16) ≤ dimF (n.val + 35550) := by decide
private theorem a0_g4_w12 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 35600)) 65535) ≤ dimF (n.val + 35600) := by decide
private theorem a1_g4_w12 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 35600)) 16) ≤ dimF (n.val + 35600) := by decide
private theorem a0_g4_w13 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 35650)) 65535) ≤ dimF (n.val + 35650) := by decide
private theorem a1_g4_w13 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 35650)) 16) ≤ dimF (n.val + 35650) := by decide
private theorem a0_g4_w14 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 35700)) 65535) ≤ dimF (n.val + 35700) := by decide
private theorem a1_g4_w14 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 35700)) 16) ≤ dimF (n.val + 35700) := by decide
private theorem a0_g4_w15 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 35750)) 65535) ≤ dimF (n.val + 35750) := by decide
private theorem a1_g4_w15 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 35750)) 16) ≤ dimF (n.val + 35750) := by decide
private theorem a0_g4_w16 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 35800)) 65535) ≤ dimF (n.val + 35800) := by decide
private theorem a1_g4_w16 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 35800)) 16) ≤ dimF (n.val + 35800) := by decide
private theorem a0_g4_w17 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 35850)) 65535) ≤ dimF (n.val + 35850) := by decide
private theorem a1_g4_w17 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 35850)) 16) ≤ dimF (n.val + 35850) := by decide
private theorem a0_g4_w18 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 35900)) 65535) ≤ dimF (n.val + 35900) := by decide
private theorem a1_g4_w18 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 35900)) 16) ≤ dimF (n.val + 35900) := by decide
private theorem a0_g4_w19 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 35950)) 65535) ≤ dimF (n.val + 35950) := by decide
private theorem a1_g4_w19 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 35950)) 16) ≤ dimF (n.val + 35950) := by decide
private theorem a0_g4_w20 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 36000)) 65535) ≤ dimF (n.val + 36000) := by decide
private theorem a1_g4_w20 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 36000)) 16) ≤ dimF (n.val + 36000) := by decide
private theorem a0_g4_w21 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 36050)) 65535) ≤ dimF (n.val + 36050) := by decide
private theorem a1_g4_w21 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 36050)) 16) ≤ dimF (n.val + 36050) := by decide
private theorem a0_g4_w22 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 36100)) 65535) ≤ dimF (n.val + 36100) := by decide
private theorem a1_g4_w22 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 36100)) 16) ≤ dimF (n.val + 36100) := by decide
private theorem a0_g4_w23 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 36150)) 65535) ≤ dimF (n.val + 36150) := by decide
private theorem a1_g4_w23 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 36150)) 16) ≤ dimF (n.val + 36150) := by decide
private theorem a0_g4_w24 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 36200)) 65535) ≤ dimF (n.val + 36200) := by decide
private theorem a1_g4_w24 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 36200)) 16) ≤ dimF (n.val + 36200) := by decide
private theorem a0_g4_w25 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 36250)) 65535) ≤ dimF (n.val + 36250) := by decide
private theorem a1_g4_w25 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 36250)) 16) ≤ dimF (n.val + 36250) := by decide
private theorem a0_g4_w26 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 36300)) 65535) ≤ dimF (n.val + 36300) := by decide
private theorem a1_g4_w26 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 36300)) 16) ≤ dimF (n.val + 36300) := by decide
private theorem a0_g4_w27 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 36350)) 65535) ≤ dimF (n.val + 36350) := by decide
private theorem a1_g4_w27 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 36350)) 16) ≤ dimF (n.val + 36350) := by decide
private theorem a0_g4_w28 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 36400)) 65535) ≤ dimF (n.val + 36400) := by decide
private theorem a1_g4_w28 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 36400)) 16) ≤ dimF (n.val + 36400) := by decide
private theorem a0_g4_w29 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 36450)) 65535) ≤ dimF (n.val + 36450) := by decide
private theorem a1_g4_w29 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 36450)) 16) ≤ dimF (n.val + 36450) := by decide
private theorem a0_g4_w30 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 36500)) 65535) ≤ dimF (n.val + 36500) := by decide
private theorem a1_g4_w30 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 36500)) 16) ≤ dimF (n.val + 36500) := by decide
private theorem a0_g4_w31 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 36550)) 65535) ≤ dimF (n.val + 36550) := by decide
private theorem a1_g4_w31 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 36550)) 16) ≤ dimF (n.val + 36550) := by decide
private theorem a0_g4_w32 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 36600)) 65535) ≤ dimF (n.val + 36600) := by decide
private theorem a1_g4_w32 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 36600)) 16) ≤ dimF (n.val + 36600) := by decide
private theorem a0_g4_w33 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 36650)) 65535) ≤ dimF (n.val + 36650) := by decide
private theorem a1_g4_w33 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 36650)) 16) ≤ dimF (n.val + 36650) := by decide
private theorem a0_g4_w34 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 36700)) 65535) ≤ dimF (n.val + 36700) := by decide
private theorem a1_g4_w34 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 36700)) 16) ≤ dimF (n.val + 36700) := by decide
private theorem a0_g4_w35 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 36750)) 65535) ≤ dimF (n.val + 36750) := by decide
private theorem a1_g4_w35 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 36750)) 16) ≤ dimF (n.val + 36750) := by decide
private theorem a0_g4_w36 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 36800)) 65535) ≤ dimF (n.val + 36800) := by decide
private theorem a1_g4_w36 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 36800)) 16) ≤ dimF (n.val + 36800) := by decide
private theorem a0_g4_w37 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 36850)) 65535) ≤ dimF (n.val + 36850) := by decide
private theorem a1_g4_w37 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 36850)) 16) ≤ dimF (n.val + 36850) := by decide
private theorem a0_g4_w38 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 36900)) 65535) ≤ dimF (n.val + 36900) := by decide
private theorem a1_g4_w38 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 36900)) 16) ≤ dimF (n.val + 36900) := by decide
private theorem a0_g4_w39 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 36950)) 65535) ≤ dimF (n.val + 36950) := by decide
private theorem a1_g4_w39 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 36950)) 16) ≤ dimF (n.val + 36950) := by decide
private theorem a0_g4_w40 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 37000)) 65535) ≤ dimF (n.val + 37000) := by decide
private theorem a1_g4_w40 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 37000)) 16) ≤ dimF (n.val + 37000) := by decide
private theorem a0_g4_w41 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 37050)) 65535) ≤ dimF (n.val + 37050) := by decide
private theorem a1_g4_w41 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 37050)) 16) ≤ dimF (n.val + 37050) := by decide
private theorem a0_g4_w42 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 37100)) 65535) ≤ dimF (n.val + 37100) := by decide
private theorem a1_g4_w42 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 37100)) 16) ≤ dimF (n.val + 37100) := by decide
private theorem a0_g4_w43 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 37150)) 65535) ≤ dimF (n.val + 37150) := by decide
private theorem a1_g4_w43 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 37150)) 16) ≤ dimF (n.val + 37150) := by decide
private theorem a0_g4_w44 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 37200)) 65535) ≤ dimF (n.val + 37200) := by decide
private theorem a1_g4_w44 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 37200)) 16) ≤ dimF (n.val + 37200) := by decide
private theorem a0_g4_w45 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 37250)) 65535) ≤ dimF (n.val + 37250) := by decide
private theorem a1_g4_w45 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 37250)) 16) ≤ dimF (n.val + 37250) := by decide
private theorem a0_g4_w46 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 37300)) 65535) ≤ dimF (n.val + 37300) := by decide
private theorem a1_g4_w46 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 37300)) 16) ≤ dimF (n.val + 37300) := by decide
private theorem a0_g4_w47 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 37350)) 65535) ≤ dimF (n.val + 37350) := by decide
private theorem a1_g4_w47 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 37350)) 16) ≤ dimF (n.val + 37350) := by decide
private theorem a0_g4_w48 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 37400)) 65535) ≤ dimF (n.val + 37400) := by decide
private theorem a1_g4_w48 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 37400)) 16) ≤ dimF (n.val + 37400) := by decide
private theorem a0_g4_w49 : ∀ n : Fin 50, dimF (Nat.land (argF (n.val + 37450)) 65535) ≤ dimF (n.val + 37450) := by decide
private theorem a1_g4_w49 : ∀ n : Fin 50, dimF (Nat.shiftRight (argF (n.val + 37450)) 16) ≤ dimF (n.val + 37450) := by decide

private theorem pair_g4 (n : ℕ) (hlo : 35000 ≤ n) (hhi : n < 37500) :
    dimF (Nat.land (argF n) 65535) ≤ dimF n ∧
    dimF (Nat.shiftRight (argF n) 16) ≤ dimF n := by
  by_cases h0 : n < 35050
  · have hr : n - 35000 < 50 := by omega
    have heq : n = (n - 35000) + 35000 := by omega
    rw [heq]
    exact ⟨a0_g4_w0 ⟨n - 35000, hr⟩, a1_g4_w0 ⟨n - 35000, hr⟩⟩
  · by_cases h1 : n < 35100
    · have hr : n - 35050 < 50 := by omega
      have heq : n = (n - 35050) + 35050 := by omega
      rw [heq]
      exact ⟨a0_g4_w1 ⟨n - 35050, hr⟩, a1_g4_w1 ⟨n - 35050, hr⟩⟩
    · by_cases h2 : n < 35150
      · have hr : n - 35100 < 50 := by omega
        have heq : n = (n - 35100) + 35100 := by omega
        rw [heq]
        exact ⟨a0_g4_w2 ⟨n - 35100, hr⟩, a1_g4_w2 ⟨n - 35100, hr⟩⟩
      · by_cases h3 : n < 35200
        · have hr : n - 35150 < 50 := by omega
          have heq : n = (n - 35150) + 35150 := by omega
          rw [heq]
          exact ⟨a0_g4_w3 ⟨n - 35150, hr⟩, a1_g4_w3 ⟨n - 35150, hr⟩⟩
        · by_cases h4 : n < 35250
          · have hr : n - 35200 < 50 := by omega
            have heq : n = (n - 35200) + 35200 := by omega
            rw [heq]
            exact ⟨a0_g4_w4 ⟨n - 35200, hr⟩, a1_g4_w4 ⟨n - 35200, hr⟩⟩
          · by_cases h5 : n < 35300
            · have hr : n - 35250 < 50 := by omega
              have heq : n = (n - 35250) + 35250 := by omega
              rw [heq]
              exact ⟨a0_g4_w5 ⟨n - 35250, hr⟩, a1_g4_w5 ⟨n - 35250, hr⟩⟩
            · by_cases h6 : n < 35350
              · have hr : n - 35300 < 50 := by omega
                have heq : n = (n - 35300) + 35300 := by omega
                rw [heq]
                exact ⟨a0_g4_w6 ⟨n - 35300, hr⟩, a1_g4_w6 ⟨n - 35300, hr⟩⟩
              · by_cases h7 : n < 35400
                · have hr : n - 35350 < 50 := by omega
                  have heq : n = (n - 35350) + 35350 := by omega
                  rw [heq]
                  exact ⟨a0_g4_w7 ⟨n - 35350, hr⟩, a1_g4_w7 ⟨n - 35350, hr⟩⟩
                · by_cases h8 : n < 35450
                  · have hr : n - 35400 < 50 := by omega
                    have heq : n = (n - 35400) + 35400 := by omega
                    rw [heq]
                    exact ⟨a0_g4_w8 ⟨n - 35400, hr⟩, a1_g4_w8 ⟨n - 35400, hr⟩⟩
                  · by_cases h9 : n < 35500
                    · have hr : n - 35450 < 50 := by omega
                      have heq : n = (n - 35450) + 35450 := by omega
                      rw [heq]
                      exact ⟨a0_g4_w9 ⟨n - 35450, hr⟩, a1_g4_w9 ⟨n - 35450, hr⟩⟩
                    · by_cases h10 : n < 35550
                      · have hr : n - 35500 < 50 := by omega
                        have heq : n = (n - 35500) + 35500 := by omega
                        rw [heq]
                        exact ⟨a0_g4_w10 ⟨n - 35500, hr⟩, a1_g4_w10 ⟨n - 35500, hr⟩⟩
                      · by_cases h11 : n < 35600
                        · have hr : n - 35550 < 50 := by omega
                          have heq : n = (n - 35550) + 35550 := by omega
                          rw [heq]
                          exact ⟨a0_g4_w11 ⟨n - 35550, hr⟩, a1_g4_w11 ⟨n - 35550, hr⟩⟩
                        · by_cases h12 : n < 35650
                          · have hr : n - 35600 < 50 := by omega
                            have heq : n = (n - 35600) + 35600 := by omega
                            rw [heq]
                            exact ⟨a0_g4_w12 ⟨n - 35600, hr⟩, a1_g4_w12 ⟨n - 35600, hr⟩⟩
                          · by_cases h13 : n < 35700
                            · have hr : n - 35650 < 50 := by omega
                              have heq : n = (n - 35650) + 35650 := by omega
                              rw [heq]
                              exact ⟨a0_g4_w13 ⟨n - 35650, hr⟩, a1_g4_w13 ⟨n - 35650, hr⟩⟩
                            · by_cases h14 : n < 35750
                              · have hr : n - 35700 < 50 := by omega
                                have heq : n = (n - 35700) + 35700 := by omega
                                rw [heq]
                                exact ⟨a0_g4_w14 ⟨n - 35700, hr⟩, a1_g4_w14 ⟨n - 35700, hr⟩⟩
                              · by_cases h15 : n < 35800
                                · have hr : n - 35750 < 50 := by omega
                                  have heq : n = (n - 35750) + 35750 := by omega
                                  rw [heq]
                                  exact ⟨a0_g4_w15 ⟨n - 35750, hr⟩, a1_g4_w15 ⟨n - 35750, hr⟩⟩
                                · by_cases h16 : n < 35850
                                  · have hr : n - 35800 < 50 := by omega
                                    have heq : n = (n - 35800) + 35800 := by omega
                                    rw [heq]
                                    exact ⟨a0_g4_w16 ⟨n - 35800, hr⟩, a1_g4_w16 ⟨n - 35800, hr⟩⟩
                                  · by_cases h17 : n < 35900
                                    · have hr : n - 35850 < 50 := by omega
                                      have heq : n = (n - 35850) + 35850 := by omega
                                      rw [heq]
                                      exact ⟨a0_g4_w17 ⟨n - 35850, hr⟩, a1_g4_w17 ⟨n - 35850, hr⟩⟩
                                    · by_cases h18 : n < 35950
                                      · have hr : n - 35900 < 50 := by omega
                                        have heq : n = (n - 35900) + 35900 := by omega
                                        rw [heq]
                                        exact ⟨a0_g4_w18 ⟨n - 35900, hr⟩, a1_g4_w18 ⟨n - 35900, hr⟩⟩
                                      · by_cases h19 : n < 36000
                                        · have hr : n - 35950 < 50 := by omega
                                          have heq : n = (n - 35950) + 35950 := by omega
                                          rw [heq]
                                          exact ⟨a0_g4_w19 ⟨n - 35950, hr⟩, a1_g4_w19 ⟨n - 35950, hr⟩⟩
                                        · by_cases h20 : n < 36050
                                          · have hr : n - 36000 < 50 := by omega
                                            have heq : n = (n - 36000) + 36000 := by omega
                                            rw [heq]
                                            exact ⟨a0_g4_w20 ⟨n - 36000, hr⟩, a1_g4_w20 ⟨n - 36000, hr⟩⟩
                                          · by_cases h21 : n < 36100
                                            · have hr : n - 36050 < 50 := by omega
                                              have heq : n = (n - 36050) + 36050 := by omega
                                              rw [heq]
                                              exact ⟨a0_g4_w21 ⟨n - 36050, hr⟩, a1_g4_w21 ⟨n - 36050, hr⟩⟩
                                            · by_cases h22 : n < 36150
                                              · have hr : n - 36100 < 50 := by omega
                                                have heq : n = (n - 36100) + 36100 := by omega
                                                rw [heq]
                                                exact ⟨a0_g4_w22 ⟨n - 36100, hr⟩, a1_g4_w22 ⟨n - 36100, hr⟩⟩
                                              · by_cases h23 : n < 36200
                                                · have hr : n - 36150 < 50 := by omega
                                                  have heq : n = (n - 36150) + 36150 := by omega
                                                  rw [heq]
                                                  exact ⟨a0_g4_w23 ⟨n - 36150, hr⟩, a1_g4_w23 ⟨n - 36150, hr⟩⟩
                                                · by_cases h24 : n < 36250
                                                  · have hr : n - 36200 < 50 := by omega
                                                    have heq : n = (n - 36200) + 36200 := by omega
                                                    rw [heq]
                                                    exact ⟨a0_g4_w24 ⟨n - 36200, hr⟩, a1_g4_w24 ⟨n - 36200, hr⟩⟩
                                                  · by_cases h25 : n < 36300
                                                    · have hr : n - 36250 < 50 := by omega
                                                      have heq : n = (n - 36250) + 36250 := by omega
                                                      rw [heq]
                                                      exact ⟨a0_g4_w25 ⟨n - 36250, hr⟩, a1_g4_w25 ⟨n - 36250, hr⟩⟩
                                                    · by_cases h26 : n < 36350
                                                      · have hr : n - 36300 < 50 := by omega
                                                        have heq : n = (n - 36300) + 36300 := by omega
                                                        rw [heq]
                                                        exact ⟨a0_g4_w26 ⟨n - 36300, hr⟩, a1_g4_w26 ⟨n - 36300, hr⟩⟩
                                                      · by_cases h27 : n < 36400
                                                        · have hr : n - 36350 < 50 := by omega
                                                          have heq : n = (n - 36350) + 36350 := by omega
                                                          rw [heq]
                                                          exact ⟨a0_g4_w27 ⟨n - 36350, hr⟩, a1_g4_w27 ⟨n - 36350, hr⟩⟩
                                                        · by_cases h28 : n < 36450
                                                          · have hr : n - 36400 < 50 := by omega
                                                            have heq : n = (n - 36400) + 36400 := by omega
                                                            rw [heq]
                                                            exact ⟨a0_g4_w28 ⟨n - 36400, hr⟩, a1_g4_w28 ⟨n - 36400, hr⟩⟩
                                                          · by_cases h29 : n < 36500
                                                            · have hr : n - 36450 < 50 := by omega
                                                              have heq : n = (n - 36450) + 36450 := by omega
                                                              rw [heq]
                                                              exact ⟨a0_g4_w29 ⟨n - 36450, hr⟩, a1_g4_w29 ⟨n - 36450, hr⟩⟩
                                                            · by_cases h30 : n < 36550
                                                              · have hr : n - 36500 < 50 := by omega
                                                                have heq : n = (n - 36500) + 36500 := by omega
                                                                rw [heq]
                                                                exact ⟨a0_g4_w30 ⟨n - 36500, hr⟩, a1_g4_w30 ⟨n - 36500, hr⟩⟩
                                                              · by_cases h31 : n < 36600
                                                                · have hr : n - 36550 < 50 := by omega
                                                                  have heq : n = (n - 36550) + 36550 := by omega
                                                                  rw [heq]
                                                                  exact ⟨a0_g4_w31 ⟨n - 36550, hr⟩, a1_g4_w31 ⟨n - 36550, hr⟩⟩
                                                                · by_cases h32 : n < 36650
                                                                  · have hr : n - 36600 < 50 := by omega
                                                                    have heq : n = (n - 36600) + 36600 := by omega
                                                                    rw [heq]
                                                                    exact ⟨a0_g4_w32 ⟨n - 36600, hr⟩, a1_g4_w32 ⟨n - 36600, hr⟩⟩
                                                                  · by_cases h33 : n < 36700
                                                                    · have hr : n - 36650 < 50 := by omega
                                                                      have heq : n = (n - 36650) + 36650 := by omega
                                                                      rw [heq]
                                                                      exact ⟨a0_g4_w33 ⟨n - 36650, hr⟩, a1_g4_w33 ⟨n - 36650, hr⟩⟩
                                                                    · by_cases h34 : n < 36750
                                                                      · have hr : n - 36700 < 50 := by omega
                                                                        have heq : n = (n - 36700) + 36700 := by omega
                                                                        rw [heq]
                                                                        exact ⟨a0_g4_w34 ⟨n - 36700, hr⟩, a1_g4_w34 ⟨n - 36700, hr⟩⟩
                                                                      · by_cases h35 : n < 36800
                                                                        · have hr : n - 36750 < 50 := by omega
                                                                          have heq : n = (n - 36750) + 36750 := by omega
                                                                          rw [heq]
                                                                          exact ⟨a0_g4_w35 ⟨n - 36750, hr⟩, a1_g4_w35 ⟨n - 36750, hr⟩⟩
                                                                        · by_cases h36 : n < 36850
                                                                          · have hr : n - 36800 < 50 := by omega
                                                                            have heq : n = (n - 36800) + 36800 := by omega
                                                                            rw [heq]
                                                                            exact ⟨a0_g4_w36 ⟨n - 36800, hr⟩, a1_g4_w36 ⟨n - 36800, hr⟩⟩
                                                                          · by_cases h37 : n < 36900
                                                                            · have hr : n - 36850 < 50 := by omega
                                                                              have heq : n = (n - 36850) + 36850 := by omega
                                                                              rw [heq]
                                                                              exact ⟨a0_g4_w37 ⟨n - 36850, hr⟩, a1_g4_w37 ⟨n - 36850, hr⟩⟩
                                                                            · by_cases h38 : n < 36950
                                                                              · have hr : n - 36900 < 50 := by omega
                                                                                have heq : n = (n - 36900) + 36900 := by omega
                                                                                rw [heq]
                                                                                exact ⟨a0_g4_w38 ⟨n - 36900, hr⟩, a1_g4_w38 ⟨n - 36900, hr⟩⟩
                                                                              · by_cases h39 : n < 37000
                                                                                · have hr : n - 36950 < 50 := by omega
                                                                                  have heq : n = (n - 36950) + 36950 := by omega
                                                                                  rw [heq]
                                                                                  exact ⟨a0_g4_w39 ⟨n - 36950, hr⟩, a1_g4_w39 ⟨n - 36950, hr⟩⟩
                                                                                · by_cases h40 : n < 37050
                                                                                  · have hr : n - 37000 < 50 := by omega
                                                                                    have heq : n = (n - 37000) + 37000 := by omega
                                                                                    rw [heq]
                                                                                    exact ⟨a0_g4_w40 ⟨n - 37000, hr⟩, a1_g4_w40 ⟨n - 37000, hr⟩⟩
                                                                                  · by_cases h41 : n < 37100
                                                                                    · have hr : n - 37050 < 50 := by omega
                                                                                      have heq : n = (n - 37050) + 37050 := by omega
                                                                                      rw [heq]
                                                                                      exact ⟨a0_g4_w41 ⟨n - 37050, hr⟩, a1_g4_w41 ⟨n - 37050, hr⟩⟩
                                                                                    · by_cases h42 : n < 37150
                                                                                      · have hr : n - 37100 < 50 := by omega
                                                                                        have heq : n = (n - 37100) + 37100 := by omega
                                                                                        rw [heq]
                                                                                        exact ⟨a0_g4_w42 ⟨n - 37100, hr⟩, a1_g4_w42 ⟨n - 37100, hr⟩⟩
                                                                                      · by_cases h43 : n < 37200
                                                                                        · have hr : n - 37150 < 50 := by omega
                                                                                          have heq : n = (n - 37150) + 37150 := by omega
                                                                                          rw [heq]
                                                                                          exact ⟨a0_g4_w43 ⟨n - 37150, hr⟩, a1_g4_w43 ⟨n - 37150, hr⟩⟩
                                                                                        · by_cases h44 : n < 37250
                                                                                          · have hr : n - 37200 < 50 := by omega
                                                                                            have heq : n = (n - 37200) + 37200 := by omega
                                                                                            rw [heq]
                                                                                            exact ⟨a0_g4_w44 ⟨n - 37200, hr⟩, a1_g4_w44 ⟨n - 37200, hr⟩⟩
                                                                                          · by_cases h45 : n < 37300
                                                                                            · have hr : n - 37250 < 50 := by omega
                                                                                              have heq : n = (n - 37250) + 37250 := by omega
                                                                                              rw [heq]
                                                                                              exact ⟨a0_g4_w45 ⟨n - 37250, hr⟩, a1_g4_w45 ⟨n - 37250, hr⟩⟩
                                                                                            · by_cases h46 : n < 37350
                                                                                              · have hr : n - 37300 < 50 := by omega
                                                                                                have heq : n = (n - 37300) + 37300 := by omega
                                                                                                rw [heq]
                                                                                                exact ⟨a0_g4_w46 ⟨n - 37300, hr⟩, a1_g4_w46 ⟨n - 37300, hr⟩⟩
                                                                                              · by_cases h47 : n < 37400
                                                                                                · have hr : n - 37350 < 50 := by omega
                                                                                                  have heq : n = (n - 37350) + 37350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact ⟨a0_g4_w47 ⟨n - 37350, hr⟩, a1_g4_w47 ⟨n - 37350, hr⟩⟩
                                                                                                · by_cases h48 : n < 37450
                                                                                                  · have hr : n - 37400 < 50 := by omega
                                                                                                    have heq : n = (n - 37400) + 37400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact ⟨a0_g4_w48 ⟨n - 37400, hr⟩, a1_g4_w48 ⟨n - 37400, hr⟩⟩
                                                                                                  · have hr : n - 37450 < 50 := by omega
                                                                                                    have heq : n = (n - 37450) + 37450 := by omega
                                                                                                    rw [heq]
                                                                                                    exact ⟨a0_g4_w49 ⟨n - 37450, hr⟩, a1_g4_w49 ⟨n - 37450, hr⟩⟩

theorem solution (n : ℕ) (hn0 : 25000 ≤ n) (hn1 : n < 37500) :
    dimF (Nat.land (argF n) 65535) ≤ dimF n ∧
    dimF (Nat.shiftRight (argF n) 16) ≤ dimF n := by
  by_cases hg0 : n < 27500
  · exact pair_g0 n (by omega) hg0
  · by_cases hg1 : n < 30000
    · exact pair_g1 n (by omega) hg1
    · by_cases hg2 : n < 32500
      · exact pair_g2 n (by omega) hg2
      · by_cases hg3 : n < 35000
        · exact pair_g3 n (by omega) hg3
        · exact pair_g4 n (by omega) hn1
