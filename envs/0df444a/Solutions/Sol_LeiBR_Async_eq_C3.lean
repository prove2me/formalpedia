-- Prove2me | solution 1 for LeiBR.Async.eq_C3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:51:34.122221+00:00
-- url     : https://prove2.me/submissions/d2eee28a-2ac5-4978-a88d-37a61dbf6987

import Mathlib
import Definitions.Def_LeiBR_Async_Game
import Definitions.Def_LeiBR_Async_Algorithm

open LeiBR.Async
open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {N : ℕ} {n : Fin N → ℕ}
    (x : ℕ → Ω → LeiBR.Sync.Profile n) (xs : LeiBR.Sync.Profile n) (I : ℕ → Finset (Fin N))
    (τ : Fin N → Fin N → ℕ → ℕ) (B1 B2 : ℕ) (hA4 : Assumption4 I τ B1 B2)
    (hτk : ∀ i j k, τ i j k ≤ k) (C ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (kbar : ℕ)
    (hind : ∀ k ≤ kbar, ∀ j, ∫ ω, ‖x k ω j - xs j‖ ∂P ≤ (C + k) * ρ ^ (k / B1)) :
    ∀ k, (kbar / B1) * B1 ≤ k → k ≤ kbar → ∀ i ∈ I k,
      (⨆ j, ∫ ω, ‖x (k - τ i j k) ω j - xs j‖ ∂P) ≤
        (C + k) * ρ ^ (kbar / B1 - nZero B1 B2) := by
  intro k hk1 hk2 i hi
  haveI : Nonempty (Fin N) := ⟨i⟩
  have hB1 := hA4.B1_pos
  have hn0 : B2 ≤ nZero B1 B2 * B1 := by
    have h := Nat.le_ceil ((B2 : ℝ) / (B1 : ℝ))
    have hB1r : (0 : ℝ) < B1 := by exact_mod_cast hB1
    rw [div_le_iff₀ hB1r] at h
    unfold nZero
    exact_mod_cast h
  apply ciSup_le
  intro j
  have hτ := hA4.delay_le k i hi j
  have hk' : k - τ i j k ≤ kbar := le_trans (Nat.sub_le _ _) hk2
  have h := hind (k - τ i j k) hk' j
  have hpos : 0 < ρ ^ ((k - τ i j k) / B1) := pow_pos hρ0 _
  have hint : 0 ≤ ∫ ω, ‖x (k - τ i j k) ω j - xs j‖ ∂P := integral_nonneg (fun ω => norm_nonneg _)
  have hC : 0 ≤ C + ((k - τ i j k : ℕ) : ℝ) := by
    by_contra hc
    push_neg at hc
    have := mul_neg_of_neg_of_pos hc hpos
    linarith
  have hm : kbar / B1 - nZero B1 B2 ≤ (k - τ i j k) / B1 := by
    rw [Nat.le_div_iff_mul_le hB1, Nat.sub_mul]
    omega
  have hpow : ρ ^ ((k - τ i j k) / B1) ≤ ρ ^ (kbar / B1 - nZero B1 B2) :=
    pow_le_pow_of_le_one hρ0.le hρ1.le hm
  have hkk : ((k - τ i j k : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le _ _
  have hpow0 : 0 ≤ ρ ^ (kbar / B1 - nZero B1 B2) := pow_nonneg hρ0.le _
  calc ∫ ω, ‖x (k - τ i j k) ω j - xs j‖ ∂P
      ≤ (C + ((k - τ i j k : ℕ) : ℝ)) * ρ ^ ((k - τ i j k) / B1) := h
    _ ≤ (C + ((k - τ i j k : ℕ) : ℝ)) * ρ ^ (kbar / B1 - nZero B1 B2) :=
        mul_le_mul_of_nonneg_left hpow hC
    _ ≤ (C + k) * ρ ^ (kbar / B1 - nZero B1 B2) :=
        mul_le_mul_of_nonneg_right (by linarith) hpow0
