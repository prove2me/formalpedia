-- Prove2me | solution 1 for GhadimiLan.TwoPhase.eq_2_28
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:35:14.370102+00:00
-- url     : https://prove2.me/submissions/60e3058d-2f68-4627-b15c-bde77977f546

import Mathlib
import Definitions.Def_GhadimiLan_TwoPhase_Model
set_option autoImplicit false
open MeasureTheory ProbabilityTheory

theorem solution {n S : ℕ} (hS : 0 < S)
    (a b : Fin S → GhadimiLan.RSG.E n) (sStar : Fin S)
    (hmin : ∀ s, ‖b sStar‖ ≤ ‖b s‖) :
    ‖a sStar‖ ^ 2 ≤
      4 * (Finset.univ : Finset (Fin S)).inf'
        (by exact ⟨⟨0, hS⟩, Finset.mem_univ _⟩) (fun s => ‖a s‖ ^ 2) +
      4 * (Finset.univ : Finset (Fin S)).sup'
        (by exact ⟨⟨0, hS⟩, Finset.mem_univ _⟩) (fun s => ‖b s - a s‖ ^ 2) +
      2 * ‖a sStar - b sStar‖ ^ 2 := by
  obtain ⟨s0, -, hs0⟩ := Finset.exists_mem_eq_inf'
    (⟨⟨0, hS⟩, Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin S)).Nonempty)
    (fun s => ‖a s‖ ^ 2)
  have hsup : ‖b s0 - a s0‖ ^ 2 ≤ (Finset.univ : Finset (Fin S)).sup'
        (⟨⟨0, hS⟩, Finset.mem_univ _⟩) (fun s => ‖b s - a s‖ ^ 2) :=
    Finset.le_sup' (fun s => ‖b s - a s‖ ^ 2) (Finset.mem_univ s0)
  rw [hs0]
  have h1 : ‖a sStar‖ ≤ ‖b sStar‖ + ‖a sStar - b sStar‖ := by
    have := norm_sub_norm_le (a sStar) (b sStar); linarith
  have h2 : ‖b s0‖ ≤ ‖a s0‖ + ‖b s0 - a s0‖ := by
    have := norm_sub_norm_le (b s0) (a s0); linarith
  have h3 := hmin s0
  have hy : ‖b sStar‖ ≤ ‖a s0‖ + ‖b s0 - a s0‖ := by linarith
  have hy0 := norm_nonneg (b sStar)
  have hx0 := norm_nonneg (a sStar)
  have e1 : ‖b sStar‖ ^ 2 ≤ (‖a s0‖ + ‖b s0 - a s0‖) ^ 2 := pow_le_pow_left₀ hy0 hy 2
  have e2 : ‖a sStar‖ ^ 2 ≤ (‖b sStar‖ + ‖a sStar - b sStar‖) ^ 2 := pow_le_pow_left₀ hx0 h1 2
  nlinarith [sq_nonneg (‖a s0‖ - ‖b s0 - a s0‖), sq_nonneg (‖b sStar‖ - ‖a sStar - b sStar‖)]
