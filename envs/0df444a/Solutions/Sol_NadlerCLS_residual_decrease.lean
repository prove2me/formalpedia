-- Prove2me | solution 1 for NadlerCLS.residual_decrease
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:08:35.297119+00:00
-- url     : https://prove2.me/submissions/968ecdee-d0fd-47d1-b474-f222ff279796

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Quadratics
import Definitions.Def_NadlerCLS_PNInstance

set_option autoImplicit false

open NetworkEquilibriumCLS.LinearNash NadlerCLS in
theorem solution {n : ℕ} (I : PNInstance n) (hI : I.Valid) (x : Fin n → ℝ)
    (hx : InCube x)
    (hN2 : ¬ (I.dist (I.Pi x x) (I.Pi (I.P x) (I.Pi x x)) >
      (I.k : ℝ) * I.dist x (I.P x) + I.ε₂)) :
    I.r (I.P x) ≤ (I.k : ℝ) * I.r x + I.ε₂ ∧
    I.r x - I.r (I.P x) ≥ (1 - (I.k : ℝ)) * I.r x - I.ε₂ ∧
    ((I.ε₁ : ℝ) < I.r x → 0 < I.r x - I.r (I.P x)) := by
  have h1 : I.r (I.P x) ≤ (I.k : ℝ) * I.r x + I.ε₂ := by
    have := not_lt.mp hN2
    simpa [PNInstance.r, PNInstance.P] using this
  obtain ⟨-, -, hε1, -, -, -, -, -, hk1, hε2⟩ := hI
  have hk1' : (I.k : ℝ) < 1 := by exact_mod_cast hk1
  have hε2' : (I.ε₂ : ℝ) < I.ε₁ * (1 - I.k) := by exact_mod_cast hε2
  refine ⟨h1, by linarith, fun h => ?_⟩
  have : (I.ε₁ : ℝ) * (1 - I.k) < I.r x * (1 - I.k) :=
    mul_lt_mul_of_pos_right h (by linarith)
  nlinarith
