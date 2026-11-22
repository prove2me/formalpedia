-- Prove2me | solution 1 for LamLitt.lam_litt_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T22:53:15.633872+00:00
-- url     : https://prove2.me/submissions/425992de-0948-428e-b342-9f4f3069e0b3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_LamLitt_Defs
import Theorems.Thm_LamLitt_eisenstein
import Theorems.Thm_LamLitt_integrality_implies_omega_integrality
import Theorems.Thm_LamLitt_omega_integrality_implies_integrality
import Theorems.Thm_LamLitt_integrality_implies_algebraicity
import Mathlib

open PowerSeries
open LamLitt

theorem solution {n : ℕ} (f : PowerSeries ℚ) (g : MvRatFunc (Fin (n + 1)) ℚ)
    (hODE : IsSolutionOfAlgebraicODE n f g) :
    List.TFAE
      [IsAlgebraic (Polynomial ℚ) f,
       ∃ N : ℕ, IsCoeffIntegralAdjointInvNat f N,
       ∃ ω : Nat.Primes → ℤ, omegaSuperlinear ω ∧ omegaIntegral ω (PowerSeries.coeff · f)] := by
  tfae_have 1 → 2 := fun hAlg => eisenstein f hAlg
  tfae_have 2 → 3 := fun ⟨N, hN⟩ => integrality_implies_omega_integrality f N hN
  tfae_have 3 → 2 := fun ⟨ω, hω⟩ => omega_integrality_implies_integrality f g hODE ω hω
  tfae_have 2 → 1 := fun ⟨N, hN⟩ => integrality_implies_algebraicity f g hODE N hN
  tfae_finish
