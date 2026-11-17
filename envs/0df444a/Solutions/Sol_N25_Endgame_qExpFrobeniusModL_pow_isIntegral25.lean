-- Prove2me | solution 1 for N25.Endgame.qExpFrobeniusModL_pow_isIntegral25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:24:23.13961+00:00
-- url     : https://prove2.me/submissions/3ce1f846-90b2-4a1a-9164-4bc10645675d

import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_N25_Endgame_exists_qExpFrobeniusModL_pow_eq_pow25

/-! Iterates of the prime q-expansion Frobenius on functions and places. -/
noncomputable section

namespace N25.Endgame

/-- The iterate of prime q-expansion Frobenius is an integral field map. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] (n : ℕ) :
    (ModularCurve.qExpFrobeniusModL K Γ25 p ^ n).toRingHom.IsIntegral := by
  intro x
  obtain ⟨y, hy⟩ := exists_qExpFrobeniusModL_pow_eq_pow25 p K n x
  refine ⟨Polynomial.X ^ (p ^ n) - Polynomial.C y,
    Polynomial.monic_X_pow_sub_C _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), ?_⟩
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero]
  exact hy.symm

end N25.Endgame
