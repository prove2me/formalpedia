-- Prove2me | solution 1 for MazurTransfer.dvr_norm_factorization_order
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T20:45:37.833443+00:00
-- url     : https://prove2.me/submissions/ac9d59d7-51d7-421a-a907-6126d26f47bc

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a norm factorization with unit factors determines a DVR
order. Named downstream consumer: finite cusp orders in the Mazur curve's
cubic principal divisor.
-/
import Mathlib

theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (a b u π : R) (n : ℕ) (hπ : Irreducible π) (hb : IsUnit b) (hu : IsUnit u)
    (hprod : a * b = u * π ^ n) :
    Associated a (π ^ n) ∧ IsDiscreteValuationRing.addVal R a = n := by
  have hassoc : Associated a (π ^ n) := by
    apply (associated_mul_isUnit_left_iff hb).mp
    rw [hprod]
    exact associated_unit_mul_left _ _ hu
  refine ⟨hassoc, ?_⟩
  rw [(IsDiscreteValuationRing.addVal_eq_iff_associated _ _).mpr hassoc]
  exact hπ.addVal_pow n
#print axioms solution
