-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicJetBound_pderiv_of_commutes
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T17:15:26.28354+00:00
-- url     : https://prove2.me/submissions/ca7d66d4-7fa7-41f5-8c94-0c87a0c3d0a2

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Mathlib.Algebra.MvPolynomial.PDeriv

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution {m K : Nat}
    (φ : Fin K → MvPolynomial (Fin (m + 1)) Complex →ₐ[Complex]
      MvPowerSeries (Fin (m + 1)) Complex)
    (v : Fin (m + 1) → Rat) (H : Real) (i : Fin m)
    (F : MvPolynomial (Fin (m + 1)) Complex)
    (hjet : ∀ j (a : Fin (m + 1) →₀ Nat),
      (∑ k, (v k : Real) * (a k : Real)) < H →
        MvPowerSeries.coeff a (φ j F) = 0)
    (hcomm : ∀ j,
      φ j (MvPolynomial.pderiv i.succ F) =
        MvPowerSeries.pderiv Complex i.succ (φ j F)) :
    ∀ j (a : Fin (m + 1) →₀ Nat),
      (∑ k, (v k : Real) * (a k : Real)) < H - (v i.succ : Real) →
        MvPowerSeries.coeff a (φ j (MvPolynomial.pderiv i.succ F)) = 0 := by
  intro j a ha
  let b : Fin (m + 1) →₀ Nat := a + Finsupp.single (i.succ) (1 : Nat)
  have hsingle :
      (∑ k : Fin (m + 1), (v k : Real) *
        ((Finsupp.single (i.succ) (1 : Nat) : Fin (m + 1) →₀ Nat) k : Real)) =
        (v i.succ : Real) := by
    simp only [Finsupp.single_apply]
    rw [Finset.sum_eq_single (i.succ)]
    · simp
    · intro x hx hne
      have hxi : i.succ ≠ x := Ne.symm hne
      simp [Finsupp.single_apply, hxi]
    · simp
  have hweight :
      (∑ k, (v k : Real) * (b k : Real)) =
        (∑ k, (v k : Real) * (a k : Real)) + (v i.succ : Real) := by
    simp only [b, Finsupp.add_apply, Nat.cast_add, mul_add,
      Finset.sum_add_distrib]
    rw [hsingle]
  have hlt : (∑ k, (v k : Real) * (b k : Real)) < H := by
    rw [hweight]
    linarith
  rw [hcomm j, MvPowerSeries.coeff_pderiv]
  rw [show a + Finsupp.single (i.succ) (1 : Nat) = b by rfl]
  rw [hjet j b hlt]
  simp
