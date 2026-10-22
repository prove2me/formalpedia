-- Prove2me | solution 1 for NewtonCartan.sameTrajectories_geomGamma
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T06:14:23.2944+00:00
-- url     : https://prove2.me/submissions/e96cb8c1-be79-43ca-90a4-5fe52d5c61a8

import Definitions.Def_NewtonCartan_defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped ContDiff BigOperators
open Classical
open NewtonCartan

/-! Trautman: geomΓ has the Newtonian trajectories of `(Γ, φ)`. -/

private lemma accel_geomΓ (Γ : Conn) (φ : E → ℝ) (γ : ℝ → E) (s : ℝ) (a : Fin 4) :
    accel (geomΓ Γ φ) γ s a =
      accel Γ γ s a + gradUp φ (γ s) a * (deriv γ s 0) ^ 2 := by
  simp only [accel, geomΓ, add_mul, Finset.sum_add_distrib]
  have hproj : (∑ b : Fin 4, tt b * deriv γ s b) = deriv γ s 0 := by
    simp [tt, Finset.sum_ite_eq']
  have hfactor :
      (∑ b : Fin 4, ∑ c : Fin 4,
          ((tt b * tt c * gradUp φ (γ s) a) * deriv γ s b * deriv γ s c)) =
        gradUp φ (γ s) a * (deriv γ s 0) ^ 2 := by
    have h1 :
        (∑ b : Fin 4, ∑ c : Fin 4,
            ((tt b * tt c * gradUp φ (γ s) a) * deriv γ s b * deriv γ s c)) =
          gradUp φ (γ s) a *
            (∑ b : Fin 4, tt b * deriv γ s b) *
            (∑ c : Fin 4, tt c * deriv γ s c) := by
      simp [mul_assoc, mul_left_comm, mul_comm, Finset.mul_sum]
    rw [h1, hproj]; ring
  rw [hfactor, add_assoc]

theorem solution (Γ : Conn) (φ : E → ℝ) :
    SameTrajectories Γ φ (geomΓ Γ φ) := by
  intro γ s₀ s₁ hγ
  constructor
  · intro hgeo s hs a
    have ht : deriv γ s 0 = 1 := hγ.2.2 s hs
    have hA := hgeo s hs a
    rw [accel_geomΓ, ht, one_pow] at hA
    linarith
  · intro hNew s hs a
    have ht : deriv γ s 0 = 1 := hγ.2.2 s hs
    rw [accel_geomΓ, ht, one_pow, hNew s hs a]; ring
