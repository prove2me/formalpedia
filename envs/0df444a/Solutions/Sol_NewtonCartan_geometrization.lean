-- Prove2me | solution 1 for NewtonCartan.geometrization
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:38:06.540347+00:00
-- url     : https://prove2.me/submissions/df88cbf5-aea8-4034-b1aa-fec06fee303e

import Definitions.Def_NewtonCartan_defs
import Theorems.Thm_NewtonCartan_geometrization_unique
import Theorems.Thm_NewtonCartan_geometrization_curvConds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped ContDiff BigOperators
open Classical
open NewtonCartan

/-! # Prop. 2.1 (Trautman) — reduction to uniqueness + curvature children
Following Malament, *Topics…*, Prop. 4.2.1 (G1)–(G3).
-/

private lemma contDiff_pd (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (b : Fin 4) :
    ContDiff ℝ ∞ (fun x => pd φ b x) := by
  have hf := (contDiff_infty_iff_fderiv.1 hφ).2
  simpa [pd] using ContDiff.clm_apply hf contDiff_const

private lemma contDiff_gradUp_apply (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (a : Fin 4) :
    ContDiff ℝ ∞ (fun x => gradUp φ x a) := by
  simpa [gradUp] using
    ContDiff.sum (s := Finset.univ) (f := fun n : Fin 4 => fun x => hh a n * pd φ n x)
      (fun n _ => contDiff_const.mul (contDiff_pd φ hφ n))

private lemma contDiff_geomΓ (Γ : Conn) (φ : E → ℝ) (hΓ : ContDiff ℝ ∞ Γ)
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (geomΓ Γ φ) := by
  apply contDiff_pi'; intro a
  apply contDiff_pi'; intro b
  apply contDiff_pi'; intro c
  have hΓabc : ContDiff ℝ ∞ (fun x => Γ x a b c) :=
    contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 hΓ a) b) c
  simpa [geomΓ] using hΓabc.add (contDiff_const.mul (contDiff_gradUp_apply φ hφ a))

private lemma gradUp_time (φ : E → ℝ) (x : E) : gradUp φ x 0 = 0 := by
  simp [gradUp, hh]

private lemma sum_tt_gradUp (φ : E → ℝ) (x : E) :
    (∑ n : Fin 4, tt n * gradUp φ x n) = 0 := by
  simp [tt, Finset.sum_ite_eq', gradUp_time]

private lemma sum_tt_hh (b : Fin 4) : (∑ n : Fin 4, tt n * hh n b) = 0 := by
  apply Finset.sum_eq_zero; intro n _; simp only [tt, hh]; split_ifs <;> simp_all

private lemma hh_comm (a b : Fin 4) : hh a b = hh b a := by
  simp only [hh]
  by_cases h : a = b
  · subst h; rfl
  · simp [h, Ne.symm h]

private lemma isDerivOp_geomΓ (Γ : Conn) (φ : E → ℝ) (hNG : IsNG Γ φ) :
    IsDerivOp (geomΓ Γ φ) := by
  refine ⟨contDiff_geomΓ Γ φ hNG.1.1.1 hNG.2.2, fun x a b c => ?_⟩
  simp [geomΓ, hNG.1.1.2 x a b c, mul_comm (tt b)]

private lemma compatible_geomΓ (Γ : Conn) (φ : E → ℝ) (hNG : IsNG Γ φ) :
    Compatible (geomΓ Γ φ) := by
  constructor
  · intro x b c
    have h0 := hNG.1.2.1 x b c
    simp only [geomΓ, add_mul, Finset.sum_add_distrib]
    have hcorr :
        (∑ n : Fin 4, (tt b * tt c * gradUp φ x n) * tt n) =
          tt b * tt c * (∑ n : Fin 4, tt n * gradUp φ x n) := by
      simp [mul_assoc, mul_left_comm, mul_comm, Finset.mul_sum]
    rw [h0, zero_add, hcorr, sum_tt_gradUp, mul_zero]
  · intro x a b c
    have h0 := hNG.1.2.2 x a b c
    have hgoal :
        (∑ n : Fin 4,
          ((Γ x b a n + tt a * tt n * gradUp φ x b) * hh n c +
            (Γ x c a n + tt a * tt n * gradUp φ x c) * hh b n)) =
          (∑ n : Fin 4, (Γ x b a n * hh n c + Γ x c a n * hh b n)) +
            (∑ n : Fin 4, (tt a * tt n * gradUp φ x b) * hh n c) +
            (∑ n : Fin 4, (tt a * tt n * gradUp φ x c) * hh b n) := by
      simp [add_mul, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]
    have hc1 :
        (∑ n : Fin 4, (tt a * tt n * gradUp φ x b) * hh n c) =
          tt a * gradUp φ x b * (∑ n : Fin 4, tt n * hh n c) := by
      simp [mul_assoc, mul_left_comm, mul_comm, Finset.mul_sum]
    have hc2 :
        (∑ n : Fin 4, (tt a * tt n * gradUp φ x c) * hh b n) =
          tt a * gradUp φ x c * (∑ n : Fin 4, tt n * hh b n) := by
      simp [mul_assoc, mul_left_comm, mul_comm, Finset.mul_sum]
    have hbn : (∑ n : Fin 4, tt n * hh b n) = 0 := by
      simp_rw [hh_comm b]; exact sum_tt_hh b
    change (∑ n : Fin 4,
        (geomΓ Γ φ x b a n * hh n c + geomΓ Γ φ x c a n * hh b n)) = 0
    simp only [geomΓ]
    rw [hgoal, h0, zero_add, hc1, hc2, sum_tt_hh, hbn, mul_zero, mul_zero, add_zero]

private lemma isClassical_geomΓ (Γ : Conn) (φ : E → ℝ) (hNG : IsNG Γ φ) :
    IsClassical (geomΓ Γ φ) :=
  ⟨isDerivOp_geomΓ Γ φ hNG, compatible_geomΓ Γ φ hNG⟩

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

private lemma sameTrajectories_geomΓ (Γ : Conn) (φ : E → ℝ) :
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

/-- Parent reduces to uniqueness + curvature children (Malament (G2) uniqueness clause
and (G3)). Classical spacetime and trajectory agreement are proved directly. -/
theorem solution (Γ : Conn) (φ ρ : E → ℝ) (hNG : IsNG Γ φ) (hρ : ContDiff ℝ ∞ ρ)
    (hP : Poisson Γ φ ρ) :
    IsClassical (geomΓ Γ φ) ∧ SameTrajectories Γ φ (geomΓ Γ φ) ∧
    (∀ Γ' : Conn, IsDerivOp Γ' → SameTrajectories Γ φ Γ' → Γ' = geomΓ Γ φ) ∧
    CurvConds (geomΓ Γ φ) ρ := by
  refine ⟨isClassical_geomΓ Γ φ hNG, sameTrajectories_geomΓ Γ φ, ?_, ?_⟩
  · exact NewtonCartan.geometrization_unique Γ φ hNG
  · exact NewtonCartan.geometrization_curvConds Γ φ ρ hNG hρ hP
