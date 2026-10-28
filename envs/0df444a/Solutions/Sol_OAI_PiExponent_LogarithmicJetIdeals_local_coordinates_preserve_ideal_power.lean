-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.local_coordinates_preserve_ideal_power
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:13:50.73973+00:00
-- url     : https://prove2.me/submissions/8ee3351a-142e-4dce-be2d-c2297a54b109

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinates
import Mathlib

open OAI.PiExponent
open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (n : ℕ)
    (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hQ : localCoordinatePolynomial c T P ∈
      Ideal.span (Set.range (fun i : Fin (m + 1) =>
        (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) ℂ) ^ e i)) ^ n) :
    P ∈ localJetIdeal c T e ^ n := by
  set σ : MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin (m + 1)) ℂ :=
    MvPolynomial.aeval (Fin.cases (1 + MvPolynomial.X 0) (fun i : Fin m =>
      MvPolynomial.C (c i) + MvPolynomial.X i.succ +
        Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0)
          (InterpolationMatrix.truncatedLog (T i)))) with hσ
  set ψ : MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin (m + 1)) ℂ :=
    MvPolynomial.aeval (jetCoordinate c T) with hψ
  have hev : ∀ (f : MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin (m + 1)) ℂ)
      (x : MvPolynomial (Fin (m + 1)) ℂ) (p : Polynomial ℂ),
      f (Polynomial.eval₂ MvPolynomial.C x p) = Polynomial.eval₂ MvPolynomial.C (f x) p := by
    intro f x p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp [Polynomial.eval₂_add, hp, hq]
    | monomial k a => simp [Polynomial.eval₂_monomial, map_mul, map_pow, MvPolynomial.algHom_C]
  have hinv : ψ.comp σ = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hσ, hψ, jetCoordinate]
    · simp only [AlgHom.comp_apply, hσ, MvPolynomial.aeval_X, Fin.cases_succ, map_add, AlgHom.id_apply]
      rw [hev]
      simp [hψ, jetCoordinate]
      ring
  have hP : P = ψ (localCoordinatePolynomial c T P) := by
    have : localCoordinatePolynomial c T P = σ P := rfl
    rw [this, ← AlgHom.comp_apply, hinv, AlgHom.id_apply]
  rw [hP]
  have h1 := Ideal.mem_map_of_mem (ψ : MvPolynomial (Fin (m + 1)) ℂ →+* MvPolynomial (Fin (m + 1)) ℂ) hQ
  rw [Ideal.map_pow, Ideal.map_span] at h1
  have e : Ideal.span ((ψ : MvPolynomial (Fin (m + 1)) ℂ →+* MvPolynomial (Fin (m + 1)) ℂ) ''
      Set.range (fun i : Fin (m + 1) => (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) ℂ) ^ e i)) =
      localJetIdeal c T e := by
    rw [localJetIdeal, ← Set.range_comp]
    have : ((ψ : MvPolynomial (Fin (m + 1)) ℂ →+* MvPolynomial (Fin (m + 1)) ℂ) ∘
        fun i : Fin (m+1) => (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) ℂ) ^ e i) =
        fun i => jetCoordinate c T i ^ e i := by
      funext i; simp [hψ]
    rw [this]
  rw [e] at h1
  exact h1
