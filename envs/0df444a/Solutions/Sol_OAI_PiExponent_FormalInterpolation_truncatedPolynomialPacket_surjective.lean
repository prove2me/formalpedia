-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncatedPolynomialPacket_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T18:34:05.312194+00:00
-- url     : https://prove2.me/submissions/bd29141d-14d7-42e2-b83d-c20e2656c6e8

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncatedPolynomialJet_box_surjective
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncatedPolynomialPacket_row_exponent_bound
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncatedPolynomialJet_CRT_gluing

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (K : Nat) (v0 theta : Real) (w : Fin m → Real)
    (R : Real) (e : Fin (m + 1) → Nat) (T : Fin m → Nat)
    (r : Fin m → Complex)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, R = (e i : Real) * InterpolationMatrix.rowWeights v0 theta w i)
    (hr : ∃ i, r i ≠ 0) :
    ∀ n : Nat,
      ∀ f : InterpolationMatrix.Row K v0 theta w ((n : Real) * R) → Complex,
        ∃ P : MvPolynomial (Fin (m + 1)) Complex,
          truncatedPolynomialPacket K v0 theta w ((n : Real) * R) r T P = f := by
  classical
  intro n f
  let S : Fin (m + 1) → Nat := fun i => n * e i
  let g : Fin K →
      {a : Fin (m + 1) → Nat // ∀ i, a i < S i} → Complex :=
    fun j a =>
      if h : a.1 ∈ OAI.PiExponent.strictWeightedSimplex
          (InterpolationMatrix.rowWeights v0 theta w) ((n : Real) * R) then
        f (j, ⟨a.1, h⟩)
      else 0
  choose Q hQ using fun j =>
    OAI.PiExponent.FormalInterpolation.truncatedPolynomialJet_box_surjective
      (fun i => (j.val : Complex) * r i) T S (g j)
  obtain ⟨P, hP⟩ :=
    OAI.PiExponent.FormalInterpolation.truncatedPolynomialJet_CRT_gluing
      K T r S Q hr
  refine ⟨P, ?_⟩
  funext rho
  change (truncatedPolynomialJet (fun i => (rho.1.val : Complex) * r i) T P).coeff
      (InterpolationMatrix.exponentVector rho.2.1) = f rho
  have hb := OAI.PiExponent.FormalInterpolation.truncatedPolynomialPacket_row_exponent_bound
    K v0 theta w R e n rho hR he hscale
  have hbox : ∀ i, rho.2.1 i < S i := by
    simpa [S] using hb
  have hrow : rho.2.1 ∈ OAI.PiExponent.strictWeightedSimplex
      (InterpolationMatrix.rowWeights v0 theta w) ((n : Real) * R) := rho.2.2
  have hlocal := hQ rho.1 ⟨rho.2.1, hbox⟩
  have hglue := hP rho.1 ⟨rho.2.1, hbox⟩
  rw [hglue, hlocal]
  simp [g, hrow]