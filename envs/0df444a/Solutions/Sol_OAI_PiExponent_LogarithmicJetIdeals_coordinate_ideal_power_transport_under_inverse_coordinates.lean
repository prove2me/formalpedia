-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.coordinate_ideal_power_transport_under_inverse_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T19:42:10.794606+00:00
-- url     : https://prove2.me/submissions/eb7f3249-7f90-478c-b934-b5a0c53d42a7

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (n : ℕ)
    (Q : MvPolynomial (Fin (m + 1)) ℂ)
    (hcoord : Q ∈
      (Ideal.span (Set.range (fun i : Fin (m + 1) =>
        MvPolynomial.X i ^ e i)) : Ideal (MvPolynomial (Fin (m + 1)) ℂ)) ^ n) :
    MvPolynomial.aeval (jetCoordinate c T) Q ∈ (localJetIdeal c T e) ^ n := by
  let f : MvPolynomial (Fin (m + 1)) ℂ →+* MvPolynomial (Fin (m + 1)) ℂ :=
    (MvPolynomial.aeval (R := ℂ) (jetCoordinate c T)).toRingHom
  let I : Ideal (MvPolynomial (Fin (m + 1)) ℂ) :=
    Ideal.span (Set.range (fun i : Fin (m + 1) => MvPolynomial.X i ^ e i))
  let J : Ideal (MvPolynomial (Fin (m + 1)) ℂ) := localJetIdeal c T e
  have hgen (i : Fin (m + 1)) :
      f (MvPolynomial.X i ^ e i) = jetCoordinate c T i ^ e i := by
    change MvPolynomial.aeval (R := ℂ) (jetCoordinate c T)
      (MvPolynomial.X i ^ e i) = jetCoordinate c T i ^ e i
    simp only [map_pow, MvPolynomial.aeval_X]
  have hmap : Ideal.map f I = J := by
    change Ideal.map f
      (Ideal.span (Set.range (fun i : Fin (m + 1) => MvPolynomial.X i ^ e i))) =
      Ideal.span (Set.range (fun i : Fin (m + 1) => jetCoordinate c T i ^ e i))
    rw [Ideal.map_span, ← Set.range_comp']
    simp only [hgen]
  have hmem : f Q ∈ Ideal.map f (I ^ n) :=
    Ideal.mem_map_of_mem f hcoord
  rw [Ideal.map_pow, hmap] at hmem
  change f Q ∈ J ^ n
  exact hmem