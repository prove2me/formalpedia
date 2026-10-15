-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.coordinate_monomial_power_implies_local_power
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T18:30:36.386625+00:00
-- url     : https://prove2.me/submissions/1701f6f4-54f1-4e75-90d0-2c9519c23a84

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_local_coordinate_inverse_identity
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coordinate_ideal_power_transport_under_inverse_coordinates

open OAI.PiExponent
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (n : ℕ)
    (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hcoord : localCoordinatePolynomial c T P ∈
      (Ideal.span (Set.range (fun i : Fin (m + 1) =>
        MvPolynomial.X i ^ e i)) : Ideal (MvPolynomial (Fin (m + 1)) ℂ)) ^ n) :
    P ∈ (localJetIdeal c T e) ^ n := by
  have htransport :=
    OAI.PiExponent.LogarithmicJetIdeals.coordinate_ideal_power_transport_under_inverse_coordinates
      c T e n (localCoordinatePolynomial c T P) hcoord
  rw [OAI.PiExponent.LogarithmicJetIdeals.local_coordinate_inverse_identity] at htransport
  exact htransport