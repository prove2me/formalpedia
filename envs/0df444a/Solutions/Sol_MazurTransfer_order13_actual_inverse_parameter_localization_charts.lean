-- Prove2me | solution 1 for MazurTransfer.order13_actual_inverse_parameter_localization_charts
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T10:00:31.774917+00:00
-- url     : https://prove2.me/submissions/ce12c103-67a5-45ea-b26c-91912bf8069c

import Definitions.Def_MazurTransfer_Order13InverseParameterChartComparison
import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Theorems.Thm_MazurTransfer_order13_actual_integral_curve_geometrically_integral
import Theorems.Thm_MazurTransfer_order13_actual_integral_curve_flat_finitely_presented_and_smooth
import Definitions.Def_MazurTransfer_Order13InverseParameterCoordinates

open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open scoped MazurTransfer.Order13InverseParameterPublicCoordinates

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: registrations of the existing canonical localization actions.
Named downstream consumer: the exact public inverse-parameter chart statement.
-/
namespace MazurTransfer.Order13InverseParameterPublicCoordinates
noncomputable scoped instance candidateAwayAlgebra.{u} (R : Type u) [CommRing R]
    (v : candidateAlgebra R) : Algebra (candidateAlgebra R) (Localization.Away v) :=
  inferInstance
noncomputable scoped instance candidateAwayBaseAlgebra.{u} (R : Type u) [CommRing R]
    (v : candidateAlgebra R) : Algebra R (Localization.Away v) :=
  inferInstance
end MazurTransfer.Order13InverseParameterPublicCoordinates

theorem solution.{u} (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (h104 : IsUnit (104 : R)) :
    ∃ sB aB bB : MazurTransfer.Order13InverseParameterPublicCoordinates.candidateAlgebra R,
    (sB : MazurTransfer.Order13InverseParameterPublicCoordinates.OrdinaryLocalization R) =
      MazurTransfer.Order13InverseParameterPublicCoordinates.s R ∧
    (aB : MazurTransfer.Order13InverseParameterPublicCoordinates.OrdinaryLocalization R) =
      MazurTransfer.Order13InverseParameterPublicCoordinates.a R ∧
    (bB : MazurTransfer.Order13InverseParameterPublicCoordinates.OrdinaryLocalization R) =
      MazurTransfer.Order13InverseParameterPublicCoordinates.b R ∧
    Module.Finite (Polynomial R) (MazurTransfer.Order13InverseParameterPublicCoordinates.candidateAlgebra R) ∧
    (PrimeSpectrum.basicOpen sB ⊔ PrimeSpectrum.basicOpen
      ((1 - 2 * sB - 2 * bB - 4 * aB ^ 2) * (1 - 2 * sB - 2 * bB)) = ⊤) ∧
    ∃ κ : Localization.Away sB ≃ₐ[R]
        MazurTransfer.Order13InverseParameterPublicCoordinates.OrdinaryLocalization R,
      (∀ v : MazurTransfer.Order13InverseParameterPublicCoordinates.candidateAlgebra R,
        κ (algebraMap (MazurTransfer.Order13InverseParameterPublicCoordinates.candidateAlgebra R)
          (Localization.Away sB) v) = (v : MazurTransfer.Order13InverseParameterPublicCoordinates.OrdinaryLocalization R)) ∧
      ∃ χ : MazurTransfer.Order13InverseParameterPublicCoordinates.PatchRing R ≃ₐ[R]
          Localization.Away ((1 - 2 * sB - 2 * bB - 4 * aB ^ 2) * (1 - 2 * sB - 2 * bB)),
        χ (MazurTransfer.Order13InverseParameterPublicCoordinates.patchS R) =
          algebraMap (MazurTransfer.Order13InverseParameterPublicCoordinates.candidateAlgebra R) _ sB ∧
        χ (MazurTransfer.Order13InverseParameterPublicCoordinates.patchA R) =
          algebraMap (MazurTransfer.Order13InverseParameterPublicCoordinates.candidateAlgebra R) _ aB ∧
        χ (MazurTransfer.Order13InverseParameterPublicCoordinates.patchB R) =
          algebraMap (MazurTransfer.Order13InverseParameterPublicCoordinates.candidateAlgebra R) _ bB
 := by
  exact InverseParameterChartComparisonLibrary.inverseChartWitnesses R h104

#print axioms solution
