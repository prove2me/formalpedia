-- Prove2me | solution 1 for MazurTransfer.Order13InfinityLocalParameter.w_add_constant_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T11:32:41.718947+00:00
-- url     : https://prove2.me/submissions/d913ba17-f9ed-409c-994e-4069c06caa2f

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: the conjugate infinity coordinate factor is a unit when 2 is nonzero.
Named downstream consumer: the actual reciprocal local uniformizer and Pell orders. -/
import Definitions.Def_MazurTransfer_Order13InfinityLocalRingCoordinates
noncomputable section
universe u
open Polynomial MazurTransfer
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13IntegralSections Order13InfinityEvaluationKernel Order13InfinityLocalParameter
variable (K : Type u) [Field K] (a : K) (ha : a ^ 2 = 1)
namespace MazurTransfer.InfinityLocalParameterUnitHelpers20261017
variable (R : Type u) [CommRing R]
theorem reciprocalInfinityEvaluation_w (a : R) (ha : a ^ 2 = 1) :
    reciprocalInfinityEvaluation R a ha (wCoordinate R) = a := by
  simp [reciprocalInfinityEvaluation, InverseParameterChartComparisonLibrary.MazurTransfer.Order13IntegralSections.reciprocalInfinityEvaluation, wCoordinate, AdjoinRoot.lift_root]
end MazurTransfer.InfinityLocalParameterUnitHelpers20261017
theorem solution (h2 : (2 : K) ≠ 0) :
    IsUnit (w K a ha + constant K a ha) := by
  dsimp [w, constant]
  rw [← map_add]
  apply (IsLocalization.AtPrime.isUnit_to_map_iff (LocalRing K a ha)
    (infinityIdeal K a ha) _).mpr
  change evaluation K a ha (wCoordinate K + algebraMap K (ReciprocalRing K) a) ≠ 0
  have hconst := RingHom.congr_fun
    (Order13IntegralSections.reciprocalInfinityEvaluation_comp_algebraMap K a ha) a
  change evaluation K a ha (algebraMap K (ReciprocalRing K) a) = a at hconst
  have hw : evaluation K a ha (wCoordinate K) = a :=
    MazurTransfer.InfinityLocalParameterUnitHelpers20261017.reciprocalInfinityEvaluation_w K a ha
  rw [map_add, hw, hconst, ← two_mul]
  apply mul_ne_zero h2
  intro hz
  have h := ha
  rw [hz, zero_pow (by decide)] at h
  exact zero_ne_one h
#print axioms solution
