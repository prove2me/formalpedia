-- Prove2me | solution 1 for MazurTransfer.Order13InfinityEvaluationKernel.evaluation_kernel
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T11:17:09.511202+00:00
-- url     : https://prove2.me/submissions/a16a3eba-f690-46dc-bca0-41e27fad3f3e

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: the exact two-generator kernel at either literal infinity point.
Named downstream consumers: the actual infinity local parameter and Pell divisor. -/
import Definitions.Def_MazurTransfer_Order13InfinityEvaluationMaps
noncomputable section
universe u
open Polynomial
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13IntegralSections MazurTransfer.Order13InfinityEvaluationKernel
variable (R : Type u) [CommRing R] (a : R) (ha : a ^ 2 = 1)
namespace MazurTransfer.InfinityEvaluationKernelHelpers20261017
theorem reciprocalInfinityEvaluation_z (a : R) (ha : a ^ 2 = 1) :
    reciprocalInfinityEvaluation R a ha (zCoordinate R) = 0 := by
  simp [reciprocalInfinityEvaluation, InverseParameterChartComparisonLibrary.MazurTransfer.Order13IntegralSections.reciprocalInfinityEvaluation, zCoordinate, AdjoinRoot.lift_of]

theorem reciprocalInfinityEvaluation_w (a : R) (ha : a ^ 2 = 1) :
    reciprocalInfinityEvaluation R a ha (wCoordinate R) = a := by
  simp [reciprocalInfinityEvaluation, InverseParameterChartComparisonLibrary.MazurTransfer.Order13IntegralSections.reciprocalInfinityEvaluation, wCoordinate, AdjoinRoot.lift_root]
theorem quotientMap_factorization : quotientMap R a =
    (Algebra.ofId R (ReciprocalRing R ⧸ sectionIdeal R a)).comp
      (evaluationAlgHom R a ha) := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change quotientMap R a (zCoordinate R) =
      algebraMap R (ReciprocalRing R ⧸ sectionIdeal R a)
        (reciprocalInfinityEvaluation R a ha (zCoordinate R))
    rw [quotientMap_z, reciprocalInfinityEvaluation_z, map_zero]
  · change quotientMap R a (wCoordinate R) =
      algebraMap R (ReciprocalRing R ⧸ sectionIdeal R a)
        (reciprocalInfinityEvaluation R a ha (wCoordinate R))
    rw [quotientMap_w, reciprocalInfinityEvaluation_w]

theorem sectionIdeal_le_kernel : sectionIdeal R a ≤ RingHom.ker (evaluation R a ha) := by
  apply Ideal.span_le.mpr
  intro b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
  rcases hb with rfl | rfl
  · exact reciprocalInfinityEvaluation_z R a ha
  · change evaluation R a ha (wCoordinate R - algebraMap R (ReciprocalRing R) a) = 0
    rw [map_sub]
    change reciprocalInfinityEvaluation R a ha (wCoordinate R) -
      reciprocalInfinityEvaluation R a ha (algebraMap R (ReciprocalRing R) a) = 0
    have h := RingHom.congr_fun (reciprocalInfinityEvaluation_comp_algebraMap R a ha) a
    change reciprocalInfinityEvaluation R a ha (algebraMap R (ReciprocalRing R) a) = a at h
    rw [reciprocalInfinityEvaluation_w, h]
    exact sub_self a
end MazurTransfer.InfinityEvaluationKernelHelpers20261017
open MazurTransfer.InfinityEvaluationKernelHelpers20261017
theorem solution : RingHom.ker (evaluation R a ha) = sectionIdeal R a := by
  apply le_antisymm
  · intro b hb
    change evaluation R a ha b = 0 at hb
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    change quotientMap R a b = 0
    have h := DFunLike.congr_fun (quotientMap_factorization R a ha) b
    change quotientMap R a b =
      algebraMap R (ReciprocalRing R ⧸ sectionIdeal R a) (evaluation R a ha b) at h
    rw [hb, map_zero] at h
    exact h
  · exact sectionIdeal_le_kernel R a ha
#print axioms solution
