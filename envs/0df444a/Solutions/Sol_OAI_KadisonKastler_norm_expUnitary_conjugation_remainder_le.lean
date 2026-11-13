-- Prove2me | solution 1 for OAI.KadisonKastler.norm_expUnitary_conjugation_remainder_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:52:16.973453+00:00
-- url     : https://prove2.me/submissions/cf949a0e-4016-47b2-b476-9325515017f4

import Mathlib
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K015

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Basic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# The concrete Kadison–Kastler distance

The distance is the operator-norm Hausdorff distance between the closed unit
balls of two concrete, unital von Neumann algebras.  All Hilbert spaces are
allowed, including the zero space. The elementary estimates belong to §2 of
*Universal strong Kadison–Kastler stability* (2026).
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The elementary displacement estimate used at every matrix level in §2. -/
theorem norm_unitaryConj_sub_le (v : unitary (H →L[ℂ] H)) (x : H →L[ℂ] H) :
    ‖unitaryConj v x - x‖ ≤ 2 * ‖(v : H →L[ℂ] H) - 1‖ * ‖x‖ := by
  have hid : unitaryConj v x - x =
      (((v : H →L[ℂ] H) - 1) * x) * star (v : H →L[ℂ] H) +
        x * (star (v : H →L[ℂ] H) - 1) := by
    dsimp [unitaryConj]
    noncomm_ring
  have hstar : ‖star (v : H →L[ℂ] H) - 1‖ = ‖(v : H →L[ℂ] H) - 1‖ := by
    simpa only [star_sub, star_one] using norm_star ((v : H →L[ℂ] H) - 1)
  calc
    ‖unitaryConj v x - x‖ ≤
        ‖(((v : H →L[ℂ] H) - 1) * x) * star (v : H →L[ℂ] H)‖ +
          ‖x * (star (v : H →L[ℂ] H) - 1)‖ := hid ▸ norm_add_le _ _
    _ = ‖((v : H →L[ℂ] H) - 1) * x‖ +
          ‖x * (star (v : H →L[ℂ] H) - 1)‖ := by
      rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary]
    _ ≤ ‖(v : H →L[ℂ] H) - 1‖ * ‖x‖ +
          ‖x‖ * ‖star (v : H →L[ℂ] H) - 1‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖(v : H →L[ℂ] H) - 1‖ * ‖x‖ := by rw [hstar]; ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UnitaryExponentialBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A quantitative exponential bound for the normalizer path argument -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem exponentialPath_deriv (h : selfAdjoint (H →L[ℂ] H)) (t : ℝ) :
    HasDerivAt (fun s => (exponentialPath h s : H →L[ℂ] H))
      ((exponentialPath h t : H →L[ℂ] H) * (Complex.I • (h : H →L[ℂ] H))) t := by
  have he (s : ℝ) : (exponentialPath h s : H →L[ℂ] H) =
      NormedSpace.exp (s • (Complex.I • (h : H →L[ℂ] H))) := by
    change NormedSpace.exp (Complex.I • (s • (h : H →L[ℂ] H))) = _
    rw [smul_comm Complex.I s]
  simp_rw [he]
  exact hasDerivAt_exp_smul_const (Complex.I • (h : H →L[ℂ] H)) t

private theorem exponentialPath_deriv_left (h : selfAdjoint (H →L[ℂ] H)) (t : ℝ) :
    HasDerivAt (fun s => (exponentialPath h s : H →L[ℂ] H))
      ((Complex.I • (h : H →L[ℂ] H)) * (exponentialPath h t : H →L[ℂ] H)) t := by
  have he (s : ℝ) : (exponentialPath h s : H →L[ℂ] H) =
      NormedSpace.exp (s • (Complex.I • (h : H →L[ℂ] H))) := by
    change NormedSpace.exp (Complex.I • (s • (h : H →L[ℂ] H))) = _
    rw [smul_comm Complex.I s]
  simp_rw [he]
  exact hasDerivAt_exp_smul_const' (Complex.I • (h : H →L[ℂ] H)) t

theorem norm_expUnitary_sub_expUnitary_le (h k : selfAdjoint (H →L[ℂ] H)) :
    ‖(selfAdjoint.expUnitary h : H →L[ℂ] H) - selfAdjoint.expUnitary k‖ ≤
      ‖(h : H →L[ℂ] H) - k‖ := by
  let f (t : ℝ) := (exponentialPath h t : H →L[ℂ] H) * exponentialPath k (1 - t)
  let f' (t : ℝ) := (exponentialPath h t : H →L[ℂ] H) *
    (Complex.I • ((h : H →L[ℂ] H) - k)) * exponentialPath k (1 - t)
  have hf (t : ℝ) : HasDerivAt f (f' t) t := by
    have hk := (exponentialPath_deriv_left k (1 - t)).scomp t
      ((hasDerivAt_id t).const_sub (1 : ℝ))
    have hd := (exponentialPath_deriv h t).mul hk
    refine hd.congr_deriv ?_
    simp only [f', Function.comp_apply, one_smul, neg_smul, smul_sub]
    noncomm_ring
  have hn (t : ℝ) : ‖f' t‖ ≤ ‖(h : H →L[ℂ] H) - k‖ := by
    dsimp [f']
    rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
      norm_smul, Complex.norm_I, one_mul]
  have hb := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hf t).hasDerivWithinAt) (fun t _ => hn t)
  have hzero (a : selfAdjoint (H →L[ℂ] H)) :
      (exponentialPath a 0 : H →L[ℂ] H) = 1 := by
    change NormedSpace.exp (Complex.I • ((0 : ℝ) • (a : H →L[ℂ] H))) = 1
    rw [zero_smul, smul_zero, NormedSpace.exp_zero]
  have hone (a : selfAdjoint (H →L[ℂ] H)) :
      exponentialPath a 1 = selfAdjoint.expUnitary a := by
    apply Subtype.ext
    change NormedSpace.exp (Complex.I • ((1 : ℝ) • (a : H →L[ℂ] H))) = _
    rw [one_smul]
    rfl
  simpa only [f, sub_self, sub_zero, hzero, hone, one_mul, mul_one] using hb

private theorem exponentialPath_zero (h : selfAdjoint (H →L[ℂ] H)) :
    exponentialPath h 0 = 1 := by
  apply Subtype.ext
  change NormedSpace.exp (Complex.I • ((0 : ℝ) • (h : H →L[ℂ] H))) = 1
  rw [zero_smul, smul_zero, NormedSpace.exp_zero]

private theorem exponentialPath_one (h : selfAdjoint (H →L[ℂ] H)) :
    exponentialPath h 1 = selfAdjoint.expUnitary h := by
  apply Subtype.ext
  change NormedSpace.exp (Complex.I • ((1 : ℝ) • (h : H →L[ℂ] H))) = _
  rw [one_smul]
  rfl

private theorem exponentialPath_sub_one_le (h : selfAdjoint (H →L[ℂ] H)) (t : ℝ) :
    ‖(exponentialPath h t : H →L[ℂ] H) - 1‖ ≤ |t| * ‖(h : H →L[ℂ] H)‖ := by
  have hb := norm_expUnitary_sub_expUnitary_le (t • h) 0
  simpa only [selfAdjoint.expUnitary_zero, OneMemClass.coe_one, ZeroMemClass.coe_zero,
    sub_zero, selfAdjoint.val_smul, norm_smul, Real.norm_eq_abs, exponentialPath] using hb

private theorem exponentialGenerator_star (h : selfAdjoint (H →L[ℂ] H)) :
    star (exponentialGenerator h) = -exponentialGenerator h := by
  rw [exponentialGenerator, star_smul, h.property.star_eq]
  change (starRingEnd ℂ) Complex.I • (h : H →L[ℂ] H) = _
  rw [Complex.conj_I, neg_smul]

private theorem exponentialGenerator_norm (h : selfAdjoint (H →L[ℂ] H)) :
    ‖exponentialGenerator h‖ = ‖(h : H →L[ℂ] H)‖ := by
  rw [exponentialGenerator, norm_smul, Complex.norm_I, one_mul]

private theorem conjugationPath_deriv (h : selfAdjoint (H →L[ℂ] H))
    (x : H →L[ℂ] H) (t : ℝ) :
    HasDerivAt (conjugationPath h x)
      (exponentialGenerator h * conjugationPath h x t -
        conjugationPath h x t * exponentialGenerator h) t := by
  have hd := ((exponentialPath_deriv_left h t).mul_const x).mul
    (exponentialPath_deriv_left h t).star
  refine hd.congr_deriv ?_
  symm
  · change exponentialGenerator h * ((exponentialPath h t : H →L[ℂ] H) * x *
      star (exponentialPath h t : H →L[ℂ] H)) -
      ((exponentialPath h t : H →L[ℂ] H) * x *
      star (exponentialPath h t : H →L[ℂ] H)) * exponentialGenerator h = _
    change _ = (exponentialGenerator h * (exponentialPath h t : H →L[ℂ] H) * x) *
      star (exponentialPath h t : H →L[ℂ] H) +
      ((exponentialPath h t : H →L[ℂ] H) * x) *
        star (exponentialGenerator h * (exponentialPath h t : H →L[ℂ] H))
    rw [star_mul, exponentialGenerator_star]
    noncomm_ring

private theorem conjugationPath_sub_le (h : selfAdjoint (H →L[ℂ] H))
    (x : H →L[ℂ] H) (t : ℝ) :
    ‖conjugationPath h x t - x‖ ≤ 2 * |t| * ‖(h : H →L[ℂ] H)‖ * ‖x‖ := by
  calc
    _ ≤ 2 * ‖(exponentialPath h t : H →L[ℂ] H) - 1‖ * ‖x‖ :=
      norm_unitaryConj_sub_le _ _
    _ ≤ 2 * (|t| * ‖(h : H →L[ℂ] H)‖) * ‖x‖ := by
      gcongr
      exact exponentialPath_sub_one_le h t
    _ = _ := by ring

private theorem conjugationRemainder_deriv (h : selfAdjoint (H →L[ℂ] H))
    (x : H →L[ℂ] H) (t : ℝ) :
    HasDerivAt (conjugationRemainder h x) (conjugationRemainderDerivative h x t) t := by
  have hd := ((conjugationPath_deriv h x t).sub_const x).sub
    ((hasDerivAt_id t).smul_const (exponentialGenerator h * x - x * exponentialGenerator h))
  refine hd.congr_deriv ?_
  · dsimp [conjugationRemainderDerivative]
    simp only [one_smul]
    noncomm_ring

private theorem conjugationRemainderDerivative_norm_le (h : selfAdjoint (H →L[ℂ] H))
    (x : H →L[ℂ] H) (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    ‖conjugationRemainderDerivative h x t‖ ≤ 4 * ‖(h : H →L[ℂ] H)‖ ^ 2 * ‖x‖ := by
  have habs : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2.le
  calc
    _ ≤ ‖exponentialGenerator h‖ * ‖conjugationPath h x t - x‖ +
      ‖conjugationPath h x t - x‖ * ‖exponentialGenerator h‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ = 2 * ‖(h : H →L[ℂ] H)‖ * ‖conjugationPath h x t - x‖ := by
      rw [exponentialGenerator_norm]; ring
    _ ≤ 2 * ‖(h : H →L[ℂ] H)‖ * (2 * |t| * ‖(h : H →L[ℂ] H)‖ * ‖x‖) := by
      gcongr
      exact conjugationPath_sub_le h x t
    _ ≤ 2 * ‖(h : H →L[ℂ] H)‖ * (2 * 1 * ‖(h : H →L[ℂ] H)‖ * ‖x‖) := by gcongr
    _ = _ := by ring

/-- The first-order conjugation formula with a uniform quadratic remainder. -/
private theorem conjugationRemainder_norm_le
    (h : selfAdjoint (H →L[ℂ] H)) (x : H →L[ℂ] H) :
    ‖conjugationRemainder h x 1‖ ≤
        4 * ‖(h : H →L[ℂ] H)‖ ^ 2 * ‖x‖ := by
  have hb := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (conjugationRemainder_deriv h x t).hasDerivWithinAt)
    (conjugationRemainderDerivative_norm_le h x)
  simpa only [conjugationRemainder, conjugationPath, exponentialPath_zero,
    unitaryConj_one, zero_smul, sub_self, sub_zero] using hb

/-- First-order conjugation by an exponential, with a quadratic norm remainder. -/
theorem norm_expUnitary_conjugation_remainder_le_oai
    (h : selfAdjoint (H →L[ℂ] H)) (x : H →L[ℂ] H) :
    ‖unitaryConj (H := H) (selfAdjoint.expUnitary h) x - x -
      (Complex.I • ((h : H →L[ℂ] H) * x - x * (h : H →L[ℂ] H)) : H →L[ℂ] H)‖ ≤
        4 * ‖(h : H →L[ℂ] H)‖ ^ 2 * ‖x‖ := by
  simpa only [conjugationRemainder, conjugationPath, exponentialPath_one,
    one_smul, exponentialGenerator, smul_sub, smul_mul_assoc, mul_smul_comm]
    using conjugationRemainder_norm_le h x

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.norm_expUnitary_conjugation_remainder_le_oai.{u_1} := @OAI.KadisonKastler.norm_expUnitary_conjugation_remainder_le_oai.{u_1}
