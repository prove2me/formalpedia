-- Prove2me | solution 1 for OAI.KadisonKastler.finiteOutwardProjection_integral_lower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:47:59.708458+00:00
-- url     : https://prove2.me/submissions/68eda193-4bdf-4579-a38e-229f423f7b5e

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Matrix.Composition
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Instances.Complex
import Definitions.Def_Q260K007

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SupportBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Square sums over orthogonal supports

These are the Hilbert-space estimates converting bounds through each
diagonal label into the uniform coefficient-column drift in §3.
-/

namespace KadisonKastler

open Finset

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem norm_sum_sq_of_pairwise_orthogonal {ι : Type*} (s : Finset ι) (v : ι → H)
    (hv : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℂ (v i) (v j) = 0) :
    ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have horth : inner ℂ (v a) (∑ i ∈ s, v i) = 0 := by
      rw [inner_sum]
      apply sum_eq_zero
      intro i hi
      exact hv a (by simp) i (by simp [hi]) (by aesop)
    rw [sum_insert ha, norm_add_sq (𝕜 := ℂ), horth]
    rw [ih (by intro i hi j hj hij; exact hv i (by simp [hi]) j (by simp [hj]) hij),
      sum_insert ha]
    simp only [map_zero, mul_zero, add_zero]

variable [CompleteSpace H]

theorem orthogonal_projection_vectors {ι : Type*} (P : ι → H →L[ℂ] H)
    (hself : ∀ i, IsSelfAdjoint (P i))
    (horth : ∀ i j, i ≠ j → P i * P j = 0) (x : H) :
    Pairwise (fun i j => inner ℂ (P i x) (P j x) = 0) := by
  intro i j hij
  have hstar : (P i).adjoint = P i := (hself i).star_eq
  rw [← ContinuousLinearMap.adjoint_inner_right, hstar]
  have hz : P i (P j x) = 0 := by
    change (P i * P j) x = 0
    rw [horth i j hij]
    rfl
  rw [hz, inner_zero_right]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_JointProjectionEnergy
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Vector energy in two commuting finite spectral partitions -/

namespace KadisonKastler

open Finset
open scoped BigOperators

noncomputable section

variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [Fintype κ]

omit [CompleteSpace H] [Fintype ι] [Fintype κ] in
theorem jointProjection_orthogonal
    (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
    (hP : ∀ i k, i ≠ k → P i * P k = 0)
    (hQ : ∀ j l, j ≠ l → Q j * Q l = 0)
    (hc : ∀ i j, Commute (P i) (Q j)) :
    ∀ a b : ι × κ, a ≠ b → (P a.1 * Q a.2) * (P b.1 * Q b.2) = 0 := by
  intro a b hab
  have he : (P a.1 * Q a.2) * (P b.1 * Q b.2) =
      (P a.1 * P b.1) * (Q a.2 * Q b.2) := by
    rw [mul_assoc,← mul_assoc (Q a.2),(hc b.1 a.2).eq.symm]
    simp only [mul_assoc]
  rw [he]
  by_cases hi : a.1 = b.1
  · have hj : a.2 ≠ b.2 := fun hj => hab (Prod.ext hi hj)
    rw [hQ _ _ hj,mul_zero]
  · rw [hP _ _ hi,zero_mul]

omit [CompleteSpace H] in
theorem jointProjection_weighted_sum
    (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
    (hP : ∑ i, P i = 1) (hQ : ∑ j, Q j = 1)
    (c : ι → ℂ) (d : κ → ℂ) :
    (∑ a : ι × κ, (c a.1-d a.2) • (P a.1 * Q a.2)) =
      (∑ i, c i • P i) - (∑ j, d j • Q j) := by
  simp_rw [sub_smul]
  rw [Finset.sum_sub_distrib,Fintype.sum_prod_type,Fintype.sum_prod_type]
  have hl : (∑ i, ∑ j, c i • (P i * Q j)) = ∑ i, c i • P i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.smul_sum,← Finset.mul_sum,hQ,mul_one]
  have hr : (∑ i, ∑ j, d j • (P i * Q j)) = ∑ j, d j • Q j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.smul_sum,← Finset.sum_mul,hP,one_mul]
  rw [hl,hr]

theorem norm_jointProjection_weighted_sum_sq
    (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
    (hP : ∀ i, IsStarProjection (P i)) (hQ : ∀ j, IsStarProjection (Q j))
    (hPo : ∀ i k, i ≠ k → P i * P k = 0)
    (hQo : ∀ j l, j ≠ l → Q j * Q l = 0)
    (hc : ∀ i j, Commute (P i) (Q j)) (c : ι × κ → ℂ) (ξ : H) :
    ‖(∑ a : ι × κ, c a • (P a.1 * Q a.2)) ξ‖ ^ 2 =
      ∑ a : ι × κ, ‖c a‖ ^ 2 * ‖(P a.1 * Q a.2) ξ‖ ^ 2 := by
  classical
  have ho := orthogonal_projection_vectors (fun a : ι × κ => P a.1 * Q a.2)
    (fun a => ((hP a.1).mul (hQ a.2) (hc a.1 a.2)).isSelfAdjoint)
    (jointProjection_orthogonal P Q hPo hQo hc) ξ
  have horth : ∀ a ∈ (univ : Finset (ι × κ)), ∀ b ∈ (univ : Finset (ι × κ)),
      a ≠ b → inner ℂ (c a • (P a.1 * Q a.2) ξ) (c b • (P b.1 * Q b.2) ξ) = 0 := by
    intro a _ b _ hab
    rw [inner_smul_left,inner_smul_right,ho hab,mul_zero,mul_zero]
  have he := norm_sum_sq_of_pairwise_orthogonal univ
    (fun a : ι × κ => c a • (P a.1 * Q a.2) ξ) horth
  simpa only [_root_.sum_apply,smul_apply,norm_smul,mul_pow] using he

theorem jointProjection_gap_energy
    (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
    (hP : ∀ i, IsStarProjection (P i)) (hQ : ∀ j, IsStarProjection (Q j))
    (hPo : ∀ i k, i ≠ k → P i * P k = 0)
    (hQo : ∀ j l, j ≠ l → Q j * Q l = 0)
    (hPt : ∑ i, P i = 1) (hQt : ∑ j, Q j = 1)
    (hc : ∀ i j, Commute (P i) (Q j)) (c : ι → ℂ) (d : κ → ℂ) (ξ : H) :
    ‖((∑ i, c i • P i) - (∑ j, d j • Q j)) ξ‖ ^ 2 =
      ∑ a : ι × κ, ‖c a.1-d a.2‖ ^ 2 * ‖(P a.1 * Q a.2) ξ‖ ^ 2 := by
  rw [← jointProjection_weighted_sum P Q hPt hQt c d]
  exact norm_jointProjection_weighted_sum_sq P Q hP hQ hPo hQo hc _ ξ

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ThresholdCutIntegral
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Averaging finite spectral threshold cuts

Two spectral values are separated by a threshold on an interval of
length equal to their distance. Finite weighted sums give the exact
average cut energy and its Cauchy--Schwarz bound.
-/

namespace KadisonKastler

open MeasureTheory
open scoped BigOperators

noncomputable section

theorem thresholdDifference_sq (x y t : ℝ) :
    thresholdDifference x y t ^ 2 =
      (Set.Ico (min x y) (max x y)).indicator (fun _ => (1 : ℝ)) t := by
  by_cases hxy : x ≤ y
  · rw [min_eq_left hxy,max_eq_right hxy]
    by_cases htx : t < x
    · have hty : t < y := htx.trans_le hxy
      simp [thresholdDifference,htx,hty,Set.mem_Ico,not_le.mpr htx]
    · by_cases hty : t < y
      · simp [thresholdDifference,htx,hty,Set.mem_Ico,le_of_not_gt htx]
      · simp [thresholdDifference,htx,hty,Set.mem_Ico]
  · have hyx : y ≤ x := le_of_not_ge hxy
    rw [min_eq_right hyx,max_eq_left hyx]
    by_cases hty : t < y
    · have htx : t < x := hty.trans_le hyx
      simp [thresholdDifference,htx,hty,Set.mem_Ico,not_le.mpr hty]
    · by_cases htx : t < x
      · simp [thresholdDifference,htx,hty,Set.mem_Ico,le_of_not_gt hty]
      · simp [thresholdDifference,htx,hty,Set.mem_Ico]

theorem thresholdDifference_sq_integrable (x y : ℝ) :
    Integrable (fun t => thresholdDifference x y t ^ 2) := by
  simp_rw [thresholdDifference_sq]
  exact (integrable_indicator_iff measurableSet_Ico).mpr
    (integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))

theorem integral_thresholdDifference_sq (x y : ℝ) :
    (∫ t, thresholdDifference x y t ^ 2) = |x - y| := by
  simp_rw [thresholdDifference_sq]
  rw [integral_indicator_const (1 : ℝ) measurableSet_Ico]
  simp only [smul_eq_mul,mul_one,Measure.real,Real.volume_Ico,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (min_le_max))]
  exact (max_sub_min_eq_abs x y).trans (abs_sub_comm y x)

theorem integral_weighted_thresholdDifference_sq {ι : Type*} (s : Finset ι)
    (x y w : ι → ℝ) :
    (∫ t, ∑ i ∈ s, w i * thresholdDifference (x i) (y i) t ^ 2) =
      ∑ i ∈ s, w i * |x i - y i| := by
  rw [integral_finsetSum s (fun i _ => (thresholdDifference_sq_integrable (x i) (y i)).const_mul _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul,integral_thresholdDifference_sq]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteThresholdProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Projection-valued threshold cuts of finite spectral sums -/

namespace KadisonKastler

open Finset MeasureTheory
open scoped BigOperators

noncomputable section

variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [Fintype κ]

theorem finiteThresholdProjection_gap_energy
    (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
    (hP : ∀ i, IsStarProjection (P i)) (hQ : ∀ j, IsStarProjection (Q j))
    (hPo : ∀ i k, i ≠ k → P i * P k = 0)
    (hQo : ∀ j l, j ≠ l → Q j * Q l = 0)
    (hPt : ∑ i, P i = 1) (hQt : ∑ j, Q j = 1)
    (hc : ∀ i j, Commute (P i) (Q j)) (c : ι → ℝ) (d : κ → ℝ) (t : ℝ) (ξ : H) :
    ‖(finiteThresholdProjection P c t - finiteThresholdProjection Q d t) ξ‖ ^ 2 =
      ∑ a : ι × κ, ‖(P a.1 * Q a.2) ξ‖ ^ 2 *
        thresholdDifference (c a.1) (d a.2) t ^ 2 := by
  rw [finiteThresholdProjection,finiteThresholdProjection,
    jointProjection_gap_energy P Q hP hQ hPo hQo hPt hQt hc]
  apply Finset.sum_congr rfl
  intro a _
  have he : ‖((if t < c a.1 then 1 else 0 : ℝ) : ℂ) -
      ((if t < d a.2 then 1 else 0 : ℝ) : ℂ)‖ ^ 2 =
      thresholdDifference (c a.1) (d a.2) t ^ 2 := by
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    rfl
  rw [he,mul_comm]

theorem finiteThresholdProjection_integrated_energy
    (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
    (hP : ∀ i, IsStarProjection (P i)) (hQ : ∀ j, IsStarProjection (Q j))
    (hPo : ∀ i k, i ≠ k → P i * P k = 0)
    (hQo : ∀ j l, j ≠ l → Q j * Q l = 0)
    (hPt : ∑ i, P i = 1) (hQt : ∑ j, Q j = 1)
    (hc : ∀ i j, Commute (P i) (Q j)) (c : ι → ℝ) (d : κ → ℝ) (ξ : H) :
    (∫ t, ‖(finiteThresholdProjection P c t - finiteThresholdProjection Q d t) ξ‖ ^ 2) =
      ∑ a : ι × κ, ‖(P a.1 * Q a.2) ξ‖ ^ 2 * |c a.1-d a.2| := by
  simp_rw [finiteThresholdProjection_gap_energy P Q hP hQ hPo hQo hPt hQt hc]
  exact integral_weighted_thresholdDifference_sq univ _ _ _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteThresholdEstimate
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Upper and lower energy bounds for finite spectral threshold cuts -/

namespace KadisonKastler

open Finset MeasureTheory
open scoped BigOperators

noncomputable section

variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [Fintype κ]
  (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
  (hP : ∀ i, IsStarProjection (P i)) (hQ : ∀ j, IsStarProjection (Q j))
  (hPo : ∀ i k, i ≠ k → P i * P k = 0)
  (hQo : ∀ j l, j ≠ l → Q j * Q l = 0)
  (hPt : ∑ i, P i = 1) (hQt : ∑ j, Q j = 1)
  (hc : ∀ i j, Commute (P i) (Q j))

include hP hQ hPo hQo hPt hQt hc

theorem jointProjection_real_gap (c : ι → ℝ) (d : κ → ℝ) (ξ : H) :
    (∑ a : ι × κ, ‖(P a.1 * Q a.2) ξ‖ ^ 2 * (c a.1-d a.2) ^ 2) =
      ‖((∑ i, (c i : ℂ) • P i) - (∑ j, (d j : ℂ) • Q j)) ξ‖ ^ 2 := by
  have he := jointProjection_gap_energy P Q hP hQ hPo hQo hPt hQt hc
    (fun i => (c i : ℂ)) (fun j => (d j : ℂ)) ξ
  rw [he]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_comm]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SignedSquareThreshold
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Signed-square coordinates for spectral cuts

Passing from a spectral value x to x |x| absorbs the weight |t| in
Haagerup's spectral-cut integral. The estimates here are scalar.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

theorem sq_gap_le_signedSquare (x y : ℝ) :
    (x-y)^2 ≤ 2*|signedSquare x-signedSquare y| := by
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · simp only [signedSquare,abs_of_nonneg hx,abs_of_nonneg hy]
    rcases le_total x y with hxy | hyx
    · have hs : x*x-y*y ≤ 0 := by nlinarith
      rw [abs_of_nonpos hs]
      nlinarith [mul_nonneg (sub_nonneg.mpr hxy) hx,sq_nonneg (x-y)]
    · have hs : 0 ≤ x*x-y*y := by nlinarith
      rw [abs_of_nonneg hs]
      nlinarith [mul_nonneg (sub_nonneg.mpr hyx) hy,sq_nonneg (x-y)]
  · simp only [signedSquare,abs_of_nonneg hx,abs_of_nonpos hy]
    have hs : 0 ≤ x*x-y*(-y) := by nlinarith [sq_nonneg x,sq_nonneg y]
    rw [abs_of_nonneg hs]
    nlinarith [sq_nonneg (x+y)]
  · simp only [signedSquare,abs_of_nonpos hx,abs_of_nonneg hy]
    have hs : x*(-x)-y*y ≤ 0 := by nlinarith [sq_nonneg x,sq_nonneg y]
    rw [abs_of_nonpos hs]
    nlinarith [sq_nonneg (x+y)]
  · simp only [signedSquare,abs_of_nonpos hx,abs_of_nonpos hy]
    rcases le_total x y with hxy | hyx
    · have hs : x*(-x)-y*(-y) ≤ 0 := by nlinarith
      rw [abs_of_nonpos hs]
      nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (neg_nonneg.mpr hy),sq_nonneg (x-y)]
    · have hs : 0 ≤ x*(-x)-y*(-y) := by nlinarith
      rw [abs_of_nonneg hs]
      nlinarith [mul_nonneg (sub_nonneg.mpr hyx) (neg_nonneg.mpr hx),sq_nonneg (x-y)]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_OutwardSpectralCuts
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite outward spectral cuts

Negative thresholds take the lower spectral projection, positive thresholds
take the upper one. Signed-square coordinates make their integrated vector
mass equal to the squared norm of the original finite spectral sum.
-/

namespace KadisonKastler

open MeasureTheory Finset
open scoped BigOperators

noncomputable section

variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [Fintype κ]

omit [CompleteSpace H] in
theorem finiteOutwardProjection_gap_eq
    (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
    (c : ι → ℝ) (d : κ → ℝ) (t : ℝ) (ξ : H) :
    ‖(finiteOutwardProjection P c t-finiteOutwardProjection Q d t) ξ‖^2 =
      ‖(finiteThresholdProjection P (signedSquare ∘ c) t-
        finiteThresholdProjection Q (signedSquare ∘ d) t) ξ‖^2 := by
  by_cases ht : t < 0
  · simp only [finiteOutwardProjection,ht,ite_true, if_true]
    rw [show (1-finiteThresholdProjection P (signedSquare ∘ c) t)-
      (1-finiteThresholdProjection Q (signedSquare ∘ d) t)=
        -(finiteThresholdProjection P (signedSquare ∘ c) t-
          finiteThresholdProjection Q (signedSquare ∘ d) t) by abel]
    rw [neg_apply,norm_neg]
  · simp only [finiteOutwardProjection,ht,ite_false, if_false]

theorem finiteOutwardProjection_integral_gap
    (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
    (hP : ∀ i, IsStarProjection (P i)) (hQ : ∀ j, IsStarProjection (Q j))
    (hPo : ∀ i k, i ≠ k → P i*P k=0) (hQo : ∀ j l, j ≠ l → Q j*Q l=0)
    (hPt : ∑ i, P i=1) (hQt : ∑ j, Q j=1) (hc : ∀ i j, Commute (P i) (Q j))
    (c : ι → ℝ) (d : κ → ℝ) (ξ : H) :
    (∫ t, ‖(finiteOutwardProjection P c t-finiteOutwardProjection Q d t) ξ‖^2)=
      ∑ a : ι × κ, ‖(P a.1*Q a.2) ξ‖^2*
        |signedSquare (c a.1)-signedSquare (d a.2)| := by
  simp_rw [finiteOutwardProjection_gap_eq]
  exact finiteThresholdProjection_integrated_energy P Q hP hQ hPo hQo hPt hQt hc _ _ ξ

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_OutwardCutEnergy
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Norm-free energy bounds for outward spectral cuts

The upper estimate uses only the two vector norms and their displacement.
The lower estimate recovers half of the original displacement energy.
-/

namespace KadisonKastler

open MeasureTheory Finset
open scoped BigOperators

noncomputable section

variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [Fintype κ]
  (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
  (hP : ∀ i, IsStarProjection (P i)) (hQ : ∀ j, IsStarProjection (Q j))
  (hPo : ∀ i k, i ≠ k → P i*P k=0) (hQo : ∀ j l, j ≠ l → Q j*Q l=0)
  (hPt : ∑ i, P i=1) (hQt : ∑ j, Q j=1) (hc : ∀ i j, Commute (P i) (Q j))

include hP hQ hPo hQo hPt hQt hc

theorem finiteOutwardProjection_integral_lower_oai (c : ι → ℝ) (d : κ → ℝ) (ξ : H) :
    ‖((∑ i, (c i : ℂ) • P i)-(∑ j, (d j : ℂ) • Q j)) ξ‖^2 ≤
      2*(∫ t, ‖(finiteOutwardProjection P c t-finiteOutwardProjection Q d t) ξ‖^2) := by
  rw [finiteOutwardProjection_integral_gap P Q hP hQ hPo hQo hPt hQt hc,
    ← jointProjection_real_gap P Q hP hQ hPo hQo hPt hQt hc,mul_sum]
  apply sum_le_sum
  intro a _
  nlinarith [mul_le_mul_of_nonneg_left (sq_gap_le_signedSquare (c a.1) (d a.2))
    (sq_nonneg ‖(P a.1*Q a.2) ξ‖)]

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.KadisonKastler.finiteOutwardProjection_integral_lower_oai.{u_1, u_2, u_3} := @OAI.KadisonKastler.finiteOutwardProjection_integral_lower_oai.{u_1, u_2, u_3}
