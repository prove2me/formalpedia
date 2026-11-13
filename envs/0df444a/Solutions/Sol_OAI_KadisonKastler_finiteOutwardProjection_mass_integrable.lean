-- Prove2me | solution 1 for OAI.KadisonKastler.finiteOutwardProjection_mass_integrable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:49:54.137196+00:00
-- url     : https://prove2.me/submissions/64d3f20a-5732-46df-b0c2-5ab73bb23be9

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
-- module Solutions.OAIQ075_KS.KadisonKastler_ThresholdCutIntegral
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SignedSquareThreshold
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

theorem outward_threshold_coefficient (x t : ℝ) :
    (if t < 0 then 1-(if t < signedSquare x then 1 else 0 : ℝ)
      else (if t < signedSquare x then 1 else 0 : ℝ)) =
        thresholdDifference (signedSquare x) 0 t ^ 2 := by
  by_cases ht : t < 0 <;> by_cases hx : t < signedSquare x <;>
    simp [thresholdDifference,ht,hx]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_OutwardSpectralCuts
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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
theorem finiteOutwardProjection_sum (P : ι → H →L[ℂ] H)
    (htotal : ∑ i, P i=1) (c : ι → ℝ) (t : ℝ) :
    finiteOutwardProjection P c t =
      ∑ i, ((thresholdDifference (signedSquare (c i)) 0 t ^ 2 : ℝ) : ℂ) • P i := by
  simp_rw [← outward_threshold_coefficient]
  by_cases ht : t < 0
  · simp only [finiteOutwardProjection,ht,ite_true, if_true,finiteThresholdProjection,Function.comp_apply]
    rw [← htotal,← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    rw [Complex.ofReal_sub,Complex.ofReal_one,sub_smul,one_smul]
  · simp only [finiteOutwardProjection,ht,ite_false, if_false,finiteThresholdProjection,Function.comp_apply]

theorem finiteSpectralSum_norm_sq (P : ι → H →L[ℂ] H)
    (hP : ∀ i, IsStarProjection (P i))
    (ho : ∀ i j, i ≠ j → P i*P j=0) (c : ι → ℝ) (ξ : H) :
    ‖(∑ i, (c i : ℂ) • P i) ξ‖^2 = ∑ i, c i^2*‖P i ξ‖^2 := by
  have hp := orthogonal_projection_vectors P (fun i => (hP i).isSelfAdjoint) ho ξ
  have he := norm_sum_sq_of_pairwise_orthogonal univ
    (fun i => (c i : ℂ) • P i ξ) (by
      intro i _ j _ hij
      rw [inner_smul_left,inner_smul_right,hp hij,mul_zero,mul_zero])
  simpa only [_root_.sum_apply,smul_apply,norm_smul,mul_pow,Complex.norm_real,
    Real.norm_eq_abs,sq_abs] using he

theorem finiteOutwardProjection_mass (P : ι → H →L[ℂ] H)
    (hP : ∀ i, IsStarProjection (P i))
    (ho : ∀ i j, i ≠ j → P i*P j=0) (htotal : ∑ i, P i=1)
    (c : ι → ℝ) (t : ℝ) (ξ : H) :
    ‖finiteOutwardProjection P c t ξ‖^2 =
      ∑ i, thresholdDifference (signedSquare (c i)) 0 t ^ 2*‖P i ξ‖^2 := by
  rw [finiteOutwardProjection_sum P htotal c t,finiteSpectralSum_norm_sq P hP ho]
  apply sum_congr rfl
  intro i _
  by_cases hx : t < signedSquare (c i) <;> by_cases ht : t < 0 <;>
    simp [thresholdDifference,hx,ht]

theorem finiteOutwardProjection_mass_integrable_oai (P : ι → H →L[ℂ] H)
    (hP : ∀ i, IsStarProjection (P i))
    (ho : ∀ i j, i ≠ j → P i*P j=0) (htotal : ∑ i, P i=1)
    (c : ι → ℝ) (ξ : H) : Integrable (fun t => ‖finiteOutwardProjection P c t ξ‖^2) := by
  simp_rw [finiteOutwardProjection_mass P hP ho htotal c]
  exact integrable_finsetSum _ (fun i _ =>
    (thresholdDifference_sq_integrable (signedSquare (c i)) 0).mul_const _)

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.finiteOutwardProjection_mass_integrable_oai.{u_1, u_2} := @OAI.KadisonKastler.finiteOutwardProjection_mass_integrable_oai.{u_1, u_2}
