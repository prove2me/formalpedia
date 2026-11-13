-- Prove2me | solution 1 for OAI.KadisonKastler.complete_bound_of_pointwise_weak_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:52:10.132232+00:00
-- url     : https://prove2.me/submissions/1893a34e-841e-4117-8795-8ef350a2b8d6

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Matrix.Composition
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Q260K015

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RectangularHilbert
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.finiteDiagonalMap_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.operatorEntry_hilbertMatrix _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Rectangular operator matrices on finite Hilbert sums -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {m n : Type*} [Fintype m] [Fintype n]

attribute [local instance] OAI.KadisonKastler.rectangularHilbertOperatorStarOrder
omit [CompleteSpace H] [InnerProductSpace ℂ H] in
theorem norm_hilbertRestrictRight_le (x : Generator.FiniteHilbert (m ⊕ n) H) :
    ‖hilbertRestrictRight x‖ ≤ ‖x‖ := by
  simp only [PiLp.norm_eq_of_L2, hilbertRestrictRight,
    Fintype.sum_sum_type]
  apply Real.sqrt_le_sqrt
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem hilbertMatrix_rectangularCorner [DecidableEq m] [DecidableEq n]
    (M : CStarMatrix m n (H →L[ℂ] H)) (x : Generator.FiniteHilbert (m ⊕ n) H) :
    hilbertMatrix (rectangularCorner M) x =
      hilbertExtendLeft (rectangularHilbertMatrix M (hilbertRestrictRight x)) := by
  ext i
  rcases i with i | i <;>
    simp [hilbertMatrix_apply, rectangularCorner, rectangularHilbertMatrix_apply,
      hilbertExtendLeft, hilbertRestrictRight, Fintype.sum_sum_type]

attribute [local instance] OAI.KadisonKastler.rectangularHilbertOperatorOrder
/-- The rectangular C⋆-matrix norm is its actual Hilbert-space operator norm. -/
theorem norm_rectangularHilbertMatrix (M : CStarMatrix m n (H →L[ℂ] H)) :
    ‖rectangularHilbertMatrix M‖ = ‖M‖ := by
  classical
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have h := (hilbertMatrix (rectangularCorner M)).le_opNorm
      (hilbertExtendRight (m := m) x)
    rw [hilbertMatrix_rectangularCorner, norm_hilbertExtendLeft, norm_hilbertMatrix,
      norm_rectangularCorner, norm_hilbertExtendRight] at h
    simpa only [hilbertRestrictRight, hilbertExtendRight, Sum.elim_inr,
      WithLp.toLp_ofLp] using h
  · rw [← norm_rectangularCorner M, ← norm_hilbertMatrix]
    apply (hilbertMatrix (rectangularCorner M)).opNorm_le_bound
      (norm_nonneg (rectangularHilbertMatrix M))
    intro x
    rw [hilbertMatrix_rectangularCorner, norm_hilbertExtendLeft]
    exact (rectangularHilbertMatrix M).le_opNorm (hilbertRestrictRight x) |>.trans
      (mul_le_mul_of_nonneg_left (norm_hilbertRestrictRight_le x) (norm_nonneg _))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakCPLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Positivity and norm bounds in pointwise weak operator limits

These lemmas retain the complete positivity of the maps obtained from
finite Hilbert-space tests. No normality of the limiting map is needed.
-/

namespace KadisonKastler

open Filter
open scoped Topology CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} {l : Filter ι} [l.NeBot]

omit [CompleteSpace H] in
/-- A uniform operator norm bound survives a weak coefficient limit. -/
theorem norm_le_of_weak_limit {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] (T : ι → H →L[ℂ] K) (S : H →L[ℂ] K)
    {C : ℝ} (hC : 0 ≤ C) (hT : ∀ i, ‖T i‖ ≤ C)
    (ht : ∀ x y, Tendsto (fun i => inner ℂ y (T i x)) l (𝓝 (inner ℂ y (S x)))) :
    ‖S‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le hC
  intro x y hx hy
  change (inner ℂ (S x) y).re ≤ C
  have hb (i : ι) : (inner ℂ y (T i x)).re ≤ C := by
    calc
      _ ≤ ‖inner ℂ y (T i x)‖ := Complex.re_le_norm _
      _ ≤ ‖y‖ * ‖T i x‖ := norm_inner_le_norm _ _
      _ ≤ ‖y‖ * (C * ‖x‖) := mul_le_mul_of_nonneg_left
        ((T i).le_of_opNorm_le (hT i) x) (norm_nonneg y)
      _ = C := by rw [hx, hy]; ring
  have hr := (Complex.continuous_re.tendsto _).comp (ht x y)
  rw [show (inner ℂ (S x) y).re = (inner ℂ y (S x)).re from
    inner_re_symm (𝕜 := ℂ) (S x) y]
  exact le_of_tendsto hr (Eventually.of_forall hb)

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [CompleteSpace H] [l.NeBot] [DecidableEq n] in
/-- The same coefficient limit statement for rectangular amplifications. -/
theorem rectangularHilbertMatrix_weak_limit {m : Type*} [Fintype m]
    (T : ι → CStarMatrix m n (H →L[ℂ] H)) (S : CStarMatrix m n (H →L[ℂ] H))
    (ht : ∀ j k x y, Tendsto (fun i => inner ℂ y (T i j k x)) l
      (𝓝 (inner ℂ y (S j k x))))
    (x : Generator.FiniteHilbert n H) (y : Generator.FiniteHilbert m H) :
    Tendsto (fun i => inner ℂ y (rectangularHilbertMatrix (T i) x)) l
      (𝓝 (inner ℂ y (rectangularHilbertMatrix S x))) := by
  have h := tendsto_finsetSum Finset.univ (fun j _ =>
    tendsto_finsetSum Finset.univ (fun k _ => ht j k (x k) (y j)))
  simpa only [PiLp.inner_apply, rectangularHilbertMatrix_apply, inner_sum] using h

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A uniform complete bound survives a pointwise weak limit. -/
theorem complete_bound_of_pointwise_weak_limit_oai
    (F : ι → A →ₗ[ℂ] (H →L[ℂ] H)) (S ρ : A →ₗ[ℂ] (H →L[ℂ] H))
    (ht : ∀ a x y, Tendsto (fun i => inner ℂ y (F i a x)) l
      (𝓝 (inner ℂ y (S a x))))
    {e : ℝ} (he : 0 ≤ e) (hF : ∀ i, CompletelyBoundedBy (F i - ρ) e) :
    CompletelyBoundedBy (S - ρ) e := by
  intro p q X
  rw [← norm_rectangularHilbertMatrix]
  apply norm_le_of_weak_limit (l := l)
    (fun i => rectangularHilbertMatrix (CStarMatrix.mapₗ (F i - ρ) X))
    (rectangularHilbertMatrix (CStarMatrix.mapₗ (S - ρ) X))
    (mul_nonneg he (norm_nonneg X))
  · intro i
    rw [norm_rectangularHilbertMatrix]
    exact hF i p q X
  · intro x y
    apply rectangularHilbertMatrix_weak_limit
    intro j k a b
    simpa only [CStarMatrix.mapₗ_apply, CStarMatrix.map_apply, LinearMap.sub_apply,
      sub_apply, inner_sub_right] using
      (ht (X j k) a b).sub tendsto_const_nhds

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2, u_4} : type_of% @OAI.KadisonKastler.complete_bound_of_pointwise_weak_limit_oai.{u_1, u_2, u_4} := @OAI.KadisonKastler.complete_bound_of_pointwise_weak_limit_oai.{u_1, u_2, u_4}
