-- Prove2me | solution 1 for OAI.KadisonKastler.exists_central_localized_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:15:43.353956+00:00
-- url     : https://prove2.me/submissions/9009f099-c8d6-49fd-96bc-bd56fd9156dd

import Mathlib
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Sublists
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences
import Definitions.Def_Q260K065
import Definitions.Def_Q260K066
import Theorems.Thm_OAI_KadisonKastler_representationRowAverage_norm_le

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RectangularWeakCompact
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Weak operator compactness for the rectangular operators in a fixed
factorization. The source and target Hilbert spaces may differ. -/

namespace KadisonKastler

noncomputable section

open Filter
open scoped Topology InnerProductSpace

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] in
theorem exists_weak_rectangular_operator_ultralimit {ι : Type*} (ω : Ultrafilter ι)
    (R : ι → H →L[ℂ] K) (d : ℝ) (hd : 0 ≤ d) (hR : ∀ i, ‖R i‖ ≤ d) :
    ∃ T : H →L[ℂ] K, ‖T‖ ≤ d ∧ ∀ ξ η,
      Tendsto (fun i => inner ℂ η (R i ξ)) (ω : Filter ι) (𝓝 (inner ℂ η (T ξ))) := by
  have h (ξ : H) := Generator.Tracial.exists_weak_vector_ultralimit ω
    (fun i => R i ξ) (d * ‖ξ‖) (fun i => (R i).le_of_opNorm_le (hR i) ξ)
  choose v hv ht using h
  have ha (ξ ζ : H) : v (ξ + ζ) = v ξ + v ζ := by
    apply ext_inner_left ℂ
    intro η
    apply tendsto_nhds_unique (ht (ξ + ζ) η)
    simpa only [map_add, inner_add_right] using (ht ξ η).add (ht ζ η)
  have hs (z : ℂ) (ξ : H) : v (z • ξ) = z • v ξ := by
    apply ext_inner_left ℂ
    intro η
    apply tendsto_nhds_unique (ht (z • ξ) η)
    simpa only [map_smul, inner_smul_right] using (ht ξ η).const_mul z
  let T : H →L[ℂ] K := LinearMap.mkContinuous
    { toFun := v, map_add' := ha, map_smul' := hs } d hv
  exact ⟨T, T.opNorm_le_bound hd hv, ht⟩

omit [CompleteSpace H] in
theorem isCompact_weakRectangularBall {d : ℝ} (hd : 0 ≤ d) :
    IsCompact (weakRectangularBall H K d) := by
  classical
  apply isCompact_iff_ultrafilter_le_nhds'.mpr
  intro ω hω
  let R : (H →WOT[ℂ] K) → H →L[ℂ] K := fun T =>
    if ‖T.toCLM‖ ≤ d then T.toCLM else 0
  have hR (T : H →WOT[ℂ] K) : ‖R T‖ ≤ d := by
    dsimp [R]
    split_ifs with h
    · exact h
    · simpa only [norm_zero] using hd
  obtain ⟨T, hT, ht⟩ := exists_weak_rectangular_operator_ultralimit ω R d hd hR
  refine ⟨ContinuousLinearMapWOT.ofCLM T, hT, ?_⟩
  have hl : Tendsto (fun U => ContinuousLinearMapWOT.ofCLM (R U))
      (ω : Filter (H →WOT[ℂ] K)) (𝓝 (ContinuousLinearMapWOT.ofCLM T)) :=
    ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr ht
  have he : (fun U => ContinuousLinearMapWOT.ofCLM (R U)) =ᶠ[ω] id := by
    filter_upwards [show ∀ᶠ U in (ω : Filter (H →WOT[ℂ] K)),
      U ∈ weakRectangularBall H K d from hω] with U hU
    simp only [weakRectangularBall, Set.mem_ofPred_eq] at hU
    simp only [R, ite_eq_left hU, ContinuousLinearMapWOT.ofCLM_toCLM, id_eq]
  exact hl.congr' he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_LocalizedFactorNorm
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! The norm of a right factor localized by an operator in the original
commutant is constant on a minimal row family. -/

namespace KadisonKastler

noncomputable section

open scoped InnerProductSpace

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {c : ℝ}

omit [CompleteSpace H] in
theorem isClosed_weakRectangularBall (a : ℝ) :
    IsClosed (weakRectangularBall H K a) := by
  by_cases ha : 0 ≤ a
  · exact (isCompact_weakRectangularBall ha).isClosed
  · have he : weakRectangularBall H K a = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro T hT
      exact ha ((norm_nonneg T.toCLM).trans hT)
    rw [he]
    exact isClosed_empty

omit [CompleteSpace H] in
theorem isClosed_localized_factor_norm {X : Type*} [TopologicalSpace X]
    (R : X → H →L[ℂ] K) (hR : Continuous (fun x => ContinuousLinearMapWOT.ofCLM (R x)))
    (T : H →L[ℂ] H) (a : ℝ) : IsClosed {x | ‖(R x).comp T‖ ≤ a} := by
  have hc : Continuous (fun x => ContinuousLinearMapWOT.ofCLM ((R x).comp T)) := by
    apply ContinuousLinearMapWOT.continuous_iff.mpr
    intro ξ η
    exact ContinuousLinearMapWOT.continuous_inner_apply hR (T ξ) η
  exact (isClosed_weakRectangularBall (H := H) (K := K) a).preimage hc

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PartialSupportSpan
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! The projection onto the closed span of the initial spaces of a family
of partial isometries. All constructions remain in the original algebra. -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem partialSupportSpace_le_ker (S : Set (PartialIsometry M))
    (T : H →L[ℂ] H) (hT : ∀ v ∈ S, T.comp (v.support.val : H →L[ℂ] H) = 0) :
    partialSupportSpace S ≤ T.ker := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro y ⟨v, hv, ξ, rfl⟩
    exact congrArg (fun A : H →L[ℂ] H => A ξ) (hT v hv)
  · exact T.isClosed_ker

theorem support_le_partialSupportProjection (S : Set (PartialIsometry M))
    (v : PartialIsometry M) (hv : v ∈ S) : v.support ≤ partialSupportProjection S := by
  apply Subtype.ext
  ext ξ
  apply Submodule.starProjection_eq_self_iff.mpr
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨v, hv, ξ, rfl⟩)

theorem partialSupportProjection_le (S : Set (PartialIsometry M))
    (q : AlgebraProjection M) (hq : ∀ v ∈ S, v.support ≤ q) :
    partialSupportProjection S ≤ q := by
  have hk : partialSupportSpace S ≤ ((q.val : H →L[ℂ] H) - 1).ker := by
    apply partialSupportSpace_le_ker
    intro v hv
    ext ξ
    have he := congrArg (fun a : Algebra M => (a : H →L[ℂ] H) ξ) (hq v hv)
    exact sub_eq_zero.mpr he
  apply Subtype.ext
  ext ξ
  exact sub_eq_zero.mp (hk ((partialSupportSpace S).starProjection_apply_mem ξ))

theorem support_le_centralSupport_of_target_le (e : AlgebraProjection M)
    (v : PartialIsometry M) (hv : v.target ≤ e) : v.support ≤ centralSupport e := by
  have ht := hv.trans (le_centralSupport e)
  have hc : (centralSupport e).val * v.val = v.val := by
    calc
      _ = (centralSupport e).val * (v.target.val * v.val) := by rw [v.target_mul]
      _ = v.val := by rw [← mul_assoc, ht, v.target_mul]
  change (centralSupport e).val * v.support.val = v.support.val
  rw [← v.initial, ← mul_assoc, ← centralSupport_commutes e (star v.val), mul_assoc, hc]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CentralSupportCover
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! An orthogonal family of initial projections equivalent to subprojections
of e fills the central support of e. This is the geometric step in the
localized row-averaging proof; no countability is imposed. -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem exists_maximal_centralSupportFamily (e : AlgebraProjection M) :
    ∃ S : Set (PartialIsometry M), Maximal (IsCentralSupportFamily e) S := by
  apply zorn_subset
  intro C hC hc
  refine ⟨⋃₀ C, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
  · rintro v ⟨s, hs, hv⟩
    exact (hC hs).1 v hv
  · rintro v ⟨s, hs, hv⟩ w ⟨t, ht, hw⟩ hvw
    obtain rfl | hst := eq_or_ne s t
    · exact (hC hs).2 hv hw hvw
    rcases hc hs ht hst with h | h
    · exact (hC ht).2 (h hv) hw hvw
    · exact (hC hs).2 hv (h hw) hvw

theorem centralSupportFamily_fills (e : AlgebraProjection M)
    (S : Set (PartialIsometry M)) (hS : Maximal (IsCentralSupportFamily e) S) :
    partialSupportProjection S = centralSupport e := by
  let P := partialSupportProjection S
  have hPc : P ≤ centralSupport e := partialSupportProjection_le S _
    (fun v hv => support_le_centralSupport_of_target_le e v (hS.prop.1 v hv).1)
  let r : AlgebraProjection M := ⟨(centralSupport e).val - P.val,
    P.property.sub_of_mul_eq_right (centralSupport e).property hPc⟩
  have hPr : P.val * r.val = 0 := by
    change P.val * ((centralSupport e).val - P.val) = 0
    rw [mul_sub, projection_mul_of_le hPc, P.property.isIdempotentElem.eq, sub_self]
  have her : ∀ a : Algebra M, e.val * a * r.val = 0 := by
    intro a
    by_contra hn
    obtain ⟨v, hvr, hve, hv0⟩ := exists_partialIsometry_of_link r e
      (e.val * a * r.val)
      (by rw [mul_assoc, r.property.isIdempotentElem.eq])
      (by rw [← mul_assoc, ← mul_assoc, e.property.isIdempotentElem.eq]) hn
    have hvo (w : PartialIsometry M) (hw : w ∈ S) :
        w.support.val * v.support.val = 0 :=
      projection_orthogonal_of_le hPr (support_le_partialSupportProjection S w hw) hvr
    have hins : IsCentralSupportFamily e (insert v S) := by
      constructor
      · intro w hw
        rcases hw with rfl | hw
        · exact ⟨hve, hv0⟩
        · exact hS.prop.1 w hw
      · apply hS.prop.2.insert
        intro w hw _
        exact ⟨PartialIsometry.orthogonal_reverse _ _ (hvo w hw), hvo w hw⟩
    have hvS : v ∈ S := (hS.2 hins (Set.subset_insert v S)) (Set.mem_insert v S)
    exact hv0 (v.support.property.isIdempotentElem.eq.symm.trans (hvo v hvS))
  have hrc : r.val * (centralSupport e).val = 0 := by
    apply mul_centralSupport_eq_zero_of_no_links e r
    intro a
    have h := congrArg star (her (star a))
    simpa only [star_mul, star_star, r.property.isSelfAdjoint.star_eq,
      e.property.isSelfAdjoint.star_eq, star_zero, mul_assoc] using h
  have hr0 : r.val = 0 := by
    have hr : r.val * (centralSupport e).val = r.val := by
      change ((centralSupport e).val - P.val) * (centralSupport e).val =
        (centralSupport e).val - P.val
      rw [sub_mul, (centralSupport e).property.isIdempotentElem.eq, projection_mul_of_le hPc]
    exact hr.symm.trans hrc
  apply Subtype.ext
  exact (sub_eq_zero.mp hr0).symm

theorem exists_centralSupportCover (e : AlgebraProjection M) :
    ∃ S : Set (PartialIsometry M), IsCentralSupportFamily e S ∧
      partialSupportProjection S = centralSupport e := by
  obtain ⟨S, hS⟩ := exists_maximal_centralSupportFamily e
  exact ⟨S, hS.prop, centralSupportFamily_fills e S hS⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteSupportRows
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.crossMatchingFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Normalized finite rows from an orthogonal family of partial isometries.
The missing initial projection is included as one extra row entry. -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem finiteSupportSum_projection (s : Finset (PartialIsometry M))
    (ho : ∀ v ∈ s, ∀ w ∈ s, v ≠ w → v.support.val * w.support.val = 0) :
    IsStarProjection (finiteSupportSum s) :=
  isStarProjection_sum_orthogonal s (fun v => v.support.val)
    (fun v _ => v.support.property) ho

theorem finiteSupportSum_mul_member (s : Finset (PartialIsometry M))
    (ho : ∀ v ∈ s, ∀ w ∈ s, v ≠ w → v.support.val * w.support.val = 0)
    (v : PartialIsometry M) (hv : v ∈ s) :
    finiteSupportSum s * v.support.val = v.support.val := by
  classical
  rw [finiteSupportSum, Finset.sum_mul, Finset.sum_eq_single v]
  · exact v.support.property.isIdempotentElem.eq
  · intro w hw hwv
    exact ho w hw v hv hwv
  · exact fun h => (h hv).elim

theorem finiteSupportSum_mul_of_subset (s t : Finset (PartialIsometry M))
    (ho : ∀ v ∈ t, ∀ w ∈ t, v ≠ w → v.support.val * w.support.val = 0)
    (hst : s ⊆ t) : finiteSupportSum t * finiteSupportSum s = finiteSupportSum s := by
  simp only [finiteSupportSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  exact finiteSupportSum_mul_member t ho v (hst hv)

theorem finiteSupportRow_normalized (s : Finset (PartialIsometry M))
    (ho : ∀ v ∈ s, ∀ w ∈ s, v ≠ w → v.support.val * w.support.val = 0) :
    ∑ i, finiteSupportRow s i * star (finiteSupportRow s i) = 1 := by
  classical
  have hp := finiteSupportSum_projection s ho
  rw [Fintype.sum_option]
  simp only [finiteSupportRow, star_sub, star_one, hp.isSelfAdjoint.star_eq, star_star]
  have hs : ∑ v : s, star v.val.val * v.val.val = finiteSupportSum s := by
    simp only [PartialIsometry.initial]
    exact Finset.sum_coe_sort s (fun v => v.support.val)
  rw [hs, (hp.one_sub).isIdempotentElem.eq]
  abel

theorem partialIsometry_mul_finiteSupportSum (s : Finset (PartialIsometry M))
    (ho : ∀ v ∈ s, ∀ w ∈ s, v ≠ w → v.support.val * w.support.val = 0)
    (v : PartialIsometry M) (hv : v ∈ s) : v.val * finiteSupportSum s = v.val := by
  have h := finiteSupportSum_mul_member s ho v hv
  have hs : v.support.val * finiteSupportSum s = v.support.val := by
    simpa only [star_mul, (finiteSupportSum_projection s ho).isSelfAdjoint.star_eq,
      v.support.property.isSelfAdjoint.star_eq] using congrArg star h
  calc
    _ = (v.val * v.support.val) * finiteSupportSum s := by rw [v.mul_support]
    _ = v.val := by rw [mul_assoc, hs, v.mul_support]

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem finiteSupportRow_diagonal_compression
    (e : AlgebraProjection M) (s : Finset (PartialIsometry M))
    (ho : ∀ v ∈ s, ∀ w ∈ s, v ≠ w → v.support.val * w.support.val = 0)
    (he : ∀ v ∈ s, v.target ≤ e)
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (R : H →L[ℂ] K) :
    (representationRowAverage π (finiteSupportRow s) R).comp
        (finiteSupportSum s : H →L[ℂ] H) =
      (representationRowAverage π (finiteSupportRow s)
        ((π e.val).comp (R.comp (e.val : H →L[ℂ] H)))).comp
          (finiteSupportSum s : H →L[ℂ] H) := by
  classical
  have hp := finiteSupportSum_projection s ho
  have hzero : (1 - finiteSupportSum s) * finiteSupportSum s = 0 := by
    rw [sub_mul, one_mul, hp.isIdempotentElem.eq, sub_self]
  have hev (v : s) : e.val * v.val.val = v.val.val := by
    calc
      _ = e.val * (v.val.target.val * v.val.val) := by rw [v.val.target_mul]
      _ = v.val.val := by rw [← mul_assoc, he v.val v.property, v.val.target_mul]
  have hve (v : s) : star v.val.val * e.val = star v.val.val := by
    simpa only [star_mul, e.property.isSelfAdjoint.star_eq] using congrArg star (hev v)
  ext ξ
  simp only [representationRowAverage, sum_apply, ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  change π (finiteSupportRow s i)
      (R (((star (finiteSupportRow s i) : Algebra M) : H →L[ℂ] H)
        ((finiteSupportSum s : H →L[ℂ] H) ξ))) =
    π (finiteSupportRow s i) (π e.val (R ((e.val : H →L[ℂ] H)
      (((star (finiteSupportRow s i) : Algebra M) : H →L[ℂ] H)
        ((finiteSupportSum s : H →L[ℂ] H) ξ)))))
  cases i with
  | none =>
      have hz : ((star (finiteSupportRow s none) : Algebra M) : H →L[ℂ] H)
          ((finiteSupportSum s : H →L[ℂ] H) ξ) = 0 := by
        have h := congrArg (fun a : Algebra M => (a : H →L[ℂ] H) ξ) hzero
        simpa only [finiteSupportRow, star_sub, star_one, hp.isSelfAdjoint.star_eq,
          MulMemClass.coe_mul, mul_apply_eq_comp, ZeroMemClass.coe_zero, zero_apply] using h
      simp only [hz, map_zero]
  | some v =>
      have hsp := partialIsometry_mul_finiteSupportSum s ho v.val v.property
      have hvξ : ((star (finiteSupportRow s (some v)) : Algebra M) : H →L[ℂ] H)
          ((finiteSupportSum s : H →L[ℂ] H) ξ) = (v.val.val : H →L[ℂ] H) ξ := by
        simpa only [finiteSupportRow, star_star, MulMemClass.coe_mul, mul_apply_eq_comp] using
          congrArg (fun a : Algebra M => (a : H →L[ℂ] H) ξ) hsp
      rw [hvξ]
      have heξ : (e.val : H →L[ℂ] H) ((v.val.val : H →L[ℂ] H) ξ) =
          (v.val.val : H →L[ℂ] H) ξ :=
        congrArg (fun a : Algebra M => (a : H →L[ℂ] H) ξ) (hev v)
      change _ = π (star v.val.val) (π e.val (R ((e.val : H →L[ℂ] H)
        ((v.val.val : H →L[ℂ] H) ξ))))
      rw [heξ]
      have hπ : π (star v.val.val) * π e.val = π (star v.val.val) := by
        rw [← map_mul, hve]
      exact (congrArg (fun A : K →L[ℂ] K => A (R ((v.val.val : H →L[ℂ] H) ξ))) hπ).symm

theorem finiteSupportRow_localized_norm_le
    (e : AlgebraProjection M) (s : Finset (PartialIsometry M))
    (ho : ∀ v ∈ s, ∀ w ∈ s, v ≠ w → v.support.val * w.support.val = 0)
    (he : ∀ v ∈ s, v.target ≤ e)
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (R : H →L[ℂ] K) :
    ‖(representationRowAverage π (finiteSupportRow s) R).comp
      (finiteSupportSum s : H →L[ℂ] H)‖ ≤
      ‖(π e.val).comp (R.comp (e.val : H →L[ℂ] H))‖ := by
  rw [finiteSupportRow_diagonal_compression e s ho he π R]
  have hp := (finiteSupportSum_projection s ho).map M.toStarSubalgebra.subtype
  have hb := (representationRowAverage π (finiteSupportRow s)
    ((π e.val).comp (R.comp (e.val : H →L[ℂ] H)))).opNorm_comp_le
      (finiteSupportSum s : H →L[ℂ] H)
  have hr := representationRowAverage_norm_le π (finiteSupportRow s)
    (finiteSupportRow_normalized s ho) ((π e.val).comp (R.comp (e.val : H →L[ℂ] H)))
  exact hb.trans ((mul_le_mul_of_nonneg_left hp.norm_le (norm_nonneg _)).trans
    (by simpa only [mul_one] using hr))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SupportSpanNorm
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Uniform norm bounds on finite initial sums extend to the full central
support. The argument uses norm density, without normality of a representation. -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [NormedSpace ℂ K]
  {M : VonNeumannAlgebra H}

theorem finiteSupportSum_fixes_of_subset (s t : Finset (PartialIsometry M))
    (ho : ∀ v ∈ t, ∀ w ∈ t, v ≠ w → v.support.val * w.support.val = 0)
    (hst : s ⊆ t) (ξ : H)
    (hξ : (finiteSupportSum s : H →L[ℂ] H) ξ = ξ) :
    (finiteSupportSum t : H →L[ℂ] H) ξ = ξ := by
  have h := congrArg (fun a : Algebra M => (a : H →L[ℂ] H) ξ)
    (finiteSupportSum_mul_of_subset s t ho hst)
  change (finiteSupportSum t : H →L[ℂ] H) ((finiteSupportSum s : H →L[ℂ] H) ξ) =
    (finiteSupportSum s : H →L[ℂ] H) ξ at h
  rwa [hξ] at h

theorem support_span_has_finite_support (S : Set (PartialIsometry M))
    (ho : S.Pairwise (fun v w => v.support.val * w.support.val = 0))
    {ξ : H} (hξ : ξ ∈ Submodule.span ℂ (partialSupportVectors S)) :
    ∃ s : Finset (PartialIsometry M), (↑s : Set (PartialIsometry M)) ⊆ S ∧
      (finiteSupportSum s : H →L[ℂ] H) ξ = ξ := by
  classical
  induction hξ using Submodule.span_induction with
  | mem ξ hξ =>
      obtain ⟨v, hv, η, rfl⟩ := hξ
      refine ⟨{v}, by simpa using hv, ?_⟩
      have h := congrArg (fun a : Algebra M => (a : H →L[ℂ] H) η)
        v.support.property.isIdempotentElem.eq
      simpa only [finiteSupportSum, Finset.sum_singleton, MulMemClass.coe_mul,
        mul_apply_eq_comp] using h
  | zero => exact ⟨∅, by simp, by simp [finiteSupportSum]⟩
  | add ξ η _ _ hξ hη =>
      obtain ⟨s, hs, hξ⟩ := hξ
      obtain ⟨t, ht, hη⟩ := hη
      have hu : (↑(s ∪ t) : Set (PartialIsometry M)) ⊆ S := by
        intro v hv
        rcases Finset.mem_union.mp hv with hv | hv
        · exact hs hv
        · exact ht hv
      have huo : ∀ v ∈ s ∪ t, ∀ w ∈ s ∪ t, v ≠ w →
          v.support.val * w.support.val = 0 := fun v hv w hw => ho (hu hv) (hu hw)
      refine ⟨s ∪ t, hu, ?_⟩
      rw [map_add, finiteSupportSum_fixes_of_subset s (s ∪ t) huo Finset.subset_union_left ξ hξ,
        finiteSupportSum_fixes_of_subset t (s ∪ t) huo Finset.subset_union_right η hη]
  | smul z ξ _ hξ =>
      obtain ⟨s, hs, hξ⟩ := hξ
      exact ⟨s, hs, by rw [map_smul, hξ]⟩

theorem norm_comp_partialSupportProjection_le (S : Set (PartialIsometry M))
    (ho : S.Pairwise (fun v w => v.support.val * w.support.val = 0))
    (A : H →L[ℂ] K) {d : ℝ} (hd : 0 ≤ d)
    (hA : ∀ s : Finset (PartialIsometry M), (↑s : Set (PartialIsometry M)) ⊆ S →
      ‖A.comp (finiteSupportSum s : H →L[ℂ] H)‖ ≤ d) :
    ‖A.comp ((partialSupportProjection S).val : H →L[ℂ] H)‖ ≤ d := by
  have hb : ∀ ξ ∈ partialSupportSpace S, ‖A ξ‖ ≤ d * ‖ξ‖ := by
    intro ξ hξ
    have hs : (Submodule.span ℂ (partialSupportVectors S) : Set H) ⊆
        {η | ‖A η‖ ≤ d * ‖η‖} := by
      intro η hη
      obtain ⟨s, hs, he⟩ := support_span_has_finite_support S ho hη
      change ‖A η‖ ≤ d * ‖η‖
      have h := (A.comp (finiteSupportSum s : H →L[ℂ] H)).le_of_opNorm_le (hA s hs) η
      simpa only [ContinuousLinearMap.comp_apply, he] using h
    have hc : IsClosed {η : H | ‖A η‖ ≤ d * ‖η‖} :=
      isClosed_le (A.continuous.norm) (continuous_const.mul continuous_norm)
    exact closure_minimal hs hc hξ
  apply ContinuousLinearMap.opNorm_le_bound _ hd
  intro ξ
  have h := hb _ ((partialSupportSpace S).starProjection_apply_mem ξ)
  have hp := ((partialSupportProjection S).property.map M.toStarSubalgebra.subtype).norm_le
  have hpξ := (((partialSupportProjection S).val : H →L[ℂ] H).le_of_opNorm_le hp ξ)
  change ‖(partialSupportSpace S).starProjection ξ‖ ≤ 1 * ‖ξ‖ at hpξ
  rw [one_mul] at hpξ
  exact h.trans (mul_le_mul_of_nonneg_left hpξ hd)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CentralLocalizationMinimum
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.crossMatchingFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Compactness assembles the finite support rows into the localized norm
bound used by Paulsen's minimal-family argument. No normality of the auxiliary
representation is needed: the finite sums are on the original space. -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H}

theorem representationRowAverage_reindex
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (r : κ → Algebra M) (R : H →L[ℂ] K) :
    representationRowAverage π (r ∘ e) R = representationRowAverage π r R := by
  exact Equiv.sum_comp e (fun i => (π (r i)).comp (R.comp (star (r i) : H →L[ℂ] H)))

omit [CompleteSpace K] in
theorem norm_comp_finiteSupportSum_mono (A : H →L[ℂ] K)
    (s t : Finset (PartialIsometry M))
    (ho : ∀ v ∈ t, ∀ w ∈ t, v ≠ w → v.support.val * w.support.val = 0)
    (hst : s ⊆ t) :
    ‖A.comp (finiteSupportSum s : H →L[ℂ] H)‖ ≤
      ‖A.comp (finiteSupportSum t : H →L[ℂ] H)‖ := by
  have he : (finiteSupportSum t : H →L[ℂ] H).comp
      (finiteSupportSum s : H →L[ℂ] H) = (finiteSupportSum s : H →L[ℂ] H) :=
    congrArg Subtype.val (finiteSupportSum_mul_of_subset s t ho hst)
  have hp := (finiteSupportSum_projection s
    (fun v hv w hw => ho v (hst hv) w (hst hw))).map M.toStarSubalgebra.subtype
  calc
    _ = ‖(A.comp (finiteSupportSum t : H →L[ℂ] H)).comp
        (finiteSupportSum s : H →L[ℂ] H)‖ := by rw [ContinuousLinearMap.comp_assoc, he]
    _ ≤ _ := ((A.comp (finiteSupportSum t : H →L[ℂ] H)).opNorm_comp_le _).trans
      ((mul_le_mul_of_nonneg_left hp.norm_le (norm_nonneg _)).trans_eq (mul_one _))

theorem exists_central_localized_norm_le_oai
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (R : X → H →L[ℂ] K)
    (hR : Continuous (fun F => ContinuousLinearMapWOT.ofCLM (R F)))
    (hrows : ∀ (F : X) (n : ℕ) (r : Fin n → Algebra M)
      (_hr : ∑ i, r i * star (r i) = 1),
      ∃ G : X, R G = representationRowAverage π r (R F))
    (e : AlgebraProjection M) (F : X) :
    ∃ G : X, ‖(R G).comp ((centralSupport e).val : H →L[ℂ] H)‖ ≤
      ‖(π e.val).comp ((R F).comp (e.val : H →L[ℂ] H))‖ := by
  classical
  obtain ⟨S, hS, hcover⟩ := exists_centralSupportCover e
  let I := {s : Finset (PartialIsometry M) // (↑s : Set (PartialIsometry M)) ⊆ S}
  let d := ‖(π e.val).comp ((R F).comp (e.val : H →L[ℂ] H))‖
  let D : I → Set X := fun s => {G | ‖(R G).comp (finiteSupportSum s.val : H →L[ℂ] H)‖ ≤ d}
  let : Nonempty I := ⟨⟨∅, by simp⟩⟩
  have ho (s : I) : ∀ v ∈ s.val, ∀ w ∈ s.val, v ≠ w →
      v.support.val * w.support.val = 0 := fun v hv w hw => hS.2 (s.property hv) (s.property hw)
  have hd (s : I) : IsClosed (D s) :=
    isClosed_localized_factor_norm R hR (finiteSupportSum s.val : H →L[ℂ] H) d
  have hn (s : I) : (D s).Nonempty := by
    let r := finiteSupportRow s.val
    let f := (Fintype.equivFin (Option s.val)).symm
    have hr : ∑ i, (r ∘ f) i * star ((r ∘ f) i) = 1 := by
      change (∑ i, r (f i) * star (r (f i))) = 1
      rw [Equiv.sum_comp f (fun j => r j * star (r j))]
      exact finiteSupportRow_normalized s.val (ho s)
    obtain ⟨G, hG⟩ := hrows F _ (r ∘ f) hr
    refine ⟨G, ?_⟩
    change ‖(R G).comp (finiteSupportSum s.val : H →L[ℂ] H)‖ ≤ d
    rw [hG, representationRowAverage_reindex]
    exact finiteSupportRow_localized_norm_le e s.val (ho s)
      (fun v hv => (hS.1 v (s.property hv)).1) π (R F)
  have hdir : Directed (· ⊇ ·) D := by
    intro s t
    let u : I := ⟨s.val ∪ t.val, by
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact s.property hv
      · exact t.property hv⟩
    refine ⟨u, ?_, ?_⟩
    · intro G hG
      exact (norm_comp_finiteSupportSum_mono (R G) s.val u.val (ho u)
        Finset.subset_union_left).trans hG
    · intro G hG
      exact (norm_comp_finiteSupportSum_mono (R G) t.val u.val (ho u)
        Finset.subset_union_right).trans hG
  obtain ⟨G, hG⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    D hdir hn (fun s => (hd s).isCompact) hd
  refine ⟨G, ?_⟩
  rw [← hcover]
  exact norm_comp_partialSupportProjection_le S hS.2 (R G) (norm_nonneg _) (fun s hs =>
    Set.mem_iInter.mp hG ⟨s, hs⟩)

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.KadisonKastler.exists_central_localized_norm_le_oai.{u_1, u_2, u_3} := @OAI.KadisonKastler.exists_central_localized_norm_le_oai.{u_1, u_2, u_3}
