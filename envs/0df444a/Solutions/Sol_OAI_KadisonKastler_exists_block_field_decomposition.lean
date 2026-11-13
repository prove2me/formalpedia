-- Prove2me | solution 1 for OAI.KadisonKastler.exists_block_field_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:59:52.856199+00:00
-- url     : https://prove2.me/submissions/e8631a9b-c663-4dcb-a74d-f20a213ea9c2

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.ChainOfFn
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
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Tactic
import Mathlib.Tactic.DeriveCountable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K013
import Definitions.Def_Q260K015

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_IntertwinerExtension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extension by zero along an isometric Hilbert-space embedding. These
identities transport the central commutant to the common scalar L² model. -/

noncomputable section
namespace KadisonSimilarity

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (J : H →ₗᵢ[ℂ] K)

/-- Star-compatible intertwining transports commutation to the extension. -/
theorem isometricExtension_commutes
    (S : H →L[ℂ] H) (R : K →L[ℂ] K)
    (hJ : J.toContinuousLinearMap.comp S = R.comp J.toContinuousLinearMap)
    (hJstar : J.toContinuousLinearMap.comp (star S) = (star R).comp J.toContinuousLinearMap)
    (T : H →L[ℂ] H) (hT : T * S = S * T) :
    isometricExtension J T * R = R * isometricExtension J T := by
  have ha : S.comp J.toContinuousLinearMap.adjoint =
      J.toContinuousLinearMap.adjoint.comp R := by
    have h := congrArg ContinuousLinearMap.adjoint hJstar
    simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_adjoint] using h
  have hTx (x : H) : T (S x) = S (T x) := congrArg (fun L : H →L[ℂ] H => L x) hT
  have hJx (x : H) : J (S x) = R (J x) :=
    congrArg (fun L : H →L[ℂ] K => L x) hJ
  have hax (x : K) : S (J.toContinuousLinearMap.adjoint x) =
      J.toContinuousLinearMap.adjoint (R x) :=
    congrArg (fun L : K →L[ℂ] H => L x) ha
  apply ContinuousLinearMap.ext
  intro x
  change J (T (J.toContinuousLinearMap.adjoint (R x))) =
    R (J (T (J.toContinuousLinearMap.adjoint x)))
  rw [← hax, hTx, hJx]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_IsometricCornerAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The von Neumann algebra on a reducing isometric range -/

namespace KadisonKastler

open KadisonSimilarity

noncomputable section

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (J : E →ₗᵢ[ℂ] H)

theorem rangeCompressionStarHom_intertwines (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : ∀ a : A, isometricExtension J 1 * a.val = a.val * isometricExtension J 1)
    (a : A) : J.toContinuousLinearMap.comp (rangeCompressionStarHom J A hA a) =
      a.val.comp J.toContinuousLinearMap := by
  ext v
  exact rangeCompression_intertwines_apply J A hA a v

variable (M : VonNeumannAlgebra H) (hJM : isometricExtension J 1 ∈ M)

theorem mem_isometricCornerAlgebra_iff (T : E →L[ℂ] E) :
    T ∈ isometricCornerAlgebra J M hJM ↔ isometricExtension J T ∈ M := by
  let σ := rangeCompressionStarHom J M.commutant.toStarSubalgebra
    (rangeProjection_commutes_commutant J M hJM)
  have hmem : T ∈ isometricCornerAlgebra J M hJM ↔ ∀ a : M.commutant.toStarSubalgebra,
      σ a * T = T * σ a := by
    change T ∈ starSubalgebraCommutant σ.range ↔ _
    rw [← SetLike.mem_coe, coe_starSubalgebraCommutant]
    constructor
    · intro h a
      exact h (σ a) ⟨a, rfl⟩
    · intro h _ ha
      obtain ⟨a, rfl⟩ := ha
      exact h a
  rw [hmem]
  conv_rhs => rw [← M.commutant_commutant]
  constructor
  · intro h
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro a ha
    let a' : M.commutant.toStarSubalgebra := ⟨a, ha⟩
    have hJ := rangeCompressionStarHom_intertwines J _
      (rangeProjection_commutes_commutant J M hJM) a'
    have hJs := rangeCompressionStarHom_intertwines J _
      (rangeProjection_commutes_commutant J M hJM) (star a')
    rw [map_star] at hJs
    exact (isometricExtension_commutes J (σ a') a hJ hJs T (h a').symm).symm
  · intro h a
    have hc := VonNeumannAlgebra.mem_commutant_iff.mp h a.val a.property
    exact (compression_commutes_of_isometricExtension_commutes J T a.val hc.symm).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HilbertSumCorners
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The reducing coordinate corners of a Hilbert sum -/

namespace KadisonKastler

open KadisonSimilarity
open scoped InnerProductSpace

noncomputable section

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace ℂ (E n)] [∀ n, CompleteSpace (E n)]

theorem hilbertSumInclusion_extension_apply (n : ℕ) (T : E n →L[ℂ] E n) (f : lp E 2) :
    isometricExtension (hilbertSumInclusion n) T f = lp.single 2 n (T (f n)) := by
  change hilbertSumInclusion n (T ((hilbertSumInclusion n).toContinuousLinearMap.adjoint f)) = _
  rw [hilbertSumInclusion_adjoint_apply, hilbertSumInclusion_apply]

theorem hilbertSumCompression_norm_le (n : ℕ) (T : lp E 2 →L[ℂ] lp E 2) :
    ‖hilbertSumCompression n T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro v
  rw [hilbertSumCompression_apply]
  exact (lp.norm_apply_le_norm (by norm_num) _ n).trans
    ((T.le_opNorm _).trans_eq (by rw [lp.norm_single (by norm_num)]))

theorem hilbertSumCompression_extension (n : ℕ) (T : lp E 2 →L[ℂ] lp E 2) :
    isometricExtension (hilbertSumInclusion n) (hilbertSumCompression n T) =
      hilbertSumProjection n * T * hilbertSumProjection n := by
  ext f
  rfl

theorem hilbertSum_diagonal_of_commutes (T : lp E 2 →L[ℂ] lp E 2)
    (hT : ∀ n, hilbertSumProjection n * T = T * hilbertSumProjection n)
    (f : lp E 2) (n : ℕ) : T f n = hilbertSumCompression n T (f n) := by
  have h := congrArg (fun S : lp E 2 →L[ℂ] lp E 2 => S f n) (hT n)
  simpa only [mul_apply_eq_comp, hilbertSumProjection_apply,
    lp.single_apply_self, hilbertSumCompression_apply] using h

theorem hilbertSumCompression_mem_corner (M : VonNeumannAlgebra (lp E 2)) (n : ℕ)
    (hn : hilbertSumProjection n ∈ M) (T : lp E 2 →L[ℂ] lp E 2) (hT : T ∈ M) :
    hilbertSumCompression n T ∈ isometricCornerAlgebra (hilbertSumInclusion (E := E) n) M hn := by
  rw [mem_isometricCornerAlgebra_iff, hilbertSumCompression_extension]
  exact M.mul_mem (M.mul_mem hn hT) hn

theorem hilbertSum_corner_commutes (M : VonNeumannAlgebra (lp E 2)) (n : ℕ)
    (hn : hilbertSumProjection n ∈ M) (F : E n →L[ℂ] E n)
    (hF : F ∈ isometricCornerAlgebra (hilbertSumInclusion (E := E) n) M hn)
    (S : lp E 2 →L[ℂ] lp E 2) (hS : S ∈ M.commutant) (v : E n) :
    F (hilbertSumCompression n S v) = hilbertSumCompression n S (F v) := by
  have hExt := (mem_isometricCornerAlgebra_iff
    (hilbertSumInclusion (E := E) n) M hn F).mp hF
  have hc := (VonNeumannAlgebra.mem_commutant_iff.mp hS) _ hExt
  have h := congrArg (fun R : lp E 2 →L[ℂ] lp E 2 => R (lp.single 2 n v) n) hc
  simpa only [mul_apply_eq_comp, hilbertSumInclusion_extension_apply,
    lp.single_apply_self, hilbertSumCompression_apply] using h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CentralBlockDecomposition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Block decomposition from central coordinate projections

Commutation with the coordinate projections gives the diagonal blocks.
Conversely, a uniformly bounded family of corner operators belongs to the
original algebra by the bicommutant theorem, without a normality assumption.
-/

namespace KadisonKastler

open KadisonSimilarity

noncomputable section

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace ℂ (E n)] [∀ n, CompleteSpace (E n)]

theorem blockAlgebraDecomposition_of_central_coordinates (M : VonNeumannAlgebra (lp E 2))
    (hQ : ∀ n, hilbertSumProjection n ∈ M ∧ hilbertSumProjection n ∈ M.commutant) :
    BlockAlgebraDecomposition
      (fun n => isometricCornerAlgebra (hilbertSumInclusion (E := E) n) M (hQ n).1) M := by
  constructor
  · intro T hT
    refine ⟨fun n => hilbertSumCompression n T,
      fun n => hilbertSumCompression_norm_le n T,
      fun n => hilbertSumCompression_mem_corner M n (hQ n).1 T hT, ?_⟩
    intro f n
    exact hilbertSum_diagonal_of_commutes T
      (fun i => ((VonNeumannAlgebra.mem_commutant_iff.mp (hQ i).2) T hT).symm) f n
  · intro F C hC hFn hFM
    let T := hilbertSumOperator F C hC hFn
    refine ⟨T, ?_, fun _ _ => hilbertSumOperator_apply F C hC hFn _ _⟩
    rw [← M.commutant_commutant]
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro S hS
    have hSd (f : lp E 2) (n : ℕ) : S f n = hilbertSumCompression n S (f n) :=
      hilbertSum_diagonal_of_commutes S
        (fun i => (VonNeumannAlgebra.mem_commutant_iff.mp hS) _ (hQ i).1) f n
    have hcomm (n : ℕ) (v : E n) :
        F n (hilbertSumCompression n S v) = hilbertSumCompression n S (F n v) := by
      exact hilbertSum_corner_commutes M n (hQ n).1 (F n) (hFM n) S hS v
    apply ContinuousLinearMap.ext
    intro f
    apply lp.ext
    funext n
    change S (T f) n = T (S f) n
    change S (hilbertSumOperator F C hC hFn f) n = hilbertSumOperator F C hC hFn (S f) n
    simp only [hSd, hilbertSumOperator_apply]
    exact (hcomm n (f n)).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FieldCoordinateCenters
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Central coordinate projections from the two actual field actions -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {X K : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  [∀ n, NormedAddCommGroup (K n)] [∀ n, InnerProductSpace ℂ (K n)]
  [∀ n, CompleteSpace (K n)] (μ : ∀ n, Measure (X n))

local notation "L" => fun n => Lp (K n) 2 (μ n)

theorem hilbertSumProjection_central_of_fields (A : VonNeumannAlgebra (lp L 2))
    (hA : HasHilbertSumFields μ A) (hA' : HasHilbertSumFields μ A.commutant) (n : ℕ) :
    hilbertSumProjection n ∈ A ∧ hilbertSumProjection n ∈ A.commutant := by
  refine ⟨hilbertSumProjection_mem_of_commutant_fields μ A hA' n, ?_⟩
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro T hT
  obtain ⟨F, hF⟩ := hA T hT
  exact (hilbertSum_field_commutes_projection μ T F hF n).symm

theorem blockAlgebraDecomposition_of_field_actions (A : VonNeumannAlgebra (lp L 2))
    (hA : HasHilbertSumFields μ A) (hA' : HasHilbertSumFields μ A.commutant) :
    BlockAlgebraDecomposition
      (fun n => isometricCornerAlgebra (hilbertSumInclusion (E := L) n) A
        (hilbertSumProjection_mem_of_commutant_fields μ A hA' n)) A := by
  exact blockAlgebraDecomposition_of_central_coordinates A
    (hilbertSumProjection_central_of_fields μ A hA hA')

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CornerFieldDecomposition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Field decomposition on each reducing Hilbert-sum corner -/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity

noncomputable section

variable {X K : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  [∀ n, NormedAddCommGroup (K n)] [∀ n, InnerProductSpace ℂ (K n)]
  [∀ n, CompleteSpace (K n)] (μ : ∀ n, Measure (X n))

local notation "L" => fun n => Lp (K n) 2 (μ n)

theorem hilbertSumCompression_isometricExtension (n : ℕ) (T : L n →L[ℂ] L n) :
    hilbertSumCompression n (isometricExtension (hilbertSumInclusion (E := L) n) T) = T := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [hilbertSumCompression_apply, hilbertSumInclusion_extension_apply,
    lp.single_apply_self]

theorem cornerOperatorFieldDecomposition
    (A : VonNeumannAlgebra (lp L 2)) (P : ∀ n, X n → VonNeumannAlgebra (K n))
    (hdec : ∀ T ∈ A, ∃ F : ∀ n, X n → K n →L[ℂ] K n,
      (∀ n v, AEStronglyMeasurable (fun x => F n x v) (μ n)) ∧
      (∀ n, ∀ᵐ x ∂μ n, ‖F n x‖ ≤ ‖T‖) ∧ (∀ n, ∀ᵐ x ∂μ n, F n x ∈ P n x) ∧
      ∀ (f : lp L 2) n, T f n =ᵐ[μ n] fun x => F n x (f n x))
    (hcomm : ∀ S ∈ A.commutant, ∃ G : ∀ n, X n → K n →L[ℂ] K n,
      (∀ n, ∀ᵐ x ∂μ n, G n x ∈ (P n x).commutant) ∧
      ∀ (f : lp L 2) n, S f n =ᵐ[μ n] fun x => G n x (f n x))
    (n : ℕ) :
    OperatorFieldDecomposition (μ n) (P n)
      (isometricCornerAlgebra (hilbertSumInclusion (E := L) n) A
        (hilbertSumProjection_mem_of_commutant_fields μ A
          (fun S hS => let ⟨G, _, hG⟩ := hcomm S hS; ⟨G, hG⟩) n)) := by
  let hn := hilbertSumProjection_mem_of_commutant_fields μ A
    (fun S hS => let ⟨G, _, hG⟩ := hcomm S hS; ⟨G, hG⟩) n
  constructor
  · intro T hT
    have hExt : isometricExtension (hilbertSumInclusion (E := L) n) T ∈ A :=
      (mem_isometricCornerAlgebra_iff _ A hn T).mp hT
    obtain ⟨F, hm, hb, hF, ha⟩ := hdec _ hExt
    refine ⟨F n, hm n, ?_, hF n, ?_⟩
    · simpa only [isometricExtension_norm] using hb n
    · have h := hilbertSumCompression_field_action μ _ F ha n
      rwa [hilbertSumCompression_isometricExtension] at h
  · intro F C _ hm hb hF
    let T := l2LinearFieldMap (μ n) F hm C hb
    have hTa : RepresentsOperatorField (μ n) F T :=
      fun f => l2LinearFieldApply_ae (μ n) F hm C hb f
    refine ⟨T, ?_, hTa⟩
    change T ∈ starSubalgebraCommutant
      (rangeCompressionStarHom (hilbertSumInclusion (E := L) n) A.commutant.toStarSubalgebra
        (rangeProjection_commutes_commutant _ A hn)).range
    rw [← SetLike.mem_coe, coe_starSubalgebraCommutant]
    rintro _ ⟨S, rfl⟩
    change hilbertSumCompression n S.val * T = T * hilbertSumCompression n S.val
    obtain ⟨G, hG, hSG⟩ := hcomm S.val S.property
    have hSa := hilbertSumCompression_field_action μ S.val G hSG n
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [hSa (T f), hTa f, hTa (hilbertSumCompression n S.val f),
      hSa f, hG n, hF] with x hsf htf hts hsf' hg hf
    change (hilbertSumCompression n S.val (T f)) x = (T (hilbertSumCompression n S.val f)) x
    rw [hsf, htf, hts, hsf']
    exact congrArg (fun R : K n →L[ℂ] K n => R (f x))
      (VonNeumannAlgebra.mem_commutant_iff.mp hg (F x) hf).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BlockFieldDecomposition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Packaging the simultaneous block and field reconstructions -/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity

noncomputable section

variable {X K : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  [∀ n, NormedAddCommGroup (K n)] [∀ n, InnerProductSpace ℂ (K n)]
  [∀ n, CompleteSpace (K n)] (μ : ∀ n, Measure (X n))

local notation "L" => fun n => Lp (K n) 2 (μ n)

theorem exists_block_field_decomposition_oai
    (A : VonNeumannAlgebra (lp L 2)) (P : ∀ n, X n → VonNeumannAlgebra (K n))
    (hdec : ∀ T ∈ A, ∃ F : ∀ n, X n → K n →L[ℂ] K n,
      (∀ n v, AEStronglyMeasurable (fun x => F n x v) (μ n)) ∧
      (∀ n, ∀ᵐ x ∂μ n, ‖F n x‖ ≤ ‖T‖) ∧ (∀ n, ∀ᵐ x ∂μ n, F n x ∈ P n x) ∧
      ∀ (f : lp L 2) n, T f n =ᵐ[μ n] fun x => F n x (f n x))
    (hcomm : ∀ S ∈ A.commutant, ∃ G : ∀ n, X n → K n →L[ℂ] K n,
      (∀ n, ∀ᵐ x ∂μ n, G n x ∈ (P n x).commutant) ∧
      ∀ (f : lp L 2) n, S f n =ᵐ[μ n] fun x => G n x (f n x)) :
    ∃ Q : ∀ n, VonNeumannAlgebra (L n), BlockAlgebraDecomposition Q A ∧
      ∀ n, OperatorFieldDecomposition (μ n) (P n) (Q n) := by
  have hAf : HasHilbertSumFields μ A := by
    intro T hT
    obtain ⟨F, _, _, _, ha⟩ := hdec T hT
    exact ⟨F, ha⟩
  have hAc : HasHilbertSumFields μ A.commutant := by
    intro T hT
    obtain ⟨F, _, ha⟩ := hcomm T hT
    exact ⟨F, ha⟩
  let Q := fun n => isometricCornerAlgebra (hilbertSumInclusion (E := L) n) A
    (hilbertSumProjection_mem_of_commutant_fields μ A hAc n)
  refine ⟨Q, blockAlgebraDecomposition_of_field_actions μ A hAf hAc, ?_⟩
  intro n
  exact cornerOperatorFieldDecomposition μ A P hdec hcomm n

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.exists_block_field_decomposition_oai.{u_1, u_2} := @OAI.KadisonKastler.exists_block_field_decomposition_oai.{u_1, u_2}
