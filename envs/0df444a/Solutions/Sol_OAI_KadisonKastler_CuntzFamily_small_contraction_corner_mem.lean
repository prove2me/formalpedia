-- Prove2me | solution 1 for OAI.KadisonKastler.CuntzFamily.small_contraction_corner_mem
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:57:46.902649+00:00
-- url     : https://prove2.me/submissions/05b69cdf-c318-482b-994d-3e80bf8642ef

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Torsion.Field
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
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Completion
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
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Extend
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
import Mathlib.Data.Fintype.BigOperators
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
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveCountable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
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
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K032

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CuntzMatrices
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Matrix amplification using common isometries

A finite Cuntz family gives an actual star equivalence between the ambient
operator algebra and its matrix amplification. If its isometries belong to
two concrete algebras, the same equivalence identifies both matrix unit
balls with their original unit balls.
-/

namespace KadisonKastler

open scoped BigOperators CStarAlgebra

noncomputable section

variable {H n : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Fintype n] [DecidableEq n]

namespace CuntzFamily

attribute [local instance] OAI.KadisonKastler.CuntzFamily.instStarOrderedRingContinuousLinearMapComplexId
variable (S : CuntzFamily n H)

theorem assemble_mem (M : VonNeumannAlgebra H) (hS : ∀ i, S.entry i ∈ M)
    (X : CStarMatrix n n (H →L[ℂ] H)) (hX : ∀ i j, X i j ∈ M) : S.assemble X ∈ M := by
  exact M.sum_mem fun i _ => M.sum_mem fun j _ =>
    M.mul_mem (M.mul_mem (hS i) (hX i j)) (M.toStarSubalgebra.star_mem' (hS j))

end CuntzFamily

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SmallContractionUnitaryAverage
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Small contractions as four-unitary averages

The half unit ball of a unital C-star algebra lies in the convex hull of
its unitaries. The explicit four-term formula is enough for the spatial
derivation argument; no unitary density theorem is required.
-/

namespace KadisonKastler

noncomputable section

open scoped ComplexStarModule

variable {A : Type*} [CStarAlgebra A]

theorem exists_four_unitaries_average (a : A) (ha : ‖a‖ ≤ 1 / 2) :
    ∃ u : Fin 4 → unitary A, a = (1 / 4 : ℝ) • ∑ i, (u i : A) := by
  let _ := CStarAlgebra.spectralOrder A
  let _ := CStarAlgebra.spectralOrderedRing A
  let b := (2 : ℝ) • a
  have hb : ‖b‖ ≤ 1 := by
    dsimp [b]
    rw [norm_smul, Real.norm_ofNat]
    linarith
  let u := selfAdjoint.unitarySelfAddISMul (ℜ b) ((realPart.norm_le b).trans hb)
  let v := selfAdjoint.unitarySelfAddISMul (ℑ b) ((imaginaryPart.norm_le b).trans hb)
  let iUnit : unitary ℂ := ⟨Complex.I, by simp [Unitary.mem_iff]⟩
  refine ⟨![u, star u, iUnit • v, iUnit • star v], ?_⟩
  have hu : (2⁻¹ : ℝ) • ((u : A) + star (u : A)) = (ℜ b : A) := by
    simpa only [realPart_apply_coe] using
      congrArg Subtype.val (selfAdjoint.realPart_unitarySelfAddISMul (ℜ b)
        ((realPart.norm_le b).trans hb))
  have hv : (2⁻¹ : ℝ) • ((v : A) + star (v : A)) = (ℑ b : A) := by
    simpa only [realPart_apply_coe] using
      congrArg Subtype.val (selfAdjoint.realPart_unitarySelfAddISMul (ℑ b)
        ((imaginaryPart.norm_le b).trans hb))
  have he := realPart_add_I_smul_imaginaryPart b
  rw [← hu, ← hv] at he
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Unitary.coe_star, Unitary.coe_smul]
  change a = (1 / 4 : ℝ) •
    ((u : A) + star (u : A) + Complex.I • (v : A) + Complex.I • star (v : A))
  calc
    a = (1 / 2 : ℝ) • b := by dsimp [b]; module
    _ = (1 / 2 : ℝ) • ((2⁻¹ : ℝ) • ((u : A) + star (u : A)) +
        Complex.I • (2⁻¹ : ℝ) • ((v : A) + star (v : A))) := congrArg _ he.symm
    _ = _ := by module

theorem map_small_contraction_mem_convex {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : A →ₗ[ℝ] E) (s : Set E) (hs : Convex ℝ s)
    (hu : ∀ u : unitary A, f (u : A) ∈ s)
    (a : A) (ha : ‖a‖ ≤ 1 / 2) : f a ∈ s := by
  obtain ⟨u, he⟩ := exists_four_unitaries_average a ha
  rw [he, map_smul, map_sum]
  have h := hs.sum_mem (t := Finset.univ) (w := fun _ : Fin 4 => (1 / 4 : ℝ))
    (z := fun i => f (u i : A)) (by intros; norm_num) (by norm_num)
    (fun i _ => hu (u i))
  simpa only [← Finset.smul_sum] using h

theorem mul_small_contractions_mem_convex {B : Type*} [CStarAlgebra B]
    (φ : A →ₐ[ℝ] B) (c : B) (s : Set B) (hs : Convex ℝ s)
    (hu : ∀ u v : unitary A, φ (u : A) * c * φ (v : A) ∈ s)
    (a b : A) (ha : ‖a‖ ≤ 1 / 2) (hb : ‖b‖ ≤ 1 / 2) :
    φ a * c * φ b ∈ s := by
  have hright (u : unitary A) : φ (u : A) * c * φ b ∈ s := by
    let f : A →ₗ[ℝ] B := {
      toFun x := φ (u : A) * c * φ x
      map_add' x y := by simp only [map_add, mul_add]
      map_smul' t x := by simp only [map_smul, mul_smul_comm, RingHom.id_apply] }
    exact map_small_contraction_mem_convex f s hs (hu u) b hb
  let f : A →ₗ[ℝ] B := {
    toFun x := φ x * c * φ b
    map_add' x y := by simp only [map_add, add_mul]
    map_smul' t x := by simp only [map_smul, smul_mul_assoc, RingHom.id_apply] }
  exact map_small_contraction_mem_convex f s hs hright a ha

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixCornerConjugation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.ScalarInvariantMean.conjugationFamily_apply _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.StandardTracialPosition.conjugation_algebraVector _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.productBoundaryRepresentation_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.rescaledGraphMap_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Independent unitary actions on an off-diagonal corner

Two orthogonal isometries identify the ambient algebra with its two-by-two
amplification. Block-diagonal conjugations then act independently on the
two sides of an off-diagonal coefficient. Convexity extends this action
to multiplication by small contractions.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace CuntzFamily

variable (S : CuntzFamily (Fin 2) H)

theorem matrixEquiv_symm_eq_assemble (X : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H)) :
    S.matrixEquiv.symm X = S.assemble X := by
  apply S.matrixEquiv.injective
  exact (S.matrixEquiv.apply_symm_apply X).trans (S.matrix_assemble X).symm

theorem matrix_liftedTwoBlockUnitary (u v : unitary (H →L[ℂ] H)) :
    S.matrix (S.liftedTwoBlockUnitary u v : H →L[ℂ] H) =
      blockDiagonal (u : H →L[ℂ] H) (v : H →L[ℂ] H) :=
  S.matrixEquiv.apply_symm_apply (twoBlockUnitary u v)

theorem liftedTwoBlockUnitary_mem (N : VonNeumannAlgebra H)
    (hS : ∀ i, S.entry i ∈ N) (u v : unitary (H →L[ℂ] H))
    (hu : (u : H →L[ℂ] H) ∈ N) (hv : (v : H →L[ℂ] H) ∈ N) :
    (S.liftedTwoBlockUnitary u v : H →L[ℂ] H) ∈ N := by
  change S.matrixEquiv.symm (twoBlockUnitary u v) ∈ N
  rw [S.matrixEquiv_symm_eq_assemble]
  apply S.assemble_mem N hS
  intro i j
  change blockDiagonal (u : H →L[ℂ] H) (v : H →L[ℂ] H) i j ∈ N
  fin_cases i <;> fin_cases j
  · exact hu
  · exact N.zero_mem
  · exact N.zero_mem
  · exact hv

theorem exists_corner_conjugate (N : VonNeumannAlgebra H)
    (hS : ∀ i, S.entry i ∈ N) (T : H →L[ℂ] H)
    (u v : unitary (Algebra N)) :
    ∃ w : unitary (Algebra N),
      S.matrix (unitaryConj (ambientAlgebraUnitary w) T) 0 1 =
        (u : Algebra N).val * S.matrix T 0 1 * (v : Algebra N).val := by
  let U : unitary (H →L[ℂ] H) := ambientAlgebraUnitary u
  let V : unitary (H →L[ℂ] H) := ambientAlgebraUnitary (star v)
  let d : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H) :=
    blockDiagonal (U : H →L[ℂ] H) (V : H →L[ℂ] H)
  let W : unitary (H →L[ℂ] H) := S.liftedTwoBlockUnitary U V
  have hW : (W : H →L[ℂ] H) ∈ N := S.liftedTwoBlockUnitary_mem N hS U V
    (u : Algebra N).property (star v : Algebra N).property
  refine ⟨algebraUnitaryOfMem W hW, ?_⟩
  have hWmat : S.matrix (W : H →L[ℂ] H) = d := S.matrix_liftedTwoBlockUnitary U V
  have he : S.matrix (unitaryConj W T) =
      d * S.matrix T * star d := by
    change S.matrixHom ((W : H →L[ℂ] H) * T * star (W : H →L[ℂ] H)) = _
    rw [map_mul, map_mul, map_star]
    change S.matrix _ * S.matrix T * star (S.matrix _) = _
    rw [hWmat]
  change S.matrix (unitaryConj W T) 0 1 = _
  rw [he]
  simp [d, U, V, ambientAlgebraUnitary, blockDiagonal, diagonalStarAlgHom_apply,
    CStarMatrix.mul_apply, CStarMatrix.star_apply, Fin.sum_univ_two, mul_assoc]

theorem small_contraction_corner_mem_oai (N : VonNeumannAlgebra H)
    (hS : ∀ i, S.entry i ∈ N) (K : Set (H →L[ℂ] H)) (hK : Convex ℝ K)
    (hinv : ∀ w : unitary (Algebra N), ∀ T ∈ K,
      unitaryConj (ambientAlgebraUnitary w) T ∈ K)
    (T : H →L[ℂ] H) (hT : T ∈ K)
    (a b : Algebra N) (ha : ‖a‖ ≤ 1 / 2) (hb : ‖b‖ ≤ 1 / 2) :
    ∃ V ∈ K, S.matrix V 0 1 = a.val * S.matrix T 0 1 * b.val := by
  let L := S.upperRightLinearMap
  have hc : Convex ℝ (L '' K) := hK.linear_image L
  have hu (u v : unitary (Algebra N)) :
      (u : Algebra N).val * S.matrix T 0 1 * (v : Algebra N).val ∈ L '' K := by
    obtain ⟨w, hw⟩ := S.exists_corner_conjugate N hS T u v
    exact ⟨_, hinv w T hT, hw⟩
  have hm := mul_small_contractions_mem_convex
    (N.toStarSubalgebra.subtype.toAlgHom.restrictScalars ℝ) (S.matrix T 0 1)
    (L '' K) hc hu a b ha hb
  exact hm

end CuntzFamily

end

end KadisonKastler

end OAI
end

theorem solution.{u_2} : type_of% @OAI.KadisonKastler.CuntzFamily.small_contraction_corner_mem_oai.{u_2} := @OAI.KadisonKastler.CuntzFamily.small_contraction_corner_mem_oai.{u_2}
