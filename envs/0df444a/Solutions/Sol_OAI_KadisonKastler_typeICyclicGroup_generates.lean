-- Prove2me | solution 1 for OAI.KadisonKastler.typeICyclicGroup_generates
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:26:19.540776+00:00
-- url     : https://prove2.me/submissions/e8164e09-8c03-479d-80c7-57ba7f3d582e

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
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Adjoint
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
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
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
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
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
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K033

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeICyclicGeneration
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Transporting weak generation through the minimal cyclic representation -/

namespace KadisonKastler

open Generator Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- The inverse minimal cyclic representation preserves the weak closure needed
for generation. The proof uses bounded approximation and weak compactness in
the original representation. -/
theorem typeICyclic_inverse_mem_of_generated_unitBall (hM : ScalarCenter M)
    (p : AlgebraProjection M) (hp : IsMinimalProjectionIn M p)
    (ξ : H) (hξ : ξ ≠ 0) (hpξ : p.val.val ξ = ξ)
    (Q : VonNeumannAlgebra H) (hQM : Q ≤ M)
    (A : StarSubalgebra ℂ (typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ))
    (hA : ∀ T ∈ A, ((typeICyclicEquiv hM p hp ξ hξ hpξ).symm T).val ∈ Q)
    (T : typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ)
    (hT : T ∈ generatedVonNeumannAlgebra A) (hnT : ‖T‖ ≤ 1) :
    ((typeICyclicEquiv hM p hp ξ hξ hpξ).symm T).val ∈ Q := by
  classical
  let K := typeICyclicSpace M ξ
  let e := typeICyclicEquiv hM p hp ξ hξ hpξ
  have hnet := publishedKaplanskyDensity.exists_weak_contraction_net (H := K)
    A T (by
      change T ∈ (generatedVonNeumannAlgebra A : Set _) at hT
      rwa [generatedVonNeumannAlgebra_coe] at hT) hnT
  let c : Finset K × ℕ → A := Classical.choose hnet
  have hc : ∀ d, ‖c d‖ ≤ 1 := (Classical.choose_spec hnet).1
  have hlim : ∀ x y : K, Tendsto (fun d => inner ℂ y ((c d).val x)) atTop
      (𝓝 (inner ℂ y (T x))) := (Classical.choose_spec hnet).2
  let a (d : Finset K × ℕ) : Algebra Q := ⟨(e.symm (c d).val).val, hA _ (c d).property⟩
  have hn (d : Finset K × ℕ) : ‖(a d).val‖ ≤ 1 := by
    change ‖e.symm (c d).val‖ ≤ 1
    rw [← typeICyclicHom_norm hM p hp ξ hξ hpξ]
    change ‖e (e.symm (c d).val)‖ ≤ 1
    rw [e.apply_symm_apply]
    exact hc d
  let ω : Ultrafilter (Finset K × ℕ) := Ultrafilter.of atTop
  obtain ⟨b, _, hb⟩ := exists_weak_operator_ultralimit ω (fun d => (a d).val)
    1 zero_le_one hn
  have hbQ : b ∈ Q := weak_operator_limit_mem Q a b hb
  let bM : Algebra M := ⟨b, hQM hbQ⟩
  have he : e bM = T := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    have h₁ : Tendsto (fun d => inner ℂ y ((c d).val x))
        (ω : Filter (Finset K × ℕ)) (𝓝 (inner ℂ y (e bM x))) := by
      have hb' := hb x.val y.val
      have hc_eval (d : Finset K × ℕ) :
          (e.symm (c d).val).val x.val = ((c d).val x : K).val := by
        change (e (e.symm (c d).val) x : H) = _
        rw [e.apply_symm_apply]
      change Tendsto (fun d => inner ℂ y.val ((e.symm (c d).val).val x.val))
        (ω : Filter (Finset K × ℕ)) (𝓝 (inner ℂ y.val (b x.val))) at hb'
      simp_rw [hc_eval] at hb'
      exact hb'
    exact tendsto_nhds_unique h₁ ((hlim x y).mono_left (Ultrafilter.of_le atTop))
  have he' : e.symm T = bM := by rw [← he, e.symm_apply_apply]
  change (e.symm T).val ∈ Q
  rw [he']
  exact hbQ

/-- Weak generation transports to the original type I representation. -/
theorem typeICyclic_inverse_mem_of_generated (hM : ScalarCenter M)
    (p : AlgebraProjection M) (hp : IsMinimalProjectionIn M p)
    (ξ : H) (hξ : ξ ≠ 0) (hpξ : p.val.val ξ = ξ)
    (Q : VonNeumannAlgebra H) (hQM : Q ≤ M)
    (A : StarSubalgebra ℂ (typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ))
    (hA : ∀ T ∈ A, ((typeICyclicEquiv hM p hp ξ hξ hpξ).symm T).val ∈ Q)
    (T : typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ)
    (hT : T ∈ generatedVonNeumannAlgebra A) :
    ((typeICyclicEquiv hM p hp ξ hξ hpξ).symm T).val ∈ Q := by
  let : CStarAlgebra (Algebra M) := {}
  let : CStarAlgebra (typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ) := {}
  let e := typeICyclicEquiv hM p hp ξ hξ hpξ
  by_cases hzero : T = 0
  · simp only [hzero, map_zero, ZeroMemClass.coe_zero]
    exact Q.zero_mem
  have hn : ‖T‖ ≠ 0 := by
    intro hn
    exact hzero (norm_eq_zero.mp hn)
  have hsmall : ‖(‖T‖ : ℂ)⁻¹ • T‖ ≤ 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg T), inv_mul_cancel₀ hn]
  have h := typeICyclic_inverse_mem_of_generated_unitBall hM p hp ξ hξ hpξ
    Q hQM A hA ((‖T‖ : ℂ)⁻¹ • T)
    ((generatedVonNeumannAlgebra A).toStarSubalgebra.smul_mem hT _) hsmall
  have hscale := Q.toStarSubalgebra.smul_mem h (‖T‖ : ℂ)
  have hnC : (‖T‖ : ℂ) ≠ 0 := by exact_mod_cast hn
  have hscale' : (e.symm ((‖T‖ : ℂ) • ((‖T‖ : ℂ)⁻¹ • T))).val ∈ Q := by
    change ((‖T‖ : ℂ) • e.symm ((‖T‖ : ℂ)⁻¹ • T)).val ∈ Q at hscale
    have hs := map_smul e.symm.toAlgEquiv.toLinearMap (‖T‖ : ℂ) ((‖T‖ : ℂ)⁻¹ • T)
    change e.symm ((‖T‖ : ℂ) • ((‖T‖ : ℂ)⁻¹ • T)) =
      (‖T‖ : ℂ) • e.symm ((‖T‖ : ℂ)⁻¹ • T) at hs
    rw [hs]
    exact hscale
  simpa only [smul_smul, mul_inv_cancel₀ hnC, one_smul] using hscale'


theorem typeICyclicGroup_generates_oai {G : Type*} [Group G] (hM : ScalarCenter M)
    (p : AlgebraProjection M) (hp : IsMinimalProjectionIn M p)
    (ξ : H) (hξ : ξ ≠ 0) (hpξ : p.val.val ξ = ξ)
    (U : G →* unitary (typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ))
    (hgen : ∀ T, T ∈ generatedVonNeumannAlgebra
      (StarAlgebra.adjoin ℂ (Set.range (fun g => (U g :
        typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ))))) :
    generatedVonNeumannAlgebra (StarAlgebra.adjoin ℂ (Set.range (fun g =>
      (typeICyclicGroup hM p hp ξ hξ hpξ U g : H →L[ℂ] H)))) = M := by
  let e := typeICyclicEquiv hM p hp ξ hξ hpξ
  let V := typeICyclicGroup hM p hp ξ hξ hpξ U
  let Q := generatedVonNeumannAlgebra
    (StarAlgebra.adjoin ℂ (Set.range (fun g => (V g : H →L[ℂ] H))))
  have hQM : Q ≤ M := by
    apply generatedVonNeumannAlgebra_le_of_le
    apply StarAlgebra.adjoin_le
    rintro _ ⟨g, rfl⟩
    exact (V g).val.property
  change Q = M
  apply le_antisymm hQM
  intro x hx
  let a : Algebra M := ⟨x, hx⟩
  have hA : ∀ T ∈ StarAlgebra.adjoin ℂ (Set.range (fun g => (U g :
        typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ))), (e.symm T).val ∈ Q := by
    let φ := M.toStarSubalgebra.subtype.comp e.symm.toStarAlgHom
    have ha : StarAlgebra.adjoin ℂ (Set.range (fun g => (U g :
        typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ))) ≤
        Q.toStarSubalgebra.comap φ := by
      apply StarAlgebra.adjoin_le
      rintro _ ⟨g, rfl⟩
      exact subset_generatedVonNeumannAlgebra _
        (StarAlgebra.subset_adjoin ℂ _ ⟨g, rfl⟩)
    exact fun T hT => ha hT
  have ht := typeICyclic_inverse_mem_of_generated hM p hp ξ hξ hpξ
    Q hQM _ hA (e a) (hgen (e a))
  change (e.symm (e a)).val ∈ Q at ht
  simpa only [e.symm_apply_apply] using ht

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.typeICyclicGroup_generates_oai.{u_1, u_2} := @OAI.KadisonKastler.typeICyclicGroup_generates_oai.{u_1, u_2}
