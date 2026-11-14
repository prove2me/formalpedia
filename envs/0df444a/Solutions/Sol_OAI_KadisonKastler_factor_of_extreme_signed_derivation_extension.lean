-- Prove2me | solution 1 for OAI.KadisonKastler.factor_of_extreme_signed_derivation_extension
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:51:58.142722+00:00
-- url     : https://prove2.me/submissions/90541b37-6426-4956-b3cb-6cd809d393a7

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
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Spectrum
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
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
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.Data.Set.Pairwise.Chain
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
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
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Tactic
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
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Discrete
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
import Definitions.Def_Q260K027

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CenterAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Recovering scalar centre from central projections

The centre is represented as the intersection with the concrete commutant.
Spectral approximation in this von Neumann algebra reduces scalarity of its
whole algebra to triviality of its projections.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Spectral approximation upgrades trivial central projections to scalar
centre. No finiteness or trace is needed for this upgrade. -/
theorem scalar_center_of_trivial_central_projections (N : VonNeumannAlgebra H)
    (hproj : ∀ q : Algebra N, IsStarProjection q →
      (∀ a : Algebra N, a * q = q * a) → q = 0 ∨ q = 1)
    (c : Algebra N) (hc : ∀ a : Algebra N, a * c = c * a) :
    ∃ z : ℂ, c = z • (1 : Algebra N) := by
  let C := concreteCenter N
  let inc : Algebra C →⋆ₐ[ℂ] Algebra N := StarSubalgebra.inclusion (show
      C.toStarSubalgebra ≤ N.toStarSubalgebra from fun _ hx => hx.1)
  have hinj : Function.Injective inc := StarSubalgebra.inclusion_injective _
  let cC : Algebra C := ⟨c.val, c.property, by
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro a ha
    exact congrArg Subtype.val (hc ⟨a, ha⟩)⟩
  let p : Generator.Tracial.AlgebraProjection C := ⟨1, IsStarProjection.one _⟩
  have hmin : ∀ q : Generator.Tracial.AlgebraProjection C, q ≤ p → q.val = 0 ∨ q.val = p.val := by
    intro q _
    have hq : IsStarProjection (inc q.val) := q.property.map inc
    have hqc : ∀ a : Algebra N, a * inc q.val = inc q.val * a := by
      intro a
      apply Subtype.ext
      exact VonNeumannAlgebra.mem_commutant_iff.mp q.val.property.2 a.val a.property
    rcases hproj (inc q.val) hq hqc with h | h
    · left
      apply hinj
      change inc q.val = inc 0
      rw [map_zero]
      exact h
    · right
      apply hinj
      change inc q.val = inc 1
      rw [map_one]
      exact h
  obtain ⟨z, hz⟩ := Generator.Tracial.corner_scalar_of_projections p hmin cC
    (by change 1 * cC = cC; exact one_mul _) (by change cC * 1 = cC; exact mul_one _)
  refine ⟨z, ?_⟩
  have he := congrArg (fun x : Algebra C => (x : H →L[ℂ] H)) hz
  exact Subtype.ext he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DerivationStarReduction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Reduction to anti-star derivations

Sakai's spatial construction treats derivations satisfying
`D (star x) = -star (D x)`. Every bounded complex derivation is a complex
linear combination of two such derivations. That decomposition transfers innerness from anti-star derivations
to arbitrary bounded complex derivations.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

/-- A derivation vanishes on an idempotent which commutes with its image.
In particular it vanishes on every central projection. -/
theorem derivation_central_idempotent_eq_zero (D : A →L[ℂ] A)
    (hD : ∀ x y, D (x * y) = D x * y + x * D y)
    (p : A) (hp : p * p = p) (hc : Commute p (D p)) : D p = 0 := by
  have hleft : p * (D p * p) = p * D p := by
    calc
      p * (D p * p) = (p * D p) * p := (mul_assoc _ _ _).symm
      _ = (D p * p) * p := congrArg (fun a => a * p) hc.eq
      _ = D p * (p * p) := mul_assoc _ _ _
      _ = D p * p := by rw [hp]
      _ = p * D p := hc.eq.symm
  have hright : p * (p * D p) = p * D p := by rw [← mul_assoc, hp]
  have htwice : p * D p = p * D p + p * D p := by
    calc
      p * D p = p * D (p * p) := by rw [hp]
      _ = p * (D p * p + p * D p) := congrArg (fun a => p * a) (hD p p)
      _ = p * D p + p * D p := by rw [mul_add, hleft, hright]
  have hz : p * D p = 0 := by
    have h : p * D p + 0 = p * D p + p * D p := by simpa using htwice
    exact (add_left_cancel h).symm
  calc
    D p = D p * p + p * D p := by simpa only [hp] using hD p p
    _ = p * D p + p * D p := by rw [hc.eq]
    _ = 0 := by rw [hz, zero_add]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialDerivationClosure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spatial derivations pass to the bicommutant

Kaplansky's constructed bounded net transfers commutator membership to
the represented closure. Central projections in that closure therefore
commute with the spatial implementer.
-/

namespace KadisonKastler

noncomputable section

open Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem spatial_commutator_mem_generated_contraction
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hS : ∀ a : S, T * a.val - a.val * T ∈ generatedVonNeumannAlgebra S)
    (b : H →L[ℂ] H) (hb : b ∈ generatedVonNeumannAlgebra S) (hbn : ‖b‖ ≤ 1) :
    T * b - b * T ∈ generatedVonNeumannAlgebra S := by
  classical
  have hb' : b ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
    rwa [← generatedVonNeumannAlgebra_coe]
  obtain ⟨a, _, ht⟩ := publishedKaplanskyDensity.exists_strong_contraction_net S b hb' hbn
  let c (d : Finset H × ℕ) : Algebra (generatedVonNeumannAlgebra S) :=
    ⟨T * (a d).val - (a d).val * T, hS (a d)⟩
  apply Generator.Tracial.weak_operator_limit_mem (ι := Finset H × ℕ) (l := atTop)
    (generatedVonNeumannAlgebra S) c
    (T * b - b * T)
  intro ξ η
  have hlim : Tendsto (fun d => T ((a d).val ξ) - (a d).val (T ξ)) atTop
      (𝓝 (T (b ξ) - b (T ξ))) :=
    (T.continuous.tendsto _ |>.comp (ht ξ)).sub (ht (T ξ))
  exact (tendsto_const_nhds : Tendsto (fun _ : Finset H × ℕ => η) atTop (𝓝 η)).inner
    (𝕜 := ℂ) hlim

theorem spatial_commutator_central_projection
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hS : ∀ a : S, T * a.val - a.val * T ∈ generatedVonNeumannAlgebra S)
    (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (hpN : p ∈ generatedVonNeumannAlgebra S)
    (hc : ∀ a ∈ generatedVonNeumannAlgebra S, Commute p a) : Commute T p := by
  let D : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
    { toFun := fun x => T * x - x * T
      map_add' := by intro x y; noncomm_ring
      map_smul' := by
        intro c x
        simp only [RingHom.id_apply, mul_smul_comm, smul_mul_assoc, smul_sub]
      cont := (continuous_const.mul continuous_id).sub (continuous_id.mul continuous_const) }
  have hD : ∀ x y, D (x * y) = D x * y + x * D y := by
    intro x y
    change T * (x * y) - (x * y) * T =
      (T * x - x * T) * y + x * (T * y - y * T)
    noncomm_ring
  have hmem := spatial_commutator_mem_generated_contraction S T hS p hpN (hp.norm_le _)
  have hzero := derivation_central_idempotent_eq_zero D hD p
    hp.isIdempotentElem.eq (hc _ hmem)
  exact sub_eq_zero.mp hzero

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DerivationExtensionFactor
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Factoriality in Sakai's one-implementer extension

In an irreducible representation of the algebra generated by the source
and its self-adjoint spatial implementer, every central projection of the
source bicommutant commutes with all generators. It is therefore trivial.
-/

namespace KadisonKastler

noncomputable section

variable {A B H : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.derivationExtensionFactorInstance1
local instance derivationExtensionFactorInstance2 : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

theorem commutes_of_normGeneratedExtension
    (φ : A →⋆ₐ[ℂ] B) (d : B) (hgen : NormGeneratedExtension φ d)
    (ρ : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (p : H →L[ℂ] H)
    (hp : IsSelfAdjoint p)
    (hA : ∀ a, Commute p (ρ (φ a))) (hd : Commute p (ρ d)) :
    ∀ b, Commute p (ρ b) := by
  let C := (StarSubalgebra.centralizer ℂ ({p} : Set (H →L[ℂ] H))).comap ρ
  have hmem (b : B) : b ∈ C ↔ Commute p (ρ b) := by
    change ρ b ∈ StarSubalgebra.centralizer ℂ ({p} : Set (H →L[ℂ] H)) ↔ _
    simp only [StarSubalgebra.mem_centralizer_iff, Set.mem_singleton_iff,
      forall_eq, hp.star_eq]
    exact ⟨fun h => h.1, fun h => ⟨h, h⟩⟩
  have hclosed : IsClosed (C : Set B) := by
    have he : (C : Set B) = {b | p * ρ b = ρ b * p} := by
      ext b
      exact (hmem b).trans Iff.rfl
    rw [he]
    exact isClosed_eq (continuous_const.mul (show Continuous ρ by fun_prop))
      ((show Continuous ρ by fun_prop).mul continuous_const)
  have htop := hgen C hclosed (fun a => (hmem _).mpr (hA a)) ((hmem _).mpr hd)
  intro b
  apply (hmem b).mp
  rw [htop]
  trivial

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ExtremeHermitianSplit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A norm-budgeted splitting of an extreme Hermitian annihilator

The compression argument splits an extreme functional into two Hermitian
annihilators with complementary norm bounds. Extremality determines each
summand from that norm budget.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem scaled_hermitian_mem_annihilator_ball
    (φ : A →⋆ₐ[ℂ] B) (F : B →L[ℂ] ℂ) (t : ℝ) (ht : 0 < t)
    (hn : ‖F‖ ≤ t) (hstar : ∀ b, F (star b) = star (F b))
    (hann : ∀ a, F (φ a) = 0) :
    StrongDual.toWeakDual (t⁻¹ • F) ∈ hermitianAnnihilatorBall φ := by
  refine ⟨?_, ?_, ?_⟩
  · change ‖t⁻¹ • F‖ ≤ 1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht.le)]
    exact (mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr ht.le)).trans_eq
      (inv_mul_cancel₀ ht.ne')
  · intro b
    change t⁻¹ • F (star b) = star (t⁻¹ • F b)
    rw [hstar]
    simp only [star_smul, star_trivial]
  · intro a
    change t⁻¹ • F (φ a) = 0
    rw [hann, smul_zero]

theorem extreme_hermitian_split
    (φ : A →⋆ₐ[ℂ] B) (F : WeakDual ℂ B)
    (hF : F ∈ (hermitianAnnihilatorBall φ).extremePoints ℝ)
    (G H : B →L[ℂ] ℂ) (t s : ℝ) (ht : 0 < t) (hs : 0 < s) (hts : t + s = 1)
    (hG : ‖G‖ ≤ t) (hH : ‖H‖ ≤ s)
    (hGs : ∀ b, G (star b) = star (G b)) (hHs : ∀ b, H (star b) = star (H b))
    (hGa : ∀ a, G (φ a) = 0) (hHa : ∀ a, H (φ a) = 0)
    (heq : G + H = F.toStrongDual) : G = t • F.toStrongDual := by
  let g := StrongDual.toWeakDual (t⁻¹ • G)
  let h := StrongDual.toWeakDual (s⁻¹ • H)
  have hg : g ∈ hermitianAnnihilatorBall φ :=
    scaled_hermitian_mem_annihilator_ball φ G t ht hG hGs hGa
  have hh : h ∈ hermitianAnnihilatorBall φ :=
    scaled_hermitian_mem_annihilator_ball φ H s hs hH hHs hHa
  have hseg : F ∈ openSegment ℝ g h := by
    refine ⟨t, s, ht, hs, hts, ?_⟩
    apply WeakDual.toStrongDual.injective
    change t • (t⁻¹ • G) + s • (s⁻¹ • H) = F.toStrongDual
    rw [smul_smul, smul_smul, mul_inv_cancel₀ ht.ne', mul_inv_cancel₀ hs.ne',
      one_smul, one_smul]
    exact heq
  have hgf := (mem_extremePoints.mp hF).2 g hg h hh hseg |>.1
  have he : t⁻¹ • G = F.toStrongDual := congrArg WeakDual.toStrongDual hgf
  calc
    G = t • (t⁻¹ • G) := by rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    _ = t • F.toStrongDual := congrArg (fun K : B →L[ℂ] ℂ => t • K) he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SignedFunctionalCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Compression identities for signed vector functionals -/

namespace KadisonKastler

noncomputable section

open HochschildNormalPart
open scoped InnerProductSpace

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem selfAdjoint_involution_norm (S : H →L[ℂ] H) (hS : IsSelfAdjoint S)
    (hSS : S * S = 1) (ξ : H) : ‖S ξ‖ = ‖ξ‖ := by
  have he : S (S ξ) = ξ := congrArg (fun T : H →L[ℂ] H => T ξ) hSS
  have hi : inner ℂ (S ξ) (S ξ) = inner ℂ ξ ξ := by
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
      hS.star_eq, he]
  have hn : ‖S ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
    calc
      ‖S ξ‖ ^ 2 = (inner ℂ (S ξ) (S ξ)).re :=
        (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
      _ = (inner ℂ ξ ξ).re := congrArg Complex.re hi
      _ = ‖ξ‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  nlinarith [norm_nonneg (S ξ), norm_nonneg ξ]

theorem signedVectorFunctional_norm_le (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSS : S * S = 1) (ξ : H) :
    ‖signedVectorFunctional π S ξ‖ ≤ ‖ξ‖ ^ 2 := by
  simpa only [signedVectorFunctional, selfAdjoint_involution_norm S hS hSS ξ, pow_two]
    using coefficient_norm π (S ξ) ξ

theorem signedVectorFunctional_star (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hcomm : ∀ a, Commute S (π a))
    (ξ : H) (a : A) :
    signedVectorFunctional π S ξ (star a) = star (signedVectorFunctional π S ξ a) := by
  have hc : S (π a ξ) = π a (S ξ) :=
    congrArg (fun T : H →L[ℂ] H => T ξ) (hcomm a).eq
  change inner ℂ (S ξ) (π (star a) ξ) = star (inner ℂ (S ξ) (π a ξ))
  calc
    inner ℂ (S ξ) (π (star a) ξ) = inner ℂ (π a (S ξ)) ξ := by
      rw [map_star, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_right]
    _ = inner ℂ (S (π a ξ)) ξ := by rw [hc]
    _ = inner ℂ (π a ξ) (S ξ) := by
      rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
        hS.star_eq]
    _ = star (inner ℂ (S ξ) (π a ξ)) := (inner_conj_symm _ _).symm

theorem signedVectorFunctional_projection (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (S p : H →L[ℂ] H) (hp : IsStarProjection p)
    (hSp : Commute p S) (hpp : ∀ a, Commute p (π a)) (ξ : H) (a : A) :
    signedVectorFunctional π S (p ξ) a = inner ℂ (S ξ) (π a (p ξ)) := by
  have hSpξ : S (p ξ) = p (S ξ) :=
    (congrArg (fun T : H →L[ℂ] H => T ξ) hSp.eq).symm
  have hppξ : p (π a (p ξ)) = π a (p ξ) := by
    have hc := congrArg (fun T : H →L[ℂ] H => T (p ξ)) (hpp a).eq
    change p (π a (p ξ)) = π a (p (p ξ)) at hc
    have he : p (p ξ) = p ξ :=
      congrArg (fun T : H →L[ℂ] H => T ξ) hp.isIdempotentElem.eq
    rwa [he] at hc
  change inner ℂ (S (p ξ)) (π a (p ξ)) = _
  have hi (u v : H) : inner ℂ (p u) v = inner ℂ u (p v) := by
    simpa only [← ContinuousLinearMap.star_eq_adjoint, hp.isSelfAdjoint.star_eq] using
      p.adjoint_inner_left v u
  rw [hSpξ, hi, hppξ]

theorem signedVectorFunctional_split_projection (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (S p : H →L[ℂ] H) (hp : IsStarProjection p)
    (hSp : Commute p S) (hpp : ∀ a, Commute p (π a)) (ξ : H) :
    signedVectorFunctional π S ξ = signedVectorFunctional π S (p ξ) +
      signedVectorFunctional π S ((1 - p) ξ) := by
  have hqS : Commute (1 - p) S := by
    change (1 - p) * S = S * (1 - p)
    rw [sub_mul, mul_sub, one_mul, mul_one, hSp.eq]
  have hqp (a : A) : Commute (1 - p) (π a) := by
    change (1 - p) * π a = π a * (1 - p)
    rw [sub_mul, mul_sub, one_mul, mul_one, (hpp a).eq]
  ext a
  rw [add_apply, signedVectorFunctional_projection π S p hp hSp hpp,
    signedVectorFunctional_projection π S (1 - p) hp.one_sub hqS hqp]
  change inner ℂ (S ξ) (π a ξ) = _
  rw [← inner_add_right, ← map_add]
  congr 2
  change ξ = p ξ + (ξ - p ξ)
  abel

theorem norm_sq_projection_add_complement (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (ξ : H) : ‖p ξ‖ ^ 2 + ‖(1 - p) ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
  have hz : p * (1 - p) = 0 := by
    rw [mul_sub, mul_one, hp.isIdempotentElem.eq, sub_self]
  have hi : inner ℂ (p ξ) ((1 - p) ξ) = 0 := by
    calc
      inner ℂ (p ξ) ((1 - p) ξ) = inner ℂ ξ (p ((1 - p) ξ)) := by
        simpa only [← ContinuousLinearMap.star_eq_adjoint, hp.isSelfAdjoint.star_eq] using
          p.adjoint_inner_left ((1 - p) ξ) ξ
      _ = 0 := by
        have he : p ((1 - p) ξ) = 0 :=
          congrArg (fun T : H →L[ℂ] H => T ξ) hz
        rw [he, inner_zero_right]
  have he : p ξ + (1 - p) ξ = ξ := by
    change p ξ + (ξ - p ξ) = ξ
    abel
  have hn := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (p ξ) ((1 - p) ξ) hi
  rw [he] at hn
  simpa only [pow_two] using hn.symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialCoefficientClosure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Vanishing vector coefficients pass to the bicommutant -/

namespace KadisonKastler

noncomputable section

open Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem coefficient_zero_generated_contraction
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ η : H)
    (hzero : ∀ a : S, inner ℂ η (a.val ξ) = 0)
    (b : H →L[ℂ] H) (hb : b ∈ generatedVonNeumannAlgebra S) (hbn : ‖b‖ ≤ 1) :
    inner ℂ η (b ξ) = 0 := by
  classical
  have hb' : b ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
    rwa [← generatedVonNeumannAlgebra_coe]
  obtain ⟨a, _, ht⟩ := publishedKaplanskyDensity.exists_strong_contraction_net S b hb' hbn
  have hlim := (tendsto_const_nhds : Tendsto (fun _ : Finset H × ℕ => η) atTop (𝓝 η)).inner
    (𝕜 := ℂ) (ht ξ)
  have he : (fun d : Finset H × ℕ => inner ℂ η ((a d).val ξ)) = fun _ => 0 :=
    funext (fun d => hzero (a d))
  rw [he] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

theorem coefficient_zero_generated
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ η : H)
    (hzero : ∀ a : S, inner ℂ η (a.val ξ) = 0)
    (b : H →L[ℂ] H) (hb : b ∈ generatedVonNeumannAlgebra S) :
    inner ℂ η (b ξ) = 0 := by
  let c : ℝ := ‖b‖ + 1
  have hc : 0 < c := by dsimp [c] <;> positivity
  have hb' : (c⁻¹ : ℝ) • b ∈ generatedVonNeumannAlgebra S :=
    ((generatedVonNeumannAlgebra S).toStarSubalgebra.toSubalgebra.toSubmodule.restrictScalars
      ℝ).smul_mem c⁻¹ hb
  have hn : ‖(c⁻¹ : ℝ) • b‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le)]
    rw [← div_eq_inv_mul]
    exact (div_le_one hc).mpr (by dsimp [c] <;> linarith)
  have hz := coefficient_zero_generated_contraction S ξ η hzero _ hb' hn
  change inner ℂ η ((c⁻¹ : ℝ) • b ξ) = 0 at hz
  rw [inner_smul_right_eq_smul] at hz
  exact (smul_eq_zero.mp hz).resolve_left (inv_ne_zero hc.ne')

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ExtremeSignedProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # An extreme signed separator has no nontrivial commuting source projection -/

namespace KadisonKastler

noncomputable section

open scoped InnerProductSpace

variable {A B H : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem commuting_operator_zero_of_cyclic (π : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ξ : H) (hcyc : DenseRange (fun b => π b ξ)) (p : H →L[ℂ] H)
    (hp : ∀ b, Commute p (π b)) (hpξ : p ξ = 0) : p = 0 := by
  have he : (fun x : H => p x) = fun _ => 0 := by
    apply hcyc.equalizer p.continuous continuous_const
    funext b
    change p (π b ξ) = 0
    have h := congrArg (fun T : H →L[ℂ] H => T ξ) (hp b).eq
    change p (π b ξ) = π b (p ξ) at h
    simpa only [hpξ, map_zero] using h
  exact ContinuousLinearMap.ext (fun x => congrFun he x)

theorem signedVectorFunctional_projection_left
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (S p : H →L[ℂ] H) (hp : IsStarProjection p)
    (hSp : Commute p S) (hpp : ∀ b, Commute p (π b)) (ξ : H) (b : B) :
    signedVectorFunctional π S (p ξ) b = inner ℂ (S (p ξ)) (π b ξ) := by
  rw [signedVectorFunctional_projection π S p hp hSp hpp]
  have hSpξ : S (p ξ) = p (S ξ) :=
    (congrArg (fun T : H →L[ℂ] H => T ξ) hSp.eq).symm
  have hpb : p (π b ξ) = π b (p ξ) :=
    congrArg (fun T : H →L[ℂ] H => T ξ) (hpp b).eq
  rw [hSpξ]
  have hi : inner ℂ (p (S ξ)) (π b ξ) = inner ℂ (S ξ) (p (π b ξ)) := by
    simpa only [← ContinuousLinearMap.star_eq_adjoint, hp.isSelfAdjoint.star_eq] using
      p.adjoint_inner_left (π b ξ) (S ξ)
  rw [hi, hpb]

theorem extreme_signed_projection_trivial
    (φ : A →⋆ₐ[ℂ] B) (F : WeakDual ℂ B)
    (hF : F ∈ (hermitianAnnihilatorBall φ).extremePoints ℝ)
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (hξ : ‖ξ‖ = 1)
    (hcyc : DenseRange (fun b => π b ξ))
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSS : S * S = 1)
    (hSπ : ∀ b, Commute S (π b)) (hrep : F.toStrongDual = signedVectorFunctional π S ξ)
    (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (hpπ : ∀ b, Commute p (π b)) (hpS : Commute p S)
    (hpN : p ∈ generatedVonNeumannAlgebra (π.comp φ).range) : p = 0 ∨ p = 1 := by
  let N := generatedVonNeumannAlgebra (π.comp φ).range
  have hsource : ∀ a : (π.comp φ).range, inner ℂ (S ξ) (a.val ξ) = 0 := by
    intro a
    obtain ⟨b, hb⟩ := a.property
    have hz := (mem_extremePoints.mp hF).1.2.2 b
    change F.toStrongDual (φ b) = 0 at hz
    rw [hrep] at hz
    change inner ℂ (S ξ) (π (φ b) ξ) = 0 at hz
    change π (φ b) = a.val at hb
    rwa [← hb]
  have hann (q : H →L[ℂ] H) (hq : IsStarProjection q)
      (hqπ : ∀ b, Commute q (π b)) (hqS : Commute q S) (hqN : q ∈ N) :
      ∀ a, signedVectorFunctional π S (q ξ) (φ a) = 0 := by
    intro a
    rw [signedVectorFunctional_projection π S q hq hqS hqπ]
    exact coefficient_zero_generated (π.comp φ).range ξ (S ξ) hsource (π (φ a) * q)
      (N.mul_mem (subset_generatedVonNeumannAlgebra (π.comp φ).range ⟨a, rfl⟩) hqN)
  have hqπ (b : B) : Commute (1 - p) (π b) := by
    change (1 - p) * π b = π b * (1 - p)
    rw [sub_mul, mul_sub, one_mul, mul_one, (hpπ b).eq]
  have hqS : Commute (1 - p) S := by
    change (1 - p) * S = S * (1 - p)
    rw [sub_mul, mul_sub, one_mul, mul_one, hpS.eq]
  have hqN : 1 - p ∈ N := N.sub_mem N.one_mem hpN
  let t : ℝ := ‖p ξ‖ ^ 2
  let s : ℝ := ‖(1 - p) ξ‖ ^ 2
  have hts : t + s = 1 := by
    simpa only [t, s, hξ, one_pow] using norm_sq_projection_add_complement p hp ξ
  by_cases ht0 : t = 0
  · left
    apply commuting_operator_zero_of_cyclic π ξ hcyc p hpπ
    apply norm_eq_zero.mp
    dsimp [t] at ht0
    nlinarith [norm_nonneg (p ξ)]
  by_cases hs0 : s = 0
  · right
    have he : 1 - p = 0 := by
      apply commuting_operator_zero_of_cyclic π ξ hcyc (1 - p) hqπ
      apply norm_eq_zero.mp
      dsimp [s] at hs0
      nlinarith [norm_nonneg ((1 - p) ξ)]
    exact (sub_eq_zero.mp he).symm
  exfalso
  have ht : 0 < t := lt_of_le_of_ne (sq_nonneg _) (Ne.symm ht0)
  have hs : 0 < s := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hs0)
  let G := signedVectorFunctional π S (p ξ)
  let K := signedVectorFunctional π S ((1 - p) ξ)
  have heq : G + K = F.toStrongDual :=
    (signedVectorFunctional_split_projection π S p hp hpS hpπ ξ).symm.trans hrep.symm
  have hG : G = t • F.toStrongDual :=
    extreme_hermitian_split φ F hF G K t s ht hs hts
      (signedVectorFunctional_norm_le π S hS hSS _)
      (signedVectorFunctional_norm_le π S hS hSS _)
      (signedVectorFunctional_star π S hS hSπ _)
      (signedVectorFunctional_star π S hS hSπ _)
      (hann p hp hpπ hpS hpN) (hann (1 - p) hp.one_sub hqπ hqS hqN) heq
  have hinner (b : B) : inner ℂ (S (p ξ)) (π b ξ) = inner ℂ (t • S ξ) (π b ξ) := by
    rw [← signedVectorFunctional_projection_left π S p hp hpS hpπ ξ b]
    have he := congrArg (fun L : B →L[ℂ] ℂ => L b) hG
    rw [hrep] at he
    simpa only [G, smul_apply, signedVectorFunctional_apply, inner_smul_left_eq_smul] using he
  have hvec : S (p ξ) = t • S ξ := by
    apply ext_inner_right ℂ
    have he := hcyc.equalizer (continuous_const.inner continuous_id)
      (continuous_const.inner continuous_id) (funext hinner)
    exact fun y => congrFun he y
  have hSSv (v : H) : S (S v) = v := congrArg (fun T : H →L[ℂ] H => T v) hSS
  have hpξ : p ξ = t • ξ := by
    have he := congrArg S hvec
    have hlin : S (t • S ξ) = t • S (S ξ) := S.map_smul_of_tower t (S ξ)
    simpa only [hlin, hSSv] using he
  have hpn : ‖p ξ‖ = t := by
    rw [hpξ, norm_smul, Real.norm_of_nonneg ht.le, hξ, mul_one]
  have htt : t = t ^ 2 := by
    change ‖p ξ‖ ^ 2 = t ^ 2
    rw [hpn]
  nlinarith

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ExtremeDerivationFactor
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The factor lemma for an extreme derivation separator

This is the unital application of the factor lemma on p.261 of Sakai's
1971 paper. The signed cyclic representation is constructed separately;
central projections commute with the spatial derivation implementer,
so extremality forces them to be trivial.
-/

namespace KadisonKastler

noncomputable section

variable {A B H : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem factor_of_extreme_signed_derivation_extension_oai
    (φ : A →⋆ₐ[ℂ] B) (d : B) (hgen : NormGeneratedExtension φ d)
    (D : A →L[ℂ] A) (hd : ∀ a, φ (D a) = d * φ a - φ a * d)
    (F : WeakDual ℂ B) (hF : F ∈ (hermitianAnnihilatorBall φ).extremePoints ℝ)
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (hξ : ‖ξ‖ = 1)
    (hcyc : DenseRange (fun b => π b ξ))
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSS : S * S = 1)
    (hSπ : ∀ b, Commute S (π b)) (hrep : F.toStrongDual = signedVectorFunctional π S ξ) :
    ScalarCenter (generatedVonNeumannAlgebra (π.comp φ).range) := by
  let N := generatedVonNeumannAlgebra (π.comp φ).range
  have hcomm : ∀ a : (π.comp φ).range,
      π d * a.val - a.val * π d ∈ N := by
    intro a
    obtain ⟨x, hx⟩ := a.property
    change π (φ x) = a.val at hx
    rw [← hx, ← map_mul, ← map_mul, ← map_sub, ← hd]
    exact subset_generatedVonNeumannAlgebra (π.comp φ).range ⟨D x, rfl⟩
  have hproj : ∀ q : Algebra N, IsStarProjection q →
      (∀ a : Algebra N, a * q = q * a) → q = 0 ∨ q = 1 := by
    intro q hq hqc
    have hp : IsStarProjection q.val := hq.map N.toStarSubalgebra.subtype
    have hqp : ∀ a ∈ N, Commute q.val a := by
      intro a ha
      exact (congrArg Subtype.val (hqc ⟨a, ha⟩)).symm
    have hqd := (spatial_commutator_central_projection
      (π.comp φ).range (π d) hcomm q.val hp q.property hqp).symm
    have hqA : ∀ a, Commute q.val (π (φ a)) := by
      intro a
      exact hqp _ (subset_generatedVonNeumannAlgebra (π.comp φ).range ⟨a, rfl⟩)
    have hqB : ∀ b, Commute q.val (π b) :=
      commutes_of_normGeneratedExtension φ d hgen π q.val hp.isSelfAdjoint hqA hqd
    have hSin : S ∈ Set.centralizer ((π.comp φ).range : Set (H →L[ℂ] H)) := by
      rintro a ⟨b, hb⟩
      change π (φ b) = a at hb
      rw [← hb]
      exact (hSπ (φ b)).eq.symm
    have hqin : q.val ∈ Set.centralizer
        (Set.centralizer ((π.comp φ).range : Set (H →L[ℂ] H))) := by
      rw [← generatedVonNeumannAlgebra_coe]
      exact q.property
    have hqS : Commute q.val S := (hqin S hSin).symm
    exact (extreme_signed_projection_trivial φ F hF π ξ hξ hcyc S hS hSS hSπ hrep
      q.val hp hqB hqS q.property).imp Subtype.ext Subtype.ext
  intro T hTN hTc
  obtain ⟨z, hz⟩ := scalar_center_of_trivial_central_projections N hproj
    ⟨T, hTN⟩ (fun a => Subtype.ext (hTc a.val a.property))
  exact ⟨z, congrArg Subtype.val hz⟩

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.KadisonKastler.factor_of_extreme_signed_derivation_extension_oai.{u_1, u_2, u_3} := @OAI.KadisonKastler.factor_of_extreme_signed_derivation_extension_oai.{u_1, u_2, u_3}
