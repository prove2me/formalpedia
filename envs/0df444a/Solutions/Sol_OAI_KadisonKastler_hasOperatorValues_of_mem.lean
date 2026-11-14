-- Prove2me | solution 1 for OAI.KadisonKastler.hasOperatorValues_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:51:34.953513+00:00
-- url     : https://prove2.me/submissions/e78013d5-8ed8-4fea-9a01-f51e130e024c

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
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
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
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
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.WeakDual
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
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Basic
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
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K027

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StrongCommutantTests
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-- d13f23b's `TopologicalSpace.exists_countable_dense_subset` (port compat, absent from our Mathlib). -/
private theorem ecdsCompat_p1 {α : Type*} [TopologicalSpace α] (s : Set α) [TopologicalSpace.SeparableSpace s] :
    ∃ t : Set α, t.Countable ∧ t ⊆ s ∧ s ⊆ closure t := by
  obtain ⟨t, ct, dt⟩ := TopologicalSpace.exists_countable_dense s
  exact ⟨Subtype.val '' t, ct.image _, by simp, fun x hx ↦ closure_subtype.1 (dt ⟨x, hx⟩)⟩

/-! # Countable strong-operator tests for commutation

On a uniformly bounded set of operators, convergence on a countable dense
set of vectors implies convergence on every vector. A countable dense set
of coordinate sequences therefore supplies all commutant tests.
-/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Every contraction-valued set on a separable space has a countable
subset that approximates each of its elements strongly by a sequence. -/
theorem exists_countable_strong_dense_contractions [SeparableSpace H]
    (S : Set (H →L[ℂ] H)) (hS : ∀ T ∈ S, ‖T‖ ≤ 1) :
    ∃ E : Set (H →L[ℂ] H), E.Countable ∧ E ⊆ S ∧
      ∀ T ∈ S, ∃ A : ℕ → H →L[ℂ] H,
        (∀ n, A n ∈ E) ∧ ∀ ξ, Tendsto (fun n => A n ξ) atTop (𝓝 (T ξ)) := by
  obtain ⟨v, hv⟩ := exists_dense_seq (α := H)
  let coordinates : (H →L[ℂ] H) → ℕ → H := fun A n => A (v n)
  obtain ⟨D, hDc, hDsub, hDdense⟩ := ecdsCompat_p1 (coordinates '' S)
  choose lift hliftS hlift using fun z : D => hDsub z.property
  let E : Set (H →L[ℂ] H) := Set.range lift
  have hEc : E.Countable := by
    let := hDc.to_subtype
    exact Set.countable_range lift
  have hES : E ⊆ S := by
    rintro T ⟨z, rfl⟩
    exact hliftS z
  refine ⟨E, hEc, hES, ?_⟩
  intro T hT
  obtain ⟨z, hz, hzt⟩ := mem_closure_iff_seq_limit.mp (hDdense ⟨T, hT, rfl⟩)
  let A : ℕ → H →L[ℂ] H := fun n => lift ⟨z n, hz n⟩
  have hAE (n : ℕ) : A n ∈ E := ⟨⟨z n, hz n⟩, rfl⟩
  refine ⟨A, hAE, ?_⟩
  apply tendsto_apply_of_dense_contractions v hv A T
    (fun n => hS (A n) (hES (hAE n))) (hS T hT)
  intro j
  have ht := tendsto_pi_nhds.mp hzt j
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  exact congrFun (hlift ⟨z n, hz n⟩) j

/-- Commutation with a fixed bounded operator is closed under strong
convergence. -/
theorem commute_of_strong_tendsto (A T : H →L[ℂ] H) (B : ℕ → H →L[ℂ] H)
    (hB : ∀ ξ, Tendsto (fun n => B n ξ) atTop (𝓝 (T ξ)))
    (hcomm : ∀ n, Commute A (B n)) : Commute A T := by
  apply ContinuousLinearMap.ext
  intro ξ
  have hl := (A.continuous.tendsto (T ξ)).comp (hB ξ)
  change Tendsto (fun n => A (B n ξ)) atTop (𝓝 (A (T ξ))) at hl
  have hr := hB (A ξ)
  have he : (fun n => A (B n ξ)) = fun n => B n (A ξ) := by
    funext n
    exact congrArg (fun U : H →L[ℂ] H => U ξ) (hcomm n).eq
  rw [he] at hl
  exact tendsto_nhds_unique hl hr

/-- Countably many operators determine the entire commutant of an
arbitrary contraction-valued set. -/
theorem exists_countable_commutant_tests [SeparableSpace H]
    (S : Set (H →L[ℂ] H)) (hS : ∀ T ∈ S, ‖T‖ ≤ 1) :
    ∃ E : Set (H →L[ℂ] H), E.Countable ∧ E ⊆ S ∧
      ∀ A : H →L[ℂ] H, (∀ T ∈ E, Commute A T) ↔ ∀ T ∈ S, Commute A T := by
  obtain ⟨E, hEc, hES, hE⟩ := exists_countable_strong_dense_contractions S hS
  refine ⟨E, hEc, hES, fun A => ⟨?_, ?_⟩⟩
  · intro hcomm T hT
    obtain ⟨B, hBE, hBT⟩ := hE T hT
    exact commute_of_strong_tendsto A T B hBT (fun n => hcomm (B n) (hBE n))
  · exact fun hcomm T hT => hcomm T (hES hT)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_OperatorFieldValues
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.NonsingularAction.operatorAction_constant _root_.OAI.KadisonKastler.NonsingularAction.operatorEquiv_apply _root_.OAI.KadisonKastler.NonsingularAction.restrictedOperatorAction_coe _root_.OAI.KadisonKastler.WeakOperatorField.pullback_constant _root_.OAI.KadisonKastler.WeakOperatorField.pullback_id _root_.OAI.KadisonKastler.WeakOperatorRepresentative.evalHom_apply _root_.OAI.KadisonKastler.WeakOperatorRepresentative.eval_kernelProjection _root_.OAI.KadisonKastler.WeakOperatorRepresentative.eval_positiveKernelProjection _root_.OAI.KadisonKastler.WeakOperatorRepresentative.eval_pullback _root_.OAI.KadisonKastler.WeakOperatorRepresentative.pullback_constant _root_.OAI.KadisonKastler.WeakOperatorRepresentative.pullback_id _root_.OAI.KadisonKastler.WeakOperatorRepresentative.topElement_val _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.operatorFieldFamilyInclusion_apply _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Von Neumann algebra values of measurable operator fields

Commuting with constant operators in the commutant is a norm-closed
condition. Countably many strong-operator tests identify this condition
with pointwise membership outside one null set.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Pointwise BoundedContinuousFunction

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [TopologicalSpace.SeparableSpace H]

/-- Countably many constant commutant tests suffice to recover actual
von Neumann algebra membership almost everywhere. -/
theorem hasOperatorValues_of_mem_oai (M : VonNeumannAlgebra H)
    (q : WeakOperatorField (H := H) μ) (hq : q ∈ operatorFieldAlgebra (μ := μ) M) :
    HasOperatorValues M q := by
  obtain ⟨E, hEc, hES, hE⟩ := exists_countable_commutant_tests (unitBall M.commutant)
    (fun _ h => h.2)
  let R := WeakOperatorField.representative q
  have hc (T : E) : ∀ᵐ x ∂μ, Commute (WeakOperatorRepresentative.eval R x) (T : H →L[ℂ] H) := by
    have hT := (mem_operatorFieldAlgebra_iff M q).mp hq T (hES T.property).1
    have he : operatorFieldQuotient (H := H) μ (operatorRepresentativeConst μ T * R) =
        operatorFieldQuotient (H := H) μ (R * operatorRepresentativeConst μ T) := by
      simpa only [map_mul, R, WeakOperatorField.quotient_representative, operatorFieldConst,
        StarAlgHom.comp_apply] using hT
    filter_upwards [(operatorFieldQuotient_eq_iff μ _ _).mp he] with x hx
    exact hx.symm
  let : Countable E := hEc.to_subtype
  filter_upwards [ae_all_iff.mpr hc] with x hx
  change WeakOperatorRepresentative.eval R x ∈ (M : Set (H →L[ℂ] H))
  rw [← M.centralizer_centralizer]
  intro T hT
  by_cases hz : T = 0
  · simp [hz]
  have hn : 0 < ‖T‖ := norm_pos_iff.mpr hz
  have hTm : T ∈ M.commutant := by
    simpa only [← SetLike.mem_coe, VonNeumannAlgebra.coe_commutant] using hT
  let c : ℂ := (‖T‖⁻¹ : ℝ)
  have hc0 : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast inv_ne_zero hn.ne'
  have ht : c • T ∈ unitBall M.commutant := by
    refine ⟨M.commutant.toStarSubalgebra.smul_mem hTm c, ?_⟩
    simp [c, norm_smul, Complex.norm_real, inv_mul_cancel₀ hn.ne']
  have hs := (hE (WeakOperatorRepresentative.eval R x)).mp
    (fun a ha => hx ⟨a, ha⟩) (c • T) ht
  have he : c • (WeakOperatorRepresentative.eval R x * T) =
      c • (T * WeakOperatorRepresentative.eval R x) := by
    simpa only [mul_smul_comm, smul_mul_assoc] using hs.eq
  exact (smul_right_inj hc0).mp he |>.symm

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.hasOperatorValues_of_mem_oai.{u_1, u_2} := @OAI.KadisonKastler.hasOperatorValues_of_mem_oai.{u_1, u_2}
