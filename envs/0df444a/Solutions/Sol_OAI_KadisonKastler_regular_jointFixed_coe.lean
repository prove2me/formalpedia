-- Prove2me | solution 1 for OAI.KadisonKastler.regular_jointFixed_coe
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:01:36.47564+00:00
-- url     : https://prove2.me/submissions/81acf163-8019-46ba-925a-280ee1cf21b3

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
import Mathlib.Algebra.Ring.GeomSum
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
import Mathlib.Analysis.Complex.Circle
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
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
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
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
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
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.Instances.Complex
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
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K024

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DirectIntegralConjugacy
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Assembling fiber conjugacies on the actual direct-integral space

`OperatorFieldDecomposition` records the decomposition and reconstruction
properties of a given constant-fiber direct integral. It is data, not a
published theorem or an existence assertion. The assembly argument below
uses actual multiplication unitaries on `L²(X,H)`.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem RepresentsOperatorField.unique {μ : Measure X} {F : X → H →L[ℂ] H}
    {T S : Lp H 2 μ →L[ℂ] Lp H 2 μ}
    (hT : RepresentsOperatorField μ F T) (hS : RepresentsOperatorField μ F S) : T = S := by
  apply ContinuousLinearMap.ext
  intro f
  exact Lp.ext ((hT f).trans (hS f).symm)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreCharacters
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Character multiplication in the regular core representation

The operators `Q_a` are actual multiplication unitaries on `L²(ℝ,H)`.
Their covariance with translations and their commutation with `π(B(H))`
are proved on representatives. These are the generator identities in
the dual-character argument of Section 8.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regularCharacter_commute_embedding
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (a : ℝ) (T : H →L[ℂ] H) :
    Commute (regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularCoreEmbedding U hU T) := by
  change (regularCharacterUnitary (H := H) a :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) * regularCoreEmbedding U hU T =
    regularCoreEmbedding U hU T * (regularCharacterUnitary (H := H) a :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularCharacterUnitary_apply_ae a (regularCoreEmbedding U hU T f),
    regularCoreEmbedding_apply_ae U hU T f,
    regularCoreEmbedding_apply_ae U hU T
      ((regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularCharacterUnitary_apply_ae a f] with t hQ hπ hπQ hq
  change (regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularCoreEmbedding U hU T f) t =
    regularCoreEmbedding U hU T
      ((regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) t
  rw [hQ, hπ, hπQ, hq]
  simp only [map_smul]

/-- The dual characters fix every embedded operator. -/
theorem regularCharacter_fixes_embedding
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (a : ℝ) (T : H →L[ℂ] H) :
    unitaryConj (regularCharacterUnitary (H := H) a) (regularCoreEmbedding U hU T) =
      regularCoreEmbedding U hU T :=
  (commute_unitary_iff_star_right_conjugate (regularCharacterUnitary (H := H) a).property).mp
    (regularCharacter_commute_embedding U hU a T)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreInvariant
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Translation-invariant measurable fields are constant

For each translation the exceptional null set may differ. Fubini and the
measure-preserving shear `(s,t) ↦ (s-t,t)` nevertheless give a single
almost-everywhere constant representative. The operator-valued version
uses only countably many dense Hilbert coefficients.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

/-- A measurable scalar function invariant under every real translation
as an almost-everywhere class is almost everywhere constant. -/
theorem measurable_real_translation_invariant_const (f : ℝ → ℂ)
    (hf : Measurable f)
    (htrans : ∀ s : ℝ, (fun t => f (t + s)) =ᵐ[volume] f) :
    ∃ c : ℂ, f =ᵐ[volume] fun _ => c := by
  have hm : MeasurableSet {p : ℝ × ℝ | f (p.1 + p.2) = f p.2} :=
    measurableSet_eq_fun (hf.comp (measurable_fst.add measurable_snd))
      (hf.comp measurable_snd)
  have hp : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), f (p.1 + p.2) = f p.2 := by
    apply (Measure.ae_prod_iff_ae_ae (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ)) hm).mpr
    apply Eventually.of_forall
    intro s
    change ∀ᵐ y : ℝ ∂(volume : Measure ℝ), f (s + y) = f y
    filter_upwards [htrans s] with t ht
    simpa only [add_comm] using ht
  have hp' : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), f p.1 = f p.2 := by
    have h := (measurePreserving_sub_prod (volume : Measure ℝ) volume).quasiMeasurePreserving.ae hp
    simpa only [sub_add_cancel] using h
  obtain ⟨s, hs⟩ := (Measure.ae_ae_of_ae_prod hp').exists
  exact ⟨f s, hs.mono fun _ h => h.symm⟩

/-- The same conclusion for a scalar almost-everywhere measurable class. -/
theorem aestronglyMeasurable_real_translation_invariant_const (f : ℝ → ℂ)
    (hf : AEStronglyMeasurable f volume)
    (htrans : ∀ s : ℝ, (fun t => f (t + s)) =ᵐ[volume] f) :
    ∃ c : ℂ, f =ᵐ[volume] fun _ => c := by
  have hmk (s : ℝ) : (fun t => hf.mk f (t + s)) =ᵐ[volume] hf.mk f := by
    have hshift := (measurePreserving_add_right (volume : Measure ℝ) s).quasiMeasurePreserving.ae_eq_comp
      hf.ae_eq_mk
    filter_upwards [hshift, htrans s, hf.ae_eq_mk] with t hshift ht hbase
    exact hshift.symm.trans (ht.trans hbase)
  obtain ⟨c, hc⟩ := measurable_real_translation_invariant_const
    (hf.mk f) hf.measurable_mk hmk
  exact ⟨c, hf.ae_eq_mk.trans hc⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [TopologicalSpace.SeparableSpace H]

/-- Scalar translation invariance of a weakly measurable operator field
implies a single almost-everywhere constant bounded operator. No common
exceptional set for the original uncountable family of translations is
required. -/
theorem operatorField_real_translation_invariant_const
    (F : ℝ → H →L[ℂ] H)
    (hF : ∀ ξ η : H, AEStronglyMeasurable
      (fun t => inner ℂ η (F t ξ)) volume)
    (htrans : ∀ (s : ℝ) (ξ η : H),
      (fun t => inner ℂ η (F (t + s) ξ)) =ᵐ[volume]
        fun t => inner ℂ η (F t ξ)) :
    ∃ T : H →L[ℂ] H, F =ᵐ[volume] fun _ => T := by
  obtain ⟨v, hv⟩ := TopologicalSpace.exists_dense_seq (α := H)
  have hex (i j : ℕ) := aestronglyMeasurable_real_translation_invariant_const
    (fun t => inner ℂ (v i) (F t (v j))) (hF (v j) (v i))
    (fun s => htrans s (v j) (v i))
  choose c hc using hex
  have hall : ∀ᵐ t : ℝ ∂volume, ∀ i j : ℕ,
      inner ℂ (v i) (F t (v j)) = c i j :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => hc i j
  obtain ⟨t₀, ht₀⟩ := hall.exists
  refine ⟨F t₀, hall.mono fun t ht => ?_⟩
  apply ContinuousLinearMap.ext
  have he : (fun ξ => F t ξ) = (fun ξ => F t₀ ξ) := by
    apply hv.equalizer (F t).continuous (F t₀).continuous
    funext j
    exact hv.eq_of_inner_right ℂ (fun i => (ht i j).trans (ht₀ i j).symm)
  exact congrFun he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreFields
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.conjugationFamily_apply _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded field multiplication and constant translation-fixed fields

Bounded measurable operator fields act on the actual vector-valued `L²`
space. Finite-measure indicator tests recover their coefficients, so this
action is faithful modulo almost-everywhere equality. A decomposable
operator commuting with every real translation is a constant operator.
No decomposability assertion for an arbitrary operator is assumed here.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Indicator tests recover each vector coefficient of an operator field
on a finite-measure set. -/
theorem RepresentsOperatorField.eval_eq_ae_on {μ : Measure X}
    {F G : X → H →L[ℂ] H} {T : Lp H 2 μ →L[ℂ] Lp H 2 μ}
    (hF : RepresentsOperatorField μ F T) (hG : RepresentsOperatorField μ G T)
    {s : Set X} (hs : MeasurableSet s) (hfinite : μ s ≠ ∞) (ξ : H) :
    ∀ᵐ t ∂μ, t ∈ s → F t ξ = G t ξ := by
  let f : Lp H 2 μ := indicatorConstLp 2 hs hfinite ξ
  filter_upwards [hF f, hG f,
    (indicatorConstLp_coeFn_mem (p := 2) (hs := hs) (hμs := hfinite) (c := ξ))]
    with t hf hg hξ
  intro ht
  rw [hξ ht] at hf hg
  exact hf.symm.trans hg

omit [CompleteSpace H] in
/-- Equality of actual real-line multiplication operators recovers each
vector value almost everywhere. -/
theorem RepresentsOperatorField.eval_eq_ae_real
    {F G : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hF : RepresentsOperatorField volume F T) (hG : RepresentsOperatorField volume G T)
    (ξ : H) : (fun t => F t ξ) =ᵐ[volume] fun t => G t ξ := by
  have hall : ∀ᵐ t : ℝ ∂volume, ∀ n : ℕ,
      t ∈ Set.Icc (-(n : ℝ)) (n : ℝ) → F t ξ = G t ξ := by
    apply ae_all_iff.mpr
    intro n
    exact hF.eval_eq_ae_on hG measurableSet_Icc (by simp) ξ
  filter_upwards [hall] with t ht
  obtain ⟨n, hn⟩ := exists_nat_gt |t|
  exact ht n (Set.mem_Icc.mpr (abs_le.mp hn.le))

omit [CompleteSpace H] in
/-- On a separable Hilbert space, equality of multiplication operators
recovers the entire field almost everywhere. -/
theorem RepresentsOperatorField.field_eq_ae_real [TopologicalSpace.SeparableSpace H]
    {F G : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hF : RepresentsOperatorField volume F T) (hG : RepresentsOperatorField volume G T) :
    F =ᵐ[volume] G := by
  obtain ⟨v, hv⟩ := TopologicalSpace.exists_dense_seq (α := H)
  have hall : ∀ᵐ t : ℝ ∂volume, ∀ n : ℕ, F t (v n) = G t (v n) :=
    ae_all_iff.mpr fun n => hF.eval_eq_ae_real hG (v n)
  filter_upwards [hall] with t ht
  apply ContinuousLinearMap.ext
  exact congrFun (hv.equalizer (F t).continuous (G t).continuous (funext ht))

/-- Translation conjugates an actual multiplication operator by shifting
its field. -/
theorem RepresentsOperatorField.real_translate
    {F : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hF : RepresentsOperatorField volume F T) (s : Multiplicative ℝ) :
    RepresentsOperatorField volume (fun t => F (t + s.toAdd))
      (unitaryConj (regularRightTranslation (H := H) s) T) := by
  intro f
  have hstar : (star (regularRightTranslation (H := H) s) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      (regularRightTranslation (H := H) s⁻¹ :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
    rw [map_inv]
    rfl
  unfold unitaryConj
  rw [hstar]
  filter_upwards [regularRightTranslation_apply_ae s
      (T ((regularRightTranslation (H := H) s⁻¹ :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)),
    (measurePreserving_add_right volume s.toAdd).quasiMeasurePreserving.ae_eq_comp
      (hF ((regularRightTranslation (H := H) s⁻¹ :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)),
    (measurePreserving_add_right volume s.toAdd).quasiMeasurePreserving.ae_eq_comp
      (regularRightTranslation_apply_ae s⁻¹ f)] with t hρ hFshift hback
  simp only [Function.comp_def] at hFshift hback
  change (regularRightTranslation (H := H) s :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (T ((regularRightTranslation (H := H) s⁻¹ :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)) t = _
  rw [hρ, hFshift, hback]
  simp

/-- An actually decomposable operator fixed by every translation is a
constant operator. Decomposability itself is not posited for arbitrary
operators. -/
theorem constant_of_regularField_translation_fixed [TopologicalSpace.SeparableSpace H]
    {F : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hF : RepresentsOperatorField volume F T)
    (hmeas : ∀ ξ, AEStronglyMeasurable (fun t => F t ξ) volume)
    (hfixed : ∀ s, unitaryConj (regularRightTranslation (H := H) s) T = T) :
    ∃ A : H →L[ℂ] H, F =ᵐ[volume] (fun _ => A) ∧ T = regularConstantHom volume A := by
  have hshift (s : ℝ) : (fun t => F (t + s)) =ᵐ[volume] F := by
    have h := hF.real_translate (Multiplicative.ofAdd s)
    rw [hfixed] at h
    exact h.field_eq_ae_real hF
  have hcoeff (s : ℝ) (ξ η : H) :
      (fun t => inner ℂ η (F (t + s) ξ)) =ᵐ[volume] fun t => inner ℂ η (F t ξ) :=
    (hshift s).mono fun _ h => congrArg (fun A : H →L[ℂ] H => inner ℂ η (A ξ)) h
  obtain ⟨A, hA⟩ := operatorField_real_translation_invariant_const F
    (fun ξ η => (hmeas ξ).const_inner (c := η)) hcoeff
  refine ⟨A, hA, hF.unique ?_⟩
  intro f
  filter_upwards [regularConstantHom_apply_ae volume A f, hA] with t ht hAt
  exact ht.trans (congrArg (fun B : H →L[ℂ] H => B (f t)) hAt.symm)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreFixed
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fixed decomposable operators in the regular representation

The gauge transforms a decomposable operator fixed by `U_s ⊗ ρ_s` into
a translation-fixed multiplier. The preceding scalar Fubini argument
then makes it a constant operator, so the original operator belongs to
the concrete regular image `π(B(H))`.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

/-- The gauge conjugation has the expected field formula. -/
theorem RepresentsOperatorField.regular_gauge
    {F : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hF : RepresentsOperatorField volume F T) :
    RepresentsOperatorField volume
      (fun t => unitaryConj (U (Multiplicative.ofAdd t)) (F t))
      (unitaryConj (regularGauge U hU) T) := by
  intro f
  filter_upwards [regularGauge_apply_ae U hU
      (T ((star (regularGauge U hU) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)),
    hF ((star (regularGauge U hU) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularGauge_star_apply_ae U hU f] with t hg hT hgs
  change (regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (T ((star (regularGauge U hU) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)) t = _
  rw [hg, hT, hgs]
  rfl

/-- Fixedness passes through the exact gauge intertwining identity. -/
theorem regularGauge_translation_fixed
    {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hfixed : ∀ s, unitaryConj (regularCoreAction U s) T = T)
    (s : Multiplicative ℝ) :
    unitaryConj (regularRightTranslation (H := H) s)
      (unitaryConj (regularGauge U hU) T) = unitaryConj (regularGauge U hU) T := by
  have he : regularGauge U hU * regularCoreAction U s =
      regularRightTranslation (H := H) s * regularGauge U hU :=
    Subtype.ext (regularGauge_intertwines_action U hU s)
  rw [← unitaryConj_mul, ← he, unitaryConj_mul, hfixed]

/-- A weakly measurable decomposable operator fixed by the common action
belongs to the actual regular image. -/
theorem exists_regularCoreEmbedding_of_field_fixed [TopologicalSpace.SeparableSpace H]
    {F : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hF : RepresentsOperatorField volume F T)
    (hmeas : ∀ ξ, AEStronglyMeasurable (fun t => F t ξ) volume)
    (hfixed : ∀ s, unitaryConj (regularCoreAction U s) T = T) :
    ∃ A : H →L[ℂ] H, T = regularCoreEmbedding U hU A := by
  let F' : ℝ → H →L[ℂ] H := fun t =>
    unitaryConj (U (Multiplicative.ofAdd t)) (F t)
  have hm (ξ : H) : AEStronglyMeasurable (fun t => F' t ξ) volume := by
    exact aestronglyMeasurable_field_apply
      (fun t => (U (Multiplicative.ofAdd t) : H →L[ℂ] H))
      (fun x => (hU x).aestronglyMeasurable)
      (fun t => F t ((star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) ξ))
      (aestronglyMeasurable_field_apply F hmeas _
        (regularGroup_star_measurable U hU ξ))
  obtain ⟨A, _, hA⟩ := constant_of_regularField_translation_fixed
    (hF.regular_gauge U hU) hm (regularGauge_translation_fixed U hU hfixed)
  refine ⟨A, ?_⟩
  have he := congrArg (unitaryConj (star (regularGauge U hU))) hA
  rw [unitaryConj_star_unitaryConj] at he
  exact he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreIntersection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The joint fixed algebra in the concrete regular representation

The reverse tensor membership is proved from the actual multiplier
representation. The joint fixed-point identification then uses only the
two separate published spectral and diagonal decomposition inputs.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))

include hU in
theorem regularCoreEmbedding_field_continuous (A : H →L[ℂ] H) (ξ : H) :
    Continuous (fun t : ℝ =>
      unitaryConj (star (U (Multiplicative.ofAdd t))) A ξ) := by
  have hs (η : H) : Continuous (fun t : ℝ =>
      (star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) η) := by
    have he : (fun t : ℝ => (star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) η) =
        (fun t : ℝ => (U (Multiplicative.ofAdd (-t)) : H →L[ℂ] H) η) := by
      funext t
      exact congrArg (fun v : unitary (H →L[ℂ] H) => (v : H →L[ℂ] H) η)
        (regularGroup_star_eq U t)
    rw [he]
    exact (hU η).comp continuous_neg
  simpa only [unitaryConj, Unitary.coe_star, star_star, mul_apply_eq_comp] using
    continuous_unitary_field_apply (fun t : ℝ => star (U (Multiplicative.ofAdd t)))
      hs (fun t : ℝ => A ((U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))
      (A.continuous.comp (hU ξ))

/-- Membership in the tensor algebra reflects membership in the original
algebra. The coefficient identity is continuous, so its almost-everywhere
validity also gives its value at zero. -/
theorem regularCoreEmbedding_mem_tensorAlgebra_iff (P : VonNeumannAlgebra H)
    (hP : ∀ s A, A ∈ P → unitaryConj (U s) A ∈ P) (A : H →L[ℂ] H) :
    regularCoreEmbedding U hU A ∈ regularTensorAlgebra P ↔ A ∈ P := by
  constructor
  · intro hA
    rw [← VonNeumannAlgebra.commutant_commutant P]
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro z hz
    have he := (mem_regularTensorAlgebra_iff P _).mp hA z hz
    let F : ℝ → H →L[ℂ] H := fun t =>
      unitaryConj (star (U (Multiplicative.ofAdd t))) A
    have hl : RepresentsOperatorField volume (fun t => z * F t)
        (regularConstantHom volume z * regularCoreEmbedding U hU A) := by
      intro f
      filter_upwards [regularConstantHom_apply_ae volume z (regularCoreEmbedding U hU A f),
        regularCoreEmbedding_apply_ae U hU A f] with t hc hp
      change regularConstantHom volume z (regularCoreEmbedding U hU A f) t = _
      rw [hc, hp]
      simp only [F, unitaryConj, Unitary.coe_star, star_star, mul_apply_eq_comp]
    have hr : RepresentsOperatorField volume (fun t => F t * z)
        (regularConstantHom volume z * regularCoreEmbedding U hU A) := by
      rw [he]
      intro f
      filter_upwards [regularCoreEmbedding_apply_ae U hU A (regularConstantHom volume z f),
        regularConstantHom_apply_ae volume z f] with t hp hc
      change regularCoreEmbedding U hU A (regularConstantHom volume z f) t = _
      rw [hp, hc]
      simp only [F, unitaryConj, Unitary.coe_star, star_star, mul_apply_eq_comp]
    apply ContinuousLinearMap.ext
    intro ξ
    have hae := hl.eval_eq_ae_real hr ξ
    have heq := Measure.eq_of_ae_eq hae
      (z.continuous.comp (regularCoreEmbedding_field_continuous U hU A ξ))
      (regularCoreEmbedding_field_continuous U hU A (z ξ))
    have hzero := congrFun heq 0
    simpa only [F, ofAdd_zero, map_one, star_one,
      unitaryConj_one, mul_apply_eq_comp] using hzero
  · exact regularCoreEmbedding_mem_tensorAlgebra U hU P hP

/-- The exact joint fixed algebra of the two concrete regular actions.
The spectral and diagonal decomposition inputs are used separately; the
algebra identification itself is the conclusion of the proof. -/
theorem mem_regular_jointFixed_iff [TopologicalSpace.SeparableSpace H]
    (hSpectral : PublishedRealSpectralCommutant.{u})
    (hDiagonal : PublishedRealDiagonalDecomposition.{u})
    (P : VonNeumannAlgebra H)
    (hP : ∀ s A, A ∈ P → unitaryConj (U s) A ∈ P)
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :
    T ∈ fixedPointAlgebra (regularCharacterRepresentation (H := H))
      (fixedPointAlgebra (regularCoreAction U) (regularTensorAlgebra P)) ↔
      ∃ A ∈ P, T = regularCoreEmbedding U hU A := by
  constructor
  · intro hT
    obtain ⟨hinner, hchar⟩ := (mem_fixedPointAlgebra_iff _ _ _).mp hT
    obtain ⟨htensor, haction⟩ := (mem_fixedPointAlgebra_iff _ _ _).mp hinner
    have hcomm (a : ℝ) : Commute T
        (regularCharacterUnitary (H := H) a :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
      exact ((commute_unitary_iff_star_right_conjugate
        (regularCharacterUnitary (H := H) a).property).mpr
        (hchar (Multiplicative.ofAdd a))).symm
    obtain ⟨F, hFm, _, hFT⟩ := hDiagonal H T (hSpectral H T hcomm)
    obtain ⟨A, hA⟩ := exists_regularCoreEmbedding_of_field_fixed U hU hFT hFm haction
    exact ⟨A, (regularCoreEmbedding_mem_tensorAlgebra_iff U hU P hP A).mp
      (hA ▸ htensor), hA⟩
  · rintro ⟨A, hA, rfl⟩
    apply (mem_fixedPointAlgebra_iff _ _ _).mpr
    refine ⟨(mem_fixedPointAlgebra_iff _ _ _).mpr
      ⟨regularCoreEmbedding_mem_tensorAlgebra U hU P hP hA,
        fun s => regularCoreEmbedding_fixed U hU s A⟩, ?_⟩
    intro a
    exact regularCharacter_fixes_embedding U hU a.toAdd A

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreActions
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Normalization by the two actual regular actions

The translation and character formulas imply the required tensor-algebra
normalization. The two actions commute as conjugations, although their
implementing unitary groups commute only up to scalar characters.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Set form of the joint fixed-point identity, matching the range premise
of the character-average descent theorem. -/
theorem regular_jointFixed_coe_oai
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))
    [TopologicalSpace.SeparableSpace H]
    (hSpectral : PublishedRealSpectralCommutant.{u})
    (hDiagonal : PublishedRealDiagonalDecomposition.{u})
    (P : VonNeumannAlgebra H)
    (hP : ∀ s x, x ∈ P → unitaryConj (U s) x ∈ P) :
    (fixedPointAlgebra (regularCharacterRepresentation (H := H))
      (fixedPointAlgebra (regularCoreAction U) (regularTensorAlgebra P)) :
        Set (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) =
      regularCoreEmbedding U hU '' (P : Set (H →L[ℂ] H)) := by
  ext T
  change T ∈ fixedPointAlgebra (regularCharacterRepresentation (H := H))
    (fixedPointAlgebra (regularCoreAction U) (regularTensorAlgebra P)) ↔
    T ∈ regularCoreEmbedding U hU '' (P : Set (H →L[ℂ] H))
  rw [mem_regular_jointFixed_iff U hU hSpectral hDiagonal P hP]
  constructor
  · rintro ⟨A, hA, hT⟩
    exact ⟨A, hA, hT.symm⟩
  · rintro ⟨A, hA, hT⟩
    exact ⟨A, hA, hT.symm⟩

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.regular_jointFixed_coe_oai.{u} := @OAI.KadisonKastler.regular_jointFixed_coe_oai.{u}
