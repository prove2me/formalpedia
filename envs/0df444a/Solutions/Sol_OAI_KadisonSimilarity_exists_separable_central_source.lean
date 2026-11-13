-- Prove2me | solution 1 for OAI.KadisonSimilarity.exists_separable_central_source
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:40:56.953292+00:00
-- url     : https://prove2.me/submissions/6ffc50c7-216d-413f-b9a7-3d9826218cc1

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Semiconj.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.Unitary
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.List.Induction
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Pairwise.Chain
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Option
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Option
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_OAIQ075A012

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_WeakOperatorCompactness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak-operator compactness of a norm ball, obtained from compact scalar
matrix-coefficient discs and the Hilbert-space representation of bounded forms. -/

noncomputable section
namespace KadisonSimilarity

open scoped Topology
open ContinuousLinearMapWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem norm_operatorOfForm_le (f : H → H → ℂ) (hf : IsOperatorForm f) (R : ℝ)
    (hR : 0 ≤ R) (hb : ∀ x y, ‖f x y‖ ≤ R * ‖x‖ * ‖y‖) :
    ‖operatorOfForm f hf R hb‖ ≤ R := by
  apply norm_le_of_matrix_coefficients _ hR
  intro x y
  rw [← norm_inner_symm, operatorOfForm_inner]
  convert hb x y using 1
  all_goals try with_reducible_and_instances rfl
  ring

omit [CompleteSpace H] in
private theorem isClosed_operatorForms : IsClosed {f : H → H → ℂ | IsOperatorForm f} := by
  have hc (x y : H) : Continuous (fun f : H → H → ℂ => f x y) :=
    (continuous_apply y).comp (continuous_apply x)
  unfold IsOperatorForm
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))
  · refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z => ?_
    exact isClosed_eq (hc (x + y) z) ((hc x z).add (hc y z))
  · refine isClosed_iInter fun c => isClosed_iInter fun x => isClosed_iInter fun y => ?_
    exact isClosed_eq (hc (c • x) y) (continuous_const.mul (hc x y))
  · refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z => ?_
    exact isClosed_eq (hc x (y + z)) ((hc x y).add (hc x z))
  · refine isClosed_iInter fun c => isClosed_iInter fun x => isClosed_iInter fun y => ?_
    exact isClosed_eq (hc x (c • y)) (continuous_const.mul (hc x y))

omit [CompleteSpace H] in
private theorem isCompact_boundedOperatorForms (R : ℝ) :
    IsCompact (boundedOperatorForms (H := H) R) := by
  have hd : IsCompact {f : H → H → ℂ | ∀ x y, f x y ∈ Metric.closedBall 0 (R * ‖x‖ * ‖y‖)} :=
    isCompact_pi_infinite fun x => isCompact_pi_infinite fun y => isCompact_closedBall _ _
  have he : boundedOperatorForms (H := H) R =
      {f | IsOperatorForm f} ∩ {f : H → H → ℂ | ∀ x y,
        f x y ∈ Metric.closedBall 0 (R * ‖x‖ * ‖y‖)} := by
    ext f
    simp [boundedOperatorForms, Metric.mem_closedBall, dist_zero_right]
  rw [he]
  exact hd.inter_left isClosed_operatorForms

private theorem continuous_boundedFormOperator (R : ℝ) :
    Continuous (boundedFormOperator (H := H) R) := by
  apply ContinuousLinearMapWOT.continuous_iff.mpr
  intro x y
  have he : (fun f : boundedOperatorForms (H := H) R =>
      inner ℂ y (boundedFormOperator R f x)) =
      fun f => star (f.val x y) := by
    funext f
    change inner ℂ y (operatorOfForm f.val f.property.1 R f.property.2 x) = _
    rw [← inner_conj_symm, operatorOfForm_inner]
    rfl
  rw [he]
  have hc : Continuous (fun f : H → H → ℂ => f x y) :=
    (continuous_apply y).comp (continuous_apply x)
  exact (hc.comp continuous_subtype_val).star

/-- The closed norm ball in bounded operators on a Hilbert space is compact
in the weak-operator topology. -/
theorem isCompact_weakOperator_ball (R : ℝ) (hR : 0 ≤ R) :
    IsCompact {T : H →WOT[ℂ] H | ‖toCLM T‖ ≤ R} := by
  let : CompactSpace (boundedOperatorForms (H := H) R) :=
    isCompact_iff_compactSpace.mp (isCompact_boundedOperatorForms R)
  have himage : Set.range (boundedFormOperator (H := H) R) =
      {T : H →WOT[ℂ] H | ‖toCLM T‖ ≤ R} := by
    ext T
    constructor
    · rintro ⟨f, rfl⟩
      exact norm_operatorOfForm_le f.val f.property.1 R hR f.property.2
    · intro hT
      let f : H → H → ℂ := fun x y => inner ℂ (T x) y
      have hf : IsOperatorForm f := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro x y z; simp [f, inner_add_left]
        · intro c x y; simp [f, inner_smul_left, mul_comm]
        · intro x y z; simp [f, inner_add_right]
        · intro c x y; simp [f, inner_smul_right]
      have hb : ∀ x y, ‖f x y‖ ≤ R * ‖x‖ * ‖y‖ := by
        intro x y
        calc
          ‖f x y‖ ≤ ‖T x‖ * ‖y‖ := norm_inner_le_norm _ _
          _ ≤ (‖toCLM T‖ * ‖x‖) * ‖y‖ :=
            mul_le_mul_of_nonneg_right ((toCLM T).le_opNorm x) (norm_nonneg y)
          _ ≤ R * ‖x‖ * ‖y‖ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hT (norm_nonneg x)) (norm_nonneg y)
      refine ⟨⟨f, hf, hb⟩, ?_⟩
      apply ContinuousLinearMapWOT.ext_inner
      intro x y
      change inner ℂ y (operatorOfForm f hf R hb x) = inner ℂ y (T x)
      rw [← inner_conj_symm, operatorOfForm_inner]
      exact inner_conj_symm _ _
  rw [← himage]
  exact isCompact_range (continuous_boundedFormOperator R)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SeparableContractionTests
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Countable weak-operator contraction tests

On a separable Hilbert space, the weak-operator unit ball embeds in a countable
product of copies of `ℂ`, by its coefficients on a dense sequence of vectors.
Compactness makes this an embedding. Thus each von Neumann algebra has a
countable weakly dense family of contractions.
-/

noncomputable section

namespace KadisonSimilarity

open ContinuousLinearMapWOT
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

/-- Countably many matrix coefficients determine the topology on the weak
operator unit ball of a separable Hilbert space. -/
theorem secondCountable_weakOperatorUnitBall :
    SecondCountableTopology (WeakOperatorUnitBall H) := by
  let d : ℕ → H := TopologicalSpace.denseSeq H
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq H
  let f : WeakOperatorUnitBall H → ℕ → ℕ → ℂ :=
    fun T i j => inner ℂ (d i) ((T : H →WOT[ℂ] H) (d j))
  have hf : Continuous f := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact ContinuousLinearMapWOT.continuous_inner_apply continuous_subtype_val (d j) (d i)
  have hinj : Function.Injective f := by
    intro S T h
    apply Subtype.ext
    apply ContinuousLinearMapWOT.ext_inner
    intro x y
    apply hd.induction_on₂ (p := fun x y =>
      inner ℂ y ((S : H →WOT[ℂ] H) x) = inner ℂ y ((T : H →WOT[ℂ] H) x))
      (isClosed_eq (by fun_prop) (by fun_prop)) _ x y
    intro i j
    exact congrFun (congrFun h j) i
  let : CompactSpace (WeakOperatorUnitBall H) :=
    isCompact_iff_compactSpace.mp (isCompact_weakOperator_ball (H := H) 1 zero_le_one)
  exact (hf.isClosedEmbedding hinj).isEmbedding.secondCountableTopology

/-- A concrete von Neumann algebra on a separable Hilbert space has a
countable weak-operator dense family in its closed unit ball. -/
theorem exists_separable_contraction_tests (P : VonNeumannAlgebra H) :
    ∃ test : ℕ → P.toStarSubalgebra,
      (∀ n, ‖test n‖ ≤ 1) ∧
      ∀ T : H →L[ℂ] H, T ∈ P → ‖T‖ ≤ 1 →
        ofCLM T ∈ closure (Set.range fun n => ofCLM (test n : H →L[ℂ] H)) := by
  let : SecondCountableTopology (WeakOperatorUnitBall H) :=
    secondCountable_weakOperatorUnitBall
  let B := {T : WeakOperatorUnitBall H // toCLM T.val ∈ P}
  let : SecondCountableTopology B :=
    (show Topology.IsEmbedding (Subtype.val : B → WeakOperatorUnitBall H) from
      Topology.IsEmbedding.subtypeVal).secondCountableTopology
  let : TopologicalSpace.SeparableSpace B := inferInstance
  let : Nonempty B := ⟨⟨⟨ofCLM 0, by simp⟩, P.zero_mem⟩⟩
  let d : ℕ → B := TopologicalSpace.denseSeq B
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq B
  let test : ℕ → P.toStarSubalgebra :=
    fun n => ⟨toCLM (d n).val.val, (d n).property⟩
  refine ⟨test, fun n => (d n).val.property, ?_⟩
  intro T hT hn
  let t : B := ⟨⟨ofCLM T, hn⟩, hT⟩
  let inclusion : B → H →WOT[ℂ] H := fun x => x.val.val
  have hc : Continuous inclusion := continuous_subtype_val.comp continuous_subtype_val
  change inclusion t ∈ _
  exact map_mem_closure (f := inclusion) hc (hd t) (by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, rfl⟩)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CountablyGeneratedCStarAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCStarQuotient.starSubalgebra_closed _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildCorners.corner_closed _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cstarCornerSubalgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerClosed _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.algebra_closed _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A separable C-star algebra generating a separably represented algebra

The complex linear span of the words in a countable family and its adjoints
is separable. Its norm closure is therefore a separable C-star algebra.
Applying this to the countable weakly dense contraction tests gives an
actual norm-separable C-star subalgebra whose bicommutant is the original
von Neumann algebra.
-/

noncomputable section
namespace KadisonSimilarity

open ContinuousLinearMapWOT
open scoped Topology Pointwise

variable {A : Type*} [CStarAlgebra A]

/-- Words in a countable generating set and its adjoints span a separable
complex star algebra. -/
theorem isSeparable_starAlgebra_adjoin {s : Set A} (hs : s.Countable) :
    TopologicalSpace.IsSeparable (StarAlgebra.adjoin ℂ s : Set A) := by
  have hstar : (star s).Countable := by
    rw [← Set.image_star]
    exact hs.image star
  have hunion := hs.union hstar
  let : Countable {x : A // x ∈ s ∪ star s} := hunion.to_subtype
  have hwords : (Submonoid.closure (s ∪ star s) : Set A).Countable := by
    rw [Submonoid.closure_eq_mrange, MonoidHom.coe_mrange]
    exact Set.countable_range _
  change TopologicalSpace.IsSeparable
    ((StarAlgebra.adjoin ℂ s).toSubalgebra.toSubmodule : Set A)
  rw [StarAlgebra.adjoin_eq_span]
  exact hwords.isSeparable.span

instance sequenceGeneratedCStarAlgebra_separable (g : ℕ → A) :
    TopologicalSpace.SeparableSpace (sequenceGeneratedCStarAlgebra g) := by
  apply TopologicalSpace.IsSeparable.separableSpace
  exact (isSeparable_starAlgebra_adjoin (Set.countable_range g)).closure

theorem mem_sequenceGeneratedCStarAlgebra (g : ℕ → A) (n : ℕ) :
    g n ∈ sequenceGeneratedCStarAlgebra g :=
  (StarSubalgebra.le_topologicalClosure _)
    (StarAlgebra.subset_adjoin ℂ (Set.range g) (Set.mem_range_self n))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A concrete von Neumann algebra contains the weak closure of any of its
subsets, proved directly from commutation with its commutant. -/
theorem mem_vonNeumannAlgebra_of_mem_weakClosure
    (P : VonNeumannAlgebra H) (S : Set (H →L[ℂ] H)) (hS : S ⊆ P)
    (T : H →L[ℂ] H) (hT : ofCLM T ∈ closure (ofCLM '' S)) : T ∈ P := by
  rw [← P.commutant_commutant]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro R hR
  have hc : IsClosed {X : H →WOT[ℂ] H | ofCLM R * X = X * ofCLM R} :=
    isClosed_eq (continuous_const_mul _) (continuous_mul_const _)
  have hs : ofCLM '' S ⊆ {X : H →WOT[ℂ] H | ofCLM R * X = X * ofCLM R} := by
    rintro _ ⟨X, hX, rfl⟩
    exact congrArg ofCLM ((VonNeumannAlgebra.mem_commutant_iff.mp hR) X (hS hX)).symm
  exact congrArg toCLM (closure_minimal hs hc hT)

/-- A norm-closed star subalgebra contained in `P`, containing a weakly dense
family of contractions, has bicommutant exactly `P`. -/
theorem representationVonNeumannAlgebra_subtype_eq_of_dense_tests
    (P : VonNeumannAlgebra H) (B : StarSubalgebra ℂ (H →L[ℂ] H))
    [IsClosed (B : Set (H →L[ℂ] H))]
    (hB : B ≤ P.toStarSubalgebra) (g : ℕ → H →L[ℂ] H) (hg : ∀ n, g n ∈ B)
    (hdense : ∀ T : H →L[ℂ] H, T ∈ P → ‖T‖ ≤ 1 →
      ofCLM T ∈ closure (Set.range fun n => ofCLM (g n))) :
    representationVonNeumannAlgebra B.subtype = P := by
  let Q := representationVonNeumannAlgebra B.subtype
  apply VonNeumannAlgebra.ext
  intro T
  constructor
  · intro hT
    rw [← P.commutant_commutant]
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro R hR
    have hT' : T ∈ Set.centralizer (Set.centralizer
        (B.subtype.range : Set (H →L[ℂ] H))) := by
      simpa only [← SetLike.mem_coe, coe_representationVonNeumannAlgebra] using hT
    apply hT' R
    rintro _ ⟨b, rfl⟩
    exact (VonNeumannAlgebra.mem_commutant_iff.mp hR) b (hB b.property)
  · intro hT
    by_cases hz : T = 0
    · rw [hz, ← SetLike.mem_coe, coe_representationVonNeumannAlgebra]
      intro R _
      simp
    let c : ℂ := (‖T‖ : ℂ)⁻¹
    have hnorm : ‖c • T‖ ≤ 1 := by
      simp only [c, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg T), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz), le_refl]
    have hC : c • T ∈ Q := by
      apply mem_vonNeumannAlgebra_of_mem_weakClosure Q (Set.range g)
      · rintro _ ⟨n, rfl⟩
        exact mem_representationVonNeumannAlgebra B.subtype ⟨g n, hg n⟩
      · simpa only [Set.range_comp'] using
          hdense (c • T) (P.toStarSubalgebra.smul_mem hT c) hnorm
    have hback : (‖T‖ : ℂ) • (c • T) = T := by
      rw [smul_smul]
      simp only [c, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)),
        one_smul]
    rw [← hback]
    exact Q.toStarSubalgebra.smul_mem hC _

/-- Every concretely separably represented von Neumann algebra is the
bicommutant of an actual norm-separable unital C-star subalgebra. -/
theorem exists_separable_generating_cstar_subalgebra
    [TopologicalSpace.SeparableSpace H] (P : VonNeumannAlgebra H) :
    ∃ B : StarSubalgebra ℂ (H →L[ℂ] H),
      IsClosed (B : Set (H →L[ℂ] H)) ∧ TopologicalSpace.SeparableSpace B ∧
      B ≤ P.toStarSubalgebra ∧ (starSubalgebraCommutant B).commutant = P := by
  obtain ⟨test, _, hdense⟩ := exists_separable_contraction_tests P
  let g : ℕ → H →L[ℂ] H := fun n => test n
  let B := sequenceGeneratedCStarAlgebra g
  have hPclosed : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
    change IsClosed (P : Set (H →L[ℂ] H))
    rw [← P.centralizer_centralizer]
    exact Set.isClosed_centralizer _
  have hB : B ≤ P.toStarSubalgebra := by
    apply StarSubalgebra.topologicalClosure_minimal _ hPclosed
    apply StarAlgebra.adjoin_le
    rintro _ ⟨n, rfl⟩
    exact (test n).property
  refine ⟨B, inferInstance, inferInstance, hB, ?_⟩
  have hmain := representationVonNeumannAlgebra_subtype_eq_of_dense_tests P B hB g
    (mem_sequenceGeneratedCStarAlgebra g) hdense
  have hrange : B.subtype.range = B := by
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      exact b.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  simpa only [representationVonNeumannAlgebra, hrange] using hmain

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_CentralCStarSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! A norm-separable commutative C-star source for the center. Its commutant
is the full central commutant, so its common spectral fields apply to every
operator required by the central-decomposition estimate. -/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every star subalgebra of the center is commutative. -/
theorem central_subalgebra_isMulCommutative (P : VonNeumannAlgebra H)
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (hA : A ≤ (vonNeumannCenter P).toStarSubalgebra) :
    IsMulCommutative A := by
  apply IsMulCommutative.of_setLike_mul_comm
  intro x hx y hy
  exact (VonNeumannAlgebra.mem_commutant_iff.mp (hA hy).2) x (hA hx).1

/-- A weakly generating central source has the full central commutant. -/
theorem central_source_commutant (P : VonNeumannAlgebra H)
    (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (hgen : (starSubalgebraCommutant A).commutant = vonNeumannCenter P) :
    starSubalgebraCommutant A = (vonNeumannCenter P).commutant := by
  have h := congrArg VonNeumannAlgebra.commutant hgen
  simpa only [VonNeumannAlgebra.commutant_commutant] using h

/-- Choose only a norm-separable source; the center itself need not be
norm separable. -/
theorem exists_separable_central_source_oai [TopologicalSpace.SeparableSpace H]
    (P : VonNeumannAlgebra H) :
    ∃ A : StarSubalgebra ℂ (H →L[ℂ] H),
      IsClosed (A : Set (H →L[ℂ] H)) ∧ TopologicalSpace.SeparableSpace A ∧
      IsMulCommutative A ∧ A ≤ (vonNeumannCenter P).toStarSubalgebra ∧
      starSubalgebraCommutant A = (vonNeumannCenter P).commutant := by
  obtain ⟨A, hclosed, hsep, hA, hgen⟩ :=
    exists_separable_generating_cstar_subalgebra (vonNeumannCenter P)
  exact ⟨A, hclosed, hsep, central_subalgebra_isMulCommutative P A hA, hA,
    central_source_commutant P A hgen⟩

end KadisonSimilarity

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonSimilarity.exists_separable_central_source_oai.{u_1} := @OAI.KadisonSimilarity.exists_separable_central_source_oai.{u_1}
