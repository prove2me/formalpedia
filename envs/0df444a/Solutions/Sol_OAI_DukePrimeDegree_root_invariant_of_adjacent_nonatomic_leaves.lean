-- Prove2me | solution 1 for OAI.DukePrimeDegree.root_invariant_of_adjacent_nonatomic_leaves
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:44:02.227023+00:00
-- url     : https://prove2.me/submissions/7e7140e4-4b0e-4353-b7b9-e3655b00dff1

import Mathlib
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke044
import Theorems.Thm_OAI_DukePrimeDegree_exists_nullset_neutral_root_holonomy
import Theorems.Thm_OAI_DukePrimeDegree_exists_nullset_nonparallel_root_constancy

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_KernelScaling
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.overlapMeasure_finite _root_.OAI.PrimeDegreePackets.RootBox.regularLeafKernel_locallyFinite _root_.OAI.PrimeDegreePackets.RootBox.regularLeafKernel_sFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.intrinsicRootKernel_locallyFinite _root_.OAI.PrimeDegreePackets.intrinsicRootKernel_sFinite _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory

open Set Filter Topology

open Set Filter Topology MeasureTheory
namespace PrimeDegreePackets



theorem rootBox_arbitrary_length_of_free {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (x : X n) (hfree : ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (R : ℝ) :
    ∃ (k : Fin n) (B : RootBox hij k) (s : RootSlice i j k) (t : ℝ),
      s ∈ B.transverse ∧ Icc (t-R) (t+R) ⊆ B.time ∧
        rootQuotientParametrization hij (s,t) = x := by
  induction x using Quotient.inductionOn with
  | h g =>
    obtain ⟨k,hk⟩ := exists_rootPivot i g
    let z := rootPivotHomeomorph (j := j) hij (⟨g,hk⟩ : RootPivot i k)
    have hz : rootQuotientParametrization hij z = Quotient.mk _ g := by
      unfold rootQuotientParametrization z
      rw [Homeomorph.symm_apply_apply]
    have hi := root_time_injective_of_free hij z.1 z.2 (hz ▸ hfree)
    obtain ⟨B,hs,hT⟩ := rootBox_contains_compact_time hij z.1 hi (z.2-R) (z.2+R)
    exact ⟨k,B,z.1,z.2,hs,hT,hz⟩

 

theorem ae_rootBox_arbitrary_length (d : ℕ) (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      Measure.map (fun x => rightAction x (diagonalFlow u)) μ = μ) :
    ∀ᵐ x ∂μ, ∀ (i j : Fin (d+1)) (hij : i ≠ j) (R : ℝ),
      ∃ (k : Fin (d+1)) (B : RootBox hij k) (s : RootSlice i j k) (t : ℝ),
        s ∈ B.transverse ∧ Icc (t-R) (t+R) ⊆ B.time ∧
          rootQuotientParametrization hij (s,t) = x := by
  filter_upwards [ae_root_stabilizer_trivial d μ hA] with x hx
  intro i j hij R
  exact rootBox_arbitrary_length_of_free hij x (hx i j hij) R

end PrimeDegreePackets

open MeasureTheory Set Filter Topology
namespace PrimeDegreePackets

variable {A : Type*} [TopologicalSpace A] [SecondCountableTopology A]
  [MeasurableSpace A] [BorelSpace A]

omit [BorelSpace A] in
lemma measure_eq_of_ae_local_restrict_eq (μ ν : Measure A) [IsFiniteMeasure μ]
    (hmass : μ univ = ν univ)
    (hloc : ∀ᵐ x ∂μ, ∃ U : Set A, IsOpen U ∧ x ∈ U ∧ μ.restrict U = ν.restrict U) :
    μ = ν := by
  let S : Set (Set A) := {U | IsOpen U ∧ μ.restrict U = ν.restrict U}
  obtain ⟨T,hTc,hTS,hTU⟩ := TopologicalSpace.isOpen_sUnion_countable S (fun U hU => hU.1)
  have hae : ∀ᵐ x ∂μ, x ∈ ⋃₀ T := by
    filter_upwards [hloc] with x hx
    obtain ⟨U,hU,hxU,heq⟩ := hx
    rw [hTU]
    exact mem_sUnion.mpr ⟨U,⟨hU,heq⟩,hxU⟩
  have heq : μ.restrict (⋃₀ T) = ν.restrict (⋃₀ T) :=
    (Measure.restrict_sUnion_congr hTc).mpr (fun U hU => (hTS hU).2)
  rw [Measure.restrict_eq_self_of_ae_mem hae] at heq
  exact Measure.eq_of_le_of_measure_univ_eq (heq.le.trans Measure.restrict_le_self) hmass

 

theorem homeomorph_measurePreserving_of_ae_local (μ : Measure A) [IsFiniteMeasure μ]
    (h : A ≃ₜ A)
    (hloc : ∀ᵐ x ∂μ, ∃ U : Set A, IsOpen U ∧ x ∈ U ∧
      ∀ S : Set A, MeasurableSet S → S ⊆ U → μ (h '' S) = μ S) :
    MeasurePreserving h μ μ := by
  have he : μ = Measure.comap h μ := by
    apply measure_eq_of_ae_local_restrict_eq
    · rw [h.measurableEmbedding.comap_apply, Set.image_univ, h.surjective.range_eq]
    · filter_upwards [hloc] with x hx
      obtain ⟨U,hU,hxU,hsets⟩ := hx
      refine ⟨U,hU,hxU,?_⟩
      ext S hS
      rw [Measure.restrict_apply hS,Measure.restrict_apply hS,
        h.measurableEmbedding.comap_apply]
      exact (hsets (S ∩ U) (hS.inter hU.measurableSet) inter_subset_right).symm
  refine ⟨h.continuous.measurable,?_⟩
  conv_lhs => rw [he]
  rw [h.measurableEmbedding.map_comap]
  simp only [h.surjective.range_eq,Measure.restrict_univ]

end PrimeDegreePackets

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
namespace PrimeDegreePackets.RootBox

variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}



lemma coordinateMeasure_of_haarConditionals (B : RootBox hij k) (μ : Measure (X n))
    [IsFiniteMeasure μ] (hhaar : B.HasHaarConditionals μ) :
    ∃ c : ℝ≥0, B.coordinateMeasure μ =
      ((B.coordinateMeasure μ).fst.prod (c • (volume : Measure ℝ))).restrict (univ ×ˢ B.time) := by
  obtain ⟨c,hc⟩ := hhaar
  refine ⟨c,?_⟩
  calc
    B.coordinateMeasure μ = (B.coordinateMeasure μ).fst ⊗ₘ B.conditionalKernel μ := by
      rw [conditionalKernel,Measure.disintegrate]
    _ = (B.coordinateMeasure μ).fst ⊗ₘ Kernel.const _ (c • volume.restrict B.time) :=
      Measure.compProd_congr hc
    _ = _ := by
      rw [Measure.compProd_const,←Measure.restrict_smul,←Measure.prod_restrict,Measure.restrict_univ]

lemma prod_volume_timeTranslation_invariant (ν : Measure (RootSlice i j k)) [SFinite ν]
    (c : ℝ≥0) (a : ℝ) :
    Measure.map (timeTranslation (i := i) (j := j) (k := k) a)
      (ν.prod (c • (volume : Measure ℝ))) = ν.prod (c • volume) := by
  change Measure.map (Prod.map id (fun t : ℝ => t+a)) _ = _
  rw [←Measure.map_prod_map ν _ measurable_id (by fun_prop),Measure.map_id,
    Measure.map_smul c (μ := (volume : Measure ℝ)) (f := fun t : ℝ => t + a),
    map_add_right_eq_self]

 

theorem coordinateMeasure_translate_of_haar (B : RootBox hij k) (μ : Measure (X n))
    [IsFiniteMeasure μ] (hhaar : B.HasHaarConditionals μ) (a : ℝ)
    {S : Set (RootSlice i j k × ℝ)} (hS : MeasurableSet S)
    (hSB : S ⊆ B.domain) (hTB : timeTranslation a '' S ⊆ B.domain) :
    B.coordinateMeasure μ (timeTranslation a '' S) = B.coordinateMeasure μ S := by
  obtain ⟨c,hc⟩ := B.coordinateMeasure_of_haarConditionals μ hhaar
  let ρ := (B.coordinateMeasure μ).fst.prod (c • (volume : Measure ℝ))
  have hT : MeasurableSet (timeTranslation a '' S) :=
    (timeTranslation a).measurableEmbedding.measurableSet_image.mpr hS
  have H := congrArg (fun m : Measure (RootSlice i j k × ℝ) => m (timeTranslation a '' S))
    (prod_volume_timeTranslation_invariant (B.coordinateMeasure μ).fst c a)
  rw [Measure.map_apply (timeTranslation a).continuous.measurable hT,
    (timeTranslation a).injective.preimage_image] at H
  rw [hc,Measure.restrict_apply hT,Measure.restrict_apply hS]
  rw [Set.inter_eq_left.mpr (hTB.trans (Set.prod_mono (subset_univ _) subset_rfl)),
    Set.inter_eq_left.mpr (hSB.trans (Set.prod_mono (subset_univ _) subset_rfl))]
  exact H.symm

end PrimeDegreePackets.RootBox
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootOverlaps
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.overlapMeasure_finite _root_.OAI.PrimeDegreePackets.RootBox.regularLeafKernel_locallyFinite _root_.OAI.PrimeDegreePackets.RootBox.regularLeafKernel_sFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.intrinsicRootKernel_locallyFinite _root_.OAI.PrimeDegreePackets.intrinsicRootKernel_sFinite _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
namespace PrimeDegreePackets.RootBox

variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

lemma overlapBox_domain_subset (B : RootBox hij k) (a : ℝ) :
    (B.overlapBox a).domain ⊆ B.domain := fun _ h => ⟨h.1,h.2.1⟩

lemma overlapBox_translate_domain_subset (B : RootBox hij k) (a : ℝ) :
    timeTranslation a '' (B.overlapBox a).domain ⊆ B.domain := by
  rintro _ ⟨z,hz,rfl⟩
  exact ⟨hz.1,hz.2.2⟩

 

theorem mass_translate_on_overlap (B : RootBox hij k) (μ : Measure (X n))
    [IsFiniteMeasure μ] (hhaar : B.HasHaarConditionals μ) (a : ℝ)
    {S : Set (X n)} (hS : MeasurableSet S) (hSC : S ⊆ (B.overlapBox a).range) :
    μ ((fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) '' S) = μ S := by
  let C := B.overlapBox a
  let T := (rootQuotientParametrization hij) ⁻¹' S ∩ C.domain
  have hT : MeasurableSet T :=
    ((rootQuotientParametrization_localHomeomorph hij).continuous.measurable hS).inter
      (C.transverse_open.prod C.time_open).measurableSet
  have hTC : T ⊆ C.domain := inter_subset_right
  have hTB : T ⊆ B.domain := hTC.trans (B.overlapBox_domain_subset a)
  have hshift : timeTranslation a '' T ⊆ B.domain :=
    (Set.image_mono hTC).trans (B.overlapBox_translate_domain_subset a)
  have hfT : rootQuotientParametrization hij '' T = S := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact hz.1
    · intro hx
      obtain ⟨z,hz⟩ := hSC hx
      refine ⟨z.val,⟨?_,z.prop⟩,hz⟩
      change rootQuotientParametrization hij z.val ∈ S
      change rootQuotientParametrization hij z.val = x at hz
      rwa [hz]
  have hfshift : rootQuotientParametrization hij '' (timeTranslation a '' T) =
      (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) '' S := by
    rw [Set.image_image,←hfT,Set.image_image]
    congr 1
    funext z
    exact rootQuotientParametrization_add hij z.1 z.2 a
  have H := B.coordinateMeasure_translate_of_haar μ hhaar a hT hTB hshift
  rw [B.coordinateMeasure_apply μ
      ((timeTranslation a).measurableEmbedding.measurableSet_image.mpr hT),
    B.coordinateMeasure_apply μ hT,
    Set.inter_eq_left.mpr hshift,Set.inter_eq_left.mpr hTB,hfshift,hfT] at H
  exact H

 

theorem local_mass_translate_of_endpoints (B : RootBox hij k) (μ : Measure (X n))
    [IsFiniteMeasure μ] (hhaar : B.HasHaarConditionals μ) (a : ℝ)
    (s : RootSlice i j k) (t : ℝ) (hs : s ∈ B.transverse)
    (ht : t ∈ B.time) (hta : t+a ∈ B.time) :
    ∃ U : Set (X n), IsOpen U ∧ rootQuotientParametrization hij (s,t) ∈ U ∧
      ∀ S : Set (X n), MeasurableSet S → S ⊆ U →
        μ ((fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) '' S) = μ S := by
  refine ⟨(B.overlapBox a).range,(B.overlapBox a).range_open,?_,?_⟩
  · exact ⟨⟨(s,t),⟨hs,ht,hta⟩⟩,rfl⟩
  · exact fun S hS hSU => B.mass_translate_on_overlap μ hhaar a hS hSU

end PrimeDegreePackets.RootBox


open MeasureTheory

open scoped BigOperators ENNReal

open NumberField Finset
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootLeaves
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.overlapMeasure_finite _root_.OAI.PrimeDegreePackets.RootBox.regularLeafKernel_locallyFinite _root_.OAI.PrimeDegreePackets.RootBox.regularLeafKernel_sFinite _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.intrinsicRootKernel_locallyFinite _root_.OAI.PrimeDegreePackets.intrinsicRootKernel_sFinite _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
namespace PrimeDegreePackets

 

lemma normalized_translation_invariant_measure (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (J : Set ℝ) (hJ : ν J = 1)
    (hinv : ∀ a : ℝ, Measure.map (fun t : ℝ => t+a) ν = ν) :
    ∃ c : ℝ≥0, ν = c • (volume : Measure ℝ) ∧ (c : ℝ≥0∞) = (volume J)⁻¹ := by
  let : ν.IsAddLeftInvariant := ⟨fun a => by simpa only [add_comm] using hinv a⟩
  let c := addHaarScalarFactor ν (volume : Measure ℝ)
  have he : ν = c • (volume : Measure ℝ) := isAddLeftInvariant_eq_smul ν volume
  refine ⟨c,he,?_⟩
  apply ENNReal.eq_inv_of_mul_eq_one_left
  have H := hJ
  rw [he,Measure.smul_apply] at H
  simpa only [ENNReal.smul_def,smul_eq_mul] using H

namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

 

theorem hasHaarConditionals_of_invariant_leafMeasure (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (hinv : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ a : ℝ,
      Measure.map (fun t : ℝ => t+a) (A.leafMeasure R μ s) = A.leafMeasure R μ s) :
    A.HasHaarConditionals μ := by
  have H : ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      ∃ c : ℝ≥0, A.conditionalKernel μ s = c • volume.restrict A.time ∧
        (c : ℝ≥0∞) = (volume A.time)⁻¹ := by
    filter_upwards [A.ae_leafMeasure_spec R hAR μ hfree,hinv] with s hs hi
    let := hs.1
    obtain ⟨c,hc,hcV⟩ := normalized_translation_invariant_measure
      (A.leafMeasure R μ s) A.time hs.2.1 hi
    refine ⟨c,?_,hcV⟩
    rw [←hs.2.2.1,hc,Measure.restrict_smul]
  by_cases hz : (A.coordinateMeasure μ).fst = 0
  · exact ⟨0,by simp only [hz,ae_zero,Filter.eventually_bot]⟩
  · let : NeZero (A.coordinateMeasure μ).fst := ⟨hz⟩
    obtain ⟨s,hs⟩ := H.exists
    obtain ⟨c,hc,hcV⟩ := hs
    refine ⟨c,?_⟩
    filter_upwards [H] with t ht
    obtain ⟨d,hd,hdV⟩ := ht
    have hdc : d = c := ENNReal.coe_injective (hdV.trans hcV.symm)
    simpa only [hdc] using hd

end RootBox
end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IntrinsicLeaves
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
namespace PrimeDegreePackets
variable {n : ℕ} {i j : Fin n} (hij : i ≠ j)



lemma ae_intrinsicRootKernel_eq (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ x ∂μ, intrinsicRootKernel hij μ hfree x = intrinsicRootLeaf hij μ x := by
  let κ : Kernel (X n) ℝ :=
    ⟨(aemeasurable_intrinsicRootLeaf hij μ hfree).mk (intrinsicRootLeaf hij μ),
      (aemeasurable_intrinsicRootLeaf hij μ hfree).measurable_mk⟩
  have he : ∀ᵐ x ∂μ, κ x = intrinsicRootLeaf hij μ x :=
    (aemeasurable_intrinsicRootLeaf hij μ hfree).ae_eq_mk.symm
  filter_upwards [he,ae_intrinsicRootLeaf_spec hij μ hfree] with x hx hs
  have : IsLocallyFiniteMeasure (κ x) := hx.symm ▸ hs.1
  exact (locallyFiniteRealVersion_eq κ x).trans hx

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma ae_eq_of_measurePreserving_ennreal_ge {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {T : α → α} (hT : MeasurePreserving T μ μ)
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hf1 : ∀ᵐ x ∂μ, f x ≤ 1)
    (hmono : ∀ᵐ x ∂μ, f (T x) ≤ f x) : f =ᵐ[μ] f ∘ T := by
  have hfT := hf.comp_quasiMeasurePreserving hT.quasiMeasurePreserving
  have he : ∫⁻ x, f (T x) ∂μ = ∫⁻ x, f x ∂μ := by
    have hf' : AEMeasurable f (μ.map T) := hT.map_eq.symm ▸ hf
    exact ((lintegral_map' hf' hT.measurable.aemeasurable).symm).trans
      (congrArg (fun ν : Measure α => ∫⁻ x, f x ∂ν) hT.map_eq)
  have hint : ∫⁻ x, f (T x) ∂μ < ∞ := by
    rw [he]
    exact (lintegral_mono_ae hf1).trans_lt (by simp)
  exact (ae_eq_of_ae_le_of_lintegral_le hmono hint.ne hf he.ge).symm

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LeafPeriods
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.chosenFinitePlaceBaseNontriviallyNormedField _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
namespace PrimeDegreePackets


lemma continuous_integral_translate (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (f : C_c(ℝ,ℝ)) : Continuous (fun a : ℝ => ∫ x, f (x+a) ∂ν) := by
  have H := ((f.hasCompactSupport.comp_homeomorph (Homeomorph.neg ℝ)).continuous_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) (locallyIntegrable_const (μ := ν) (1:ℝ))
    (f.continuous.comp continuous_neg)).comp continuous_neg
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  ext a
  simp only [Function.comp_apply,convolution_def,ContinuousLinearMap.mul_apply',one_mul]
  congr 1
  funext x
  congr 1
  simp

lemma realLeafPeriods_eq_tests (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] :
    (realLeafPeriods ν : Set ℝ) =
      ⋂ f : C_c(ℝ,ℝ), {a | (∫ x, f (x+a) ∂ν) = ∫ x, f x ∂ν} := by
  ext a
  simp only [mem_iInter,mem_ofPred_eq]
  constructor
  · intro ha f
    change ν.map (fun x => x+a) = ν at ha
    have H := integral_map (μ := ν) («φ» := fun x : ℝ => x+a)
      (f := fun x => f x) (by fun_prop) f.continuous.aestronglyMeasurable
    rw [ha] at H
    exact H.symm
  · intro ha
    have : (ν.map (fun x : ℝ => x+a)).Regular :=
      Measure.Regular.map (Homeomorph.addRight a)
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_map (μ := ν) («φ» := fun x : ℝ => x+a)
      (f := fun x => f x) (by fun_prop) f.continuous.aestronglyMeasurable]
    exact ha f

 

theorem isClosed_realLeafPeriods (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] :
    IsClosed (realLeafPeriods ν : Set ℝ) := by
  rw [realLeafPeriods_eq_tests]
  exact isClosed_iInter fun f => isClosed_eq (continuous_integral_translate ν f) continuous_const

lemma realLeafPeriods_eq_top_of_dense (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hd : Dense (realLeafPeriods ν : Set ℝ)) : realLeafPeriods ν = ⊤ := by
  apply SetLike.coe_injective
  change (realLeafPeriods ν : Set ℝ) = univ
  rw [←(isClosed_realLeafPeriods ν).closure_eq,hd.closure_eq]

 

theorem realLeaf_invariant_of_small_periods (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hs : ∀ ε > 0, ∃ a ∈ realLeafPeriods ν, a ∈ Set.Ioo 0 ε) (a : ℝ) :
    ν.map (fun x => x+a) = ν := by
  have H := realLeafPeriods_eq_top_of_dense ν ((realLeafPeriods ν).dense_of_not_isolated_zero hs)
  change a ∈ realLeafPeriods ν
  rw [H]
  trivial



end PrimeDegreePackets


namespace PrimeDegreePackets

lemma leafTest_apply (N k : ℕ) (x : ℝ) :
    leafTest N k x = (denseSeq (leafTestSpace N) k).val x := rfl

lemma continuous_leafTestSpace_integral (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (N : ℕ) (a : ℝ) : Continuous
      (fun f : leafTestSpace N => ∫ x, f.val (x+a) ∂ν) := by
  rw [←continuousOn_univ]
  apply continuousOn_integral_of_compact_support
    ((Homeomorph.addRight a).isCompact_preimage.mpr (isCompact_Icc (a := -(N:ℝ)) (b := N)))
  · have H : Continuous (fun p : leafTestSpace N × ℝ => p.1.val (p.2+a)) := by
      exact continuous_eval.comp ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_snd.add_const a))
    exact H.continuousOn
  · intro f x _ hx
    exact f.prop (x+a) hx

 
lemma realLeafPeriods_iff_countable_tests (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] (a : ℝ) :
    a ∈ realLeafPeriods ν ↔ ∀ N k : ℕ,
      (∫ x, leafTest N k (x+a) ∂ν) = ∫ x, leafTest N k x ∂ν := by
  rw [show a ∈ realLeafPeriods ν ↔ ∀ f : C_c(ℝ,ℝ),
      (∫ x, f (x+a) ∂ν) = ∫ x, f x ∂ν from by
    rw [←SetLike.mem_coe,realLeafPeriods_eq_tests]
    simp only [mem_iInter,mem_ofPred_eq]]
  constructor
  · intro h N k
    exact h _
  · intro h f
    obtain ⟨R,hR⟩ := f.hasCompactSupport.isBounded.subset_closedBall 0
    obtain ⟨N,hN⟩ := exists_nat_gt R
    have hs : ∀ x : ℝ, x ∉ Icc (-(N:ℝ)) N → f x = 0 := by
      intro x hx
      by_contra hf
      have hb := hR (subset_closure hf)
      rw [Metric.mem_closedBall,Real.dist_eq,sub_zero] at hb
      have hb' := abs_le.mp (hb.trans hN.le)
      exact hx hb'
    let f' : leafTestSpace N := ⟨f.toContinuousMap,hs⟩
    have hh : (fun g : leafTestSpace N => ∫ x, g.val (x+a) ∂ν) =
        (fun g : leafTestSpace N => ∫ x, g.val (x+0) ∂ν) := by
      apply (denseRange_denseSeq (leafTestSpace N)).equalizer
        (continuous_leafTestSpace_integral ν N a) (continuous_leafTestSpace_integral ν N 0)
      funext k
      simpa only [Function.comp_apply,add_zero,leafTest_apply] using h N k
    have H := congrFun hh f'
    simpa only [f',add_zero,CompactlySupportedContinuousMap.coe_toContinuousMap] using H

 

lemma continuous_leafTest_discrepancy (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (N k : ℕ) : Continuous (fun a : ℝ =>
      (∫ x, leafTest N k (x+a) ∂ν) - ∫ x, leafTest N k x ∂ν) :=
  (continuous_integral_translate ν (leafTest N k)).sub continuous_const

lemma measurable_leafTest_discrepancy {α : Type*} [MeasurableSpace α]
    (κ : Kernel α ℝ) (N k : ℕ) (a : ℝ) : Measurable (fun z =>
      (∫ x, leafTest N k (x+a) ∂κ z) - ∫ x, leafTest N k x ∂κ z) := by
  exact (((leafTest N k).continuous.comp (continuous_id.add_const a)).stronglyMeasurable.integral_kernel).measurable.sub
    ((leafTest N k).continuous.stronglyMeasurable.integral_kernel).measurable

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma realLeafPeriods_smul (ν : Measure ℝ) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hcT : c ≠ ∞) :
    realLeafPeriods (c • ν) = realLeafPeriods ν := by
  ext a
  simp only [mem_realLeafPeriods,Measure.map_smul c (μ := ν) (f := fun x : ℝ => x+a)]
  constructor
  · intro he
    have H := congrArg (fun ρ : Measure ℝ => c⁻¹ • ρ) he
    simpa only [smul_smul,ENNReal.inv_mul_cancel hc0 hcT,one_smul] using H
  · exact congrArg (fun ρ : Measure ℝ => c • ρ)

lemma realLeafPeriods_scaling (ν : Measure ℝ) (c : ℝ) (hc : c ≠ 0) (a : ℝ) :
    c*a ∈ realLeafPeriods (ν.map (Homeomorph.mulLeft₀ c hc)) ↔ a ∈ realLeafPeriods ν := by
  have H : (ν.map (Homeomorph.mulLeft₀ c hc)).map (fun x => x+c*a) =
      (ν.map (fun x => x+a)).map (Homeomorph.mulLeft₀ c hc) := by
    rw [Measure.map_map (by fun_prop) (Homeomorph.mulLeft₀ c hc).measurable,
      Measure.map_map (Homeomorph.mulLeft₀ c hc).measurable (by fun_prop)]
    congr 1
    ext x
    change c*x+c*a = c*(x+a)
    ring
  simp only [mem_realLeafPeriods,H]
  exact (Homeomorph.mulLeft₀ c hc).measurableEmbedding.map_injective.eq_iff

lemma realLeafPeriods_normalized_scaling (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hp : ∀ r : ℝ, 0 < r → 0 < ν (Metric.ball 0 r))
    (c : ℝ) (hc : 0 < c) (a : ℝ) :
    c*a ∈ realLeafPeriods
      (anchorNormalize (ν.map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1)) ↔
        a ∈ realLeafPeriods ν := by
  have hm : ν.map (Homeomorph.mulLeft₀ c hc.ne') (Metric.ball 0 1) =
      ν (Metric.ball 0 (1/c)) := by
    rw [Measure.map_apply (Homeomorph.mulLeft₀ c hc.ne').measurable
      Metric.isOpen_ball.measurableSet,realScaling_preimage_ball c 1 hc]
  unfold anchorNormalize
  rw [realLeafPeriods_smul _ _ (by rw [hm]; exact ENNReal.inv_ne_zero.mpr measure_ball_lt_top.ne)
    (by rw [hm]; exact ENNReal.inv_ne_top.mpr (hp _ (by positivity)).ne')]
  exact realLeafPeriods_scaling ν c hc.ne' a


lemma hasSmallLeafPeriod_mono (ν : Measure ℝ) {r R : ℝ} (hr : r ≤ R) :
    hasSmallLeafPeriod ν r → hasSmallLeafPeriod ν R := by
  rintro ⟨a,ha,hp,hs⟩
  exact ⟨a,ha,hp,hs.trans hr⟩

lemma hasSmallLeafPeriod_normalized_scaling (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hp : ∀ r : ℝ, 0 < r → 0 < ν (Metric.ball 0 r))
    (c : ℝ) (hc : 0 < c) (R : ℝ) :
    hasSmallLeafPeriod
      (anchorNormalize (ν.map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1)) R ↔
      hasSmallLeafPeriod ν (R/c) := by
  constructor
  · rintro ⟨a,ha,hap,haR⟩
    refine ⟨a/c,?_,div_pos hap hc,(div_le_div_iff_of_pos_right hc).mpr haR⟩
    apply (realLeafPeriods_normalized_scaling ν hp c hc (a/c)).mp
    simpa only [mul_div_cancel₀ _ hc.ne'] using ha
  · rintro ⟨a,ha,hap,haR⟩
    exact ⟨c*a,(realLeafPeriods_normalized_scaling ν hp c hc a).mpr ha,
      mul_pos hc hap,by simpa only [mul_comm] using (le_div_iff₀ hc).mp haR⟩

 

lemma exists_pos_leafPeriod_normalized_scaling (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hp : ∀ r : ℝ, 0 < r → 0 < ν (Metric.ball 0 r))
    (c : ℝ) (hc : 0 < c) :
    (∃ a ∈ realLeafPeriods
      (anchorNormalize (ν.map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1)), 0 < a) ↔
    ∃ a ∈ realLeafPeriods ν, 0 < a := by
  constructor
  · rintro ⟨a,ha,hap⟩
    refine ⟨a/c,?_,div_pos hap hc⟩
    apply (realLeafPeriods_normalized_scaling ν hp c hc (a/c)).mp
    simpa only [mul_div_cancel₀ _ hc.ne'] using ha
  · rintro ⟨a,ha,hap⟩
    exact ⟨c*a,(realLeafPeriods_normalized_scaling ν hp c hc a).mpr ha,mul_pos hc hap⟩

end PrimeDegreePackets

open MeasureTheory Set Filter TopologicalSpace
namespace PrimeDegreePackets

lemma exists_compact_zero_iff_dense_tests {T : Type*} [TopologicalSpace T]
    [CompactSpace T] [SeparableSpace T] [Nonempty T]
    (F : ℕ → T → ℝ) (hF : ∀ n, Continuous (F n)) :
    (∃ t : T, ∀ n, F n t = 0) ↔
      ∀ k : ℕ, ∃ j : ℕ, ∀ i : Fin (k+1),
        |F i (denseSeq T j)| < 1/((k:ℝ)+1) := by
  constructor
  · rintro ⟨t,ht⟩ k
    let U := ⋂ i : Fin (k+1), {t : T | |F i t| < 1/((k:ℝ)+1)}
    have hU : IsOpen U := isOpen_iInter_of_finite fun i =>
      isOpen_lt (hF i).abs continuous_const
    have htU : t ∈ U := by
      simp only [U,mem_iInter,mem_ofPred_eq,ht,abs_zero]
      intro _
      positivity
    obtain ⟨j,hj⟩ := (denseRange_denseSeq T).exists_mem_open hU ⟨t,htU⟩
    exact ⟨j,fun i => mem_iInter.mp hj i⟩
  · intro h
    let C (k : ℕ) := ⋂ i : Fin (k+1), {t : T | |F i t| ≤ 1/((k:ℝ)+1)}
    have hclosed (k : ℕ) : IsClosed (C k) := isClosed_iInter fun i =>
      isClosed_le (hF i).abs continuous_const
    have hnonempty (k : ℕ) : (C k).Nonempty := by
      obtain ⟨j,hj⟩ := h k
      exact ⟨denseSeq T j,mem_iInter.mpr fun i => (hj i).le⟩
    have hanti (k : ℕ) : C (k+1) ⊆ C k := by
      intro t ht
      apply mem_iInter.mpr
      intro i
      have H : |F i t| ≤ 1/(((k+1:ℕ):ℝ)+1) :=
        mem_iInter.mp ht ⟨i.val,by omega⟩
      exact H.trans (Nat.one_div_le_one_div (Nat.le_succ k))
    obtain ⟨t,ht⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
      hanti hnonempty (hclosed 0).isCompact hclosed
    refine ⟨t,fun i => ?_⟩
    have H : ∀ᶠ k : ℕ in atTop, |F i t| ≤ 1/((k:ℝ)+1) := by
      filter_upwards [eventually_ge_atTop i] with k hk
      exact mem_iInter.mp (mem_iInter.mp ht k) ⟨i,by omega⟩
    have hz : |F i t| ≤ 0 := ge_of_tendsto tendsto_one_div_add_atTop_nhds_zero_nat H
    exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))

 

theorem measurableSet_exists_compact_zero {α T : Type*} [MeasurableSpace α]
    [TopologicalSpace T] [CompactSpace T] [SeparableSpace T] [Nonempty T]
    (F : ℕ → α → T → ℝ)
    (hm : ∀ n t, Measurable (fun x => F n x t))
    (hc : ∀ n x, Continuous (F n x)) :
    MeasurableSet {x : α | ∃ t : T, ∀ n, F n x t = 0} := by
  simp_rw [exists_compact_zero_iff_dense_tests (fun n => F n _) (fun n => hc n _)]
  simp_rw [Set.ofPred_forall,Set.ofPred_exists]
  exact MeasurableSet.iInter fun k => MeasurableSet.iUnion fun j =>
    by
      rw [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i : Fin (k+1) =>
        measurableSet_lt (hm i (denseSeq T j)).abs measurable_const

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma measurableSet_exists_leafPeriod_Icc {α : Type*} [MeasurableSpace α]
    (κ : Kernel α ℝ) [∀ x, IsLocallyFiniteMeasure (κ x)] (a b : ℝ) :
    MeasurableSet {x : α | ∃ t ∈ Icc a b, t ∈ realLeafPeriods (κ x)} := by
  by_cases hab : a ≤ b
  · let T := ↥(Icc a b)
    let : Nonempty T := ⟨⟨a,le_rfl,hab⟩⟩
    let : CompactSpace T := isCompact_iff_compactSpace.mp isCompact_Icc
    let : SecondCountableTopology T := Subtype.secondCountableTopology _
    let F (n : ℕ) (x : α) (t : T) : ℝ :=
      (∫ y, leafTest n.unpair.1 n.unpair.2 (y+t.val) ∂κ x) -
        ∫ y, leafTest n.unpair.1 n.unpair.2 y ∂κ x
    have H := measurableSet_exists_compact_zero F
      (fun n t => measurable_leafTest_discrepancy κ _ _ t.val)
      (fun n x => (continuous_leafTest_discrepancy (κ x) _ _).comp continuous_subtype_val)
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    constructor
    · rintro ⟨t,ht,hp⟩
      exact ⟨⟨t,ht⟩,fun n => sub_eq_zero.mpr
        ((realLeafPeriods_iff_countable_tests (κ x) t).mp hp _ _)⟩
    · rintro ⟨t,ht⟩
      refine ⟨t.val,t.prop,(realLeafPeriods_iff_countable_tests (κ x) t.val).mpr ?_⟩
      intro N k
      have H := ht (Nat.pair N k)
      simpa only [F,Nat.unpair_pair,sub_eq_zero] using H
  · have he : {x : α | ∃ t ∈ Icc a b, t ∈ realLeafPeriods (κ x)} = ∅ := by
      ext x
      simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false,not_exists]
      rintro t ⟨ht,_⟩
      exact hab (ht.1.trans ht.2)
    rw [he]
    exact MeasurableSet.empty

 

theorem measurableSet_hasSmallLeafPeriod {α : Type*} [MeasurableSpace α]
    (κ : Kernel α ℝ) [∀ x, IsLocallyFiniteMeasure (κ x)] (R : ℝ) :
    MeasurableSet {x : α | hasSmallLeafPeriod (κ x) R} := by
  have he : {x : α | hasSmallLeafPeriod (κ x) R} =
      ⋃ m : ℕ, {x : α | ∃ t ∈ Icc (1/((m:ℝ)+1)) R, t ∈ realLeafPeriods (κ x)} := by
    ext x
    simp only [mem_iUnion,mem_ofPred_eq]
    constructor
    · rintro ⟨t,ht,hp,hs⟩
      obtain ⟨m,hm⟩ := exists_nat_one_div_lt hp
      exact ⟨m,t,⟨hm.le,hs⟩,ht⟩
    · rintro ⟨m,t,ht,hp⟩
      exact ⟨t,hp,lt_of_lt_of_le (by positivity) ht.1,ht.2⟩
  rw [he]
  exact MeasurableSet.iUnion fun m => measurableSet_exists_leafPeriod_Icc κ _ _

 
theorem measurableSet_exists_pos_leafPeriod {α : Type*} [MeasurableSpace α]
    (κ : Kernel α ℝ) [∀ x, IsLocallyFiniteMeasure (κ x)] :
    MeasurableSet {x : α | ∃ a ∈ realLeafPeriods (κ x), 0 < a} := by
  have he : {x : α | ∃ a ∈ realLeafPeriods (κ x), 0 < a} =
      ⋃ m : ℕ, {x : α | hasSmallLeafPeriod (κ x) ((m:ℝ)+1)} := by
    ext x
    simp only [mem_iUnion,mem_ofPred_eq]
    constructor
    · rintro ⟨a,ha,hap⟩
      obtain ⟨m,hm⟩ := exists_nat_gt a
      exact ⟨m,a,ha,hap,by linarith⟩
    · rintro ⟨m,a,ha,hap,_⟩
      exact ⟨a,ha,hap⟩
  rw [he]
  exact MeasurableSet.iUnion fun m => measurableSet_hasSmallLeafPeriod κ _

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma ae_hasSmallLeafPeriod_scaling {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α ℝ)
    [∀ x, IsLocallyFiniteMeasure (κ x)]
    (hp : ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 < κ x (Metric.ball 0 r))
    {T : α → α} (hT : MeasurePreserving T μ μ) (c : ℝ) (hc : 1 ≤ c)
    (hcov : ∀ᵐ x ∂μ, κ (T x) =
      anchorNormalize ((κ x).map (Homeomorph.mulLeft₀ c (by linarith))) (Metric.ball 0 1))
    (R : ℝ) (hR : 0 ≤ R) :
    ∀ᵐ x ∂μ, hasSmallLeafPeriod (κ x) R ↔ hasSmallLeafPeriod (κ x) (R/c) := by
  classical
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  let E : Set α := {x | hasSmallLeafPeriod (κ x) R}
  let f : α → ℝ≥0∞ := E.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator (measurableSet_hasSmallLeafPeriod κ R)
  have he : ∀ᵐ x ∂μ, T x ∈ E ↔ hasSmallLeafPeriod (κ x) (R/c) := by
    filter_upwards [hp,hcov] with x hx hcovx
    change hasSmallLeafPeriod (κ (T x)) R ↔ _
    rw [hcovx]
    exact hasSmallLeafPeriod_normalized_scaling (κ x) hx c hc0 R
  have hmono : ∀ᵐ x ∂μ, f (T x) ≤ f x := by
    filter_upwards [he] with x hx
    by_cases h : T x ∈ E
    · have hxE : x ∈ E := hasSmallLeafPeriod_mono (κ x)
        (div_le_self hR hc) (hx.mp h)
      simp only [f,indicator_of_mem h,indicator_of_mem hxE,le_refl]
    · simp only [f,indicator_of_notMem h]
      exact bot_le
  have heq := ae_eq_of_measurePreserving_ennreal_ge μ hT hf.aemeasurable
    (Eventually.of_forall fun x => show f x ≤ 1 from by
      by_cases hx : x ∈ E <;> simp [f,hx]) hmono
  filter_upwards [he,heq] with x hx heqx
  have hiff : x ∈ E ↔ T x ∈ E := by
    by_cases hxE : x ∈ E <;> by_cases hTE : T x ∈ E <;>
      simp_all [f,Function.comp_apply]
  exact hiff.trans hx

 

theorem ae_realLeafPeriods_bot_or_top {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α ℝ)
    [∀ x, IsLocallyFiniteMeasure (κ x)]
    (hp : ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 < κ x (Metric.ball 0 r))
    (hscaling : ∀ (c : ℝ) (hc : 0 < c), ∃ T : α → α, MeasurePreserving T μ μ ∧
      ∀ᵐ x ∂μ, κ (T x) = anchorNormalize
        ((κ x).map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1)) :
    ∀ᵐ x ∂μ, realLeafPeriods (κ x) = ⊥ ∨ realLeafPeriods (κ x) = ⊤ := by
  have H (m k : ℕ) : ∀ᵐ x ∂μ, hasSmallLeafPeriod (κ x) ((m:ℝ)+1) ↔
      hasSmallLeafPeriod (κ x) (1/((k:ℝ)+1)) := by
    let c : ℝ := ((m:ℝ)+1)*((k:ℝ)+1)
    have hc : 1 ≤ c := by
      dsimp [c]
      nlinarith [Nat.cast_nonneg (α := ℝ) m,Nat.cast_nonneg (α := ℝ) k]
    obtain ⟨T,hT,hcov⟩ := hscaling c (zero_lt_one.trans_le hc)
    have he := ae_hasSmallLeafPeriod_scaling μ κ hp hT c hc hcov ((m:ℝ)+1) (by positivity)
    have hdiv : ((m:ℝ)+1)/c = 1/((k:ℝ)+1) := by
      dsimp [c]
      field_simp
    simpa only [hdiv] using he
  have HH : ∀ᵐ x ∂μ, ∀ m k : ℕ, hasSmallLeafPeriod (κ x) ((m:ℝ)+1) ↔
      hasSmallLeafPeriod (κ x) (1/((k:ℝ)+1)) := by
    exact ae_all_iff.mpr fun m => ae_all_iff.mpr fun k => H m k
  filter_upwards [HH] with x hx
  by_cases hn : ∃ a ∈ realLeafPeriods (κ x), 0 < a
  · right
    obtain ⟨a,ha,hap⟩ := hn
    obtain ⟨m,hm⟩ := exists_nat_gt a
    have hlarge : hasSmallLeafPeriod (κ x) ((m:ℝ)+1) :=
      ⟨a,ha,hap,by linarith⟩
    apply SetLike.coe_injective
    ext a
    simp only [AddSubgroup.coe_top,mem_univ,iff_true]
    apply realLeaf_invariant_of_small_periods
    intro ε hε
    obtain ⟨k,hk⟩ := exists_nat_one_div_lt hε
    obtain ⟨t,ht,htp,htr⟩ := (hx m k).mp hlarge
    exact ⟨t,ht,htp,htr.trans_lt hk⟩
  · left
    ext a
    rw [AddSubgroup.mem_bot]
    constructor
    · intro ha
      have ha0 : a ≤ 0 := le_of_not_gt fun h => hn ⟨a,ha,h⟩
      have hna : -a ≤ 0 := le_of_not_gt fun h => hn ⟨-a,(realLeafPeriods (κ x)).neg_mem ha,h⟩
      linarith
    · rintro rfl
      exact (realLeafPeriods (κ x)).zero_mem

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_AmbientLeaves
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
namespace PrimeDegreePackets
namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

lemma ae_coordinate_of_ambient (A : RootBox hij k) (μ : Measure (X n))
    {P : X n → Prop} (hp : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ z ∂A.coordinateMeasure μ, P (rootQuotientParametrization hij z) := by
  have H : ∀ᵐ x ∂μ.restrict A.range, P x := ae_restrict_of_ae hp
  rw [←A.map_coordinateMeasure μ] at H
  exact ae_of_ae_map (rootQuotientParametrization_localHomeomorph hij).continuous.measurable.aemeasurable H

 

theorem ae_leafMeasure_of_ambient (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    {P : X n → Prop} (hp : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ᵐ t ∂A.leafMeasure R μ s,
      P (rootQuotientParametrization hij (s,t)) := by
  let C := rootLongBoxFamily hij k R
  let (m : ℕ) : Countable (C m) := (rootLongBoxFamily_countable hij k R m).to_subtype
  have hT (m : ℕ) (B : C m) : B.val.time = rootLeafWindow R m :=
    rootLongBoxFamily_time hij k R m B.val B.prop
  have hinc (m : ℕ) (B : C m) : A.time ⊆ B.val.time := by
    rw [hT m B]
    exact hAR.trans (rootLeafWindow_mono R (Nat.zero_le m))
  have HD (D : RootBox hij k) : ∀ᵐ s ∂(D.coordinateMeasure μ).fst,
      ∀ᵐ t ∂D.conditionalKernel μ s, P (rootQuotientParametrization hij (s,t)) := by
    have H : ∀ᵐ z ∂(D.coordinateMeasure μ).fst ⊗ₘ D.conditionalKernel μ,
        P (rootQuotientParametrization hij z) := by
      simpa only [conditionalKernel,Measure.disintegrate] using D.ae_coordinate_of_ambient μ hp
    exact Measure.ae_ae_of_ae_compProd H
  have H (m : ℕ) (B : C m) : ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      s ∈ B.val.transverse → ∀ᵐ t ∂(A.leafMeasure R μ s).restrict (rootLeafWindow R m),
        P (rootQuotientParametrization hij (s,t)) := by
    filter_upwards [A.ae_leafMeasure_restrict R hAR μ hfree B.val (hinc m B),
      A.base_ae_of_ae B.val (hinc m B) μ (HD B.val)] with s hs hd hsb
    have hh := ae_restrict_of_ae (s := B.val.time) (Measure.ae_smul_measure (hd hsb)
      ((B.val.conditionalKernel μ s A.time)⁻¹))
    change ∀ᵐ t ∂(anchorNormalize (B.val.conditionalKernel μ s) A.time).restrict B.val.time,
      P (rootQuotientParametrization hij (s,t)) at hh
    rw [←(hs hsb).2,hT m B] at hh
    exact hh
  have Hall := ae_all_iff.mpr (fun m => ae_all_iff.mpr (H m))
  filter_upwards [Hall,A.ae_injective_root_slice_of_ae_free μ hfree] with s hs hi
  have HW (m : ℕ) : ∀ᵐ t ∂(A.leafMeasure R μ s).restrict (rootLeafWindow R m),
      P (rootQuotientParametrization hij (s,t)) := by
    obtain ⟨B,hBC,hsB⟩ := rootLongBoxFamily_covers hij k R m s hi
    exact hs m ⟨B,hBC⟩ hsB
  have HH := (ae_restrict_iUnion_iff (μ := A.leafMeasure R μ s) (rootLeafWindow R) _).mpr HW
  simpa only [rootLeafWindow_cover,Measure.restrict_univ] using HH

lemma ae_basedLeaf_of_ambient (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    {P : X n → Prop} (hp : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ z ∂A.coordinateMeasure μ, ∀ᵐ t ∂A.basedLeaf R μ z,
      P (rightAction (rootQuotientParametrization hij z)
        (Matrix.SpecialLinearGroup.transvection hij t)) := by
  have H := ae_of_ae_map measurable_fst.aemeasurable (A.ae_leafMeasure_of_ambient R hAR μ hfree hp)
  filter_upwards [H] with z hz
  apply Measure.ae_smul_measure
  apply (Homeomorph.subRight z.2).measurableEmbedding.ae_map_iff.mpr
  filter_upwards [hz] with t ht
  change P (rightAction (rootQuotientParametrization hij z)
    (Matrix.SpecialLinearGroup.transvection hij (t-z.2)))
  rw [←rootQuotientParametrization_add]
  simpa only [←add_sub_assoc,add_sub_cancel_left] using ht

end RootBox

 

theorem ae_intrinsicRootLeaf_of_ambient {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    {P : X n → Prop} (hp : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ x ∂μ, ∀ᵐ t ∂intrinsicRootLeaf hij μ x,
      P (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) := by
  let : Countable (boundedRootAtlas hij) := (boundedRootAtlas_countable hij).to_subtype
  have H (B : boundedRootAtlas hij) : ∀ᵐ x ∂μ.restrict B.val.box.range,
      ∀ᵐ t ∂intrinsicRootLeaf hij μ x,
        P (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) := by
    apply B.val.box.ae_of_coordinate μ
    filter_upwards [B.val.box.ae_intrinsicRootLeaf_coordinates B.val.radius B.val.time_bound μ hfree,
      B.val.box.ae_basedLeaf_of_ambient B.val.radius B.val.time_bound μ hfree hp] with z he hz
    rwa [he]
  have HH := (ae_restrict_iUnion_iff (μ := μ) (fun B : boundedRootAtlas hij => B.val.box.range) _).mpr H
  simpa only [boundedRootAtlas_iUnion,Measure.restrict_univ] using HH

end PrimeDegreePackets


open scoped Topology ENNReal

open scoped Matrix Topology ENNReal ProbabilityTheory


namespace PrimeDegreePackets

lemma translation_invariant_of_based (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (t : ℝ) (ht : 0 < ν (Metric.ball t 1))
    (hinv : ∀ a : ℝ, (basedRealMeasure ν t).map (fun u => u+a) = basedRealMeasure ν t) :
    ∀ a : ℝ, ν.map (fun u => u+a) = ν := by
  have hnorm : centerRealMeasure ν t = ν (Metric.ball t 1) • basedRealMeasure ν t := by
    unfold basedRealMeasure anchorNormalize
    rw [centerRealMeasure_ball,smul_smul,ENNReal.mul_inv_cancel ht.ne' measure_ball_lt_top.ne,one_smul]
  intro a
  apply (Homeomorph.subRight t).measurableEmbedding.map_injective
  change centerRealMeasure (ν.map (fun u => u+a)) t = centerRealMeasure ν t
  have hcomm : centerRealMeasure (ν.map (fun u => u+a)) t =
      (centerRealMeasure ν t).map (fun u => u+a) := by
    unfold centerRealMeasure
    rw [Measure.map_map (Homeomorph.subRight t).measurable (by fun_prop),
      Measure.map_map (by fun_prop) (Homeomorph.subRight t).measurable]
    congr 1
    funext u
    change u+a-t=(u-t)+a
    ring
  rw [hcomm,hnorm,Measure.map_smul (f := fun value : ℝ => value+a),hinv a]

namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

 

theorem hasHaarConditionals_of_intrinsic (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (hinv : ∀ᵐ x ∂μ, ∀ a : ℝ,
      (intrinsicRootLeaf hij μ x).map (fun t => t+a) = intrinsicRootLeaf hij μ x) :
    A.HasHaarConditionals μ := by
  apply A.hasHaarConditionals_of_invariant_leafMeasure R hAR μ hfree
  have H : ∀ᵐ z ∂A.coordinateMeasure μ, ∀ a : ℝ,
      (A.leafMeasure R μ z.1).map (fun t => t+a) = A.leafMeasure R μ z.1 := by
    have Hlf := ae_of_ae_map measurable_fst.aemeasurable
      ((A.ae_leafMeasure_spec R hAR μ hfree).mono fun _ h => h.1)
    filter_upwards [A.ae_coordinate_of_ambient μ hinv,
      A.ae_intrinsicRootLeaf_coordinates R hAR μ hfree,
      A.ae_leafMeasure_ball_pos R hAR μ hfree,Hlf] with z hi he hp hf
    let : IsLocallyFiniteMeasure (A.leafMeasure R μ z.1) := hf
    apply translation_invariant_of_based _ z.2 (hp 1 zero_lt_one)
    rwa [he] at hi
  have HC : ∀ᵐ z ∂(A.coordinateMeasure μ).fst ⊗ₘ A.conditionalKernel μ, ∀ a : ℝ,
      (A.leafMeasure R μ z.1).map (fun t => t+a) = A.leafMeasure R μ z.1 := by
    simpa only [conditionalKernel,Measure.disintegrate] using H
  filter_upwards [Measure.ae_ae_of_ae_compProd HC] with s hs
  obtain ⟨t,ht⟩ := hs.exists
  exact ht

end RootBox

 

theorem root_invariant_of_intrinsic (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hinv : ∀ᵐ x ∂μ, ∀ a : ℝ,
      (intrinsicRootLeaf hij μ x).map (fun t => t+a) = intrinsicRootLeaf hij μ x)
    (a : ℝ) : μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij a)) = μ := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  apply (homeomorph_measurePreserving_of_ae_local μ
    (rightActionHomeomorph (Matrix.SpecialLinearGroup.transvection hij a)) ?_).map_eq
  filter_upwards [ae_rootBox_arbitrary_length d μ hA] with x hx
  obtain ⟨k,B,s,t,hs,hI,hx⟩ := hx i j hij (|a|+1)
  let W := Ioo (t-(|a|+1)) (t+(|a|+1))
  let C := B.shrink B.transverse W B.transverse_open isOpen_Ioo subset_rfl (Ioo_subset_Icc_self.trans hI)
  have hbound : C.time ⊆ rootLeafWindow (|t|+|a|+2) 0 := by
    intro u hu
    change u ∈ W at hu
    change -((|t|+|a|+2)+(0:ℕ)) < u ∧ u < (|t|+|a|+2)+(0:ℕ)
    dsimp [W] at hu
    constructor <;> push_cast <;> linarith [hu.1,hu.2,neg_abs_le t,le_abs_self t]
  have ht : t ∈ C.time := by
    change t ∈ W
    dsimp [W]
    constructor <;> linarith [abs_nonneg a]
  have hta : t+a ∈ C.time := by
    change t+a ∈ W
    dsimp [W]
    constructor <;> linarith [neg_abs_le a,le_abs_self a]
  change ∃ U : Set (X (d+1)), IsOpen U ∧ x ∈ U ∧
    ∀ S : Set (X (d+1)), MeasurableSet S → S ⊆ U →
      μ ((fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) '' S) = μ S
  simpa only [hx] using C.local_mass_translate_of_endpoints μ
    (C.hasHaarConditionals_of_intrinsic _ hbound μ hfree hinv) a s t hs ht hta



end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootInvariance
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
namespace PrimeDegreePackets

 

theorem ae_intrinsicRootLeaf_periods_bot_or_top (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ, realLeafPeriods (intrinsicRootLeaf hij μ x) = ⊥ ∨
      realLeafPeriods (intrinsicRootLeaf hij μ x) = ⊤ := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  let κ := intrinsicRootKernel hij μ hfree
  have heq : ∀ᵐ x ∂μ, κ x = intrinsicRootLeaf hij μ x := ae_intrinsicRootKernel_eq hij μ hfree
  have hp : ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 < κ x (Metric.ball 0 r) := by
    filter_upwards [heq,ae_intrinsicRootLeaf_ball_pos hij μ hfree] with x hx hp
    rwa [hx]
  have H := ae_realLeafPeriods_bot_or_top μ κ hp (by
    intro c hc
    let T : X (d+1) → X (d+1) := fun x => rightAction x (rootCanonicalFlow d j (Real.log c))
    have hT : MeasurePreserving T μ μ := rootCanonicalFlow_preserving d j (Real.log c) μ hA
    refine ⟨T,hT,?_⟩
    have heqmap : ∀ᵐ x ∂μ.map T, κ x = intrinsicRootLeaf hij μ x := by
      rw [hT.map_eq]
      exact heq
    have heqT : ∀ᵐ x ∂μ, κ (T x) = intrinsicRootLeaf hij μ (T x) :=
      ae_of_ae_map hT.measurable.aemeasurable heqmap
    filter_upwards [heq,heqT,ae_intrinsicRootLeaf_canonical d hij μ hA (Real.log c)] with x hx hTx hcq
    rw [hTx,hx]
    simpa only [Real.exp_log hc,T] using hcq)
  filter_upwards [heq,H] with x hx h
  rwa [hx] at h

 

theorem root_invariant_of_nonzero_intrinsic_period (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hp : ∀ᵐ x ∂μ, ∃ v : ℝ, v ≠ 0 ∧ v ∈ realLeafPeriods (intrinsicRootLeaf hij μ x))
    (a : ℝ) : μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) = μ := by
  apply root_invariant_of_intrinsic d hij μ hA
  filter_upwards [hp,ae_intrinsicRootLeaf_periods_bot_or_top d hij μ hA] with x hx hperiod
  obtain ⟨v,hv,hvp⟩ := hx
  rcases hperiod with hb | ht
  · rw [hb,AddSubgroup.mem_bot] at hvp
    exact (hv hvp).elim
  · intro t
    change t ∈ realLeafPeriods (intrinsicRootLeaf hij μ x)
    rw [ht]
    trivial

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma ae_intrinsicRootLeaf_exists_period_diagonal (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) (u : LogCoordinates d) :
    ∀ᵐ x ∂μ, (∃ a ∈ realLeafPeriods (intrinsicRootLeaf hij μ x), 0 < a) ↔
      ∃ a ∈ realLeafPeriods (intrinsicRootLeaf hij μ (rightAction x (diagonalFlow u))), 0 < a := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  let ell : Fin (d+1) → ℝ := Fin.snoc u (-∑ k, u k)
  have hell : ∑ k, ell k = 0 := by simp [ell,Fin.sum_univ_castSucc]
  have ha : diagonalOneParameter ell hell 1 = diagonalFlow u := by
    rw [diagonalOneParameter_eq_diagonalFlow]
    congr 1
    funext k
    simp [ell]
  have H := ae_intrinsicRootLeaf_diagonal hij ell hell 1 μ hfree (by rw [ha]; exact hA u)
  have hs : rootTimeScaling ell i j 1 =
      Homeomorph.mulLeft₀ (Real.exp (ell j-ell i)) (Real.exp_ne_zero _) := by
    apply Homeomorph.ext
    intro t
    simp [rootTimeScaling]
  rw [ha,hs] at H
  filter_upwards [H,ae_intrinsicRootLeaf_spec hij μ hfree,
    ae_intrinsicRootLeaf_ball_pos hij μ hfree] with x hx hspec hp
  let : IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ x) := hspec.1
  rw [hx]
  exact (exists_pos_leafPeriod_normalized_scaling _ hp _ (Real.exp_pos _)).symm

 

theorem intrinsicRootLeaf_periods_ergodic_alternative (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ] :
    (∀ a : ℝ, μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij a)) = μ) ∨
      (∀ᵐ x ∂μ, realLeafPeriods (intrinsicRootLeaf hij μ x) = ⊥) := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  let κ := intrinsicRootKernel hij μ hfree
  let S : Set (X (d+1)) := {x | ∃ a ∈ realLeafPeriods (intrinsicRootLeaf hij μ x), 0 < a}
  have hm : NullMeasurableSet S μ := by
    apply (measurableSet_exists_pos_leafPeriod κ).nullMeasurableSet.congr
    filter_upwards [ae_intrinsicRootKernel_eq hij μ hfree] with x hx
    change (∃ a ∈ realLeafPeriods (κ x), 0 < a) =
      (∃ a ∈ realLeafPeriods (intrinsicRootLeaf hij μ x), 0 < a)
    rw [show κ x = intrinsicRootLeaf hij μ x from hx]
  have he : EventuallyConst S (ae μ) :=
    aeconst_of_forall_preimage_smul_ae_eq (Multiplicative (LogCoordinates d)) hm (by
      intro u
      filter_upwards [ae_intrinsicRootLeaf_exists_period_diagonal d hij μ hA u.toAdd] with x hx
      change (∃ a ∈ realLeafPeriods (intrinsicRootLeaf hij μ (rightAction x (diagonalFlow u.toAdd))), 0 < a) =
        (∃ a ∈ realLeafPeriods (intrinsicRootLeaf hij μ x), 0 < a)
      exact propext hx.symm)
  rcases eventuallyConst_set.mp he with hp | hn
  · left
    apply root_invariant_of_nonzero_intrinsic_period d hij μ hA
    filter_upwards [hp] with x hx
    obtain ⟨a,ha,hap⟩ := hx
    exact ⟨a,hap.ne',ha⟩
  · right
    filter_upwards [hn,ae_intrinsicRootLeaf_periods_bot_or_top d hij μ hA] with x hx hp
    rcases hp with hb | ht
    · exact hb
    · exact (hx ⟨1,by rw [ht]; trivial,zero_lt_one⟩).elim

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma realMeasures_eq_iff_leafTests (ν ρ : Measure ℝ)
    [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure ρ] :
    ν = ρ ↔ ∀ N k : ℕ, (∫ x, leafTest N k x ∂ν) = ∫ x, leafTest N k x ∂ρ := by
  constructor
  · rintro rfl N k
    rfl
  · intro h
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    obtain ⟨R,hR⟩ := f.hasCompactSupport.isBounded.subset_closedBall 0
    obtain ⟨N,hN⟩ := exists_nat_gt R
    have hs : ∀ x : ℝ, x ∉ Icc (-(N:ℝ)) N → f x = 0 := by
      intro x hx
      by_contra hf
      have hb := hR (subset_closure hf)
      rw [Metric.mem_closedBall,Real.dist_eq,sub_zero] at hb
      exact hx (abs_le.mp (hb.trans hN.le))
    let f' : leafTestSpace N := ⟨f.toContinuousMap,hs⟩
    have hh : (fun g : leafTestSpace N => ∫ x, g.val (x+0) ∂ν) =
        (fun g : leafTestSpace N => ∫ x, g.val (x+0) ∂ρ) := by
      apply (denseRange_denseSeq (leafTestSpace N)).equalizer
        (continuous_leafTestSpace_integral ν N 0) (continuous_leafTestSpace_integral ρ N 0)
      funext k
      simpa only [Function.comp_apply,add_zero,leafTest_apply] using h N k
    have H := congrFun hh f'
    simpa only [f',add_zero,CompactlySupportedContinuousMap.coe_toContinuousMap] using H


lemma projectiveLeafPeriod_iff_tests (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] (p : ℝ × ℝ) :
    projectiveLeafPeriod ν p ↔ ∀ N k : ℕ,
      (∫ x, leafTest N k (x+p.1) ∂ν) = Real.exp p.2 * ∫ x, leafTest N k x ∂ν := by
  let : (ν.map (fun x : ℝ => x+p.1)).Regular := Measure.Regular.map (Homeomorph.addRight p.1)
  let : IsFiniteMeasureOnCompacts (ENNReal.ofReal (Real.exp p.2) • ν) :=
    IsFiniteMeasureOnCompacts.smul ν ENNReal.ofReal_ne_top
  unfold projectiveLeafPeriod
  rw [realMeasures_eq_iff_leafTests]
  congr! 2
  rename_i N k
  rw [integral_map (μ := ν) («φ» := fun x : ℝ => x+p.1)
    (f := fun x => leafTest N k x) (by fun_prop)
    (leafTest N k).continuous.aestronglyMeasurable,
    integral_smul_measure,ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul]

lemma continuous_projectiveLeaf_discrepancy (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (N k : ℕ) : Continuous (fun p : ℝ × ℝ =>
      (∫ x, leafTest N k (x+p.1) ∂ν) - Real.exp p.2 * ∫ x, leafTest N k x ∂ν) :=
  ((continuous_integral_translate ν (leafTest N k)).comp continuous_fst).sub
    ((Real.continuous_exp.comp continuous_snd).mul continuous_const)

lemma measurable_projectiveLeaf_discrepancy {α : Type*} [MeasurableSpace α]
    (κ : Kernel α ℝ) (N k : ℕ) (p : ℝ × ℝ) : Measurable (fun z =>
      (∫ x, leafTest N k (x+p.1) ∂κ z) - Real.exp p.2 * ∫ x, leafTest N k x ∂κ z) := by
  exact (((leafTest N k).continuous.comp (continuous_id.add_const p.1)).stronglyMeasurable.integral_kernel).measurable.sub
    (measurable_const.mul ((leafTest N k).continuous.stronglyMeasurable.integral_kernel).measurable)

lemma isClosed_projectiveLeafPeriods (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] :
    IsClosed {p | projectiveLeafPeriod ν p} := by
  have he : {p | projectiveLeafPeriod ν p} =
      ⋂ N : ℕ, ⋂ k : ℕ, {p : ℝ × ℝ |
        (∫ x, leafTest N k (x+p.1) ∂ν) - Real.exp p.2 * ∫ x, leafTest N k x ∂ν = 0} := by
    ext p
    simp only [Set.mem_ofPred_eq,mem_iInter,sub_eq_zero,projectiveLeafPeriod_iff_tests]
  rw [he]
  exact isClosed_iInter fun N => isClosed_iInter fun k =>
    isClosed_eq (continuous_projectiveLeaf_discrepancy ν N k) continuous_const

 

lemma projectiveLeafPeriod_zero_time (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hp : 0 < ν (Metric.ball 0 1)) (b : ℝ) (h : projectiveLeafPeriod ν (0,b)) : b = 0 := by
  have he : ν = ENNReal.ofReal (Real.exp b) • ν := by
    simpa [projectiveLeafPeriod] using h
  have H := congrArg (fun ρ : Measure ℝ => ρ (Metric.ball 0 1)) he
  rw [Measure.smul_apply,smul_eq_mul] at H
  have HH : (1:ℝ≥0∞) = ENNReal.ofReal (Real.exp b) :=
    (ENNReal.mul_left_inj hp.ne' measure_ball_lt_top.ne).mp (by simpa only [one_mul] using H)
  exact (Real.exp_eq_one_iff b).mp (ENNReal.ofReal_eq_one.mp HH.symm)

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma projectiveLeafPeriod_smul (ν : Measure ℝ) (q : ℝ≥0∞) (hq0 : q ≠ 0) (hqT : q ≠ ∞)
    (p : ℝ × ℝ) : projectiveLeafPeriod (q • ν) p ↔ projectiveLeafPeriod ν p := by
  unfold projectiveLeafPeriod
  rw [Measure.map_smul (f := fun value : ℝ => value+p.1),
    smul_comm (ENNReal.ofReal (Real.exp p.2)) q ν]
  constructor
  · intro he
    have H := congrArg (fun ρ : Measure ℝ => q⁻¹ • ρ) he
    simpa only [smul_smul,←mul_assoc,ENNReal.inv_mul_cancel hq0 hqT,one_mul,one_smul] using H
  · exact congrArg (fun ρ : Measure ℝ => q • ρ)

lemma projectiveLeafPeriod_scaling (ν : Measure ℝ) (c : ℝ) (hc : c ≠ 0) (p : ℝ × ℝ) :
    projectiveLeafPeriod (ν.map (Homeomorph.mulLeft₀ c hc)) (c*p.1,p.2) ↔
      projectiveLeafPeriod ν p := by
  have H : (ν.map (Homeomorph.mulLeft₀ c hc)).map (fun x => x+c*p.1) =
      (ν.map (fun x => x+p.1)).map (Homeomorph.mulLeft₀ c hc) := by
    rw [Measure.map_map (by fun_prop) (Homeomorph.mulLeft₀ c hc).measurable,
      Measure.map_map (Homeomorph.mulLeft₀ c hc).measurable (by fun_prop)]
    congr 1
    ext x
    change c*x+c*p.1 = c*(x+p.1)
    ring
  unfold projectiveLeafPeriod
  rw [H,←Measure.map_smul]
  exact (Homeomorph.mulLeft₀ c hc).measurableEmbedding.map_injective.eq_iff

lemma projectiveLeafPeriod_normalized_scaling (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hp : ∀ r : ℝ, 0 < r → 0 < ν (Metric.ball 0 r))
    (c : ℝ) (hc : 0 < c) (p : ℝ × ℝ) :
    projectiveLeafPeriod
      (anchorNormalize (ν.map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1)) (c*p.1,p.2) ↔
        projectiveLeafPeriod ν p := by
  have hm : ν.map (Homeomorph.mulLeft₀ c hc.ne') (Metric.ball 0 1) =
      ν (Metric.ball 0 (1/c)) := by
    rw [Measure.map_apply (Homeomorph.mulLeft₀ c hc.ne').measurable
      Metric.isOpen_ball.measurableSet,realScaling_preimage_ball c 1 hc]
  unfold anchorNormalize
  rw [projectiveLeafPeriod_smul _ _ (by rw [hm]; exact ENNReal.inv_ne_zero.mpr measure_ball_lt_top.ne)
    (by rw [hm]; exact ENNReal.inv_ne_top.mpr (hp _ (by positivity)).ne')]
  exact projectiveLeafPeriod_scaling ν c hc.ne' p



lemma boundedProjectiveLeafPeriod_mono (ν : Measure ℝ) {r R l u : ℝ} (hr : r ≤ R) :
    boundedProjectiveLeafPeriod ν r l u → boundedProjectiveLeafPeriod ν R l u := by
  rintro ⟨p,hp,hrp,hs⟩
  exact ⟨p,hp,hrp.trans hr,hs⟩

lemma boundedProjectiveLeafPeriod_normalized_scaling (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hp : ∀ r : ℝ, 0 < r → 0 < ν (Metric.ball 0 r))
    (c : ℝ) (hc : 0 < c) (R l u : ℝ) :
    boundedProjectiveLeafPeriod
      (anchorNormalize (ν.map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1)) R l u ↔
      boundedProjectiveLeafPeriod ν (R/c) l u := by
  constructor
  · rintro ⟨p,hp',hpa,hpb⟩
    refine ⟨(p.1/c,p.2),?_,?_,hpb⟩
    · apply (projectiveLeafPeriod_normalized_scaling ν hp c hc (p.1/c,p.2)).mp
      simpa only [mul_div_cancel₀ _ hc.ne'] using hp'
    · change |p.1/c| ≤ R/c
      rw [abs_div,abs_of_pos hc]
      exact (div_le_div_iff_of_pos_right hc).mpr hpa
  · rintro ⟨p,hp',hpa,hpb⟩
    refine ⟨(c*p.1,p.2),(projectiveLeafPeriod_normalized_scaling ν hp c hc p).mpr hp',?_,hpb⟩
    change |c*p.1| ≤ R
    rw [abs_mul,abs_of_pos hc,mul_comm]
    exact (le_div_iff₀ hc).mp hpa

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma measurableSet_exists_projectiveLeafPeriod_mem {α : Type*} [MeasurableSpace α]
    (κ : Kernel α ℝ) [∀ x, IsLocallyFiniteMeasure (κ x)]
    (K : Set (ℝ × ℝ)) (hK : IsCompact K) :
    MeasurableSet {x : α | ∃ p ∈ K, projectiveLeafPeriod (κ x) p} := by
  by_cases he : K.Nonempty
  · let T := ↥K
    let : Nonempty T := he.to_subtype
    let : CompactSpace T := isCompact_iff_compactSpace.mp hK
    let : SecondCountableTopology T := Subtype.secondCountableTopology _
    let F (n : ℕ) (x : α) (p : T) : ℝ :=
      (∫ y, leafTest n.unpair.1 n.unpair.2 (y+p.val.1) ∂κ x) -
        Real.exp p.val.2 * ∫ y, leafTest n.unpair.1 n.unpair.2 y ∂κ x
    have H := measurableSet_exists_compact_zero F
      (fun n p => measurable_projectiveLeaf_discrepancy κ _ _ p.val)
      (fun n x => (continuous_projectiveLeaf_discrepancy (κ x) _ _).comp continuous_subtype_val)
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    constructor
    · rintro ⟨p,hp,hper⟩
      exact ⟨⟨p,hp⟩,fun n => sub_eq_zero.mpr
        ((projectiveLeafPeriod_iff_tests (κ x) p).mp hper _ _)⟩
    · rintro ⟨p,hp⟩
      refine ⟨p.val,p.prop,(projectiveLeafPeriod_iff_tests (κ x) p.val).mpr ?_⟩
      intro N k
      have H := hp (Nat.pair N k)
      simpa only [F,Nat.unpair_pair,sub_eq_zero] using H
  · simp only [Set.not_nonempty_iff_eq_empty.mp he,mem_empty_iff_false,false_and,exists_false,
      Set.ofPred_false,MeasurableSet.empty]

lemma measurableSet_boundedProjectiveLeafPeriod {α : Type*} [MeasurableSpace α]
    (κ : Kernel α ℝ) [∀ x, IsLocallyFiniteMeasure (κ x)] (R l u : ℝ) :
    MeasurableSet {x : α | boundedProjectiveLeafPeriod (κ x) R l u} := by
  have he : {x : α | boundedProjectiveLeafPeriod (κ x) R l u} =
      {x : α | ∃ p ∈ (Icc (-R) R ×ˢ Icc l u), projectiveLeafPeriod (κ x) p} := by
    ext x
    simp only [Set.mem_ofPred_eq,boundedProjectiveLeafPeriod,mem_prod]
    constructor
    · rintro ⟨p,hp,ha,hb⟩
      exact ⟨p,⟨abs_le.mp ha,hb⟩,hp⟩
    · rintro ⟨p,⟨ha,hb⟩,hp⟩
      exact ⟨p,hp,abs_le.mpr ha,hb⟩
  rw [he]
  exact measurableSet_exists_projectiveLeafPeriod_mem κ _ (isCompact_Icc.prod isCompact_Icc)

 

lemma not_forall_boundedProjectiveLeafPeriod (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hp : 0 < ν (Metric.ball 0 1)) (l u : ℝ) (hzero : (0:ℝ) ∉ Icc l u) :
    ¬ ∀ k : ℕ, boundedProjectiveLeafPeriod ν (1/((k:ℝ)+1)) l u := by
  intro H
  let C (k : ℕ) : Set (ℝ × ℝ) := {p | projectiveLeafPeriod ν p} ∩
    (Icc (-(1/((k:ℝ)+1))) (1/((k:ℝ)+1)) ×ˢ Icc l u)
  have hc (k : ℕ) : IsClosed (C k) :=
    (isClosed_projectiveLeafPeriods ν).inter (isClosed_Icc.prod isClosed_Icc)
  have hne (k : ℕ) : (C k).Nonempty := by
    obtain ⟨p,hp,ha,hb⟩ := H k
    exact ⟨p,hp,abs_le.mp ha,hb⟩
  have ha (k : ℕ) : C (k+1) ⊆ C k := by
    rintro p ⟨hp,ha,hb⟩
    refine ⟨hp,?_,hb⟩
    exact abs_le.mp ((abs_le.mpr ha).trans (Nat.one_div_le_one_div (Nat.le_succ k)))
  have hcomp : IsCompact (C 0) :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset (hc 0) (fun _ h => h.2)
  obtain ⟨p,hpC⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C ha hne hcomp hc
  have hpa : ∀ᶠ k : ℕ in atTop, |p.1| ≤ 1/((k:ℝ)+1) :=
    Eventually.of_forall fun k => abs_le.mpr (mem_iInter.mp hpC k).2.1
  have hp0 : p.1 = 0 := abs_eq_zero.mp (le_antisymm
    (ge_of_tendsto tendsto_one_div_add_atTop_nhds_zero_nat hpa) (abs_nonneg _))
  have hper := (mem_iInter.mp hpC 0).1
  have hrect := (mem_iInter.mp hpC 0).2.2
  have he : p = (0,p.2) := Prod.ext hp0 rfl
  rw [he] at hper
  have hp2 : p.2 = 0 := projectiveLeafPeriod_zero_time ν hp p.2 hper
  exact hzero (hp2 ▸ hrect)

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma ae_boundedProjectiveLeafPeriod_scaling {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α ℝ)
    [∀ x, IsLocallyFiniteMeasure (κ x)]
    (hp : ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 < κ x (Metric.ball 0 r))
    {T : α → α} (hT : MeasurePreserving T μ μ) (c : ℝ) (hc : 1 ≤ c)
    (hcov : ∀ᵐ x ∂μ, κ (T x) =
      anchorNormalize ((κ x).map (Homeomorph.mulLeft₀ c (by linarith))) (Metric.ball 0 1))
    (R l u : ℝ) (hR : 0 ≤ R) :
    ∀ᵐ x ∂μ, boundedProjectiveLeafPeriod (κ x) R l u ↔
      boundedProjectiveLeafPeriod (κ x) (R/c) l u := by
  classical
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  let E : Set α := {x | boundedProjectiveLeafPeriod (κ x) R l u}
  let f : α → ℝ≥0∞ := E.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator (measurableSet_boundedProjectiveLeafPeriod κ R l u)
  have he : ∀ᵐ x ∂μ, T x ∈ E ↔ boundedProjectiveLeafPeriod (κ x) (R/c) l u := by
    filter_upwards [hp,hcov] with x hx hcovx
    change boundedProjectiveLeafPeriod (κ (T x)) R l u ↔ _
    rw [hcovx]
    exact boundedProjectiveLeafPeriod_normalized_scaling (κ x) hx c hc0 R l u
  have hmono : ∀ᵐ x ∂μ, f (T x) ≤ f x := by
    filter_upwards [he] with x hx
    by_cases h : T x ∈ E
    · have hxE : x ∈ E := boundedProjectiveLeafPeriod_mono (κ x)
        (div_le_self hR hc) (hx.mp h)
      simp only [f,indicator_of_mem h,indicator_of_mem hxE,le_refl]
    · simp only [f,indicator_of_notMem h]
      exact bot_le
  have heq := ae_eq_of_measurePreserving_ennreal_ge μ hT hf.aemeasurable
    (Eventually.of_forall fun x => show f x ≤ 1 from by
      by_cases hx : x ∈ E <;> simp [f,hx]) hmono
  filter_upwards [he,heq] with x hx heqx
  have hiff : x ∈ E ↔ T x ∈ E := by
    by_cases hxE : x ∈ E <;> by_cases hTE : T x ∈ E <;>
      simp_all [f,Function.comp_apply]
  exact hiff.trans hx

lemma ae_projectiveLeafPeriod_avoids_interval {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α ℝ)
    [∀ x, IsLocallyFiniteMeasure (κ x)]
    (hp : ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 < κ x (Metric.ball 0 r))
    (hscaling : ∀ (c : ℝ) (hc : 0 < c), ∃ T : α → α, MeasurePreserving T μ μ ∧
      ∀ᵐ x ∂μ, κ (T x) = anchorNormalize
        ((κ x).map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1))
    (l u : ℝ) (hzero : (0:ℝ) ∉ Icc l u) :
    ∀ᵐ x ∂μ, ∀ p : ℝ × ℝ, projectiveLeafPeriod (κ x) p → p.2 ∉ Icc l u := by
  have H (m k : ℕ) : ∀ᵐ x ∂μ, boundedProjectiveLeafPeriod (κ x) ((m:ℝ)+1) l u ↔
      boundedProjectiveLeafPeriod (κ x) (1/((k:ℝ)+1)) l u := by
    let c : ℝ := ((m:ℝ)+1)*((k:ℝ)+1)
    have hc : 1 ≤ c := by
      dsimp [c]
      nlinarith [Nat.cast_nonneg (α := ℝ) m,Nat.cast_nonneg (α := ℝ) k]
    obtain ⟨T,hT,hcov⟩ := hscaling c (zero_lt_one.trans_le hc)
    have he := ae_boundedProjectiveLeafPeriod_scaling μ κ hp hT c hc hcov ((m:ℝ)+1) l u (by positivity)
    have hdiv : ((m:ℝ)+1)/c = 1/((k:ℝ)+1) := by
      dsimp [c]
      field_simp
    simpa only [hdiv] using he
  have HH : ∀ᵐ x ∂μ, ∀ m k : ℕ, boundedProjectiveLeafPeriod (κ x) ((m:ℝ)+1) l u ↔
      boundedProjectiveLeafPeriod (κ x) (1/((k:ℝ)+1)) l u :=
    ae_all_iff.mpr fun m => ae_all_iff.mpr fun k => H m k
  filter_upwards [hp,HH] with x hx hxx
  intro p hper hmem
  obtain ⟨m,hm⟩ := exists_nat_gt |p.1|
  have hlarge : boundedProjectiveLeafPeriod (κ x) ((m:ℝ)+1) l u := ⟨p,hper,by linarith,hmem⟩
  exact not_forall_boundedProjectiveLeafPeriod (κ x) (hx 1 zero_lt_one) l u hzero
    (fun k => (hxx m k).mp hlarge)

lemma exists_nat_mem_Icc_inv_succ {b : ℝ} (hb : 0 < b) :
    ∃ n : ℕ, b ∈ Icc (1/((n:ℝ)+1)) ((n:ℝ)+1) := by
  obtain ⟨m,hm⟩ := exists_nat_gt b
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt hb
  refine ⟨max m k,?_,?_⟩
  · exact (Nat.one_div_le_one_div (Nat.le_max_right m k)).trans hk.le
  · have H : (m:ℝ) ≤ ((max m k:ℕ):ℝ) := Nat.cast_le.mpr (Nat.le_max_left m k)
    linarith

 

theorem ae_projectiveLeafPeriod_multiplier_zero {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α ℝ)
    [∀ x, IsLocallyFiniteMeasure (κ x)]
    (hp : ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 < κ x (Metric.ball 0 r))
    (hscaling : ∀ (c : ℝ) (hc : 0 < c), ∃ T : α → α, MeasurePreserving T μ μ ∧
      ∀ᵐ x ∂μ, κ (T x) = anchorNormalize
        ((κ x).map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1)) :
    ∀ᵐ x ∂μ, ∀ p : ℝ × ℝ, projectiveLeafPeriod (κ x) p → p.2 = 0 := by
  have Hpos (n : ℕ) := ae_projectiveLeafPeriod_avoids_interval μ κ hp hscaling
    (1/((n:ℝ)+1)) ((n:ℝ)+1) (by
      intro h
      have : 0 < 1/((n:ℝ)+1) := by positivity
      linarith [h.1])
  have Hneg (n : ℕ) := ae_projectiveLeafPeriod_avoids_interval μ κ hp hscaling
    (-((n:ℝ)+1)) (-(1/((n:ℝ)+1))) (by
      intro h
      have : 0 < 1/((n:ℝ)+1) := by positivity
      linarith [h.2])
  filter_upwards [ae_all_iff.mpr Hpos,ae_all_iff.mpr Hneg] with x hx hy
  intro p hp
  rcases lt_trichotomy (0:ℝ) p.2 with h | h | h
  · obtain ⟨n,hn⟩ := exists_nat_mem_Icc_inv_succ h
    exact (hx n p hp hn).elim
  · exact h.symm
  · obtain ⟨n,hn⟩ := exists_nat_mem_Icc_inv_succ (neg_pos.mpr h)
    exact (hy n p hp ⟨by linarith [hn.2],by linarith [hn.1]⟩).elim

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_PublishedEKL
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Haar rigidity from root-leaf symmetries

Projective normalization can be removed from root-leaf symmetries, and
nontrivial root periods yield invariance under the corresponding
unipotent group. Haar measure follows from all root periods, or from
a single root and a transitive prime-degree symmetry group.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree

open PrimeDegreePackets

/-- A projective period of a leaf with zero logarithmic multiplier is an
ordinary period. -/
lemma leaf_period_of_projective_multiplier_zero
    (ν : Measure ℝ) (p : ℝ × ℝ) (hp : projectiveLeafPeriod ν p) (hzero : p.2 = 0) :
    p.1 ∈ realLeafPeriods ν := by
  change ν.map (fun x => x + p.1) = ν
  simpa only [projectiveLeafPeriod, hzero, Real.exp_zero, ENNReal.ofReal_one, one_smul] using hp

/-- Equality with a rebased normalized leaf yields a projective period.
The normalizing scalar is recovered from the unit-ball mass. -/
lemma projectivePeriod_of_based_fixed
    (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] (hunit : ν (Metric.ball 0 1) = 1)
    (t : ℝ) (hfixed : basedRealMeasure ν t = ν) :
    projectiveLeafPeriod ν (-t, Real.log (ν (Metric.ball t 1)).toReal) := by
  let m := ν (Metric.ball t 1)
  have hmul : m⁻¹ * m = 1 := by
    have he := congrArg (fun ρ : Measure ℝ => ρ (Metric.ball 0 1)) hfixed
    simpa only [basedRealMeasure, anchorNormalize, Measure.smul_apply,
      smul_eq_mul, centerRealMeasure_ball, hunit] using he
  have hm0 : m ≠ 0 := by
    intro hm
    simp [hm] at hmul
  have hmT : m ≠ ∞ := measure_ball_lt_top.ne
  have hcenter : centerRealMeasure ν t = m • ν := by
    have hs := congrArg (fun ρ : Measure ℝ => m • ρ) hfixed
    simp only [basedRealMeasure, anchorNormalize, centerRealMeasure_ball] at hs
    change m • (m⁻¹ • centerRealMeasure ν t) = m • ν at hs
    rw [smul_smul, ENNReal.mul_inv_cancel hm0 hmT, one_smul] at hs
    exact hs
  change ν.map (fun x => x + -t) = ENNReal.ofReal (Real.exp (Real.log m.toReal)) • ν
  rw [Real.exp_log (ENNReal.toReal_pos hm0 hmT), ENNReal.ofReal_toReal hmT]
  simpa only [centerRealMeasure, Homeomorph.coe_subRight, sub_eq_add_neg] using hcenter

/-- For a finite invariant ambient measure, the full diagonal scaling
covariance forces every projective root-leaf period to have multiplier
one. This is the normalization step needed by the low-entropy argument. -/
theorem ae_intrinsic_projective_multiplier_zero
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ, ∀ p : ℝ × ℝ,
      projectiveLeafPeriod (intrinsicRootLeaf hij μ x) p → p.2 = 0 := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  let κ := intrinsicRootKernel hij μ hfree
  have heq : ∀ᵐ x ∂μ, κ x = intrinsicRootLeaf hij μ x :=
    ae_intrinsicRootKernel_eq hij μ hfree
  have hp : ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 < κ x (Metric.ball 0 r) := by
    filter_upwards [heq, ae_intrinsicRootLeaf_ball_pos hij μ hfree] with x hx hp
    rwa [hx]
  have H := ae_projectiveLeafPeriod_multiplier_zero μ κ hp (by
    intro c hc
    let T : X (d + 1) → X (d + 1) :=
      fun x => rightAction x (rootCanonicalFlow d j (Real.log c))
    have hT : MeasurePreserving T μ μ :=
      rootCanonicalFlow_preserving d j (Real.log c) μ hA
    refine ⟨T, hT, ?_⟩
    have heqmap : ∀ᵐ x ∂μ.map T, κ x = intrinsicRootLeaf hij μ x := by
      rw [hT.map_eq]
      exact heq
    have heqT : ∀ᵐ x ∂μ, κ (T x) = intrinsicRootLeaf hij μ (T x) :=
      ae_of_ae_map hT.measurable.aemeasurable heqmap
    filter_upwards [heq, heqT,
      ae_intrinsicRootLeaf_canonical d hij μ hA (Real.log c)] with x hx hTx hcq
    rw [hTx, hx]
    simpa only [Real.exp_log hc, T] using hcq)
  filter_upwards [heq, H] with x hx h
  simpa only [hx] using h

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_OwnLeafSeparation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Separation along a noninvariant root leaf

This is the root-leaf separation used in EKL (2006), Lemma 4.4(2).
The projective multiplier vanishes by diagonal recurrence, and ergodicity
makes every translation period trivial unless the ambient measure is
invariant under the root group. No product-structure assertion for a larger
horospherical group is included here.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

/-- In the noninvariant ergodic case, a normalized leaf cannot equal a
nontrivial rebasing of itself. This is pointwise in the rebase parameter. -/
theorem ae_based_rootLeaf_eq_only_at_zero
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    (hnot : ¬ ∀ a : ℝ, μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij a)) = μ) :
    ∀ᵐ x ∂μ, ∀ t : ℝ,
      basedRealMeasure (intrinsicRootLeaf hij μ x) t = intrinsicRootLeaf hij μ x → t = 0 := by
  have hA (u : LogCoordinates d) :
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  have hbot : ∀ᵐ x ∂μ, realLeafPeriods (intrinsicRootLeaf hij μ x) = ⊥ :=
    (intrinsicRootLeaf_periods_ergodic_alternative d hij μ).resolve_left hnot
  filter_upwards [hbot, ae_intrinsicRootLeaf_spec hij μ hfree,
    ae_intrinsic_projective_multiplier_zero d hij μ hA] with x hb hs hm
  let ν := intrinsicRootLeaf hij μ x
  let : IsLocallyFiniteMeasure ν := hs.1
  intro t ht
  have hp := projectivePeriod_of_based_fixed ν hs.2 t ht
  have hz := hm _ hp
  have hperiod := leaf_period_of_projective_multiplier_zero ν _ hp hz
  change -t ∈ realLeafPeriods (intrinsicRootLeaf hij μ x) at hperiod
  rw [hb, AddSubgroup.mem_bot] at hperiod
  exact neg_eq_zero.mp hperiod

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LeafNullClosure
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Enlarging a null set to avoid it along every conditional root leaf

Iterating the ambient-to-leaf null-set implication gives one measurable
null set whose complement is leafwise conull at every remaining point.
This lets the commutator construction choose all of its vertices outside
the same exceptional set.
-/

noncomputable section
open Set Filter MeasureTheory

namespace DukePrimeDegree
open PrimeDegreePackets

theorem enlarge_nullset_leafwise
    {X T I : Type*} [MeasurableSpace X] [MeasurableSpace T] [Countable I]
    (μ : Measure X) (ν : I → X → Measure T) (R : I → X → T → X)
    (hdis : ∀ i {P : X → Prop}, (∀ᵐ x ∂μ, P x) →
      ∀ᵐ x ∂μ, ∀ᵐ t ∂ν i x, P (R i x t))
    (N : Set X) (hN : MeasurableSet N) (hNzero : μ N = 0) :
    ∃ M : Set X, MeasurableSet M ∧ μ M = 0 ∧ N ⊆ M ∧
      ∀ x ∉ M, ∀ i, ∀ᵐ t ∂ν i x, R i x t ∉ M := by
  let S := {A : Set X // MeasurableSet A ∧ μ A = 0}
  have hstep (A : S) : ∃ B : S, A.val ⊆ B.val ∧
      ∀ x ∉ B.val, ∀ i, ∀ᵐ t ∂ν i x, R i x t ∉ A.val := by
    have ha : ∀ᵐ x ∂μ, x ∉ A.val := by
      rw [ae_iff]
      simpa only [not_not, Set.ofPred_mem_eq] using A.prop.2
    have hall : ∀ᵐ x ∂μ, ∀ i, ∀ᵐ t ∂ν i x, R i x t ∉ A.val :=
      ae_all_iff.mpr fun i => hdis i ha
    obtain ⟨B, hbad, hB, hBzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hall)
    refine ⟨⟨A.val ∪ B, A.prop.1.union hB, measure_union_null A.prop.2 hBzero⟩,
      subset_union_left, ?_⟩
    intro x hx
    by_contra h
    exact hx (Or.inr (hbad h))
  let next (A : S) : S := (hstep A).choose
  let A : ℕ → S := fun m => Nat.rec ⟨N, hN, hNzero⟩ (fun _ prev => next prev) m
  have hAstep (m : ℕ) : ∀ x ∉ (A (m + 1)).val, ∀ i,
      ∀ᵐ t ∂ν i x, R i x t ∉ (A m).val :=
    (hstep (A m)).choose_spec.2
  let M := ⋃ m : ℕ, (A m).val
  refine ⟨M, MeasurableSet.iUnion (fun m => (A m).prop.1),
    measure_iUnion_null (fun m => (A m).prop.2), ?_, ?_⟩
  · exact fun x hx => mem_iUnion.mpr ⟨0, hx⟩
  · intro x hx i
    have ha (m : ℕ) : ∀ᵐ t ∂ν i x, R i x t ∉ (A m).val :=
      hAstep m x (fun h => hx (mem_iUnion.mpr ⟨m + 1, h⟩)) i
    filter_upwards [ae_all_iff.mpr ha] with t ht
    simpa only [M, mem_iUnion, not_exists] using ht

theorem enlarge_nullset_all_roots
    (d : ℕ) (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (N : Set (X (d + 1))) (hN : MeasurableSet N) (hNzero : μ N = 0) :
    ∃ M : Set (X (d + 1)), MeasurableSet M ∧ μ M = 0 ∧ N ⊆ M ∧
      ∀ x ∉ M, ∀ (a b : Fin (d + 1)) (hab : a ≠ b),
        ∀ᵐ t ∂intrinsicRootLeaf hab μ x,
          rightAction x (Matrix.SpecialLinearGroup.transvection hab t) ∉ M := by
  let I := {p : Fin (d + 1) × Fin (d + 1) // p.1 ≠ p.2}
  let ν : I → X (d + 1) → Measure ℝ := fun q => intrinsicRootLeaf q.prop μ
  let R : I → X (d + 1) → ℝ → X (d + 1) :=
    fun q x t => rightAction x (Matrix.SpecialLinearGroup.transvection q.prop t)
  have hd (q : I) {P : X (d + 1) → Prop} (hp : ∀ᵐ x ∂μ, P x) :
      ∀ᵐ x ∂μ, ∀ᵐ t ∂ν q x, P (R q x t) := by
    apply ae_intrinsicRootLeaf_of_ambient q.prop μ _ hp
    exact (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx q.val.1 q.val.2 q.prop
  obtain ⟨M, hM, hMzero, hNM, hleaf⟩ := enlarge_nullset_leafwise μ ν R hd N hN hNzero
  exact ⟨M, hM, hMzero, hNM, fun x hx a b hab => hleaf x hx ⟨(a, b), hab⟩⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootWeights
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Neutral diagonal directions for root leaves

Root leaves are unchanged along the kernel of their root character.
For two nonparallel roots, an explicit diagonal direction is neutral on
the first and expands the second. These are the directions used to
compare the root foliations in the entropy argument.
-/

open MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology Classical

namespace DukePrimeDegree

open PrimeDegreePackets

lemma rootCanonicalWeights_neutral (d : ℕ) {i j p : Fin (d + 1)}
    (hip : i ≠ p) (hjp : j ≠ p) :
    rootCanonicalWeights d p i = rootCanonicalWeights d p j := by
  simp [rootCanonicalWeights, coordinateContractionWeights, hip, hjp]

/-- Every root which is not equal or opposite to a fixed root is expanded
by a diagonal direction which centralizes the fixed root. -/
theorem exists_neutral_expanding_weights (d : ℕ)
    {i j k l : Fin (d + 1)} (_hij : i ≠ j) (hkl : k ≠ l)
    (hforward : ¬ (k = i ∧ l = j)) (hbackward : ¬ (k = j ∧ l = i)) :
    ∃ ell : Fin (d + 1) → ℝ,
      (∑ r, ell r) = 0 ∧ ell i = ell j ∧ ell l - ell k = 1 := by
  by_cases hli : l = i
  · have hki : k ≠ i := by simpa only [hli] using hkl
    have hkj : k ≠ j := by
      intro h
      exact hbackward ⟨h, hli⟩
    refine ⟨fun r => -rootCanonicalWeights d k r, ?_, ?_, ?_⟩
    · simp only [Finset.sum_neg_distrib, rootCanonicalWeights_sum, neg_zero]
    · exact congrArg Neg.neg (rootCanonicalWeights_neutral d hki.symm hkj.symm)
    · have h := rootCanonicalWeights_difference d hkl.symm
      linarith
  · by_cases hlj : l = j
    · have hki : k ≠ i := by
        intro h
        exact hforward ⟨h, hlj⟩
      have hkj : k ≠ j := by simpa only [hlj] using hkl
      refine ⟨fun r => -rootCanonicalWeights d k r, ?_, ?_, ?_⟩
      · simp only [Finset.sum_neg_distrib, rootCanonicalWeights_sum, neg_zero]
      · exact congrArg Neg.neg (rootCanonicalWeights_neutral d hki.symm hkj.symm)
      · have h := rootCanonicalWeights_difference d hkl.symm
        linarith
    · exact ⟨rootCanonicalWeights d l, rootCanonicalWeights_sum d l,
        rootCanonicalWeights_neutral d (Ne.symm hli) (Ne.symm hlj),
        rootCanonicalWeights_difference d hkl⟩

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootStableHolonomy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Root-leaf constancy along every stable root pair off a null set
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma root_conjugate_tendsto_one
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (ell : Fin n → ℝ) (hell : ∑ r, ell r = 0) (hneg : ell i - ell j < 0) (r : ℝ) :
    Tendsto (fun t : ℝ => diagonalOneParameter ell hell t *
      Matrix.SpecialLinearGroup.transvection hij r * diagonalOneParameter ell hell (-t))
      atTop (𝓝 1) := by
  have he (t : ℝ) : (ell i - ell j) * t = -((ell j - ell i) * t) := by ring
  have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (Filter.Tendsto.const_mul_atTop (by linarith : 0 < ell j - ell i) tendsto_id)
  have hp : Tendsto (fun t : ℝ => Real.exp ((ell i - ell j) * t) * r) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, he, zero_mul] using ht.mul_const r
  have h := (continuous_rootTransvection hij).tendsto 0 |>.comp hp
  simpa only [Function.comp_def, diagonal_conjugation_transvection,
    Matrix.SpecialLinearGroup.transvection_coeff_zero] using h

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootCommutator
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The three-root commutator rectangle

The two orders of the adjacent root translations differ by the product
of their parameters in the long root. Under a diagonal flow neutral on
the long root and contracting the first root, this is the exact limit.
-/

noncomputable section
open Set Filter Matrix
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma adjacent_root_conjugation
    {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (r s : ℝ) :
    Matrix.SpecialLinearGroup.transvection hbc (-s) *
      Matrix.SpecialLinearGroup.transvection hab r *
      Matrix.SpecialLinearGroup.transvection hbc s =
    Matrix.SpecialLinearGroup.transvection hab r *
      Matrix.SpecialLinearGroup.transvection hac (r * s) := by
  apply Subtype.ext
  change ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.single b c (-s)) *
      (1 + Matrix.single a b r) * (1 + Matrix.single b c s) =
    (1 + Matrix.single a b r) * (1 + Matrix.single a c (r * s))
  have h1 : Matrix.single b c (-s) * Matrix.single a b r = 0 :=
    Matrix.single_mul_single_of_ne (c := -s) (h := hac.symm) (i := b) (j := c) (k := a) (d := r)
  have h2 : Matrix.single b c (-s) * Matrix.single b c s = 0 :=
    Matrix.single_mul_single_of_ne (c := -s) (h := hbc.symm) (i := b) (j := c) (k := b) (d := s)
  have h3 : Matrix.single a b r * Matrix.single a c (r * s) = 0 :=
    Matrix.single_mul_single_of_ne (c := r) (h := hab.symm) (i := a) (j := b) (k := a) (d := r * s)
  simp only [mul_add, add_mul, one_mul, mul_one, h1, h2, h3,
    Matrix.single_mul_single_same, add_zero]
  rw [← Matrix.single_neg]
  abel

theorem adjacent_root_conjugate_limit
    {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (ell : Fin n → ℝ) (hell : ∑ k, ell k = 0)
    (hneut : ell a = ell c) (hneg : ell a - ell b < 0) (r s : ℝ) :
    Tendsto (fun t : ℝ => diagonalOneParameter ell hell t *
      (Matrix.SpecialLinearGroup.transvection hbc (-s) *
        Matrix.SpecialLinearGroup.transvection hab r *
        Matrix.SpecialLinearGroup.transvection hbc s) * diagonalOneParameter ell hell (-t))
      atTop (𝓝 (Matrix.SpecialLinearGroup.transvection hac (r * s))) := by
  have he (t : ℝ) : diagonalOneParameter ell hell t *
      (Matrix.SpecialLinearGroup.transvection hbc (-s) *
        Matrix.SpecialLinearGroup.transvection hab r *
        Matrix.SpecialLinearGroup.transvection hbc s) * diagonalOneParameter ell hell (-t) =
      (diagonalOneParameter ell hell t * Matrix.SpecialLinearGroup.transvection hab r *
        diagonalOneParameter ell hell (-t)) * Matrix.SpecialLinearGroup.transvection hac (r * s) := by
    rw [adjacent_root_conjugation hab hbc hac]
    have hn := diagonal_conjugation_transvection ell hell hac (r * s) t
    simp only [hneut, sub_self, zero_mul, Real.exp_zero, one_mul] at hn
    calc
      _ = (diagonalOneParameter ell hell t * Matrix.SpecialLinearGroup.transvection hab r *
            diagonalOneParameter ell hell (-t)) *
          (diagonalOneParameter ell hell t * Matrix.SpecialLinearGroup.transvection hac (r * s) *
            diagonalOneParameter ell hell (-t)) := by
        rw [diagonalOneParameter_neg]
        group
      _ = _ := by rw [hn]
  simp_rw [he]
  simpa only [one_mul] using
    (root_conjugate_tendsto_one hab ell hell hneg r).mul_const
      (Matrix.SpecialLinearGroup.transvection hac (r * s))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_CommutatorInvariance
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Invariance under a commutator root

Two nonatomic adjacent root conditionals force invariance under the long
root. This proves EKL (2006), Lemma 3.3 / Einsiedler–Katok (2003), Lemma 6.1,
for the arithmetic quotient. Every vertex is selected outside a common
leafwise saturated null set.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma exists_nonzero_parameter_of_ae
    (ν : Measure ℝ) [NullSingletonClass ν]
    (hunit : ν (Metric.ball 0 1) = 1) {P : ℝ → Prop} (hP : ∀ᵐ t ∂ν, P t) :
    ∃ t, t ≠ 0 ∧ P t := by
  let : NeZero ν := ⟨by
    intro h
    have he := congrArg (fun μ : Measure ℝ => μ (Metric.ball 0 1)) h
    rw [hunit] at he
    simp at he⟩
  have hn : ∀ᵐ t ∂ν, t ≠ 0 := by rw [ae_iff]; simp
  exact (hn.and hP).exists

theorem root_invariant_of_adjacent_nonatomic_leaves_oai
    (d : ℕ) {a b c : Fin (d + 1)} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    (hatom_ab : ∀ᵐ x ∂μ, NullSingletonClass (intrinsicRootLeaf hab μ x))
    (hatom_bc : ∀ᵐ x ∂μ, NullSingletonClass (intrinsicRootLeaf hbc μ x)) :
    ∀ t : ℝ, μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hac t)) = μ := by
  by_contra hnot
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hfree (i j : Fin (d + 1)) (hij : i ≠ j) : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  have hQ : ∀ᵐ x ∂μ,
      NullSingletonClass (intrinsicRootLeaf hab μ x) ∧
      NullSingletonClass (intrinsicRootLeaf hbc μ x) ∧
      intrinsicRootLeaf hab μ x (Metric.ball 0 1) = 1 ∧
      intrinsicRootLeaf hbc μ x (Metric.ball 0 1) = 1 ∧
      ∀ t : ℝ, basedRealMeasure (intrinsicRootLeaf hac μ x) t =
        intrinsicRootLeaf hac μ x → t = 0 := by
    filter_upwards [hatom_ab, hatom_bc, ae_intrinsicRootLeaf_spec hab μ (hfree a b hab),
      ae_intrinsicRootLeaf_spec hbc μ (hfree b c hbc),
      ae_based_rootLeaf_eq_only_at_zero d hac μ hnot] with x ha hb hsa hsb hs
    exact ⟨ha, hb, hsa.2, hsb.2, hs⟩
  obtain ⟨N5, hbad, hN5, hz5⟩ := exists_measurable_superset_of_null (ae_iff.mp hQ)
  have hf1 : ¬ (a = a ∧ b = c) := by tauto
  have hb1 : ¬ (a = c ∧ b = a) := by tauto
  obtain ⟨N1, hN1, hz1, hconst1⟩ :=
    exists_nullset_nonparallel_root_constancy d hac hab hf1 hb1 μ hA
  have hf2 : ¬ (b = a ∧ c = c) := by tauto
  have hb2 : ¬ (b = c ∧ c = a) := by tauto
  obtain ⟨N2, hN2, hz2, hconst2⟩ :=
    exists_nullset_nonparallel_root_constancy d hac hbc hf2 hb2 μ hA
  have hf3 : ¬ (a = b ∧ b = c) := by tauto
  have hb3 : ¬ (a = c ∧ b = b) := by tauto
  obtain ⟨N3, hN3, hz3, hconst3⟩ :=
    exists_nullset_nonparallel_root_constancy d hbc hab hf3 hb3 μ hA
  obtain ⟨ell, hell, hn, hw⟩ := exists_neutral_expanding_weights d hac hab hf1 hb1
  obtain ⟨N4, hN4, hz4, hhol⟩ := exists_nullset_neutral_root_holonomy d hac μ hA ell hell hn
  let B := N1 ∪ (N2 ∪ (N3 ∪ (N4 ∪ N5)))
  have hB : MeasurableSet B := hN1.union (hN2.union (hN3.union (hN4.union hN5)))
  have hBzero : μ B = 0 := measure_union_null hz1
    (measure_union_null hz2 (measure_union_null hz3 (measure_union_null hz4 hz5)))
  obtain ⟨M, hM, hMzero, hBM, hleaf⟩ := enlarge_nullset_all_roots d μ hA B hB hBzero
  have hout (w : X (d + 1)) (hwM : w ∉ M) :
      w ∉ N1 ∧ w ∉ N2 ∧ w ∉ N3 ∧ w ∉ N4 ∧ w ∉ N5 := by
    have hb : w ∉ B := fun h => hwM (hBM h)
    simpa only [B, mem_union, not_or] using hb
  have hgood (w : X (d + 1)) (hwM : w ∉ M) :
      NullSingletonClass (intrinsicRootLeaf hab μ w) ∧
      NullSingletonClass (intrinsicRootLeaf hbc μ w) ∧
      intrinsicRootLeaf hab μ w (Metric.ball 0 1) = 1 ∧
      intrinsicRootLeaf hbc μ w (Metric.ball 0 1) = 1 ∧
      ∀ t : ℝ, basedRealMeasure (intrinsicRootLeaf hac μ w) t =
        intrinsicRootLeaf hac μ w → t = 0 := by
    by_contra h
    exact (hout w hwM).2.2.2.2 (hbad h)
  have hae : ∀ᵐ z ∂μ, z ∉ M := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hMzero
  obtain ⟨z, hz⟩ := hae.exists
  let : NullSingletonClass (intrinsicRootLeaf hab μ z) := (hgood z hz).1
  let : NullSingletonClass (intrinsicRootLeaf hbc μ z) := (hgood z hz).2.1
  obtain ⟨r, hr, hzr⟩ := exists_nonzero_parameter_of_ae (intrinsicRootLeaf hab μ z)
    (hgood z hz).2.2.1 (hleaf z hz a b hab)
  let z' := rightAction z (Matrix.SpecialLinearGroup.transvection hab r)
  have hbcEq : intrinsicRootLeaf hbc μ z' = intrinsicRootLeaf hbc μ z :=
    hconst3 z (hout z hz).2.2.1 r (hout z' hzr).2.2.1
  have hs' : ∀ᵐ s ∂intrinsicRootLeaf hbc μ z,
      rightAction z' (Matrix.SpecialLinearGroup.transvection hbc s) ∉ M := by
    rw [← hbcEq]
    exact hleaf z' hzr b c hbc
  obtain ⟨s, hs, hx, hy⟩ := exists_nonzero_parameter_of_ae (intrinsicRootLeaf hbc μ z)
    (hgood z hz).2.2.2.1 ((hleaf z hz b c hbc).and hs')
  let x := rightAction z (Matrix.SpecialLinearGroup.transvection hbc s)
  let y := rightAction z' (Matrix.SpecialLinearGroup.transvection hbc s)
  let g := Matrix.SpecialLinearGroup.transvection hbc (-s) *
    Matrix.SpecialLinearGroup.transvection hab r * Matrix.SpecialLinearGroup.transvection hbc s
  have hxy : rightAction x g = y := by
    dsimp only [x, y, z', g]
    simp only [rightAction_mul]
    congr 1
    rw [← Matrix.SpecialLinearGroup.transvection_inv hbc s]
    group
  have heq : intrinsicRootLeaf hac μ y = intrinsicRootLeaf hac μ x := by
    calc
      intrinsicRootLeaf hac μ y = intrinsicRootLeaf hac μ z' :=
        hconst2 z' (hout z' hzr).2.1 s (hout y hy).2.1
      _ = intrinsicRootLeaf hac μ z := hconst1 z (hout z hz).1 r (hout z' hzr).1
      _ = intrinsicRootLeaf hac μ x := (hconst2 z (hout z hz).2.1 s (hout x hx).2.1).symm
  have hh := hhol x (hout x hx).2.2.2.1 y (hout y hy).2.2.2.1 g hxy (r * s)
    (adjacent_root_conjugate_limit hab hbc hac ell hell hn (by linarith) r s)
  have he : r * s = 0 := (hgood x hx).2.2.2.2 (r * s) (hh.symm.trans heq)
  exact mul_ne_zero hr hs he

end DukePrimeDegree

end

end OAI
end

theorem solution : type_of% @OAI.DukePrimeDegree.root_invariant_of_adjacent_nonatomic_leaves_oai := @OAI.DukePrimeDegree.root_invariant_of_adjacent_nonatomic_leaves_oai
