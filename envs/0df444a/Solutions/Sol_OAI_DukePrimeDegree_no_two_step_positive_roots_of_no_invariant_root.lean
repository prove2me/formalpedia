-- Prove2me | solution 1 for OAI.DukePrimeDegree.no_two_step_positive_roots_of_no_invariant_root
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:43:58.238025+00:00
-- url     : https://prove2.me/submissions/970affec-28b6-4001-b913-0ffa1d2c40c8

import Mathlib
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
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
import Theorems.Thm_OAI_DukePrimeDegree_canonicalRootCoefficient_zero_iff
import Theorems.Thm_OAI_DukePrimeDegree_root_invariant_of_adjacent_nonatomic_leaves
import Theorems.Thm_OAI_DukePrimeDegree_root_invariant_of_atomic_companion_leaves

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LeafSupport
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

lemma centerRealMeasure_center (ν : Measure ℝ) (t u : ℝ) :
    centerRealMeasure (centerRealMeasure ν t) u = centerRealMeasure ν (t+u) := by
  unfold centerRealMeasure
  rw [Measure.map_map (Homeomorph.subRight u).measurable (Homeomorph.subRight t).measurable]
  congr 1
  funext x
  change (x-t)-u=x-(t+u)
  ring

lemma basedRealMeasure_center (ν : Measure ℝ) (t u : ℝ) :
    basedRealMeasure (centerRealMeasure ν t) u = basedRealMeasure ν (t+u) := by
  unfold basedRealMeasure
  rw [centerRealMeasure_center]

 

lemma basedRealMeasure_rebase (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (t u : ℝ) (ht : 0 < ν (Metric.ball t 1)) :
    basedRealMeasure (basedRealMeasure ν t) u = basedRealMeasure ν (t+u) := by
  change basedRealMeasure ((centerRealMeasure ν t (Metric.ball 0 1))⁻¹ • centerRealMeasure ν t) u = _
  rw [basedRealMeasure_smul]
  · exact basedRealMeasure_center ν t u
  · rw [centerRealMeasure_ball]
    exact ENNReal.inv_ne_zero.mpr measure_ball_lt_top.ne
  · rw [centerRealMeasure_ball]
    exact ENNReal.inv_ne_top.mpr ht.ne'

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LeafAnchors
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.overlapMeasure_finite _root_.OAI.PrimeDegreePackets.intrinsicRootKernel_locallyFinite _root_.OAI.PrimeDegreePackets.intrinsicRootKernel_sFinite _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
namespace PrimeDegreePackets.RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

 

theorem ae_leafMeasure_change_anchor (A B : RootBox hij k) (R S : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0) (hBS : B.time ⊆ rootLeafWindow S 0)
    (hAB : A.time ⊆ B.time) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst, s ∈ B.transverse →
      A.leafMeasure R μ s = anchorNormalize (B.leafMeasure S μ s) A.time := by
  let C := rootLongBoxFamily hij k S
  let (m : ℕ) : Countable (C m) := (rootLongBoxFamily_countable hij k S m).to_subtype
  have hT (m : ℕ) (D : C m) : D.val.time = rootLeafWindow S m :=
    rootLongBoxFamily_time hij k S m D.val D.prop
  have hinc (m : ℕ) (D : C m) : B.time ⊆ D.val.time := by
    rw [hT m D]
    exact hBS.trans (rootLeafWindow_mono S (Nat.zero_le m))
  have hA : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ (m : ℕ) (D : C m),
      s ∈ D.val.transverse → D.val.conditionalKernel μ s A.time ≠ 0 ∧
      (A.leafMeasure R μ s).restrict D.val.time =
        (anchorNormalize (D.val.conditionalKernel μ s) A.time).restrict D.val.time := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro D
    exact A.ae_leafMeasure_restrict R hAR μ hfree D.val (hAB.trans (hinc m D))
  have hB := base_ae_of_ae A B hAB μ (B.ae_leafMeasure_spec S hBS μ hfree)
  filter_upwards [hA,hB,A.ae_injective_root_slice_of_ae_free μ hfree] with s hsA hsB hi
  intro hsBt
  have hsB' := hsB hsBt
  apply measure_eq_of_restrictionChain (rootLeafWindow S) (rootLeafWindow_mono S)
    (rootLeafWindow_cover S)
  intro m
  obtain ⟨D,hDC,hsD⟩ := rootLongBoxFamily_covers hij k S m s hi
  let D' : C m := ⟨D,hDC⟩
  have ha := hsA m D' hsD
  have hb := hsB'.2.2.2 m D hDC hsD
  have hBD : B.time ⊆ rootLeafWindow S m := hBS.trans (rootLeafWindow_mono S (Nat.zero_le m))
  have hAD : A.time ⊆ rootLeafWindow S m := hAB.trans hBD
  have hmB : D.conditionalKernel μ s B.time ≠ 0 :=
    (lt_of_lt_of_le (pos_iff_ne_zero.mpr ha.1) (measure_mono hAB)).ne'
  have he := congrArg (fun ν : Measure ℝ => anchorNormalize ν A.time) hb
  rw [anchorNormalize_restrict_comm _ A.time_open.measurableSet hAD,
    anchorNormalize_restrict_comm _ A.time_open.measurableSet hAD,
    anchorNormalize_twice _ _ _ hmB (measure_ne_top _ _)] at he
  rw [he]
  simpa only [hT m D'] using ha.2

 

theorem ae_change_anchor_mass (A B : RootBox hij k) (R S : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0) (hBS : B.time ⊆ rootLeafWindow S 0)
    (hAB : A.time ⊆ B.time) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst, s ∈ B.transverse →
      B.leafMeasure S μ s A.time ≠ 0 ∧ B.leafMeasure S μ s A.time ≠ ∞ := by
  filter_upwards [A.ae_leafMeasure_change_anchor B R S hAR hBS hAB μ hfree,
    A.ae_leafMeasure_spec R hAR μ hfree] with s hs hspec
  intro hsB
  have H : anchorNormalize (B.leafMeasure S μ s) A.time A.time = 1 := by
    rw [←hs hsB]
    exact hspec.2.1
  constructor
  · intro hz
    simp only [anchorNormalize,Measure.smul_apply,smul_eq_mul,hz,mul_zero] at H
    exact zero_ne_one H
  · intro hz
    simp only [anchorNormalize,Measure.smul_apply,smul_eq_mul,hz,ENNReal.inv_top,zero_mul] at H
    exact zero_ne_one H



end PrimeDegreePackets.RootBox


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IntrinsicLeaves
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

lemma ae_eq_of_measurePreserving_ennreal_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {T : α → α} (hT : MeasurePreserving T μ μ)
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hf1 : ∀ᵐ x ∂μ, f x ≤ 1)
    (hmono : ∀ᵐ x ∂μ, f x ≤ f (T x)) : f =ᵐ[μ] f ∘ T := by
  have hint : ∫⁻ x, f x ∂μ < ∞ :=
    (lintegral_mono_ae hf1).trans_lt (by simp)
  have he : ∫⁻ x, f (T x) ∂μ = ∫⁻ x, f x ∂μ := by
    have hf' : AEMeasurable f (μ.map T) := hT.map_eq.symm ▸ hf
    exact ((lintegral_map' hf' hT.measurable.aemeasurable).symm).trans
      (congrArg (fun ν : Measure α => ∫⁻ x, f x ∂ν) hT.map_eq)
  exact ae_eq_of_ae_le_of_lintegral_le hmono hint.ne
    (hf.comp_quasiMeasurePreserving hT.quasiMeasurePreserving) he.le

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

lemma realScaling_preimage_singleton (c : ℝ) (hc : c ≠ 0) :
    (Homeomorph.mulLeft₀ c hc) ⁻¹' ({0} : Set ℝ) = {0} := by
  ext x
  change c*x=0 ↔ x=0
  exact mul_eq_zero.trans (or_iff_right hc)

lemma realScaling_preimage_unitBall_subset (c : ℝ) (hc : 1 ≤ c) :
    (Homeomorph.mulLeft₀ c (ne_of_gt (zero_lt_one.trans_le hc))) ⁻¹' Metric.ball (0:ℝ) 1 ⊆
      Metric.ball 0 1 := by
  intro x hx
  simp only [Set.mem_preimage,Metric.mem_ball,Homeomorph.coe_mulLeft₀,Real.dist_eq,sub_zero] at hx ⊢
  rw [abs_mul,abs_of_nonneg (zero_le_one.trans hc)] at hx
  nlinarith [abs_nonneg x]

lemma realScaling_unitBall_subset_preimage (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    Metric.ball (0:ℝ) 1 ⊆ (Homeomorph.mulLeft₀ c hc.ne') ⁻¹' Metric.ball 0 1 := by
  intro x hx
  simp only [Set.mem_preimage,Metric.mem_ball,Homeomorph.coe_mulLeft₀,Real.dist_eq,sub_zero] at hx ⊢
  rw [abs_mul,abs_of_pos hc]
  nlinarith [abs_nonneg x]

lemma normalized_realScaling_atom (ν : Measure ℝ) (c : ℝ) (hc : c ≠ 0) :
    anchorNormalize (ν.map (Homeomorph.mulLeft₀ c hc)) (Metric.ball 0 1) {0} =
      (ν ((Homeomorph.mulLeft₀ c hc) ⁻¹' Metric.ball 0 1))⁻¹ * ν {0} := by
  change (ν.map (Homeomorph.mulLeft₀ c hc) (Metric.ball 0 1))⁻¹ *
    ν.map (Homeomorph.mulLeft₀ c hc) {0} = _
  rw [Measure.map_apply (Homeomorph.mulLeft₀ c hc).measurable Metric.isOpen_ball.measurableSet,
    Measure.map_apply (Homeomorph.mulLeft₀ c hc).measurable (measurableSet_singleton 0),
    realScaling_preimage_singleton]

 

theorem ae_atom_eq_of_scaling_covariance {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {T : α → α} (hT : MeasurePreserving T μ μ)
    (ν : α → Measure ℝ) (hν : AEMeasurable ν μ)
    (hball : ∀ᵐ x ∂μ, ν x (Metric.ball 0 1) = 1)
    (c : ℝ) (hc : 0 < c)
    (hcov : ∀ᵐ x ∂μ, ν (T x) =
      anchorNormalize ((ν x).map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1)) :
    ∀ᵐ x ∂μ, ν x {0} = ν (T x) {0} := by
  have hm : AEMeasurable (fun x => ν x {0}) μ :=
    (Measure.measurable_coe (measurableSet_singleton 0)).comp_aemeasurable hν
  have hle : ∀ᵐ x ∂μ, ν x {0} ≤ 1 := by
    filter_upwards [hball] with x hx
    rw [←hx]
    exact measure_mono (singleton_subset_iff.mpr (Metric.mem_ball_self zero_lt_one))
  rcases le_total 1 c with h | h
  · apply ae_eq_of_measurePreserving_ennreal_le μ hT hm hle
    filter_upwards [hball,hcov] with x hx he
    rw [he,normalized_realScaling_atom]
    have hb : ν x ((Homeomorph.mulLeft₀ c hc.ne') ⁻¹' Metric.ball 0 1) ≤ 1 := by
      rw [←hx]
      exact measure_mono (realScaling_preimage_unitBall_subset c h)
    calc
      ν x {0} = 1 * ν x {0} := (one_mul _).symm
      _ ≤ _ := mul_le_mul' (ENNReal.one_le_inv.mpr hb) le_rfl
  · apply ae_eq_of_measurePreserving_ennreal_ge μ hT hm hle
    filter_upwards [hball,hcov] with x hx he
    rw [he,normalized_realScaling_atom]
    have hb : 1 ≤ ν x ((Homeomorph.mulLeft₀ c hc.ne') ⁻¹' Metric.ball 0 1) := by
      rw [←hx]
      exact measure_mono (realScaling_unitBall_subset_preimage c hc h)
    calc
      _ ≤ 1 * ν x {0} := mul_le_mul' (ENNReal.inv_le_one.mpr hb) le_rfl
      _ = ν x {0} := one_mul _

lemma scaling_ball_mass_of_atom_eq (ν : Measure ℝ) (c : ℝ) (hc : c ≠ 0)
    (h0 : ν {0} ≠ 0) (hT : ν {0} ≠ ∞)
    (he : anchorNormalize (ν.map (Homeomorph.mulLeft₀ c hc)) (Metric.ball 0 1) {0} = ν {0}) :
    ν ((Homeomorph.mulLeft₀ c hc) ⁻¹' Metric.ball 0 1) = 1 := by
  rw [normalized_realScaling_atom] at he
  have H := congrArg (fun a : ℝ≥0∞ => a*(ν {0})⁻¹) he
  rw [ENNReal.mul_inv_cancel_right h0 hT,ENNReal.mul_inv_cancel h0 hT] at H
  exact ENNReal.inv_eq_one.mp H

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma real_iInter_ball_inv_nat :
    (⋂ m : ℕ, Metric.ball (0:ℝ) ((m+1:ℝ)⁻¹)) = {0} := by
  ext x
  simp only [mem_iInter,mem_singleton_iff,Metric.mem_ball,Real.dist_eq,sub_zero]
  constructor
  · intro h
    by_contra hx
    have hx0 : 0 < |x| := abs_pos.mpr hx
    obtain ⟨m,hm⟩ := exists_nat_gt (|x|⁻¹)
    have hm0 : (0:ℝ) < m+1 := by positivity
    have hh := h m
    have hl : (m+1:ℝ)⁻¹ < |x| := by
      rw [←one_div]
      apply (one_div_lt hm0 hx0).mpr
      simpa only [one_div] using hm.trans (by linarith : (m:ℝ) < m+1)
    exact (not_lt_of_ge hl.le) hh
  · rintro rfl m
    simp only [abs_zero]
    positivity

lemma realMeasure_eq_dirac_of_ball_masses (ν : Measure ℝ)
    (hsmall : ∀ m : ℕ, ν (Metric.ball 0 ((m+1:ℝ)⁻¹)) = 1)
    (hlarge : ∀ m : ℕ, ν (Metric.ball 0 (m+1:ℝ)) = 1) : ν = Measure.dirac 0 := by
  have hmono : Monotone (fun m : ℕ => Metric.ball (0:ℝ) (m+1:ℝ)) := by
    intro a b hab
    exact Metric.ball_subset_ball (by exact_mod_cast Nat.add_le_add_right hab 1)
  have hu : ν univ = 1 := by
    rw [← Metric.iUnion_ball_nat_succ (0:ℝ),hmono.measure_iUnion]
    simp only [hlarge,iSup_const]
  have hanti : Antitone (fun m : ℕ => Metric.ball (0:ℝ) ((m+1:ℝ)⁻¹)) := by
    intro a b hab
    apply Metric.ball_subset_ball
    exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
  have h0 : ν {0} = 1 := by
    rw [←real_iInter_ball_inv_nat,hanti.measure_iInter
      (fun _ => Metric.isOpen_ball.measurableSet.nullMeasurableSet) ⟨0,by rw [hsmall]; exact ENNReal.one_ne_top⟩]
    simp only [hsmall,iInf_const]
  let : IsFiniteMeasure ν := ⟨by rw [hu]; exact ENNReal.one_lt_top⟩
  have hc : ν ({0} : Set ℝ)ᶜ = 0 := by
    rw [measure_compl (measurableSet_singleton _) (by finiteness),hu,h0,tsub_self]
  ext s hs
  by_cases hx : (0:ℝ) ∈ s
  · rw [Measure.dirac_apply_of_mem hx]
    apply le_antisymm
    · simpa only [hu] using measure_mono (subset_univ s) (μ := ν)
    · rw [←h0]
      exact measure_mono (singleton_subset_iff.mpr hx)
  · simp only [Measure.dirac_apply,indicator_of_notMem hx]
    apply le_antisymm _ bot_le
    exact (measure_mono (subset_compl_singleton_iff.mpr hx)).trans hc.le

 

theorem ae_dirac_of_scaling_covariance {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (ν : α → Measure ℝ)
    (hν : AEMeasurable ν μ) (hball : ∀ᵐ x ∂μ, ν x (Metric.ball 0 1) = 1)
    (hscale : ∀ (c : ℝ) (hc : 0 < c), ∃ T : α → α,
      MeasurePreserving T μ μ ∧ ∀ᵐ x ∂μ, ν (T x) =
        anchorNormalize ((ν x).map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1)) :
    ∀ᵐ x ∂μ, ν x {0} ≠ 0 → ν x = Measure.dirac 0 := by
  have H (c : ℝ) (hc : 0 < c) : ∀ᵐ x ∂μ, ν x {0} ≠ 0 → ν x (Metric.ball 0 (1/c)) = 1 := by
    obtain ⟨T,hT,hcov⟩ := hscale c hc
    have he := ae_atom_eq_of_scaling_covariance μ hT ν hν hball c hc hcov
    filter_upwards [hball,hcov,he] with x hx hc' he' h0
    have hT' : ν x {0} ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (by
      rw [←hx]
      exact measure_mono (singleton_subset_iff.mpr (Metric.mem_ball_self zero_lt_one)))
    have hh := scaling_ball_mass_of_atom_eq (ν x) c hc.ne' h0 hT' (by rw [←hc']; exact he'.symm)
    rwa [realScaling_preimage_ball c 1 hc] at hh
  have HS := ae_all_iff.mpr (fun m : ℕ => H (m+1) (by positivity))
  have HL := ae_all_iff.mpr (fun m : ℕ => H ((m+1:ℝ)⁻¹) (by positivity))
  filter_upwards [HS,HL] with x hs hl h0
  apply realMeasure_eq_dirac_of_ball_masses (ν x)
  · intro m
    simpa only [one_div] using hs m h0
  · intro m
    simpa only [one_div,inv_inv] using hl m h0

end PrimeDegreePackets


namespace PrimeDegreePackets

 

theorem ae_intrinsicRootLeaf_atom_dirac (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x {0} ≠ 0 →
      intrinsicRootLeaf hij μ x = Measure.dirac 0 := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  apply ae_dirac_of_scaling_covariance μ (intrinsicRootLeaf hij μ)
    (aemeasurable_intrinsicRootLeaf hij μ hfree)
    ((ae_intrinsicRootLeaf_spec hij μ hfree).mono fun x hx => hx.2)
  intro c hc
  let ell := coordinateContractionWeights d j
  have hell : ∑ k, ell k = 0 := coordinateContractionWeights_sum d j
  let t := Real.log c / (d+1:ℝ)
  let a := diagonalOneParameter ell hell t
  have hinv : μ.map (fun x => rightAction x a) = μ := by
    rw [show a = diagonalFlow (fun k : Fin d => ell k.castSucc*t) from
      diagonalOneParameter_eq_diagonalFlow ell hell t]
    exact hA _
  refine ⟨(fun x => rightAction x a),⟨(continuous_rightAction a).measurable,hinv⟩,?_⟩
  have hrate : ell j-ell i = (d+1:ℝ) := by
    simp [ell,coordinateContractionWeights,hij]
  have he : Real.exp ((ell j-ell i)*t) = c := by
    rw [hrate]
    dsimp [t]
    rw [mul_comm,div_mul_cancel₀ _ (by positivity),Real.exp_log hc]
  have hs : rootTimeScaling ell i j t = Homeomorph.mulLeft₀ c hc.ne' := by
    apply Homeomorph.ext
    intro v
    simp only [rootTimeScaling,Homeomorph.coe_mulLeft₀,he]
  have H := ae_intrinsicRootLeaf_diagonal hij ell hell t μ hfree hinv
  simpa only [hs] using H



end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_AmbientLeaves
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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


namespace PrimeDegreePackets
namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

 

theorem ae_leafMeasure_intrinsic (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ᵐ t ∂A.leafMeasure R μ s,
      intrinsicRootLeaf hij μ (rootQuotientParametrization hij (s,t)) =
        basedRealMeasure (A.leafMeasure R μ s) t := by
  let C := rootLongBoxFamily hij k R
  let (m : ℕ) : Countable (C m) := (rootLongBoxFamily_countable hij k R m).to_subtype
  have hT (m : ℕ) (B : C m) : B.val.time = rootLeafWindow R m :=
    rootLongBoxFamily_time hij k R m B.val B.prop
  have hinc (m : ℕ) (B : C m) : A.time ⊆ B.val.time := by
    rw [hT m B]
    exact hAR.trans (rootLeafWindow_mono R (Nat.zero_le m))
  have hbound (m : ℕ) (B : C m) : B.val.time ⊆ rootLeafWindow (R+m) 0 := by
    rw [hT m B]
    simp only [rootLeafWindow,Nat.cast_zero,add_zero,subset_refl]
  have HD (m : ℕ) (B : C m) : ∀ᵐ s ∂(B.val.coordinateMeasure μ).fst,
      ∀ᵐ t ∂B.val.conditionalKernel μ s,
      intrinsicRootLeaf hij μ (rootQuotientParametrization hij (s,t)) =
        basedRealMeasure (B.val.leafMeasure (R+m) μ s) t := by
    have H : ∀ᵐ z ∂(B.val.coordinateMeasure μ).fst ⊗ₘ B.val.conditionalKernel μ,
        intrinsicRootLeaf hij μ (rootQuotientParametrization hij z) = B.val.basedLeaf (R+m) μ z := by
      simpa only [conditionalKernel,Measure.disintegrate] using
        B.val.ae_intrinsicRootLeaf_coordinates (R+m) (hbound m B) μ hfree
    exact Measure.ae_ae_of_ae_compProd H
  have H (m : ℕ) (B : C m) : ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      s ∈ B.val.transverse → ∀ᵐ t ∂(A.leafMeasure R μ s).restrict (rootLeafWindow R m),
      intrinsicRootLeaf hij μ (rootQuotientParametrization hij (s,t)) =
        basedRealMeasure (A.leafMeasure R μ s) t := by
    filter_upwards [A.ae_leafMeasure_restrict R hAR μ hfree B.val (hinc m B),
      A.base_ae_of_ae B.val (hinc m B) μ (HD m B),
      A.ae_leafMeasure_change_anchor B.val R (R+m) hAR (hbound m B) (hinc m B) μ hfree,
      A.ae_change_anchor_mass B.val R (R+m) hAR (hbound m B) (hinc m B) μ hfree]
      with s hs hd he hm hsb
    have he' (t : ℝ) : basedRealMeasure (A.leafMeasure R μ s) t =
        basedRealMeasure (B.val.leafMeasure (R+m) μ s) t := by
      rw [he hsb]
      exact basedRealMeasure_smul _ _ (ENNReal.inv_ne_zero.mpr (hm hsb).2)
        (ENNReal.inv_ne_top.mpr (hm hsb).1) _
    have hh := ae_restrict_of_ae (s := B.val.time) (Measure.ae_smul_measure (hd hsb)
      ((B.val.conditionalKernel μ s A.time)⁻¹))
    change ∀ᵐ t ∂(anchorNormalize (B.val.conditionalKernel μ s) A.time).restrict B.val.time,
      intrinsicRootLeaf hij μ (rootQuotientParametrization hij (s,t)) =
        basedRealMeasure (B.val.leafMeasure (R+m) μ s) t at hh
    rw [←(hs hsb).2,hT m B] at hh
    simpa only [he'] using hh
  have Hall := ae_all_iff.mpr (fun m => ae_all_iff.mpr (H m))
  filter_upwards [Hall,A.ae_injective_root_slice_of_ae_free μ hfree] with s hs hi
  have HW (m : ℕ) : ∀ᵐ t ∂(A.leafMeasure R μ s).restrict (rootLeafWindow R m),
      intrinsicRootLeaf hij μ (rootQuotientParametrization hij (s,t)) =
        basedRealMeasure (A.leafMeasure R μ s) t := by
    obtain ⟨B,hBC,hsB⟩ := rootLongBoxFamily_covers hij k R m s hi
    exact hs m ⟨B,hBC⟩ hsB
  have HH := (ae_restrict_iUnion_iff (μ := A.leafMeasure R μ s) (rootLeafWindow R) _).mpr HW
  simpa only [rootLeafWindow_cover,Measure.restrict_univ] using HH

lemma ae_basedLeaf_rebase (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ z ∂A.coordinateMeasure μ, ∀ᵐ t ∂A.basedLeaf R μ z,
      intrinsicRootLeaf hij μ (rightAction (rootQuotientParametrization hij z)
        (Matrix.SpecialLinearGroup.transvection hij t)) = basedRealMeasure (A.basedLeaf R μ z) t := by
  have H := ae_of_ae_map measurable_fst.aemeasurable (A.ae_leafMeasure_intrinsic R hAR μ hfree)
  have HL := ae_of_ae_map measurable_fst.aemeasurable
    ((A.ae_leafMeasure_spec R hAR μ hfree).mono fun _ h => h.1)
  filter_upwards [H,HL,A.ae_leafMeasure_ball_pos R hAR μ hfree] with z hz hlf hp
  let : IsLocallyFiniteMeasure (A.leafMeasure R μ z.1) := hlf
  apply Measure.ae_smul_measure
  apply (Homeomorph.subRight z.2).measurableEmbedding.ae_map_iff.mpr
  filter_upwards [hz] with t ht
  change intrinsicRootLeaf hij μ (rightAction (rootQuotientParametrization hij z)
    (Matrix.SpecialLinearGroup.transvection hij (t-z.2))) =
      basedRealMeasure (basedRealMeasure (A.leafMeasure R μ z.1) z.2) (t-z.2)
  rw [←rootQuotientParametrization_add,basedRealMeasure_rebase _ _ _ (hp 1 zero_lt_one),←add_sub_assoc,add_sub_cancel_left]
  exact ht

end RootBox

 

theorem ae_intrinsicRootLeaf_rebase {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ x ∂μ, ∀ᵐ t ∂intrinsicRootLeaf hij μ x,
      intrinsicRootLeaf hij μ (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) =
        basedRealMeasure (intrinsicRootLeaf hij μ x) t := by
  let : Countable (boundedRootAtlas hij) := (boundedRootAtlas_countable hij).to_subtype
  have H (B : boundedRootAtlas hij) : ∀ᵐ x ∂μ.restrict B.val.box.range,
      ∀ᵐ t ∂intrinsicRootLeaf hij μ x,
        intrinsicRootLeaf hij μ (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) =
          basedRealMeasure (intrinsicRootLeaf hij μ x) t := by
    apply B.val.box.ae_of_coordinate μ
    filter_upwards [B.val.box.ae_intrinsicRootLeaf_coordinates B.val.radius B.val.time_bound μ hfree,
      B.val.box.ae_basedLeaf_rebase B.val.radius B.val.time_bound μ hfree] with z he hz
    rwa [he]
  have HH := (ae_restrict_iUnion_iff (μ := μ) (fun B : boundedRootAtlas hij => B.val.box.range) _).mpr H
  simpa only [boundedRootAtlas_iUnion,Measure.restrict_univ] using HH

end PrimeDegreePackets

open scoped Topology ENNReal
namespace PrimeDegreePackets

lemma centerRealMeasure_singleton (ν : Measure ℝ) (t u : ℝ) :
    centerRealMeasure ν t {u} = ν {u+t} := by
  rw [centerRealMeasure,Measure.map_apply (Homeomorph.subRight t).measurable (measurableSet_singleton u)]
  congr 1
  ext v
  simp only [Set.mem_preimage,mem_singleton_iff,Homeomorph.coe_subRight]
  exact sub_eq_iff_eq_add

lemma basedRealMeasure_atom_ne_zero (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (t : ℝ) (ht : ν {t} ≠ 0) : basedRealMeasure ν t {0} ≠ 0 := by
  change (centerRealMeasure ν t (Metric.ball 0 1))⁻¹ * centerRealMeasure ν t {0} ≠ 0
  rw [centerRealMeasure_ball,centerRealMeasure_singleton,zero_add]
  exact mul_ne_zero (ENNReal.inv_ne_zero.mpr measure_ball_lt_top.ne) ht

lemma ae_property_at_atom {α : Type*} [MeasurableSpace α] (ν : Measure α)
    {P : α → Prop} (hP : ∀ᵐ x ∂ν, P x) {t : α} (ht : ν {t} ≠ 0) : P t := by
  by_contra h
  exact ht (measure_mono_null (singleton_subset_iff.mpr h) (ae_iff.mp hP))

 

theorem realLeaf_nullSingleton_or_dirac (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hunit : ν (Metric.ball 0 1) = 1)
    (hsupport : ∀ r : ℝ, 0 < r → 0 < ν (Metric.ball 0 r))
    (hbase : ∀ᵐ t ∂ν, basedRealMeasure ν t {0} ≠ 0 →
      basedRealMeasure ν t = Measure.dirac 0) :
    NullSingletonClass ν ∨ ν = Measure.dirac 0 := by
  classical
  by_cases h : ∀ t : ℝ, ν {t} = 0
  · exact Or.inl ⟨h⟩
  · right
    obtain ⟨t,ht⟩ := not_forall.mp h
    have hb := (ae_property_at_atom ν hbase ht) (basedRealMeasure_atom_ne_zero ν t ht)
    have hball : ν (Metric.ball t 1) ≠ 0 :=
      (lt_of_lt_of_le (pos_iff_ne_zero.mpr ht)
        (measure_mono (singleton_subset_iff.mpr (Metric.mem_ball_self zero_lt_one)))).ne'
    have hcomp : centerRealMeasure ν t ({0}ᶜ) = ν ({t}ᶜ) := by
      rw [centerRealMeasure,Measure.map_apply (Homeomorph.subRight t).measurable
        (measurableSet_singleton 0).compl]
      congr 1
      ext v
      simp [sub_eq_zero]
    have hh := congrArg (fun ρ : Measure ℝ => ρ ({0}ᶜ)) hb
    change (centerRealMeasure ν t (Metric.ball 0 1))⁻¹ * centerRealMeasure ν t ({0}ᶜ) = _ at hh
    rw [centerRealMeasure_ball,hcomp] at hh
    have hc : ν ({t}ᶜ) = 0 := by
      have hz : (ν (Metric.ball t 1))⁻¹ * ν ({t}ᶜ) = 0 := by simpa using hh
      exact (mul_eq_zero.mp hz).resolve_left (ENNReal.inv_ne_zero.mpr measure_ball_lt_top.ne)
    have ht0 : t = 0 := by
      by_contra hne
      have hsub : Metric.ball (0:ℝ) (|t|/2) ⊆ {t}ᶜ := by
        intro v hv he
        have hvt : v = t := he
        subst v
        have hav := Metric.mem_ball.mp hv
        rw [Real.dist_eq,sub_zero] at hav
        linarith [abs_nonneg t]
      exact (hsupport _ (half_pos (abs_pos.mpr hne))).ne' (measure_mono_null hsub hc)
    subst t
    have hdir : ν = ν {0} • Measure.dirac 0 := by
      have ha : ∀ᵐ t ∂ν, t ∈ ({0} : Finset ℝ) := by
        have ha' : ∀ᵐ x ∂ν, x ∈ ({0} : Set ℝ) := mem_ae_iff.mpr hc
        filter_upwards [ha'] with x hx
        simpa only [mem_singleton_iff,Finset.mem_singleton] using hx
      simpa using Measure.ae_mem_finset_iff.mp ha
    have hmass : ν {0} = 1 := by
      rw [hdir,Measure.smul_apply] at hunit
      simpa using hunit
    rwa [hmass,one_smul] at hdir

end PrimeDegreePackets

open scoped Matrix Topology ENNReal ProbabilityTheory
namespace PrimeDegreePackets



theorem ae_intrinsicRootLeaf_nullSingleton_or_dirac (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ, NullSingletonClass (intrinsicRootLeaf hij μ x) ∨
      intrinsicRootLeaf hij μ x = Measure.dirac 0 := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  have HA := ae_intrinsicRootLeaf_of_ambient hij μ hfree
    (ae_intrinsicRootLeaf_atom_dirac d hij μ hA)
  filter_upwards [HA,ae_intrinsicRootLeaf_rebase hij μ hfree,
    ae_intrinsicRootLeaf_spec hij μ hfree,ae_intrinsicRootLeaf_ball_pos hij μ hfree] with x ha hr hs hp
  let : IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ x) := hs.1
  apply realLeaf_nullSingleton_or_dirac _ hs.2 hp
  filter_upwards [ha,hr] with t ht he
  rwa [he] at ht

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ScalingCovariance
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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


namespace PrimeDegreePackets

 

theorem ae_intrinsicRootLeaf_atom_diagonal (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) (u : LogCoordinates d) :
    ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x {0} =
      intrinsicRootLeaf hij μ (rightAction x (diagonalFlow u)) {0} := by
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
  exact ae_atom_eq_of_scaling_covariance μ
    ⟨(continuous_rightAction _).measurable,hA u⟩ (intrinsicRootLeaf hij μ)
    (aemeasurable_intrinsicRootLeaf hij μ hfree)
    ((ae_intrinsicRootLeaf_spec hij μ hfree).mono fun x hx => hx.2)
    _ (Real.exp_pos _) H

 

theorem intrinsicRootLeaf_ergodic_alternative (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ] :
    (∀ᵐ x ∂μ, NullSingletonClass (intrinsicRootLeaf hij μ x)) ∨
      (∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x = Measure.dirac 0) := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  let S : Set (X (d+1)) := {x | intrinsicRootLeaf hij μ x {0} = 0}
  have hm : NullMeasurableSet S μ := by
    exact nullMeasurableSet_eq_fun
      ((Measure.measurable_coe (measurableSet_singleton 0)).comp_aemeasurable
        (aemeasurable_intrinsicRootLeaf hij μ hfree)) aemeasurable_const
  have he : EventuallyConst S (ae μ) :=
    aeconst_of_forall_preimage_smul_ae_eq (Multiplicative (LogCoordinates d)) hm (by
      intro u
      filter_upwards [ae_intrinsicRootLeaf_atom_diagonal d hij μ hA u.toAdd] with x hx
      change (intrinsicRootLeaf hij μ (rightAction x (diagonalFlow u.toAdd)) {0} = 0) =
        (intrinsicRootLeaf hij μ x {0} = 0)
      rw [hx])
  rcases eventuallyConst_set.mp he with hz | hn
  · left
    filter_upwards [hz,ae_intrinsicRootLeaf_nullSingleton_or_dirac d hij μ hA] with x hx h
    rcases h with h | h
    · exact h
    · change intrinsicRootLeaf hij μ x {0} = 0 at hx
      rw [h] at hx
      simp at hx
  · right
    filter_upwards [hn,ae_intrinsicRootLeaf_atom_dirac d hij μ hA] with x hx h
    exact h hx

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_CanonicalRootBasic
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mean root coefficients and their elementary properties

The coefficient is the mean leaf information at unit scale. Diagonal
covariance makes real-time mean information linear in time.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable (d : ℕ) (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
  (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)

lemma canonicalRootCoefficient_diagonal (i : Fin (d + 1)) :
    canonicalRootCoefficient d μ i i = 0 := by simp [canonicalRootCoefficient]

lemma canonicalRootCoefficient_nonneg (i j : Fin (d + 1)) :
    0 ≤ canonicalRootCoefficient d μ i j := by
  unfold canonicalRootCoefficient
  split_ifs
  · exact le_rfl
  · exact ENNReal.toReal_nonneg

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_NoInvariantRootGraph
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Without invariant roots the positive-root graph has no two-step path -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

private lemma positive_coefficient_atomless (d : ℕ)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    {i j : Fin (d+1)} (hij : i ≠ j) (hp : 0 < canonicalRootCoefficient d μ i j) :
    ∀ᵐ x ∂μ, NullSingletonClass (intrinsicRootLeaf hij μ x) := by
  rcases intrinsicRootLeaf_ergodic_alternative d hij μ with h | h
  · exact h
  · have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
      (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
    exact (hp.ne' ((canonicalRootCoefficient_zero_iff d μ hA i j hij).mpr h)).elim

/-- The commutator argument handles distinct endpoints; the isolated
opposite-root pair is handled by the already proved low-entropy theorem. -/
theorem no_two_step_positive_roots_of_no_invariant_root_oai (d : ℕ) (hd : 2 < d+1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (hnone : ∀ (i j : Fin (d+1)) (hij : i ≠ j), ¬ ∀ t : ℝ,
      μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij t))=μ) :
    ∀ a b c : Fin (d+1), 0 < canonicalRootCoefficient d μ a b →
      0 < canonicalRootCoefficient d μ b c → False := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hdistinct {i j : Fin (d+1)} (h : 0 < canonicalRootCoefficient d μ i j) : i ≠ j := by
    rintro rfl
    simp only [canonicalRootCoefficient_diagonal,lt_self_iff_false] at h
  have hno {a b c : Fin (d+1)} (hac : a ≠ c)
      (hab : 0 < canonicalRootCoefficient d μ a b)
      (hbc : 0 < canonicalRootCoefficient d μ b c) : False :=
    hnone a c hac (root_invariant_of_adjacent_nonatomic_leaves d
      (hdistinct hab) (hdistinct hbc) hac μ
      (positive_coefficient_atomless d μ (hdistinct hab) hab)
      (positive_coefficient_atomless d μ (hdistinct hbc) hbc))
  intro a b c hab hbc
  by_cases hac : a=c
  · subst c
    have hab' := hdistinct hab
    apply hnone a b hab'
    apply root_invariant_of_atomic_companion_leaves d hd hab' μ
    · filter_upwards [positive_coefficient_atomless d μ hab' hab] with x hx
      let : NullSingletonClass (intrinsicRootLeaf hab' μ x) := hx
      intro he
      have hz := measure_singleton (μ := intrinsicRootLeaf hab' μ x) (0:ℝ)
      simp [he] at hz
    · intro k hka hkb
      apply (canonicalRootCoefficient_zero_iff d μ hA a k hka.symm).mp
      exact le_antisymm (le_of_not_gt fun hp => hno hkb.symm hbc hp)
        (canonicalRootCoefficient_nonneg d μ a k)
    · intro k hka hkb
      apply (canonicalRootCoefficient_zero_iff d μ hA k b hkb).mp
      exact le_antisymm (le_of_not_gt fun hp => hno hka hp hbc)
        (canonicalRootCoefficient_nonneg d μ k b)
  · exact hno hac hab hbc

end DukePrimeDegree

end

end OAI
end

theorem solution : type_of% @OAI.DukePrimeDegree.no_two_step_positive_roots_of_no_invariant_root_oai := @OAI.DukePrimeDegree.no_two_step_positive_roots_of_no_invariant_root_oai
