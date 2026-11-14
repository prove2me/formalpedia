-- Prove2me | solution 1 for OAI.DukePrimeDegree.positive_root_sum_le_diagonal_entropy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:46:41.562201+00:00
-- url     : https://prove2.me/submissions/79d58bc3-7609-464e-9401-ee7ae41efe59

import Mathlib
import Mathlib.Algebra.Order.SuccPred.PartialSups
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Logic.Encodable.Lattice
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.Piecewise
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Comap
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.PartialSups
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke044
import Theorems.Thm_OAI_DukePrimeDegree_EliminationChain_wholeFuture_conditionalInformation_integrable_integral
import Theorems.Thm_OAI_DukePrimeDegree_conditionalSigmaEntropy_heightClip_tendsto
import Theorems.Thm_OAI_DukePrimeDegree_exists_cover_stationary_wholeFutureKernel
import Theorems.Thm_OAI_PrimeDegreePackets_observationEntropyRate_eq_futureConditional

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ShannonEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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
namespace PrimeDegreePackets

lemma orbitName_measurable_fiber {Y α : Type*} [MeasurableSpace Y]
    {T : Y → Y} (hT : Measurable T) {P : Y → α}
    (hP : ∀ a, MeasurableSet {y | P y = a}) (N : ℕ) (a : Fin N → α) :
    MeasurableSet {y | orbitName T P N y = a} := by
  have heq : {y | orbitName T P N y = a} = ⋂ j : Fin N, {y | P (T^[j] y) = a j} := by
    ext y
    simp [orbitName,funext_iff]
  rw [heq]
  exact MeasurableSet.iInter fun j => (hP (a j)).preimage (hT.iterate j)

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_EntropyMixtures
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xBorelSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
namespace PrimeDegreePackets

variable {Z Y ι : Type*} [MeasurableSpace Z] [MeasurableSpace Y]



lemma measurable_kernel_real (κ : Kernel Z Y) {S : Set Y} (hS : MeasurableSet S) :
    Measurable (fun z => (κ z).real S) := (κ.measurable_coe hS).ennreal_toReal

lemma integrable_kernel_real (τ : Measure Z) [IsFiniteMeasure τ]
    (κ : Kernel Z Y) [IsMarkovKernel κ] {S : Set Y} (hS : MeasurableSet S) :
    Integrable (fun z => (κ z).real S) τ := by
  refine Integrable.mono' (integrable_const (1:ℝ)) (measurable_kernel_real κ hS).aestronglyMeasurable ?_
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ObservationSigmaAlgebra
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sigma algebra and conditional expectations of finite observations -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace PrimeDegreePackets

variable {Y β : Type*} [mY : MeasurableSpace Y] [Fintype β]

lemma observationSigma_le (Q : Y → β)
    (hQ : ∀ b, MeasurableSet {y | Q y = b}) : observationSigma Q ≤ mY := by
  classical
  rintro s ⟨t,_,rfl⟩
  have heq : Q ⁻¹' t = ⋃ b : t, {y | Q y = b.val} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨⟨Q y,h⟩,rfl⟩, fun ⟨b,h⟩ => h ▸ b.property⟩
  rw [heq]
  exact MeasurableSet.iUnion (fun b => hQ b.val)

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_ConditionalSigmaOrder
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditioning on more measurable information decreases entropy

Conditional Jensen and the tower property apply directly to the actual
conditional expectations defining finite-observation entropy.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma integrable_negMulLog_of_unit_bounds {Y : Type*} [mY : MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] {f : Y → ℝ}
    (hf : AEStronglyMeasurable f μ) (hb : ∀ᵐ y ∂μ, f y ∈ Icc 0 1) :
    Integrable (fun y => Real.negMulLog (f y)) μ := by
  apply (integrable_const (1:ℝ)).mono'
    (Real.continuous_negMulLog.comp_aestronglyMeasurable hf)
  filter_upwards [hb] with y hy
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.negMulLog_nonneg hy.1 hy.2)]
  have H := Real.negMulLog_le_one_sub_self hy.1
  linarith [hy.1]

lemma conditionalProbability_unit_bounds {Y : Type*} [mY : MeasurableSpace Y]
    (μ : Measure Y) (S : Set Y) (m : MeasurableSpace Y) :
    ∀ᵐ y ∂μ, (μ[S.indicator (fun _ => (1:ℝ)) | m]) y ∈ Icc 0 1 := by
  have hn : 0 ≤ᵐ[μ] S.indicator (fun _ => (1:ℝ)) := by
    apply ae_of_all
    intro y
    by_cases hy : y ∈ S <;> simp [hy]
  have hu : ∀ᵐ y ∂μ, S.indicator (fun _ => (1:ℝ)) y ≤ 1 := by
    apply ae_of_all
    intro y
    by_cases hy : y ∈ S <;> simp [hy]
  filter_upwards [condExp_nonneg (m := m) hn,
    condExp_le_nonneg_const (m := m) (show (0:ℝ)≤1 by norm_num) hu] with y hy hz
  exact ⟨hy,hz⟩

theorem conditionalSigmaEntropy_antitone {Y α : Type*} [mY : MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y=a})
    {m n : MeasurableSpace Y} (hmn : m ≤ n) (hn : n ≤ mY) :
    conditionalSigmaEntropy (mY := mY) μ P n ≤ conditionalSigmaEntropy (mY := mY) μ P m := by
  have hm := hmn.trans hn
  let g (a : α) : Y → ℝ := {y | P y=a}.indicator (fun _ => 1)
  have hg a : Integrable (g a) μ := (integrable_const (1:ℝ)).indicator (hP a)
  have hi (s : MeasurableSpace Y) (hs : s ≤ mY) (a : α) :
      Integrable (fun y => Real.negMulLog ((μ[g a | s]) y)) μ :=
    integrable_negMulLog_of_unit_bounds (mY := mY) μ
      (stronglyMeasurable_condExp.mono hs).aestronglyMeasurable
      (conditionalProbability_unit_bounds (mY := mY) μ {y | P y=a} s)
  unfold conditionalSigmaEntropy finiteShannon
  rw [integral_finsetSum _ (fun a _ => hi n hn a),
    integral_finsetSum _ (fun a _ => hi m hm a)]
  apply Finset.sum_le_sum
  intro a _
  have hJ := Real.concaveOn_negMulLog.condExp_map_le (μ := μ) (f := μ[g a | n]) hm
    (Real.continuous_negMulLog.upperSemicontinuous.upperSemicontinuousOn _)
    ((conditionalProbability_unit_bounds (mY := mY) μ {y | P y=a} n).mono fun _ h => h.1)
    isClosed_Ici integrable_condExp (hi n hn a)
  have hTower := condExp_condExp_of_le (μ := μ) (f := g a) hmn hn
  have hle : (μ[(fun y => Real.negMulLog ((μ[g a | n]) y)) | m]) ≤ᵐ[μ]
      (fun y => Real.negMulLog ((μ[g a | m]) y)) := by
    filter_upwards [hJ,hTower] with y hy ht
    simpa only [Function.comp_def,ht] using hy
  calc
    _ = ∫ y, (μ[(fun z => Real.negMulLog ((μ[g a | n]) z)) | m]) y ∂μ :=
      (integral_condExp hm).symm
    _ ≤ _ := integral_mono_ae integrable_condExp (hi m hm a) hle

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_ConditionalInformationLowerBound
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Whole-future conditional information is bounded by metric entropy

Finite present clips have their own, smaller future sigma algebra.
Conditioning on the full countable future and further transverse data
only decreases their entropy. Passing to the proved clipping limit gives
the bound without a finite Shannon entropy assumption on the countable
observation.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable {Y : Type*}

lemma clipped_future_sigma_le (T : Y → Y) (Q : Y → ℕ)
    (m : MeasurableSpace Y)
    (hfuture : (⨆ k : ℕ, observationSigma (fun y => Q (T^[k+1] y))) ≤ m)
    (N : ℕ) : (⨆ k, observationSigma (futureName T (heightClip Q N) k)) ≤ m := by
  let : MeasurableSpace Y := m
  have hcoord (k : ℕ) : Measurable (fun y => Q (T^[k+1] y)) :=
    (comap_measurable _).mono ((le_iSup _ k).trans hfuture) le_rfl
  apply iSup_le
  intro k
  apply observationSigma_le
  intro w
  have hName : Measurable (futureName T (heightClip Q N) k) := by
    apply measurable_pi_iff.mpr
    intro i
    have heq : (fun y => futureName T (heightClip Q N) k y i) =
        heightClip (fun y => Q (T^[i.val+1] y)) N := by
      funext y
      apply Fin.ext
      simp only [futureName, orbitName, heightClip, Function.iterate_succ_apply]
    rw [heq]
    exact heightClip_measurable (hcoord i.val) N
  exact hName (measurableSet_singleton w)

theorem conditionalInformation_integral_le_metricEntropy
    (m : MeasurableSpace Y) [mY : MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (Q : Y → ℕ) (hQ : Measurable Q) (hm : m ≤ mY)
    (hfuture : (⨆ k : ℕ, observationSigma (fun y => Q (T^[k+1] y))) ≤ m)
    (hpos : ∀ᵐ y ∂μ,
      0 < (μ[({z | Q z = Q y}.indicator (fun _ => (1 : ℝ))) | m]) y)
    (hint : Integrable (conditionalInformation μ Q m) μ) :
    ENNReal.ofReal (∫ y, conditionalInformation μ Q m y ∂μ) ≤ measureEntropy μ T := by
  have hclip := conditionalSigmaEntropy_heightClip_tendsto m μ Q hQ hm hpos hint
  apply le_of_tendsto (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hclip)
  apply Filter.Eventually.of_forall
  intro N
  have hP := heightClip_measurable hQ N
  have hle : conditionalSigmaEntropy μ (heightClip Q N) m ≤
      observationEntropyRate μ T (heightClip Q N) := by
    rw [observationEntropyRate_eq_futureConditional μ hT _
      (fun a => hP (measurableSet_singleton a))]
    exact conditionalSigmaEntropy_antitone μ _
      (fun a => hP (measurableSet_singleton a))
      (clipped_future_sigma_le T Q m hfuture N) hm
  apply (ENNReal.ofReal_le_ofReal hle).trans
  unfold measureEntropy
  exact le_iSup_of_le (N+1) (le_iSup_of_le (heightClip Q N)
    (le_iSup_of_le (fun a => hP (measurableSet_singleton a)) le_rfl))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootEuclideanCoordinates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# One real coordinate for each positive root

The elimination time space is canonically a finite product of real
lines, indexed without repetition by the positive roots. Diagonal
conjugation scales each coordinate by its own root character.
-/

noncomputable section
open Matrix Set
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

lemma timeVectorHomeomorph_cube (c : EliminationChain P D) (R : ℝ) (t : c.Time) :
    t ∈ c.cube R ↔ ∀ k, |c.timeVectorHomeomorph t k| < R := by
  induction c with
  | done => simp [cube, roots]
  | step a b hab hP hb tail ih =>
      change tail.Time × ℝ at t
      change t.1 ∈ tail.cube R ∧ t.2 ∈ Ioo (-R) R ↔
        ∀ k : Fin (tail.roots.length + 1),
          |Fin.cons (α := fun _ : Fin (tail.roots.length + 1) => ℝ) t.2 (tail.timeVectorHomeomorph t.1) k| < R
      rw [ih, Set.mem_Ioo, ←abs_lt]
      constructor
      · rintro ⟨h₁, h₂⟩ k
        refine Fin.cases ?_ (fun j => ?_) k
        · simpa only [Fin.cons_zero] using h₂
        · simpa only [Fin.cons_succ] using h₁ j
      · intro h
        exact ⟨fun j => by simpa only [Fin.cons_succ] using h j.succ,
          by simpa only [Fin.cons_zero] using h 0⟩

lemma timeVectorHomeomorph_dilation (c : EliminationChain P D) (ell : Fin n → ℝ)
    (r : ℝ) (t : c.Time) (k : Fin c.roots.length) :
    c.timeVectorHomeomorph (c.rootDilation ell r t) k =
      Real.exp ((ell (c.roots.get k).1 - ell (c.roots.get k).2) * r) *
        c.timeVectorHomeomorph t k := by
  induction c with
  | done => exact Fin.elim0 k
  | step a b hab hP hb tail ih =>
      change tail.Time × ℝ at t
      change Fin (tail.roots.length + 1) at k
      change Fin.cons (α := fun _ : Fin (tail.roots.length + 1) => ℝ)
        (Real.exp ((ell a - ell b) * r) * t.2)
          (tail.timeVectorHomeomorph (tail.rootDilation ell r t.1)) k =
        Real.exp ((ell (((a, b) :: tail.roots).get k).1 -
          ell (((a, b) :: tail.roots).get k).2) * r) *
            Fin.cons (α := fun _ : Fin (tail.roots.length + 1) => ℝ)
              t.2 (tail.timeVectorHomeomorph t.1) k
      refine Fin.cases ?_ (fun j => ?_) k
      · rfl
      · exact ih t.1 j

end EliminationChain

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RemainingProductMass
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mass of actual remaining-root cubes under the intrinsic product -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

lemma remainingEuclideanCoordinates_cube (c : EliminationChain P D)
    (hfinal : c.finalEntries = allPositiveRoots n) (R : ℝ) (t : c.Time) :
    t ∈ c.cube R ↔ ∀ p, |c.remainingEuclideanCoordinates hfinal t p| < R := by
  rw [c.timeVectorHomeomorph_cube]
  change (∀ k, |c.timeVectorHomeomorph t k| < R) ↔
    ∀ p, |c.timeVectorHomeomorph t ((c.remainingIndexEquiv hfinal).symm p)| < R
  constructor
  · exact fun h p => h _
  · intro h k
    simpa only [Equiv.symm_apply_apply] using h (c.remainingIndexEquiv hfinal k)

end EliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NormalizedPiMeasures
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalization of finite products on rectangles -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable {ι : Type*} [Fintype ι] {A : ι → Type*}
  [∀ i, MeasurableSpace (A i)]

lemma pi_smul_measures (ν : (i : ι) → Measure (A i)) [∀ i, SigmaFinite (ν i)]
    (c : ι → ℝ≥0∞) [∀ i, SigmaFinite (c i • ν i)] :
    Measure.pi (fun i => c i • ν i) = (∏ i, c i) • Measure.pi ν := by
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_pi, Finset.prod_mul_distrib]

lemma sigmaFinite_anchorNormalize {B : Type*} [MeasurableSpace B]
    (ν : Measure B) [SigmaFinite ν] (V : Set B) (hV : ν V ≠ 0) :
    SigmaFinite (anchorNormalize ν V) := by
  have h : (((ν V)⁻¹).toNNReal : ℝ≥0∞) = (ν V)⁻¹ :=
    ENNReal.coe_toNNReal (ENNReal.inv_ne_top.mpr hV)
  unfold anchorNormalize
  rw [←h, Measure.coe_nnreal_smul]
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem pi_anchorNormalize (ν : (i : ι) → Measure (A i)) [∀ i, SigmaFinite (ν i)]
    (V : (i : ι) → Set (A i)) (h0 : ∀ i, ν i (V i) ≠ 0) :
    Measure.pi (fun i => anchorNormalize (ν i) (V i)) =
      anchorNormalize (Measure.pi ν) (Set.univ.pi V) := by
  let : ∀ i, SigmaFinite ((ν i (V i))⁻¹ • ν i) :=
    fun i => sigmaFinite_anchorNormalize (ν i) (V i) (h0 i)
  unfold anchorNormalize
  rw [pi_smul_measures, Measure.pi_pi,
    ENNReal.prod_inv_distrib (fun i _ _ _ _ => Or.inl (h0 i))]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootProductCovariance
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Diagonal covariance of the actual product of root leaves

The normalization is on the unit rectangle. No independence or
conditional-entropy identification is assumed in this calculation.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

private lemma locallyFinite_map_real (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (E : ℝ ≃ₜ ℝ) : IsLocallyFiniteMeasure (ν.map E) := by
  constructor
  intro x
  obtain ⟨U, hx, hU, hfin⟩ := Measure.exists_isOpen_measure_lt_top ν (E.symm x)
  refine ⟨E '' U, (E.isOpenMap _ hU).mem_nhds ⟨E.symm x, hx, E.apply_symm_apply x⟩, ?_⟩
  rw [Measure.map_apply E.measurable (E.isOpenMap _ hU).measurableSet,
    E.injective.preimage_image]
  exact hfin

theorem ae_rootProduct_diagonal {ι : Type*} [Fintype ι]
    (d : ℕ) (i j : ι → Fin (d+1)) (hij : ∀ a, i a ≠ j a)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k = 0) (t : ℝ) :
    ∀ᵐ x ∂μ,
      (Measure.pi fun a => intrinsicRootLeaf (hij a) μ
        (rightAction x (diagonalOneParameter ell hell t))) =
      anchorNormalize
        ((Measure.pi fun a => intrinsicRootLeaf (hij a) μ x).map
          (fun v a => rootTimeScaling ell (i a) (j a) t (v a)))
        (Set.univ.pi fun _ : ι => Metric.ball 0 1) := by
  have hfree (a : ι) : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection (hij a) v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun _ hx => hx (i a) (j a) (hij a)
  have hinv : μ.map (fun x => rightAction x (diagonalOneParameter ell hell t)) = μ := by
    rw [diagonalOneParameter_eq_diagonalFlow ell hell t]
    exact hA _
  have hcov := ae_all_iff.mpr (fun a =>
    ae_intrinsicRootLeaf_diagonal (hij a) ell hell t μ (hfree a) hinv)
  have hspec := ae_all_iff.mpr (fun a => ae_intrinsicRootLeaf_spec (hij a) μ (hfree a))
  have hpos := ae_all_iff.mpr (fun a => ae_intrinsicRootLeaf_ball_pos (hij a) μ (hfree a))
  filter_upwards [hcov, hspec, hpos] with x hx hs hp
  let ν : ι → Measure ℝ := fun a => intrinsicRootLeaf (hij a) μ x
  let F (a : ι) := rootTimeScaling ell (i a) (j a) t
  let : ∀ a, IsLocallyFiniteMeasure (ν a) := fun a => (hs a).1
  let : ∀ a, IsLocallyFiniteMeasure ((ν a).map (F a)) :=
    fun a => locallyFinite_map_real (ν a) (F a)
  have hmass (a : ι) : (ν a).map (F a) (Metric.ball 0 1) ≠ 0 := by
    rw [Measure.map_apply (F a).measurable isOpen_ball.measurableSet]
    change ν a ((Homeomorph.mulLeft₀ _ _) ⁻¹' Metric.ball 0 1) ≠ 0
    rw [realScaling_preimage_ball _ _ (Real.exp_pos _)]
    exact (hp a _ (by positivity)).ne'
  calc
    _ = Measure.pi (fun a => anchorNormalize ((ν a).map (F a)) (Metric.ball 0 1)) := by
      congr 1
      funext a
      exact hx a
    _ = anchorNormalize (Measure.pi fun a => (ν a).map (F a))
        (Set.univ.pi fun _ : ι => Metric.ball 0 1) :=
      pi_anchorNormalize _ _ hmass
    _ = _ := by
      rw [Measure.pi_map_pi (fun a => (F a).measurable.aemeasurable)]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RemainingProductDiagonal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Diagonal covariance in actual remaining-root time coordinates -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

lemma remainingEuclideanCoordinates_dilation (c : EliminationChain P D)
    (hf : c.finalEntries = allPositiveRoots n) (ell : Fin n → ℝ) (r : ℝ)
    (u : c.Time) (p : ↥(allPositiveRoots n \ P)) :
    c.remainingEuclideanCoordinates hf (c.rootDilation ell r u) p =
      Real.exp ((ell p.val.1 - ell p.val.2) * r) *
        c.remainingEuclideanCoordinates hf u p := by
  have h := c.timeVectorHomeomorph_dilation ell r u ((c.remainingIndexEquiv hf).symm p)
  have he : c.roots.get ((c.remainingIndexEquiv hf).symm p) = p.val :=
    congrArg Subtype.val ((c.remainingIndexEquiv hf).apply_symm_apply p)
  change c.timeVectorHomeomorph (c.rootDilation ell r u) ((c.remainingIndexEquiv hf).symm p) =
    Real.exp ((ell p.val.1 - ell p.val.2) * r) *
      c.timeVectorHomeomorph u ((c.remainingIndexEquiv hf).symm p)
  simpa only [he] using h

lemma remainingTimeProduct_eq_map (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots n)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (x : X n) :
    c.remainingTimeProduct hP hf μ x =
      (Measure.pi fun p : ↥(allPositiveRoots n \ P) =>
        intrinsicRootLeaf (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) μ x).map
          (c.remainingEuclideanCoordinates hf).symm := by
  unfold remainingTimeProduct remainingIntrinsicProduct
  rw [Measure.map_map (c.remainingWordHomeomorph hP hf).symm.measurable
    (c.remainingGroupCoordinates hP hf).symm.measurable]
  congr 1
  funext v
  simp [remainingGroupCoordinates]

lemma remainingCoordinates_unit_cube (c : EliminationChain P D)
    (hf : c.finalEntries = allPositiveRoots n) :
    (c.remainingEuclideanCoordinates hf).symm ''
      (Set.univ.pi fun _ : ↥(allPositiveRoots n \ P) => Metric.ball 0 1) = c.cube 1 := by
  let E := c.remainingEuclideanCoordinates hf
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    apply (c.remainingEuclideanCoordinates_cube hf 1 _).mpr
    intro p
    have hp := hv p (mem_univ p)
    change |E (E.symm v) p| < 1
    rw [E.apply_symm_apply]
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hp
  · intro hu
    refine ⟨E u, ?_, E.symm_apply_apply u⟩
    intro p _
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using
      (c.remainingEuclideanCoordinates_cube hf 1 u).mp hu p

theorem ae_remainingTimeProduct_diagonal (d : ℕ)
    {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k = 0) (t : ℝ) :
    ∀ᵐ x ∂μ,
      c.remainingTimeProduct hP hf μ (rightAction x (diagonalOneParameter ell hell t)) =
        anchorNormalize ((c.remainingTimeProduct hP hf μ x).map (c.rootDilation ell (-t)))
          (c.cube 1) := by
  let I := ↥(allPositiveRoots (d+1) \ P)
  let E := c.remainingEuclideanCoordinates hf
  let S : (I → ℝ) → (I → ℝ) := fun v p => rootTimeScaling ell p.val.1 p.val.2 t (v p)
  let ν := fun x => Measure.pi fun p : I =>
    intrinsicRootLeaf (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) μ x
  let R : Set (I → ℝ) := Set.univ.pi fun _ : I => Metric.ball 0 1
  have hcov := ae_rootProduct_diagonal d (fun p : I => p.val.1) (fun p : I => p.val.2)
    (fun p => ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2)
    μ hA ell hell t
  filter_upwards [hcov] with x hx
  change ν (rightAction x (diagonalOneParameter ell hell t)) =
    anchorNormalize ((ν x).map S) R at hx
  have hS : Measurable S := measurable_pi_iff.mpr fun p =>
    (rootTimeScaling ell p.val.1 p.val.2 t).measurable.comp (measurable_pi_apply p)
  have he : E.symm ∘ S = c.rootDilation ell (-t) ∘ E.symm := by
    funext v
    apply E.injective
    change E (E.symm (S v)) = E (c.rootDilation ell (-t) (E.symm v))
    rw [E.apply_symm_apply]
    funext p
    rw [c.remainingEuclideanCoordinates_dilation hf]
    change Real.exp ((ell p.val.2 - ell p.val.1) * t) * v p =
      Real.exp ((ell p.val.1 - ell p.val.2) * (-t)) * E (E.symm v) p
    rw [E.apply_symm_apply]
    congr 2
    ring
  rw [c.remainingTimeProduct_eq_map hP hf, c.remainingTimeProduct_eq_map hP hf]
  change (ν (rightAction x (diagonalOneParameter ell hell t))).map E.symm =
    anchorNormalize (((ν x).map E.symm).map (c.rootDilation ell (-t))) (c.cube 1)
  have hnorm : (anchorNormalize ((ν x).map S) R).map E.symm =
      anchorNormalize (((ν x).map S).map E.symm) (E.symm '' R) := by
    simpa only [Homeomorph.toMeasurableEquiv_coe] using
      (anchorNormalize_map_equiv ((ν x).map S) E.symm.toMeasurableEquiv R).symm
  rw [hx, hnorm, c.remainingCoordinates_unit_cube hf]
  congr 1
  rw [Measure.map_map E.symm.measurable hS,
    Measure.map_map (c.rootDilation ell (-t)).measurable E.symm.measurable, he]

end EliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RemainingFutureShift
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact shift of future atoms along remaining-root leaves -/

noncomputable section
open Set
open MeasureTheory
namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

lemma measurableSet_remainingFutureAtom (c : EliminationChain P D)
    (hf : c.finalEntries = allPositiveRoots n)
    (ell : Fin n → ℝ) (hell : ∑ k, ell k = 0) (Q : X n → ℕ)
    (hQ : Measurable Q) (m : ℕ) (x : X n) :
    MeasurableSet (c.remainingFutureAtom ell hell Q m x) := by
  let T : X n → X n := fun z => rightAction z (diagonalOneParameter ell hell (-1))
  have hT : Measurable T := (continuous_rightAction _).measurable
  have hF : Measurable (fun u => rightAction x (c.word u)) :=
    ((continuous_rightAction_uncurry n).comp
      (continuous_const.prodMk (c.word_isEmbedding_remaining hf).continuous)).measurable
  change MeasurableSet {u | ∀ k : ℕ, Q (T^[k+m] (rightAction x (c.word u))) = _}
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  exact (hQ.comp ((hT.iterate (k+m)).comp hF)) (measurableSet_singleton _)

lemma remaining_orbit_diagonal (c : EliminationChain P D)
    (ell : Fin n → ℝ) (hell : ∑ k, ell k = 0) (x : X n) (u : c.Time) :
    rightAction (rightAction x (diagonalOneParameter ell hell (-1)))
        (c.word (c.rootDilation ell 1 u)) =
      rightAction (rightAction x (c.word u)) (diagonalOneParameter ell hell (-1)) := by
  rw [rightAction_mul, rightAction_mul, c.word_rootDilation ell hell 1,
    diagonalOneParameter_neg]
  congr 1
  group

end EliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_DiagonalRootTubes
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite diagonal orbit tubes in a remaining root group

These are actual conjugation tubes, not assumed entropy partitions.
Their information is computed exactly; the passage from these tubes to
metric entropy is a separate step.
-/

noncomputable section
open Matrix MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace DukePrimeDegree
open PrimeDegreePackets

lemma exp_scaled_abs_lt_iff (a ρ x : ℝ) :
    |Real.exp a * x| < Real.exp (-ρ) ↔ |x| < Real.exp (-(ρ+a)) := by
  rw [abs_mul, abs_of_pos (Real.exp_pos a), mul_comm (Real.exp a),
    ←lt_div_iff₀ (Real.exp_pos a), ←Real.exp_sub,
    show -ρ-a = -(ρ+a) by ring]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RemainingExpansionInformation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The mean normalization in the actual remaining-root covariance -/

noncomputable section
open MeasureTheory Set
open scoped Topology ENNReal BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain

variable {d : ℕ} {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}

lemma remainingDilationCube_preimage (c : EliminationChain P D)
    (hf : c.finalEntries = allPositiveRoots (d+1)) (ell : Fin (d+1) → ℝ) :
    (c.remainingEuclideanCoordinates hf).symm ⁻¹'
        ((c.rootDilation ell 1) ⁻¹' c.cube 1) =
      Set.univ.pi (fun p : ↥(allPositiveRoots (d+1) \ P) =>
        Metric.ball 0 (Real.exp (-(ell p.val.1-ell p.val.2)))) := by
  ext v
  simp only [Set.mem_preimage, c.remainingEuclideanCoordinates_cube hf,
    Set.mem_pi, Set.mem_univ, forall_const, Metric.mem_ball, Real.dist_eq, sub_zero]
  apply forall_congr'
  intro p
  rw [c.remainingEuclideanCoordinates_dilation hf]
  simp only [Homeomorph.apply_symm_apply, mul_one]
  simpa only [neg_zero, Real.exp_zero, zero_add] using
    exp_scaled_abs_lt_iff (ell p.val.1-ell p.val.2) 0 (v p)

/-- Every expanding normalization rectangle has positive finite mass. -/
theorem ae_remainingExpansionMass_pos_ne_top (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots (d+1))
    (ell : Fin (d+1) → ℝ) (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ,
      0 < c.remainingTimeProduct hP hf μ x ((c.rootDilation ell 1) ⁻¹' c.cube 1) ∧
      c.remainingTimeProduct hP hf μ x ((c.rootDilation ell 1) ⁻¹' c.cube 1) ≠ ∞ := by
  let I := ↥(allPositiveRoots (d+1) \ P)
  let hij (p : I) := ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2
  have hfree (p : I) : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection (hij p) v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun _ hx => hx _ _ _
  have hs := ae_all_iff.mpr (fun p : I => ae_intrinsicRootLeaf_spec (hij p) μ (hfree p))
  have hp := ae_all_iff.mpr (fun p : I => ae_intrinsicRootLeaf_ball_pos (hij p) μ (hfree p))
  filter_upwards [hs, hp] with x hxs hxp
  let : ∀ p : I, IsLocallyFiniteMeasure (intrinsicRootLeaf (hij p) μ x) :=
    fun p => (hxs p).1
  rw [c.remainingTimeProduct_eq_map hP hf μ x,
    Measure.map_apply (c.remainingEuclideanCoordinates hf).symm.measurable
      ((c.cube_open 1).preimage (c.rootDilation ell 1).continuous).measurableSet,
    c.remainingDilationCube_preimage hf, Measure.pi_pi]
  constructor
  · exact pos_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr
      (fun p _ => (hxp p _ (Real.exp_pos _)).ne'))
  · exact ENNReal.prod_ne_top (fun p _ => measure_ball_lt_top.ne)

end EliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_FutureBlockInformation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Iterated whole-future masses

The same normalization factor occurs for every future index. In
particular every later whole-future atom has positive finite mass once
the zero-future atom does, despite the nonintegrable possible height.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain

lemma remainingFutureAtom_shift_index
    {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    (c : EliminationChain P D) (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (m : ℕ) (x : X n) :
    (c.rootDilation ell 1) ⁻¹' c.remainingFutureAtom ell hell Q m
      (rightAction x (diagonalOneParameter ell hell (-1))) =
      c.remainingFutureAtom ell hell Q (m+1) x := by
  ext u
  simp only [mem_preimage,remainingFutureAtom,Set.mem_ofPred_eq,
    c.remaining_orbit_diagonal ell hell]
  simp only [←Nat.add_assoc,Function.iterate_succ_apply]

theorem ae_remainingTimeProduct_futureAtom_index
    (d : ℕ) {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries=allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q) (m : ℕ) :
    ∀ᵐ x ∂μ,
      c.remainingTimeProduct hP hf μ (rightAction x (diagonalOneParameter ell hell (-1)))
        (c.remainingFutureAtom ell hell Q m
          (rightAction x (diagonalOneParameter ell hell (-1)))) =
      (c.remainingTimeProduct hP hf μ x ((c.rootDilation ell 1) ⁻¹' c.cube 1))⁻¹ *
        c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q (m+1) x) := by
  filter_upwards [c.ae_remainingTimeProduct_diagonal d hP hf μ hA ell hell (-1)] with x hx
  rw [hx]
  simp only [neg_neg]
  rw [anchorNormalize,Measure.smul_apply,smul_eq_mul,
    Measure.map_apply (c.rootDilation ell 1).measurable
      (c.measurableSet_remainingFutureAtom hf ell hell Q hQ m _),
    c.remainingFutureAtom_shift_index ell hell Q m x,
    Measure.map_apply (c.rootDilation ell 1).measurable (c.cube_open 1).measurableSet]

theorem ae_all_futureMass_pos_ne_top
    (d : ℕ) {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries=allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (hmass : ∀ᵐ x ∂μ,
      0 < c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ∧
      c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ≤ 1) :
    ∀ᵐ x ∂μ, ∀ m : ℕ,
      0 < c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q m x) ∧
      c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q m x) ≠ ∞ := by
  let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  let M := fun m x => c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q m x)
  let C := fun x => c.remainingTimeProduct hP hf μ x ((c.rootDilation ell 1) ⁻¹' c.cube 1)
  have hT : MeasurePreserving T μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    dsimp only [T]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  have hC := c.ae_remainingExpansionMass_pos_ne_top hP hf ell μ hA
  apply ae_all_iff.mpr
  intro m
  induction m with
  | zero =>
    filter_upwards [hmass] with x hx
    exact ⟨hx.1,ne_of_lt (hx.2.trans_lt ENNReal.one_lt_top)⟩
  | succ m ih =>
    filter_upwards [hT.quasiMeasurePreserving.ae ih,hC,
      c.ae_remainingTimeProduct_futureAtom_index d hP hf μ hA ell hell Q hQ m]
      with x hx hc hcov
    have he : M (m+1) x=C x*M m (T x) := by
      change M m (T x)=(C x)⁻¹*M (m+1) x at hcov
      rw [hcov,←mul_assoc,ENNReal.mul_inv_cancel hc.1.ne' hc.2,one_mul]
    change 0 < M (m+1) x ∧ M (m+1) x ≠ ∞
    rw [he]
    exact ⟨ENNReal.mul_pos hc.1.ne' hx.1.ne',ENNReal.mul_ne_top hc.2 hx.2⟩

end EliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NormalizedRestrictionLimit
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Entropy limits for decreasing positive-mass conditioning cells -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

lemma normalized_restriction_real {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) (A B : Set Y) (hB : MeasurableSet B) :
    ((anchorNormalize ν A).restrict A).real B = ν.real (B ∩ A) / ν.real A := by
  rw [measureReal_def,Measure.restrict_apply hB,anchorNormalize,Measure.smul_apply]
  simp only [smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_inv,measureReal_def,
    div_eq_mul_inv,mul_comm]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_StationaryRestrictions
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gluing stationary restrictions over a countable cover

For a Markov kernel, stationary restrictions of one finite measure are
closed under intersections and unions. Thus local stationarity on a
countable almost-everywhere cover implies global stationarity.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DukePrimeDegree

variable {Y : Type*} [MeasurableSpace Y]

theorem bind_kernel_real (κ : Kernel Y Y) [IsMarkovKernel κ]
    (μ : Measure Y) (A : Set Y) (hA : MeasurableSet A) :
    (μ.bind κ).real A = ∫ y, (κ y).real A ∂μ := by
  rw [Measure.real, Measure.bind_apply hA κ.measurable.aemeasurable]
  exact (integral_toReal (κ.measurable_coe hA).aemeasurable
    (Filter.Eventually.of_forall fun y => measure_lt_top (κ y) A)).symm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_SelfConditionalKernel
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional distributions from a stationary fiber kernel

A stationary kernel which is constant almost everywhere on each of its
own probability fibers is the conditional distribution for the sigma
algebra generated by that kernel. This is the precise extra condition
needed beyond stationarity in the whole-future application.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable {Y : Type*} [mY : MeasurableSpace Y]

theorem setIntegral_selfConstant_kernel
    (μ : Measure Y) [IsFiniteMeasure μ]
    (κ : Kernel Y Y) [IsMarkovKernel κ]
    (hstat : μ.bind κ = μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y = κ x)
    {S : Set Y} (hS : MeasurableSet[MeasurableSpace.comap κ inferInstance] S)
    {A : Set Y} (hA : MeasurableSet A) :
    (∫ x in S, (κ x).real A ∂μ) = μ.real (A ∩ S) := by
  have hSm : MeasurableSet S := κ.measurable.comap_le S hS
  obtain ⟨B,hB,rfl⟩ := hS
  have he : ∀ᵐ x ∂μ,
      (κ x).real (A ∩ (κ ⁻¹' B)) =
        (κ ⁻¹' B).indicator (fun x => (κ x).real A) x := by
    filter_upwards [hself] with x hx
    by_cases hb : κ x ∈ B
    · rw [Set.indicator_of_mem (show x ∈ κ ⁻¹' B from hb)]
      apply congrArg ENNReal.toReal
      apply measure_congr
      filter_upwards [hx] with y hy
      show (_ ∈ (_ : Set _)) = (_ ∈ (_ : Set _))
      simp only [Set.mem_setOf_eq,mem_inter_iff,mem_preimage,hy,hb,and_true]
    · rw [Set.indicator_of_notMem (show x ∉ κ ⁻¹' B from hb)]
      have hz : (κ x) (A ∩ (κ ⁻¹' B)) = 0 := by
        rw [←measure_empty (μ := κ x)]
        apply measure_congr
        filter_upwards [hx] with y hy
        show (y ∈ (A ∩ κ ⁻¹' B : Set Y)) = (y ∈ (∅ : Set Y))
        simp only [Set.mem_setOf_eq,mem_inter_iff,mem_preimage,hy,hb,and_false,mem_empty_iff_false]
      rw [Measure.real,hz,ENNReal.toReal_zero]
  calc
    _ = ∫ x, (κ ⁻¹' B).indicator (fun x => (κ x).real A) x ∂μ :=
      (integral_indicator hSm).symm
    _ = ∫ x, (κ x).real (A ∩ (κ ⁻¹' B)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [he] with x hx
      exact hx.symm
    _ = (μ.bind κ).real (A ∩ (κ ⁻¹' B)) :=
      (bind_kernel_real κ μ _ (hA.inter hSm)).symm
    _ = _ := by rw [hstat]

/-- The kernel evaluations are actual conditional probabilities. -/
theorem selfConstant_kernel_ae_eq_condExp
    (μ : Measure Y) [IsFiniteMeasure μ]
    (κ : Kernel Y Y) [IsMarkovKernel κ]
    (hstat : μ.bind κ = μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y = κ x)
    {A : Set Y} (hA : MeasurableSet A) :
    (fun x => (κ x).real A) =ᵐ[μ]
      μ[A.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap κ inferInstance] := by
  have hm : MeasurableSpace.comap (fun x => κ x)
      (inferInstance : MeasurableSpace (Measure Y)) ≤ mY := κ.measurable.comap_le
  apply ae_eq_condExp_of_forall_setIntegral_eq (μ := μ) hm
    ((integrable_const (μ := μ) (1 : ℝ)).indicator hA)
  · exact fun _ _ _ => (integrable_kernel_real μ κ hA).integrableOn
  · intro S hS _
    rw [setIntegral_selfConstant_kernel μ κ hstat hself hS hA,
      integral_indicator_const (1 : ℝ) hA]
    simp only [smul_eq_mul,mul_one,Measure.real,Measure.restrict_apply hA]
  · have h : @Measurable Y ℝ (MeasurableSpace.comap κ inferInstance)
        inferInstance (fun x => (κ x).real A) :=
      (Measure.measurable_coe hA).ennreal_toReal.comp (comap_measurable κ)
    exact h.stronglyMeasurable.aestronglyMeasurable

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_FutureBlockConditionalInformation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Information of finite words against delayed future kernels -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain

lemma remainingFutureAtom_word_inter
    {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    (c : EliminationChain P D) (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (N : ℕ) (x : X n) :
    let T := fun y => rightAction y (diagonalOneParameter ell hell (-1))
    {u | orbitName T Q N (rightAction x (c.word u))=orbitName T Q N x} ∩
      c.remainingFutureAtom ell hell Q N x = c.remainingFutureAtom ell hell Q 0 x := by
  let T := fun y => rightAction y (diagonalOneParameter ell hell (-1))
  ext u
  constructor
  · rintro ⟨hword,hfuture⟩ k
    by_cases hk : k<N
    · exact congrFun hword ⟨k,hk⟩
    · have hkN : N≤k := Nat.le_of_not_gt hk
      have h := hfuture (k-N)
      simpa only [Nat.sub_add_cancel hkN,Nat.add_zero] using h
  · intro h
    refine ⟨?_,?_⟩
    · funext k
      exact h k.val
    · intro k
      exact h (k+N)

theorem futureBlock_conditionalProbability
    (d : ℕ) {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries=allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (κ : Kernel (X (d+1)) (X (d+1))) [IsMarkovKernel κ]
    (hstat : μ.bind κ=μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x)
    (N : ℕ)
    (hversion : ∀ᵐ x ∂μ, κ x=c.ambientFutureMeasure hP hf μ ell hell Q N x) :
    let T := fun y => rightAction y (diagonalOneParameter ell hell (-1))
    (fun x => (μ[({y | orbitName T Q N y=orbitName T Q N x}.indicator
      (fun _ => (1 : ℝ))) | MeasurableSpace.comap κ inferInstance]) x) =ᵐ[μ]
      fun x => (c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) /
          c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q N x)).toReal := by
  let T := fun y => rightAction y (diagonalOneParameter ell hell (-1))
  have hT : Measurable T := (continuous_rightAction _).measurable
  have hword := orbitName_measurable_fiber hT (fun a => hQ (measurableSet_singleton a)) N
  have H := ae_all_iff.mpr (fun a =>
    selfConstant_kernel_ae_eq_condExp μ κ hstat hself (hword a))
  filter_upwards [H,hversion] with x hx hv
  rw [←hx (orbitName T Q N x),hv]
  have hF : Measurable (fun u => rightAction x (c.word u)) :=
    ((continuous_rightAction_uncurry (d+1)).comp
      (continuous_const.prodMk (c.word_isEmbedding_remaining hf).continuous)).measurable
  have hA : MeasurableSet {y | orbitName T Q N y=orbitName T Q N x} := hword _
  rw [ambientFutureMeasure,Measure.real,Measure.map_apply hF hA]
  change ((anchorNormalize (c.remainingTimeProduct hP hf μ x)
      (c.remainingFutureAtom ell hell Q N x)).restrict
      (c.remainingFutureAtom ell hell Q N x)).real
      {u | orbitName T Q N (rightAction x (c.word u))=orbitName T Q N x} = _
  rw [normalized_restriction_real _ _
      {u | orbitName T Q N (rightAction x (c.word u))=orbitName T Q N x} (hA.preimage hF),
    c.remainingFutureAtom_word_inter ell hell Q N x,ENNReal.toReal_div]
  rfl

end EliminationChain

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_StationaryFiberConditioning
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditioning a stationary kernel on its actual fiber labels -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable {Y S : Type*} [mY : MeasurableSpace Y] [MeasurableSpace S]

theorem fiberConstant_kernel_ae_eq_condExp
    (μ : Measure Y) [IsFiniteMeasure μ]
    (κ : Kernel Y Y) [IsMarkovKernel κ]
    (F : Y → S) (hF : Measurable F)
    (hκF : @Measurable Y (Measure Y) (MeasurableSpace.comap F inferInstance)
      inferInstance κ)
    (hstat : μ.bind κ=μ)
    (hconst : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, F y=F x)
    {A : Set Y} (hA : MeasurableSet A) :
    (fun x => (κ x).real A) =ᵐ[μ]
      μ[A.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap F inferInstance] := by
  have hm := hF.comap_le
  apply ae_eq_condExp_of_forall_setIntegral_eq (μ := μ) hm
    ((integrable_const (μ := μ) (1 : ℝ)).indicator hA)
  · exact fun _ _ _ => (integrable_kernel_real μ κ hA).integrableOn
  · intro U hU _
    have hUm : MeasurableSet U := hm U hU
    obtain ⟨B,hB,rfl⟩ := hU
    have he : ∀ᵐ x ∂μ, (κ x).real (A ∩ (F ⁻¹' B)) =
        (F ⁻¹' B).indicator (fun x => (κ x).real A) x := by
      filter_upwards [hconst] with x hx
      by_cases hb : F x ∈ B
      · rw [Set.indicator_of_mem (show x ∈ F ⁻¹' B from hb)]
        apply congrArg ENNReal.toReal
        apply measure_congr
        filter_upwards [hx] with y hy
        show (_ ∈ (_ : Set _)) = (_ ∈ (_ : Set _))
        simp only [Set.mem_setOf_eq,mem_inter_iff,mem_preimage,hy,hb,and_true]
      · rw [Set.indicator_of_notMem (show x ∉ F ⁻¹' B from hb)]
        have hz : (κ x) (A ∩ (F ⁻¹' B))=0 := by
          rw [←measure_empty (μ := κ x)]
          apply measure_congr
          filter_upwards [hx] with y hy
          show (y ∈ (A ∩ F ⁻¹' B : Set Y)) = (y ∈ (∅ : Set Y))
          simp only [Set.mem_setOf_eq,mem_inter_iff,mem_preimage,hy,hb,and_false,mem_empty_iff_false]
        rw [Measure.real,hz,ENNReal.toReal_zero]
    calc
      (∫ x in F ⁻¹' B, (κ x).real A ∂μ) =
          ∫ x, (F ⁻¹' B).indicator (fun x => (κ x).real A) x ∂μ :=
        (integral_indicator hUm).symm
      _ = ∫ x, (κ x).real (A ∩ (F ⁻¹' B)) ∂μ :=
        integral_congr_ae (by
          filter_upwards [he] with x hx
          exact hx.symm)
      _ = (μ.bind κ).real (A ∩ (F ⁻¹' B)) :=
        (bind_kernel_real κ μ _ (hA.inter hUm)).symm
      _ = ∫ x in F ⁻¹' B, A.indicator (fun _ => (1 : ℝ)) x ∂μ := by
        rw [hstat,integral_indicator_const (1 : ℝ) hA]
        simp only [smul_eq_mul,mul_one,Measure.real,Measure.restrict_apply hA]
  · exact ((Measure.measurable_coe hA).ennreal_toReal.comp hκF).stronglyMeasurable.aestronglyMeasurable

theorem selfConstant_kernel_with_label_ae_eq_condExp
    (μ : Measure Y) [IsFiniteMeasure μ]
    (κ : Kernel Y Y) [IsMarkovKernel κ]
    (F : Y → S) (hF : Measurable F)
    (hstat : μ.bind κ=μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x)
    (hconst : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, F y=F x)
    {A : Set Y} (hA : MeasurableSet A) :
    (fun x => (κ x).real A) =ᵐ[μ]
      μ[A.indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance] := by
  apply fiberConstant_kernel_ae_eq_condExp μ κ (fun x => (κ x,F x))
    (κ.measurable.prodMk hF) (measurable_fst.comp (comap_measurable _)) hstat
  · filter_upwards [hself,hconst] with x hs hc
    filter_upwards [hs,hc] with y hy hc
    exact Prod.ext hy hc
  · exact hA

theorem selfConstant_kernel_with_label_information
    (μ : Measure Y) [IsFiniteMeasure μ]
    (κ : Kernel Y Y) [IsMarkovKernel κ]
    (F : Y → S) (hF : Measurable F)
    (hstat : μ.bind κ=μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x)
    (hconst : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, F y=F x)
    (Q : Y → ℕ) (hQ : Measurable Q) :
    conditionalInformation μ Q
        (MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance) =ᵐ[μ]
      conditionalInformation μ Q (MeasurableSpace.comap κ inferInstance) := by
  have h (a : ℕ) :=
    (selfConstant_kernel_with_label_ae_eq_condExp μ κ F hF hstat hself hconst
      (hQ (measurableSet_singleton a))).symm.trans
    (selfConstant_kernel_ae_eq_condExp μ κ hstat hself (hQ (measurableSet_singleton a)))
  filter_upwards [ae_all_iff.mpr h] with x hx
  exact congrArg (-Real.log ·) (hx (Q x))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_KernelFutureInformation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual root information is bounded by full metric entropy

The entire future is an almost sure fiber label of the constructed
kernel. Adding that label to the conditioning sigma algebra leaves its
conditional law unchanged, and makes the future inclusion literal.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain

theorem ambientFutureMeasure_ae_same_names
    {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries=allPositiveRoots n)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (ell : Fin n → ℝ) (hell : ∑ k, ell k=0)
    (Q : X n → ℕ) (hQ : Measurable Q) (m : ℕ) (x : X n) :
    ∀ᵐ y ∂c.ambientFutureMeasure hP hf μ ell hell Q m x, ∀ k : ℕ,
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+m] y) =
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+m] x) := by
  have hF : Measurable (fun u => rightAction x (c.word u)) :=
    ((continuous_rightAction_uncurry n).comp
      (continuous_const.prodMk (c.word_isEmbedding_remaining hf).continuous)).measurable
  unfold ambientFutureMeasure
  apply (ae_map_iff hF.aemeasurable ?_).mpr
  · exact ae_restrict_mem (c.measurableSet_remainingFutureAtom hf ell hell Q hQ m x)
  · simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro k
    exact (hQ.comp (((continuous_rightAction _).measurable).iterate (k+m)))
      (measurableSet_singleton _)

theorem wholeFuture_rootSum_le_metricEntropy
    (d : ℕ) {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries=allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (κ : Kernel (X (d+1)) (X (d+1))) [IsMarkovKernel κ]
    (hstat : μ.bind κ=μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x)
    (hversion : ∀ᵐ x ∂μ, κ x=c.ambientFutureMeasure hP hf μ ell hell Q 1 x)
    (hmass : ∀ᵐ x ∂μ,
      0 < c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ∧
      c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ≤ 1) :
    ENNReal.ofReal (∑ p : ↥(allPositiveRoots (d+1) \ P),
      (ell p.val.2-ell p.val.1) * canonicalRootCoefficient d μ p.val.1 p.val.2) ≤
      measureEntropy μ (fun z => rightAction z (diagonalOneParameter ell hell (-1))) := by
  let T := fun z => rightAction z (diagonalOneParameter ell hell (-1))
  let F := entireFutureObservation T Q
  have hT : MeasurePreserving T μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    dsimp [T]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  have hF : Measurable F := entireFutureObservation_measurable hT.measurable hQ
  have hconst : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, F y=F x := by
    filter_upwards [hversion] with x hx
    rw [hx]
    filter_upwards [c.ambientFutureMeasure_ae_same_names hP hf μ ell hell Q hQ 1 x]
      with y hy
    exact funext hy
  have hm : MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance ≤
      (inferInstance : MeasurableSpace (X (d+1))) := (κ.measurable.prodMk hF).comap_le
  have hfuture : (⨆ k : ℕ, observationSigma (fun y => Q (T^[k+1] y))) ≤ MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance := by
    rw [countableFutureSigma_eq_comap]
    exact (measurable_snd.comp (comap_measurable (fun x => (κ x,F x)))).comap_le
  have he := selfConstant_kernel_with_label_information μ κ F hF hstat hself hconst Q hQ
  have HI := c.wholeFuture_conditionalInformation_integrable_integral d hP hf μ hA
    ell hell Q hQ κ hstat hself hversion hmass
  have Hint : Integrable (conditionalInformation μ Q (MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance)) μ := HI.1.congr he.symm
  have hprob (a : ℕ) :=
    (selfConstant_kernel_with_label_ae_eq_condExp μ κ F hF hstat hself hconst
      (hQ (measurableSet_singleton a))).symm.trans
    (selfConstant_kernel_ae_eq_condExp μ κ hstat hself (hQ (measurableSet_singleton a)))
  have hp := c.futureBlock_conditionalProbability d hP hf μ ell hell Q hQ κ
    hstat hself 1 hversion
  have hM := c.ae_all_futureMass_pos_ne_top d hP hf μ hA ell hell Q hQ hmass
  have hpos : ∀ᵐ x ∂μ, 0 < (μ[({z | Q z=Q x}.indicator
      (fun _ => (1 : ℝ))) | MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance]) x := by
    filter_upwards [ae_all_iff.mpr hprob,hp,hM] with x hx hp hM
    have hqx := hx (Q x)
    change (μ[({z | Q z=Q x}.indicator (fun _ => (1 : ℝ))) |
      MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance]) x =
        (μ[({z | Q z=Q x}.indicator (fun _ => (1 : ℝ))) |
          MeasurableSpace.comap κ inferInstance]) x at hqx
    rw [hqx]
    have ha : {y | orbitName T Q 1 y=orbitName T Q 1 x}={y | Q y=Q x} := by
      ext y
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro h
        exact congrFun h 0
      · intro h
        funext i
        have hi : i=0 := Subsingleton.elim _ _
        subst i
        exact h
    change (μ[({y | orbitName T Q 1 y=orbitName T Q 1 x}.indicator
      (fun _ => (1 : ℝ))) | MeasurableSpace.comap κ inferInstance]) x = _ at hp
    rw [ha] at hp
    rw [hp,ENNReal.toReal_div]
    exact div_pos (ENNReal.toReal_pos (hM 0).1.ne' (hM 0).2)
      (ENNReal.toReal_pos (hM 1).1.ne' (hM 1).2)
  have H := conditionalInformation_integral_le_metricEntropy
    (MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance) μ hT Q hQ hm hfuture hpos Hint
  rwa [integral_congr_ae he,HI.2] at H

end EliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RegularRootEntropyLower
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An unconditional lower bound by actual expanding-root information -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

/-- The stationary whole-future kernel is constructed here; its existence,
normalization and disintegration properties are not additional inputs. -/
theorem positive_root_sum_le_diagonal_entropy_oai (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ] :
    ENNReal.ofReal (∑ p : allPositiveRoots (d+1),
      (ell p.val.2-ell p.val.1) * canonicalRootCoefficient d μ p.val.1 p.val.2) ≤
      measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell (-1))) := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  obtain ⟨H,Q,κ,hH,hQ,hκ,_,_,_,_,hstat,hself,hversion,hmass,_⟩ :=
    exists_cover_stationary_wholeFutureKernel d ell hell hgap μ (by norm_num : (0:ℝ)<1)
  let : IsMarkovKernel κ := hκ
  let c := completeRootChain (d+1)
  have hP : InitialRootPattern (∅ : Finset (Fin (d+1) × Fin (d+1))) := by
    intro p hp
    simp at hp
  have hb := c.wholeFuture_rootSum_le_metricEntropy d hP (completeRootChain_final (d+1))
    μ hA ell hell Q hQ κ hstat hself hversion hmass
  let f : Fin (d+1) × Fin (d+1) → ℝ := fun p =>
    (ell p.2-ell p.1) * canonicalRootCoefficient d μ p.1 p.2
  have hs : (∑ p : ↥(allPositiveRoots (d+1) \ ∅), f p) =
      ∑ p : allPositiveRoots (d+1), f p := by
    rw [← Finset.sum_subtype (allPositiveRoots (d+1) \ ∅) (by intro p; rfl) f,
      ← Finset.sum_subtype (allPositiveRoots (d+1)) (by intro p; rfl) f,
      Finset.sdiff_empty]
  change ENNReal.ofReal (∑ p : ↥(allPositiveRoots (d+1) \ ∅), f p) ≤ _ at hb
  rw [hs] at hb
  exact hb

end DukePrimeDegree

end

end OAI
end

theorem solution : type_of% @OAI.DukePrimeDegree.positive_root_sum_le_diagonal_entropy_oai := @OAI.DukePrimeDegree.positive_root_sum_le_diagonal_entropy_oai
