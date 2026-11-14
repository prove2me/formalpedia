-- Prove2me | solution 1 for OAI.DukePrimeDegree.exists_nullset_atomic_root_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:43:52.72491+00:00
-- url     : https://prove2.me/submissions/03da107b-3e74-4c9e-812a-12c1bbf9f40d

import Mathlib
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke044

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
-- module Solutions.OAIQ244_DUKE.PrimePackets_AmbientLeaves
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
namespace PrimeDegreePackets

lemma centerRealMeasure_singleton (ν : Measure ℝ) (t u : ℝ) :
    centerRealMeasure ν t {u} = ν {u+t} := by
  rw [centerRealMeasure,Measure.map_apply (Homeomorph.subRight t).measurable (measurableSet_singleton u)]
  congr 1
  ext v
  simp only [Set.mem_preimage,mem_singleton_iff,Homeomorph.coe_subRight]
  exact sub_eq_iff_eq_add

end PrimeDegreePackets

open scoped Matrix Topology ENNReal ProbabilityTheory
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_HopfMaximal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite maximal ergodic inequality

The maximal recurrence estimate used in EKL (2006), Section 4.3, follows
from this elementary finite Hopf inequality. The running maximum is built
recursively, so its integrability and its coboundary bound require no
pointwise ergodic theorem.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace DukePrimeDegree

lemma positiveRunningSum_nonneg {Y : Type*} (T : Y → Y) (f : Y → ℝ)
    (n : ℕ) (x : Y) : 0 ≤ positiveRunningSum T f n x := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_left _ _

lemma positiveRunningSum_mono {Y : Type*} (T : Y → Y) (f : Y → ℝ)
    (x : Y) : Monotone (fun n => positiveRunningSum T f n x) := by
  suffices h : ∀ n x, positiveRunningSum T f n x ≤ positiveRunningSum T f (n + 1) x
    from monotone_nat_of_le_succ (fun n => h n x)
  intro n
  induction n with
  | zero => exact fun x => positiveRunningSum_nonneg T f 1 x
  | succ n ih =>
    intro x
    exact max_le_max le_rfl (add_le_add le_rfl (ih (T x)))

lemma birkhoffSum_le_positiveRunningSum {Y : Type*} (T : Y → Y) (f : Y → ℝ)
    (n : ℕ) (x : Y) : birkhoffSum T f n x ≤ positiveRunningSum T f n x := by
  induction n generalizing x with
  | zero => simp [positiveRunningSum]
  | succ n ih =>
    rw [birkhoffSum_succ']
    exact (add_le_add le_rfl (ih (T x))).trans (le_max_right _ _)

lemma measurable_positiveRunningSum {Y : Type*} [MeasurableSpace Y]
    {T : Y → Y} {f : Y → ℝ} (hT : Measurable T) (hf : Measurable f) (n : ℕ) :
    Measurable (positiveRunningSum T f n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact measurable_const.max (hf.add (ih.comp hT))

lemma integrable_positiveRunningSum {Y : Type*} [MeasurableSpace Y]
    {μ : Measure Y} {T : Y → Y} {f : Y → ℝ}
    (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (n : ℕ) :
    Integrable (positiveRunningSum T f n) μ := by
  induction n with
  | zero => exact integrable_zero _ _ _
  | succ n ih =>
    exact (integrable_zero _ _ _).sup (hf.add (hT.integrable_comp_of_integrable ih))

/-- A finite running maximum has nonnegative signed mass on its positive set. -/
theorem finite_hopf_maximal {Y : Type*} [MeasurableSpace Y]
    {μ : Measure Y} {T : Y → Y} {f : Y → ℝ}
    (hT : MeasurePreserving T μ μ) (hf : Integrable f μ)
    (hfmeas : Measurable f) (n : ℕ) :
    0 ≤ ∫ x in {x | 0 < positiveRunningSum T f n x}, f x ∂μ := by
  let m := positiveRunningSum T f n
  let E := {x | 0 < m x}
  have hm : Integrable m μ := integrable_positiveRunningSum hT hf n
  have hmmeas : Measurable m := measurable_positiveRunningSum hT.measurable hfmeas n
  have hE : MeasurableSet E := measurableSet_lt measurable_const hmmeas
  have hpoint (x : Y) : m x - m (T x) ≤ E.indicator f x := by
    by_cases hx : x ∈ E
    · rw [indicator_of_mem hx]
      have hle := positiveRunningSum_mono T f x (Nat.le_succ n)
      change m x ≤ max 0 (f x + m (T x)) at hle
      have hpos : 0 < m x := hx
      have hle' := (le_max_iff.mp hle).resolve_left (not_le_of_gt hpos)
      linarith
    · rw [indicator_of_notMem hx]
      have hz : m x = 0 := le_antisymm (le_of_not_gt hx)
        (positiveRunningSum_nonneg T f n x)
      rw [hz]
      linarith [positiveRunningSum_nonneg T f n (T x)]
  have hcomp : ∫ x, m (T x) ∂μ = ∫ x, m x ∂μ := by
    have hmap : AEStronglyMeasurable m (μ.map T) := by
      simpa only [hT.map_eq] using hm.aestronglyMeasurable
    exact (integral_map hT.measurable.aemeasurable hmap).symm.trans
      (by rw [hT.map_eq])
  have hle := integral_mono (hm.sub (hT.integrable_comp_of_integrable hm))
    (hf.indicator hE) hpoint
  simp only [Pi.sub_apply, Function.comp_apply] at hle
  have hmt : Integrable (fun x => m (T x)) μ := hT.integrable_comp_of_integrable hm
  rw [integral_sub hm hmt, hcomp, sub_self,
    integral_indicator hE] at hle
  exact hle

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_DiscreteMaximal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform discrete orbit averages

The finite Hopf inequality bounds the union over all averaging lengths.
The resulting measurable good set controls every positive integer time,
as needed before passing to the continuous diagonal flow.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace DukePrimeDegree

theorem positiveRunningSum_measure_bound
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    {g : Y → ℝ} (hg : Integrable g μ) (hgmeas : Measurable g)
    (hgnonneg : ∀ x, 0 ≤ g x) (c : ℝ) (hc : 0 < c) :
    μ (⋃ n : ℕ, {x | 0 < positiveRunningSum T (fun y => g y - c) n x}) ≤
      ENNReal.ofReal ((∫ x, g x ∂μ) / c) := by
  let f : Y → ℝ := fun x => g x - c
  let E : ℕ → Set Y := fun n => {x | 0 < positiveRunningSum T f n x}
  have hf : Integrable f μ := hg.sub (integrable_const c)
  have hfmeas : Measurable f := hgmeas.sub measurable_const
  have hEmeas (n : ℕ) : MeasurableSet (E n) :=
    measurableSet_lt measurable_const (measurable_positiveRunningSum hT.measurable hfmeas n)
  have hEmono : Monotone E := by
    intro a b hab x hx
    exact hx.trans_le (positiveRunningSum_mono T f x hab)
  have hbound (n : ℕ) : μ (E n) ≤ ENNReal.ofReal ((∫ x, g x ∂μ) / c) := by
    have hhopf := finite_hopf_maximal hT hf hfmeas n
    change 0 ≤ ∫ x in E n, g x - c ∂μ at hhopf
    rw [integral_sub hg.restrict (integrable_const c), setIntegral_const, smul_eq_mul] at hhopf
    have hsub : ∫ x in E n, g x ∂μ ≤ ∫ x, g x ∂μ :=
      setIntegral_le_integral hg (Eventually.of_forall hgnonneg)
    apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _)
      (div_nonneg (integral_nonneg hgnonneg) hc.le)).mpr
    apply (le_div_iff₀ hc).mpr
    change μ.real (E n) * c ≤ _
    linarith
  rw [hEmono.measure_iUnion]
  exact iSup_le hbound

/-- The complement of one measurable exceptional set controls all finite
averages, with the sharp Hopf bound on its measure. -/
theorem exists_discrete_average_good_set
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    {g : Y → ℝ} (hg : Integrable g μ) (hgmeas : Measurable g)
    (hgnonneg : ∀ x, 0 ≤ g x) (c : ℝ) (hc : 0 < c) :
    ∃ G : Set Y, MeasurableSet G ∧
      μ Gᶜ ≤ ENNReal.ofReal ((∫ x, g x ∂μ) / c) ∧
      ∀ x ∈ G, ∀ n : ℕ, birkhoffSum T g n x ≤ c * n := by
  let f : Y → ℝ := fun x => g x - c
  let B := ⋃ n : ℕ, {x | 0 < positiveRunningSum T f n x}
  have hfmeas : Measurable f := hgmeas.sub measurable_const
  have hB : MeasurableSet B := MeasurableSet.iUnion fun n =>
    measurableSet_lt measurable_const (measurable_positiveRunningSum hT.measurable hfmeas n)
  refine ⟨Bᶜ, hB.compl, ?_, ?_⟩
  · simpa only [compl_compl] using positiveRunningSum_measure_bound μ hT hg hgmeas hgnonneg c hc
  · intro x hx n
    have hnot : ¬ 0 < positiveRunningSum T f n x := by
      intro h
      exact hx (mem_iUnion.mpr ⟨n, h⟩)
    have hs := (birkhoffSum_le_positiveRunningSum T f n x).trans (le_of_not_gt hnot)
    have heq : birkhoffSum T f n x = birkhoffSum T g n x - (n : ℝ) * c := by
      change (∑ k ∈ Finset.range n, (g (T^[k] x) - c)) = _
      rw [Finset.sum_sub_distrib]
      simp [birkhoffSum]
    rw [heq] at hs
    linarith

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_FlowOccupation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# One-unit occupation observables

For a measurable measure-preserving flow, the time spent in a measurable
set during one unit interval is a measurable integrable observable. Its
space integral is exactly the measure of that set. Its discrete sums
are the occupation integrals on the corresponding integer intervals.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace DukePrimeDegree

lemma integrable_one_indicator_comp
    {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure Z) [IsFiniteMeasure ν] {F : Z → Y} (hF : Measurable F)
    {E : Set Y} (hE : MeasurableSet E) :
    Integrable (fun z => E.indicator (fun _ => (1 : ℝ)) (F z)) ν := by
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_const.indicator hE).comp hF).aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    by_cases hz : F z ∈ E <;> simp [hz]

lemma measurable_unitFlowOccupation
    {Y : Type*} [MeasurableSpace Y] {Φ : ℝ → Y → Y}
    (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    {E : Set Y} (hE : MeasurableSet E) : Measurable (unitFlowOccupation Φ E) := by
  have hχ : Measurable (fun p : Y × ℝ =>
      E.indicator (fun _ => (1 : ℝ)) (Φ p.2 p.1)) :=
    (measurable_const.indicator hE).comp hΦ
  exact hχ.stronglyMeasurable.integral_prod_right'.measurable

lemma unitFlowOccupation_nonneg
    {Y : Type*} (Φ : ℝ → Y → Y) (E : Set Y) (x : Y) :
    0 ≤ unitFlowOccupation Φ E x := by
  apply integral_nonneg
  intro t
  exact indicator_nonneg (fun _ _ => zero_le_one) (Φ t x)

lemma unitFlowOccupation_le_one
    {Y : Type*} [MeasurableSpace Y] {Φ : ℝ → Y → Y}
    (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    {E : Set Y} (hE : MeasurableSet E) (x : Y) : unitFlowOccupation Φ E x ≤ 1 := by
  have hF : Measurable (fun t => Φ t x) := hΦ.comp (measurable_const.prodMk measurable_id)
  have hi := integrable_one_indicator_comp (volume.restrict (Ioc (0 : ℝ) 1)) hF hE
  have h := integral_mono hi (integrable_const (1 : ℝ))
    (fun t => show E.indicator (fun _ => (1 : ℝ)) (Φ t x) ≤ 1 from by
      by_cases ht : Φ t x ∈ E <;> simp [ht])
  simpa [unitFlowOccupation, measureReal_def] using h

lemma integrable_unitFlowOccupation
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    {Φ : ℝ → Y → Y} (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    {E : Set Y} (hE : MeasurableSet E) : Integrable (unitFlowOccupation Φ E) μ := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_unitFlowOccupation hΦ hE).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (unitFlowOccupation_nonneg Φ E x)]
    exact unitFlowOccupation_le_one hΦ hE x

theorem integral_unitFlowOccupation
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    {Φ : ℝ → Y → Y} (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    (hpres : ∀ t, MeasurePreserving (Φ t) μ μ)
    {E : Set Y} (hE : MeasurableSet E) :
    ∫ x, unitFlowOccupation Φ E x ∂μ = μ.real E := by
  have hi := integrable_one_indicator_comp
    (μ.prod (volume.restrict (Ioc (0 : ℝ) 1))) hΦ hE
  change (∫ x, (∫ t in Ioc (0 : ℝ) 1,
    E.indicator (fun _ => (1 : ℝ)) (Φ t x)) ∂μ) = _
  rw [integral_integral_swap hi]
  have heq (t : ℝ) : (∫ x, E.indicator (fun _ => (1 : ℝ)) (Φ t x) ∂μ) = μ.real E := by
    have hm : AEStronglyMeasurable (E.indicator (fun _ => (1 : ℝ))) (μ.map (Φ t)) := by
      rw [(hpres t).map_eq]
      exact (measurable_const.indicator hE).aestronglyMeasurable
    rw [← integral_map (hpres t).measurable.aemeasurable hm, (hpres t).map_eq,
      integral_indicator_const (1 : ℝ) hE]
    simp
  simp_rw [heq]
  simp [measureReal_def]

lemma intervalIntegrable_flow_indicator
    {Y : Type*} [MeasurableSpace Y] {Φ : ℝ → Y → Y}
    (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    {E : Set Y} (hE : MeasurableSet E) (x : Y) (a b : ℝ) :
    IntervalIntegrable (fun t => E.indicator (fun _ => (1 : ℝ)) (Φ t x)) volume a b := by
  let : IsFiniteMeasure (volume.restrict (uIcc a b)) :=
    isFiniteMeasure_restrict.mpr (isCompact_uIcc.measure_lt_top.ne)
  apply (intervalIntegrable_iff').mpr
  exact integrable_one_indicator_comp (volume.restrict (uIcc a b))
    (hΦ.comp (measurable_const.prodMk measurable_id)) hE

lemma flow_nat_iterate {Y : Type*} {Φ : ℝ → Y → Y}
    (hzero : ∀ x, Φ 0 x = x) (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (n : ℕ) (x : Y) : (Φ 1)^[n] x = Φ n x := by
  induction n generalizing x with
  | zero => simpa using (hzero x).symm
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Nat.cast_add, Nat.cast_one,
      add_comm (n : ℝ) 1, hadd]

theorem birkhoffSum_unitFlowOccupation
    {Y : Type*} [MeasurableSpace Y] {Φ : ℝ → Y → Y}
    (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    (hzero : ∀ x, Φ 0 x = x) (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    {E : Set Y} (hE : MeasurableSet E) (n : ℕ) (x : Y) :
    birkhoffSum (Φ 1) (unitFlowOccupation Φ E) n x =
      ∫ t in (0 : ℝ)..(n : ℝ), E.indicator (fun _ => (1 : ℝ)) (Φ t x) := by
  have hterm (k : ℕ) : unitFlowOccupation Φ E ((Φ 1)^[k] x) =
      ∫ t in (k : ℝ)..(k + 1 : ℕ), E.indicator (fun _ => (1 : ℝ)) (Φ t x) := by
    rw [flow_nat_iterate hzero hadd]
    change (∫ t in Ioc (0 : ℝ) 1, E.indicator (fun _ => (1 : ℝ)) (Φ t (Φ k x))) = _
    simp_rw [← hadd]
    rw [← intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
    have hs := intervalIntegral.integral_comp_add_right
      (fun t => E.indicator (fun _ => (1 : ℝ)) (Φ t x)) (a := 0) (b := 1) (k : ℝ)
    simpa [Nat.cast_add, Nat.cast_one, add_comm] using hs
  simp_rw [birkhoffSum, hterm]
  simpa only [Nat.cast_zero] using
    intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ => (k : ℝ))
      (fun k _ => by
        simpa only [Nat.cast_add, Nat.cast_one] using
          intervalIntegrable_flow_indicator hΦ hE x k (k + 1))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_FlowMaximal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Maximal occupation control for long flow intervals

The discrete Hopf inequality, applied to one-unit occupation, controls
every real interval of length at least one. This is sufficient for the
large logarithmic time windows in EKL (2006), Lemmas 4.5 and 4.6.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace DukePrimeDegree

theorem exists_flow_average_good_set
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    {Φ : ℝ → Y → Y} (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    (hzero : ∀ x, Φ 0 x = x) (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hpres : ∀ t, MeasurePreserving (Φ t) μ μ)
    {E : Set Y} (hE : MeasurableSet E) (c : ℝ) (hc : 0 < c) :
    ∃ G : Set Y, MeasurableSet G ∧ μ Gᶜ ≤ ENNReal.ofReal (2 * μ.real E / c) ∧
      ∀ x ∈ G, ∀ T : ℝ, 1 ≤ T →
        (∫ t in (0 : ℝ)..T, E.indicator (fun _ => (1 : ℝ)) (Φ t x)) ≤ c * T := by
  obtain ⟨G, hG, hmass, hgood⟩ := exists_discrete_average_good_set μ (hpres 1)
    (integrable_unitFlowOccupation μ hΦ hE) (measurable_unitFlowOccupation hΦ hE)
    (unitFlowOccupation_nonneg Φ E) (c / 2) (by linarith)
  refine ⟨G, hG, ?_, ?_⟩
  · rw [integral_unitFlowOccupation μ hΦ hpres hE] at hmass
    convert hmass using 2
    all_goals try with_reducible_and_instances rfl
    ring
  · intro x hx T hT
    let n := Nat.ceil T
    have hTn : T ≤ (n : ℝ) := Nat.le_ceil T
    have hn : (n : ℝ) ≤ 2 * T := by
      have hnlt : (n : ℝ) < T + 1 := Nat.ceil_lt_add_one (by linarith)
      linarith
    have hmono := intervalIntegral.integral_mono_interval
      (f := fun t => E.indicator (fun _ => (1 : ℝ)) (Φ t x))
      (le_refl (0 : ℝ)) (by linarith : (0 : ℝ) ≤ T) hTn
      (Eventually.of_forall fun t => indicator_nonneg (fun _ _ => zero_le_one) (Φ t x))
      (intervalIntegrable_flow_indicator hΦ hE x 0 n)
    rw [← birkhoffSum_unitFlowOccupation hΦ hzero hadd hE n x] at hmono
    have hdiscrete := hgood x hx n
    have hfinal : c / 2 * (n : ℝ) ≤ c * T := by nlinarith
    exact hmono.trans (hdiscrete.trans hfinal)

lemma flow_occupation_eq_time_measure
    {Y : Type*} [MeasurableSpace Y] {Φ : ℝ → Y → Y}
    (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    {E : Set Y} (hE : MeasurableSet E) (x : Y) (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, E.indicator (fun _ => (1 : ℝ)) (Φ t x)) =
      volume.real (Ioc 0 T ∩ {t | Φ t x ∈ E}) := by
  let S := {t | Φ t x ∈ E}
  have hS : MeasurableSet S := hE.preimage (hΦ.comp (measurable_const.prodMk measurable_id))
  have heq : (fun t => E.indicator (fun _ => (1 : ℝ)) (Φ t x)) =
      S.indicator (fun _ => (1 : ℝ)) := by
    funext t
    by_cases ht : Φ t x ∈ E <;> simp [S, ht]
  rw [intervalIntegral.integral_of_le hT, heq, integral_indicator_const (1 : ℝ) hS,
    measureReal_restrict_apply hS, inter_comm]
  simp only [smul_eq_mul, mul_one]
  rfl

/-- Every long interval has a uniformly small fraction of bad visits
outside one set with the explicit maximal-inequality bound. -/
theorem exists_flow_return_good_set
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    {Φ : ℝ → Y → Y} (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    (hzero : ∀ x, Φ 0 x = x) (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hpres : ∀ t, MeasurePreserving (Φ t) μ μ)
    {E : Set Y} (hE : MeasurableSet E) (c : ℝ) (hc : 0 < c) :
    ∃ G : Set Y, MeasurableSet G ∧ μ Gᶜ ≤ ENNReal.ofReal (2 * μ.real E / c) ∧
      ∀ x ∈ G, ∀ T : ℝ, 1 ≤ T →
        volume.real (Ioc 0 T ∩ {t | Φ t x ∈ E}) ≤ c * T := by
  obtain ⟨G, hG, hmass, hgood⟩ :=
    exists_flow_average_good_set μ hΦ hzero hadd hpres hE c hc
  refine ⟨G, hG, hmass, ?_⟩
  intro x hx T hT
  rw [← flow_occupation_eq_time_measure hΦ hE x T (by linarith)]
  exact hgood x hx T hT

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_CompactFlowReturns
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compact simultaneous returns outside a prescribed null set

A summable sequence of maximal-inequality exceptional sets gives one
conull set on which any two points return to a common compact set with
uniformly positive overlap. No ergodicity of the individual flow is used.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DukePrimeDegree

theorem exists_eventual_flow_good_sets
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ]
    {Φ : ℝ → Y → Y} (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    (hzero : ∀ x, Φ 0 x = x) (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hpres : ∀ t, MeasurePreserving (Φ t) μ μ)
    (K : ℕ → Set Y) (hK : ∀ m, MeasurableSet (K m))
    (hsmall : ∀ m, μ (K m)ᶜ < ENNReal.ofReal (((1 / 2 : ℝ) ^ m) / 8)) :
    ∃ G : ℕ → Set Y, (∀ m, MeasurableSet (G m)) ∧
      (∀ᵐ x ∂μ, ∀ᶠ m in atTop, x ∈ G m) ∧
      ∀ m x, x ∈ G m → ∀ T : ℝ, 1 ≤ T →
        volume.real (Ioc 0 T ∩ {t | Φ t x ∉ K m}) ≤ T / 4 := by
  have hG (m : ℕ) := exists_flow_return_good_set μ hΦ hzero hadd hpres
    (hK m).compl (1 / 4) (by norm_num)
  choose G hGmeas hGmass hgood using hG
  have hmass (m : ℕ) : μ (G m)ᶜ ≤ (2⁻¹ : ℝ≥0∞) ^ m := by
    have hr : μ.real (K m)ᶜ ≤ ((1 / 2 : ℝ) ^ m) / 8 := by
      have h := (ENNReal.toReal_le_toReal (measure_ne_top μ _)
        ENNReal.ofReal_ne_top).mpr (hsmall m).le
      rw [ENNReal.toReal_ofReal (by positivity)] at h
      exact h
    calc
      μ (G m)ᶜ ≤ ENNReal.ofReal (2 * μ.real (K m)ᶜ / (1 / 4)) := hGmass m
      _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ m) := ENNReal.ofReal_le_ofReal (by linarith)
      _ = (2⁻¹ : ℝ≥0∞) ^ m := by
        rw [ENNReal.ofReal_pow (by norm_num)]
        congr 1
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num
  have hs : (∑' m, μ (G m)ᶜ) ≠ ∞ := by
    apply ne_top_of_le_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    calc
      (∑' m, μ (G m)ᶜ) ≤ ∑' m, (2⁻¹ : ℝ≥0∞) ^ m := ENNReal.tsum_le_tsum hmass
      _ = 2 := ENNReal.tsum_geometric_two
  refine ⟨G, hGmeas, ?_, ?_⟩
  · simpa only [notMem_compl_iff] using (ae_eventually_notMem hs)
  · intro m x hx T hT
    simpa only [mem_compl_iff, one_div, div_eq_mul_inv, one_mul, mul_comm] using hgood m x hx T hT

theorem exists_compact_flow_return_family
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] [Measure.InnerRegularCompactLTTop μ]
    {Φ : ℝ → Y → Y} (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    (hzero : ∀ x, Φ 0 x = x) (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hpres : ∀ t, MeasurePreserving (Φ t) μ μ)
    (N : Set Y) (hN : MeasurableSet N) (hNzero : μ N = 0) :
    ∃ K G : ℕ → Set Y,
      (∀ m, IsCompact (K m) ∧ K m ⊆ Nᶜ ∧ MeasurableSet (G m)) ∧
      (∀ᵐ x ∂μ, ∀ᶠ m in atTop, x ∈ G m) ∧
      ∀ m x, x ∈ G m → ∀ T : ℝ, 1 ≤ T →
        volume.real (Ioc 0 T ∩ {t | Φ t x ∉ K m}) ≤ T / 4 := by
  have hK (m : ℕ) : ∃ K : Set Y, IsCompact K ∧ K ⊆ Nᶜ ∧
      μ Kᶜ < ENNReal.ofReal (((1 / 2 : ℝ) ^ m) / 8) := by
    have he : ENNReal.ofReal (((1 / 2 : ℝ) ^ m) / 8) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    obtain ⟨K, hKN, hK, hsmall⟩ := hN.compl.exists_isCompact_sdiff_lt
      (measure_ne_top μ Nᶜ) he
    refine ⟨K, hK, hKN, ?_⟩
    have hset : Nᶜ \ K = Kᶜ \ N := by ext x; simp only [Set.mem_sdiff, mem_compl_iff, and_comm]
    rwa [hset, measure_sdiff_null hNzero] at hsmall
  choose K hcompact hKN hsmall using hK
  obtain ⟨G, hG, hae, hgood⟩ := exists_eventual_flow_good_sets μ hΦ hzero hadd hpres
    K (fun m => (hcompact m).isClosed.measurableSet) hsmall
  exact ⟨K, G, fun m => ⟨hcompact m, hKN m, hG m⟩, hae, hgood⟩

theorem exists_late_simultaneous_compact_return
    {Y : Type*} (Φ : ℝ → Y → Y) (K : Set Y) (x y : Y)
    (hx : ∀ T : ℝ, 1 ≤ T →
      volume.real (Ioc 0 T ∩ {t | Φ t x ∉ K}) ≤ T / 4)
    (hy : ∀ T : ℝ, 1 ≤ T →
      volume.real (Ioc 0 T ∩ {t | Φ t y ∉ K}) ≤ T / 4)
    (R : ℝ) : ∃ t : ℝ, R < t ∧ Φ t x ∈ K ∧ Φ t y ∈ K := by
  let T : ℝ := 4 * (max R 1 + 1)
  have hT : 1 ≤ T := by dsimp [T] <;> linarith [le_max_right R 1]
  have hTpos : 0 < T := by linarith
  let A : Set ℝ := Ioc 0 T ∩ {t | Φ t x ∉ K}
  let B : Set ℝ := Ioc 0 T ∩ {t | Φ t y ∉ K}
  by_contra h
  have hcover : Ioc (T / 4) T ⊆ A ∪ B := by
    intro t ht
    have ht0 : t ∈ Ioc 0 T := ⟨by linarith [ht.1], ht.2⟩
    by_cases htx : Φ t x ∈ K
    · apply Or.inr
      refine ⟨ht0, ?_⟩
      intro hty
      apply h ⟨t, ?_, htx, hty⟩
      dsimp [T] at ht
      linarith [ht.1, le_max_left R 1]
    · exact Or.inl ⟨ht0, htx⟩
  have hsub : A ∪ B ⊆ Ioc 0 T := union_subset inter_subset_left inter_subset_left
  have hfinite : volume (A ∪ B) ≠ ∞ :=
    measure_ne_top_of_subset hsub (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hle := measureReal_mono hcover hfinite
  have hu := measureReal_union_le (μ := volume) A B
  have hAx : volume.real A ≤ T / 4 := hx T hT
  have hBy : volume.real B ≤ T / 4 := hy T hT
  rw [Real.volume_real_Ioc_of_le (by linarith : T / 4 ≤ T)] at hle
  linarith

theorem exists_conull_simultaneous_compact_returns
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] [Measure.InnerRegularCompactLTTop μ]
    {Φ : ℝ → Y → Y} (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    (hzero : ∀ x, Φ 0 x = x) (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hpres : ∀ t, MeasurePreserving (Φ t) μ μ)
    (N : Set Y) (hN : MeasurableSet N) (hNzero : μ N = 0) :
    ∃ M : Set Y, MeasurableSet M ∧ μ M = 0 ∧
      ∀ x ∉ M, ∀ y ∉ M, ∃ K : Set Y, IsCompact K ∧ K ⊆ Nᶜ ∧
        ∀ R : ℝ, ∃ t : ℝ, R < t ∧ Φ t x ∈ K ∧ Φ t y ∈ K := by
  obtain ⟨K, G, hKG, hae, hgood⟩ :=
    exists_compact_flow_return_family μ hΦ hzero hadd hpres N hN hNzero
  obtain ⟨M, hbad, hM, hMzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hae)
  refine ⟨M, hM, hMzero, ?_⟩
  intro x hx y hy
  have hxG : ∀ᶠ m in atTop, x ∈ G m := by
    by_contra h
    exact hx (hbad h)
  have hyG : ∀ᶠ m in atTop, y ∈ G m := by
    by_contra h
    exact hy (hbad h)
  obtain ⟨m, hxm, hym⟩ := (hxG.and hyG).exists
  exact ⟨K m, (hKG m).1, (hKG m).2.1,
    exists_late_simultaneous_compact_return Φ (K m) x y
      (hgood m x hxm) (hgood m y hym)⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_DiagonalFlowMaximal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform long-time returns for the diagonal flow

This specializes the proved maximal occupation bound to the actual
canonical diagonal flow on the arithmetic quotient.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma continuous_diagonalOneParameter {n : ℕ} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) : Continuous (diagonalOneParameter ell hell) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun t : ℝ => Matrix.diagonal (fun k => Real.exp (ell k * t)) i j)
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
    fun_prop
  · simp only [Matrix.diagonal_apply_ne _ hij]
    exact continuous_const

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LeafBoxSeparation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Pointwise separation of root fibers on a conull set

Coordinate disintegration gives one ambient null set outside which the
intrinsic leaf agrees with the chart leaf at every remaining point.
Within a fixed root box, equal leaves at points in one fiber then force
equal points in the noninvariant ergodic case. This strengthens the
conditional-almost-everywhere form needed in EKL (2006), Lemma 4.4(2).
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rootBox_exists_nullset_for_coordinates
    {n : ℕ} {i j k : Fin n} {hij : i ≠ j}
    (A : RootBox hij k) (μ : Measure (X n))
    (Q : RootSlice i j k × ℝ → Prop)
    (hQ : ∀ᵐ z ∂A.coordinateMeasure μ, Q z) :
    ∃ N : Set (X n), MeasurableSet N ∧ μ N = 0 ∧
      ∀ z ∈ A.domain, rootQuotientParametrization hij z ∉ N → Q z := by
  have hchart : ∀ᵐ x ∂μ.restrict A.range,
      ∀ z ∈ A.domain, rootQuotientParametrization hij z = x → Q z := by
    apply A.ae_of_coordinate μ
    filter_upwards [hQ, A.coordinateMeasure_ae_domain μ] with z hz hzd
    intro w hw heq
    have he : (⟨w, hw⟩ : A.domain) = ⟨z, hzd⟩ := A.embedding.injective heq
    have he' : w = z := congrArg Subtype.val he
    simpa only [he'] using hz
  have hall := (ae_restrict_iff' A.range_open.measurableSet).mp hchart
  obtain ⟨N, hbad, hN, hzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hall)
  refine ⟨N, hN, hzero, ?_⟩
  intro z hz hx
  by_contra h
  apply hx
  apply hbad
  intro H
  exact h (H ⟨⟨z, hz⟩, rfl⟩ z hz rfl)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_RootOrbitRebase
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rebasing at every pair outside a single null set

Countably many long root boxes turn coordinate disintegration into a
pointwise rebasing law along all root orbits. In particular, if a root
conditional is Dirac almost everywhere, one conull set meets each root
orbit at most once. This is the atomic case needed by the support argument.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rootBox_rebase_outside_nullset
    {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (A : RootBox hij k) (R : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0) :
    ∃ N : Set (X n), MeasurableSet N ∧ μ N = 0 ∧
      ∀ z ∈ A.domain, ∀ w ∈ A.domain,
        rootQuotientParametrization hij z ∉ N →
        rootQuotientParametrization hij w ∉ N → z.1 = w.1 →
        intrinsicRootLeaf hij μ (rootQuotientParametrization hij w) =
          basedRealMeasure (intrinsicRootLeaf hij μ (rootQuotientParametrization hij z))
            (w.2 - z.2) := by
  let Q := fun z : RootSlice i j k × ℝ =>
    intrinsicRootLeaf hij μ (rootQuotientParametrization hij z) = A.basedLeaf R μ z ∧
    IsLocallyFiniteMeasure (A.leafMeasure R μ z.1) ∧
    0 < A.leafMeasure R μ z.1 (Metric.ball z.2 1)
  have hQ : ∀ᵐ z ∂A.coordinateMeasure μ, Q z := by
    have hloc := ae_of_ae_map measurable_fst.aemeasurable
      ((A.ae_leafMeasure_spec R hAR μ hfree).mono fun _ h => h.1)
    filter_upwards [A.ae_intrinsicRootLeaf_coordinates R hAR μ hfree, hloc,
      A.ae_leafMeasure_ball_pos R hAR μ hfree] with z hz hl hp
    exact ⟨hz, hl, hp 1 zero_lt_one⟩
  obtain ⟨N, hN, hzero, hgood⟩ := rootBox_exists_nullset_for_coordinates A μ Q hQ
  refine ⟨N, hN, hzero, ?_⟩
  intro z hz w hw hzN hwN hbase
  have hgz := hgood z hz hzN
  have hgw := hgood w hw hwN
  let : IsLocallyFiniteMeasure (A.leafMeasure R μ z.1) := hgz.2.1
  rw [hgz.1, hgw.1]
  change basedRealMeasure (A.leafMeasure R μ w.1) w.2 =
    basedRealMeasure (basedRealMeasure (A.leafMeasure R μ z.1) z.2) (w.2 - z.2)
  rw [← hbase, basedRealMeasure_rebase _ _ _ hgz.2.2]
  congr 1
  ring

theorem exists_nullset_root_orbit_rebase
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∃ N : Set (X (d + 1)), MeasurableSet N ∧ μ N = 0 ∧ ∀ x ∉ N, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) ∉ N →
      intrinsicRootLeaf hij μ (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) =
        basedRealMeasure (intrinsicRootLeaf hij μ x) t := by
  have hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  let C := fun (k : Fin (d + 1)) (m : ℕ) => rootLongBoxFamily hij k 1 m
  let (k : Fin (d + 1)) (m : ℕ) : Countable (C k m) :=
    (rootLongBoxFamily_countable hij k 1 m).to_subtype
  let I := Σ k : Fin (d + 1), Σ m : ℕ, C k m
  let box := fun q : I => q.2.2.val
  have htime (q : I) : (box q).time ⊆ rootLeafWindow (1 + (q.2.1 : ℝ)) 0 := by
    rw [rootLongBoxFamily_time hij q.1 1 q.2.1 (box q) q.2.2.property]
    simp only [rootLeafWindow, Nat.cast_zero, add_zero, subset_refl]
  have hlocal (q : I) := rootBox_rebase_outside_nullset hij μ hfree (box q)
    (1 + (q.2.1 : ℝ)) (htime q)
  choose N hN hzero hrebase using hlocal
  obtain ⟨M, hbad, hM, hMzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hfree)
  let E := M ∪ ⋃ q : I, N q
  have hEzero : μ E = 0 := measure_union_null hMzero (measure_iUnion_null hzero)
  refine ⟨E, hM.union (MeasurableSet.iUnion hN), hEzero, ?_⟩
  intro x hx t hy
  have hxfree : ∀ u : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij u) = x → u = 0 := by
    by_contra h
    exact hx (Or.inl (hbad h))
  obtain ⟨k, B, z, hz⟩ := exists_rootBox_at hij x
  let s := z.val.1
  let v := z.val.2
  have hxparam : rootQuotientParametrization hij (s, v) = x := hz
  have hyparam : rootQuotientParametrization hij (s, v + t) =
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) := by
    rw [rootQuotientParametrization_add, hxparam]
  have hsfree := root_time_injective_of_free hij s v (by rwa [hxparam])
  obtain ⟨m, hm⟩ := exists_nat_gt (max |v| |v + t|)
  have hv : v ∈ rootLeafWindow 1 m := by
    apply abs_lt.mp
    exact (lt_of_le_of_lt (le_max_left _ _) hm).trans (by linarith)
  have hvt : v + t ∈ rootLeafWindow 1 m := by
    apply abs_lt.mp
    exact (lt_of_le_of_lt (le_max_right _ _) hm).trans (by linarith)
  obtain ⟨D, hD, hsD⟩ := rootLongBoxFamily_covers hij k 1 m s hsfree
  let q : I := ⟨k, m, ⟨D, hD⟩⟩
  have htD : D.time = rootLeafWindow 1 m := rootLongBoxFamily_time hij k 1 m D hD
  have hzD : (s, v) ∈ (box q).domain := ⟨hsD, htD.symm ▸ hv⟩
  have hwD : (s, v + t) ∈ (box q).domain := ⟨hsD, htD.symm ▸ hvt⟩
  have hNx : rootQuotientParametrization hij (s, v) ∉ N q := by
    rw [hxparam]
    exact fun h => hx (Or.inr (mem_iUnion.mpr ⟨q, h⟩))
  have hNy : rootQuotientParametrization hij (s, v + t) ∉ N q := by
    rw [hyparam]
    exact fun h => hy (Or.inr (mem_iUnion.mpr ⟨q, h⟩))
  have h := hrebase q (s, v) hzD (s, v + t) hwD hNx hNy rfl
  simpa only [hxparam, hyparam, add_sub_cancel_left] using h

lemma based_dirac_eq_self_only_at_zero (t : ℝ)
    (h : basedRealMeasure (Measure.dirac 0) t = Measure.dirac 0) : t = 0 := by
  by_contra ht
  have he := congrArg (fun ν : Measure ℝ => ν {0}) h
  change (centerRealMeasure (Measure.dirac 0) t (Metric.ball 0 1))⁻¹ *
    centerRealMeasure (Measure.dirac 0) t {0} = (Measure.dirac 0) {0} at he
  rw [centerRealMeasure_singleton, zero_add] at he
  simp [Ne.symm ht] at he

theorem exists_nullset_atomic_root_transversal
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hatom : ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x = Measure.dirac 0) :
    ∃ N : Set (X (d + 1)), MeasurableSet N ∧ μ N = 0 ∧ ∀ x ∉ N, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) ∉ N → t = 0 := by
  obtain ⟨N, hN, hNzero, hrebase⟩ := exists_nullset_root_orbit_rebase d hij μ hA
  obtain ⟨M, hbad, hM, hMzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hatom)
  refine ⟨N ∪ M, hN.union hM, measure_union_null hNzero hMzero, ?_⟩
  intro x hx t hy
  have hxatom : intrinsicRootLeaf hij μ x = Measure.dirac 0 := by
    by_contra h
    exact hx (Or.inr (hbad h))
  have hyatom : intrinsicRootLeaf hij μ
      (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) = Measure.dirac 0 := by
    by_contra h
    exact hy (Or.inr (hbad h))
  apply based_dirac_eq_self_only_at_zero
  simpa only [hxatom, hyatom] using
    (hrebase x (fun h => hx (Or.inl h)) t (fun h => hy (Or.inl h))).symm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingCollision
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compactness for pairs with equal leaf data

The last limiting step of the low-entropy argument: equal continuous
leaf data on a compact set survive a normalized shearing limit. This
isolates the compactness step from the return-time selection and the
horospherical separation argument in EKL (2006), Section 4.2.
-/

noncomputable section
open Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

theorem compact_equal_data_orbit_limit
    {n : ℕ} {Z : Type*} [TopologicalSpace Z] [T2Space Z]
    (K : Set (X n)) (hK : IsCompact K) (F : X n → Z) (hF : ContinuousOn F K)
    (x : ℕ → X n) (H : ℕ → G n) (h : G n)
    (hx : ∀ m, x m ∈ K) (hy : ∀ m, rightAction (x m) (H m) ∈ K)
    (heq : ∀ m, F (x m) = F (rightAction (x m) (H m)))
    (hH : Tendsto H atTop (𝓝 h)) :
    ∃ z ∈ K, rightAction z h ∈ K ∧ F z = F (rightAction z h) := by
  obtain ⟨z, hz, φ, hφ, hlim⟩ := hK.isSeqCompact hx
  have hxlim : Tendsto (x ∘ φ) atTop (𝓝 z) := hlim
  have hylim : Tendsto (fun m => rightAction (x (φ m)) (H (φ m)))
      atTop (𝓝 (rightAction z h)) :=
    (continuous_rightAction_uncurry n).continuousAt.tendsto.comp
      (hxlim.prodMk_nhds (hH.comp hφ.tendsto_atTop))
  have hzy : rightAction z h ∈ K := hK.isClosed.mem_of_tendsto hylim
    (Eventually.of_forall fun m => hy (φ m))
  have hFx : Tendsto (fun m => F (x (φ m))) atTop (𝓝 (F z)) :=
    (hF z hz).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hxlim, Eventually.of_forall fun m => hx (φ m)⟩)
  have hFy : Tendsto (fun m => F (rightAction (x (φ m)) (H (φ m))))
      atTop (𝓝 (F (rightAction z h))) :=
    (hF _ hzy).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hylim, Eventually.of_forall fun m => hy (φ m)⟩)
  have heq' : (fun m => F (x (φ m))) =
      (fun m => F (rightAction (x (φ m)) (H (φ m)))) := funext fun m => heq (φ m)
  exact ⟨z, hz, hzy, tendsto_nhds_unique hFx (heq' ▸ hFy)⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_AtomicRootLimits
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Atomic root leaves exclude nonzero diagonal limits

Compact simultaneous recurrence converts any root limit of diagonal
conjugates into two points on one root orbit in an atomic transversal.
Consequently the root parameter must vanish. Only invariance under the
diagonal group and atomicity of the specified root are used.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_nullset_atomic_root_limit_oai
    (d : ℕ) {a b : Fin (d + 1)} (hab : a ≠ b)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hatom : ∀ᵐ x ∂μ, intrinsicRootLeaf hab μ x = Measure.dirac 0)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ r, ell r = 0) :
    ∃ M : Set (X (d + 1)), MeasurableSet M ∧ μ M = 0 ∧
      ∀ x ∉ M, ∀ y ∉ M, ∀ g : G (d + 1), rightAction x g = y → ∀ c : ℝ,
        Tendsto (fun t : ℝ => diagonalOneParameter ell hell t * g *
          diagonalOneParameter ell hell (-t)) atTop
          (𝓝 (Matrix.SpecialLinearGroup.transvection hab c)) → c = 0 := by
  obtain ⟨N, hN, hNzero, htrans⟩ := exists_nullset_atomic_root_transversal d hab μ hA hatom
  let Φ : ℝ → X (d + 1) → X (d + 1) :=
    fun t x => rightAction x (diagonalOneParameter ell hell (-t))
  have hcont : Continuous (fun p : X (d + 1) × ℝ => Φ p.2 p.1) := by
    exact (continuous_rightAction_uncurry (d + 1)).comp
      (continuous_fst.prodMk ((continuous_diagonalOneParameter ell hell).comp continuous_snd.neg))
  have hzero (x : X (d + 1)) : Φ 0 x = x := by
    simp [Φ, diagonalOneParameter_zero]
  have hadd (s t : ℝ) (x : X (d + 1)) : Φ (s + t) x = Φ s (Φ t x) := by
    dsimp [Φ]
    rw [rightAction_mul, ← diagonalOneParameter_add]
    congr 2
    ring
  have hpres (t : ℝ) : MeasurePreserving (Φ t) μ μ := by
    refine ⟨(continuous_rightAction _).measurable, ?_⟩
    dsimp only [Φ]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  obtain ⟨M, hM, hMzero, hreturns⟩ := exists_conull_simultaneous_compact_returns
    μ hcont.measurable hzero hadd hpres N hN hNzero
  refine ⟨M, hM, hMzero, ?_⟩
  intro x hx y hy g hxy c hlim
  obtain ⟨K, hK, hKN, hret⟩ := hreturns x hx y hy
  have hseq (m : ℕ) : ∃ t : ℝ, (m : ℝ) < t ∧ Φ t x ∈ K ∧ Φ t y ∈ K := hret m
  choose t ht htx hty using hseq
  have htop : Tendsto t atTop atTop :=
    tendsto_atTop_mono (fun m => (ht m).le) tendsto_natCast_atTop_atTop
  let H : ℕ → G (d + 1) := fun m => diagonalOneParameter ell hell (t m) * g *
    diagonalOneParameter ell hell (-t m)
  have hpair (m : ℕ) : rightAction (Φ (t m) x) (H m) = Φ (t m) y := by
    rw [← hxy]
    dsimp only [Φ, H]
    rw [rightAction_mul, rightAction_mul]
    congr 1
    rw [diagonalOneParameter_neg]
    group
  obtain ⟨z, hz, hzc, _⟩ := compact_equal_data_orbit_limit K hK (fun _ => ())
    continuous_const.continuousOn (fun m => Φ (t m) x) H
    (Matrix.SpecialLinearGroup.transvection hab c) htx
    (fun m => by rw [hpair]; exact hty m) (fun _ => rfl) (hlim.comp htop)
  exact htrans z (hKN hz) c (hKN hzc)

end DukePrimeDegree

end

end OAI
end

theorem solution : type_of% @OAI.DukePrimeDegree.exists_nullset_atomic_root_limit_oai := @OAI.DukePrimeDegree.exists_nullset_atomic_root_limit_oai
